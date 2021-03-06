/* 
 * Copyright (c) 2020, Daniel Beßler
 * All rights reserved.
 * 
 * This file is part of KnowRob, please consult
 * https://github.com/knowrob/knowrob for license details.
 */

#include <mongoc.h>
#include <sstream>

#include <rosprolog/rosprolog_kb/rosprolog_kb.h>

#include "knowrob/db/mongo/MongoInterface.h"
#include "knowrob/db/mongo/bson_pl.h"

static const mongoc_insert_flags_t INSERT_NO_VALIDATE_FLAG =
		(mongoc_insert_flags_t)MONGOC_INSERT_NO_VALIDATE;
static const mongoc_update_flags_t UPDATE_NO_VALIDATE_FLAG =
		(mongoc_update_flags_t)MONGOC_UPDATE_NO_VALIDATE;
static const mongoc_update_flags_t UPDATE_FLAGS =
		(mongoc_update_flags_t)(MONGOC_UPDATE_MULTI_UPDATE | UPDATE_NO_VALIDATE_FLAG);

static const PlAtom ATOM_minus("-");
static const PlAtom ATOM_insert("insert");
static const PlAtom ATOM_remove("remove");
static const PlAtom ATOM_update("update");

/*********************************/
/********** static functions *****/
/*********************************/

MongoInterface& MongoInterface::get()
{
	static MongoInterface the_iface;
	return the_iface;
}

mongoc_client_pool_t* MongoInterface::pool()
{
	return MongoInterface::get().pool_;
}

MongoCursor* MongoInterface::cursor_create(const char *db_name, const char *coll_name)
{
	MongoCursor *c = new MongoCursor(MongoInterface::pool(),db_name,coll_name);
	{
		std::lock_guard<std::mutex> scoped_lock(MongoInterface::get().mongo_mutex_);
		MongoInterface::get().cursors_[c->id()] = c;
	}
	return c;
}

void MongoInterface::cursor_destroy(const char *curser_id)
{
	std::string key(curser_id);
	MongoCursor *c;
	{
		std::lock_guard<std::mutex> scoped_lock(MongoInterface::get().mongo_mutex_);
		c = MongoInterface::get().cursors_[key];
		MongoInterface::get().cursors_.erase(key);
	}
	delete c;
}

MongoCursor* MongoInterface::cursor(const char *curser_id)
{
	MongoCursor *c;
	{
		std::lock_guard<std::mutex> scoped_lock(MongoInterface::get().mongo_mutex_);
		c = MongoInterface::get().cursors_[std::string(curser_id)];
	}
	return c;
}

MongoCollection* MongoInterface::get_collection(const char *db_name, const char *coll_name)
{
	return new MongoCollection(MongoInterface::get().pool_,db_name,coll_name);
}

MongoWatch* MongoInterface::get_watch()
{
	return MongoInterface::get().watch_;
}

/*********************************/
/********** MongoInterface *******/
/*********************************/

MongoInterface::MongoInterface()
{
	mongoc_init();
	bson_error_t err;
	std::string mongo_uri;
	if(!rosprolog_kb::node().getParam(std::string("mongodb_uri"),mongo_uri)) {
		char *mongo_host = std::getenv("KNOWROB_MONGO_HOST");
		if(mongo_host != NULL) {
			char *mongo_user_name = std::getenv("KNOWROB_MONGO_USER");
			char *mongo_user_pw = std::getenv("KNOWROB_MONGO_PASS");
			char *mongo_database = std::getenv("KNOWROB_MONGO_DB");
			char *mongo_port = std::getenv("KNOWROB_MONGO_PORT");
			std::stringstream ss;
			ss << "mongodb://" << mongo_user_name << ":" << mongo_user_pw 
				<< "@" << mongo_host << ":" << mongo_port << "/" << mongo_database
				// FIXME: this should be a parameter
				//<< "?authSource=admin"
				;
			mongo_uri = ss.str();
		}
		else {
			mongo_uri = std::string("mongodb://localhost:27017/?appname=knowrob");
		}
	}
	uri_ = mongoc_uri_new_with_error(mongo_uri.c_str(),&err);
	if(!uri_) {
		throw MongoException("invalid_uri",err);
	}
	pool_ = mongoc_client_pool_new(uri_);
	mongoc_client_pool_set_error_api(pool_, 2);
	watch_ = new MongoWatch(pool_);
}

MongoInterface::~MongoInterface()
{
	if(watch_ != NULL) {
		delete watch_;
		watch_ = NULL;
	}
	mongoc_client_pool_destroy(pool_);
	mongoc_uri_destroy(uri_);
	mongoc_cleanup();
}

void MongoInterface::drop(const char *db_name, const char *coll_name)
{
	MongoCollection coll(pool_,db_name,coll_name);
	bson_error_t err;
	if(!mongoc_collection_drop(coll(),&err)) {
		throw MongoException("drop_failed",err);
	}
}

void MongoInterface::store(
		const char *db_name,
		const char *coll_name,
		const PlTerm &doc_term)
{
	MongoCollection coll(pool_,db_name,coll_name);
	bson_error_t err;
	//
	bson_t *doc = bson_new();
	if(!bsonpl_concat(doc,doc_term,&err)) {
		bson_destroy(doc);
		throw MongoException("invalid_term",err);
	}
	bool success = mongoc_collection_insert(coll(),INSERT_NO_VALIDATE_FLAG,doc,NULL,&err);
	bson_destroy(doc);
	if(!success) {
		throw MongoException("insert_failed",err);
	}
}

void MongoInterface::remove(
		const char *db_name,
		const char *coll_name,
		const PlTerm &doc_term)
{
	MongoCollection coll(pool_,db_name,coll_name);
	bson_error_t err;
	//
	bson_t *doc = bson_new();
	if(!bsonpl_concat(doc,doc_term,&err)) {
		bson_destroy(doc);
		throw MongoException("invalid_term",err);
	}
	bool success = mongoc_collection_remove(coll(),MONGOC_REMOVE_NONE,doc,NULL,&err);
	bson_destroy(doc);
	if(!success) {
		throw MongoException("collection_remove",err);
	}
}

void MongoInterface::bulk_write(
		const char *db_name,
		const char *coll_name,
		const PlTerm &doc_term)
{
	MongoCollection coll(pool_,db_name,coll_name);
	bson_t reply;
	// bulk options: set ordered to false to allow server performing
	//               the steps in parallel
	bson_t opts = BSON_INITIALIZER;
	BSON_APPEND_BOOL(&opts, "ordered", false);
	// create the bulk operation
	mongoc_bulk_operation_t *bulk =
			mongoc_collection_create_bulk_operation_with_opts(coll(), NULL);
	// iterate over input list and insert steps
	PlTail pl_list(doc_term);
	PlTerm pl_member;
	while(pl_list.next(pl_member)) {
		const PlAtom operation_name(pl_member.name());
		const PlTerm &pl_value1 = pl_member[1];
		bool is_operation_queued = false;
		bson_error_t err;
		// parse the document
		bson_t *doc1 = bson_new();
		if(!bsonpl_concat(doc1,pl_value1,&err)) {
			bson_destroy(doc1);
			mongoc_bulk_operation_destroy(bulk);
			throw MongoException("invalid_term",err);
		}
		if(operation_name == ATOM_insert) {
			is_operation_queued = mongoc_bulk_operation_insert_with_opts(
					bulk, doc1, NULL, &err);
		}
		else if(operation_name == ATOM_remove) {
			is_operation_queued = mongoc_bulk_operation_remove_many_with_opts(
					bulk, doc1, NULL, &err);
		}
		else if(operation_name == ATOM_update) {
			const PlTerm &pl_value2 = pl_member[2];
			bson_t *doc2 = bson_new();
			if(!bsonpl_concat(doc2,pl_value2,&err)) {
				bson_destroy(doc1);
				bson_destroy(doc2);
				mongoc_bulk_operation_destroy(bulk);
				throw MongoException("invalid_term",err);
			}
			is_operation_queued = mongoc_bulk_operation_update_many_with_opts(
					bulk, doc1, doc2, NULL, &err);
			bson_destroy(doc2);
		}
		else {
			bson_set_error(&err,
					MONGOC_ERROR_COMMAND,
					MONGOC_ERROR_COMMAND_INVALID_ARG,
					"unknown bulk operation '%s'", pl_member.name());
		}
		bson_destroy(doc1);
		if(!is_operation_queued) {
			mongoc_bulk_operation_destroy(bulk);
			throw MongoException("bulk_operation",err);
		}
	}
	bson_error_t bulk_err;
	// perform the bulk write
	bool success = mongoc_bulk_operation_execute(bulk, &reply, &bulk_err);
	// cleanup
	bson_destroy(&reply);
	mongoc_bulk_operation_destroy(bulk);
	// throw exception on error
	if(!success) {
		throw MongoException("bulk_operation",bulk_err);
	}
}

void MongoInterface::update(
		const char *db_name,
		const char *coll_name,
		const PlTerm &query_term,
		const PlTerm &update_term)
{
	MongoCollection coll(pool_,db_name,coll_name);
	bson_error_t err;
	//
	bson_t *query = bson_new();
	if(!bsonpl_concat(query,query_term,&err)) {
		bson_destroy(query);
		throw MongoException("invalid_query",err);
	}
	bson_t *update = bson_new();
	if(!bsonpl_concat(update,update_term,&err)) {
		bson_destroy(query);
		bson_destroy(update);
		throw MongoException("invalid_update",err);
	}
	bool success = mongoc_collection_update(coll(),
		UPDATE_FLAGS,
		query,
		update,
		NULL,
		&err);
	bson_destroy(query);
	bson_destroy(update);
	if(!success) {
		throw MongoException("update_failed",err);
	}
}

void MongoInterface::create_index(const char *db_name, const char *coll_name, const PlTerm &keys_pl)
{
	MongoDatabase db_handle(pool_,db_name);
	bson_t reply;
	bson_error_t err;
	bson_t keys;
	//
	bson_init(&keys);
	PlTail pl_list(keys_pl);
	PlTerm pl_member;
	while(pl_list.next(pl_member)) {
		const PlAtom mode_atom(pl_member.name());
		const PlTerm &pl_value = pl_member[1];
		if(mode_atom == ATOM_minus) {
			BSON_APPEND_INT32(&keys, (char*)pl_value, -1);
		}
		else {
			BSON_APPEND_INT32(&keys, (char*)pl_value, 1);
		}
	}
	char *index_name = mongoc_collection_keys_to_index_string(&keys);
	//
	bson_t *cmd = BCON_NEW ("createIndexes", BCON_UTF8(coll_name),
				 "indexes", "[", "{",
						 "key",  BCON_DOCUMENT(&keys),
						 "name", BCON_UTF8(index_name),
					"}",  "]"
	);
	bool success = mongoc_database_write_command_with_opts (
				db_handle(), cmd, NULL /* opts */, &reply, &err);
	bson_free(index_name);
	bson_destroy(&reply);
	bson_destroy(cmd);
	if(!success) {
		throw MongoException("create_index_failed",err);
	}
}
