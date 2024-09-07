/*
 * This file is part of KnowRob, please consult
 * https://github.com/knowrob/knowrob for license details.
 */

#ifndef KNOWROB_H_
#define KNOWROB_H_

#include <cstdlib>
#include <sstream>
#include <string>
#include "knowrob/terms/IRIAtom.h"

namespace knowrob {
	/**
	 * Static initialization of the knowledge base.
	 * Note that it is important that argv[0] holds the name
	 * of the executable.
	 * @param argc number of arguments in argv.
	 * @param argv array of program arguments, argv[0] is the name of the binary.
	 * @param initPython whether to initialize the Python module.
	 */
	void InitKnowRob(int argc, char **argv, bool initPython = true);

	/**
	 * Shutdown the knowledge base.
	 * This will ensure that all worker threads in the global DefaultThreadPool
	 * are joined.
	 * It is best to call this before exiting an application to avoid
	 * shutdown-crashes due to static resources associated with the main thread
	 * being destroyed before the worker threads (this is the case for spdlog).
	 */
	void ShutdownKnowRob();

	/**
	 * @return the name of the executable in which the knowledge base is running.
	 */
	char *getNameOfExecutable();

	/**
	 * Combine a hash value with another value.
	 * @param seed a hash value.
	 * @param v a value to combine with the seed.
	 */
	void hashCombine(std::size_t &seed, const std::size_t &v);

	/**
	 * Insert a unique identifier into a stream.
	 * @param os the output stream.
	 */
	void insertUnique(std::ostream &os);

	namespace py {
		/**
		 * Initialize the Python module.
		 */
		void staticKnowRobModuleInit();
	}

	/**
	 * Global settings for the knowledge base.
	 */
	class GlobalSettings {
	public:
		/**
		 * @return the batch size.
		 */
		static uint32_t batchSize() { return batchSize_; }

		/**
		 * The size of the container used when triples are processed in batches.
		 * @param batchSize the batch size for the backend.
		 */
		static void setBatchSize(uint32_t batchSize) { batchSize_ = batchSize; }

		/**
		 * @return the ego IRI atom.
		 */
		static IRIAtomPtr egoIRI() { return egoIRI_; }

		/**
		 * Set the egoIRI atom.
		 * @param egoIRI the ego IRI atom.
		 */
		static void setEgoIRI(const IRIAtomPtr &egoIRI) { egoIRI_ = egoIRI; }

	protected:
		static uint32_t batchSize_;
		static IRIAtomPtr egoIRI_;
	};
}

#endif //KNOWROB_H_
