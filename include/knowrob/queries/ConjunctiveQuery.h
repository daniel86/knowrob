/*
 * This file is part of KnowRob, please consult
 * https://github.com/knowrob/knowrob for license details.
 */

#ifndef KNOWROB_CONJUNCTIVE_QUERY_H
#define KNOWROB_CONJUNCTIVE_QUERY_H

#include "knowrob/queries/Query.h"
#include "knowrob/triples/GraphTerm.h"
#include "knowrob/triples/FramedTriplePattern.h"
#include "knowrob/formulas/SimpleConjunction.h"

namespace knowrob {
	/**
	 * A Query that is constructed from a sequence of literals which are considered to be in a conjunction.
	 * The literals are part of a dependency group, meaning that they are connected through free variables.
	 */
	class ConjunctiveQuery : public Query {
	public:
		/**
		 * @param query an ordered sequence of triple patterns.
		 * @param ctx the query context.
		 */
		explicit ConjunctiveQuery(const std::vector<FirstOrderLiteralPtr> &query,
								  const QueryContextPtr &ctx = DefaultQueryContext());

		/**
		 * @param query a single triple pattern.
		 * @param ctx the query context.
		 */
		explicit ConjunctiveQuery(const FirstOrderLiteralPtr &query, const QueryContextPtr &ctx);

		/**
		 * @return the formula of the query.
		 */
		auto &formula() const { return formula_; }

		/**
		 * @return the literals of the formula.
		 */
		auto &literals() const { return formula_->literals(); }

		// Override Printable
		void write(std::ostream &os) const override;

	protected:
		SimpleConjunctionPtr formula_;

		explicit ConjunctiveQuery(const QueryContextPtr &ctx = DefaultQueryContext()) : Query(ctx) {}
	};

	// A shared pointer to a GraphQuery
	using ConjunctiveQueryPtr = std::shared_ptr<ConjunctiveQuery>;

} // knowrob

#endif //KNOWROB_CONJUNCTIVE_QUERY_H
