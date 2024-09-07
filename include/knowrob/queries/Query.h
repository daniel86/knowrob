/*
 * This file is part of KnowRob, please consult
 * https://github.com/knowrob/knowrob for license details.
 */

#ifndef KNOWROB_QUERY_H_
#define KNOWROB_QUERY_H_

#include <ostream>
#include <knowrob/formulas/Formula.h>
#include "QueryContext.h"

namespace knowrob {
	/**
	 * @return a query context that selects the default graph, i.e. the one that represents
	 *          the current state of the world from the perspective of the robot.
	 */
	QueryContextPtr DefaultQueryContext();

	/**
	 * @return same as DefaultQueryContext() but with the QUERY_FLAG_ONE_SOLUTION flag set.
	 */
	QueryContextPtr OneSolutionContext();

	/**
	 * A baseclass for queries. The only commitment is that queries are evaluated
	 * within a certain context. The context defines additional parameters for the evaluation.
	 */
	class Query : public Printable {
	public:
		/**
		 * @param ctx the query context.
		 */
		explicit Query(QueryContextPtr ctx = DefaultQueryContext()) : ctx_(std::move(ctx)) {}

		virtual ~Query() = default;

		/**
		 * @return the query context.
		 */
		auto &ctx() const { return ctx_; }

		/**
		 * @param ctx the query context.
		 */
		void setContext(QueryContextPtr ctx) { ctx_ = std::move(ctx); }

	protected:
		QueryContextPtr ctx_;
	};
}

#endif //KNOWROB_QUERY_H_
