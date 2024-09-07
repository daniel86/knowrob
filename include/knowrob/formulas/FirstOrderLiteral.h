/*
 * This file is part of KnowRob, please consult
 * https://github.com/knowrob/knowrob for license details.
 */

#ifndef KNOWROB_FIRST_ORDER_LITERAL_H
#define KNOWROB_FIRST_ORDER_LITERAL_H

#include <memory>
#include "Predicate.h"
#include "knowrob/triples/FramedTriple.h"

namespace knowrob {
	/**
	 * A FOL literal is an atomic formula or its negation.
	 */
	class FirstOrderLiteral : public Printable {
	public:
		FirstOrderLiteral(const PredicatePtr &predicate, bool isNegative);

		/**
		 * @return the predicate of this literal.
		 */
		const auto &predicate() const { return predicate_; }

		/**
		 * @return true if this is a negative literal.
		 */
		auto isNegated() const { return isNegated_; }

		/**
		 * Set the negated flag of this literal.
		 * @param isNegated true indicates the literal is negated.
		 */
		void setIsNegated(bool isNegated) { isNegated_ = isNegated; }

		/**
		 * Get the functor of this literal.
		 *
		 * @return the functor name.
		 */
		auto &functor() const { return predicate_->functor(); }

		/**
		 * Get the arity of this predicate.
		 *
		 * @return arity of predicate
		 */
		auto arity() const { return predicate_->arity(); }

		/**
		 * @return The number of variables contained in this literal.
		 */
		virtual uint32_t numVariables() const { return predicate_->variables().size(); }

		// Printable interface
		void write(std::ostream &os) const override;

	protected:
		const PredicatePtr predicate_;
		bool isNegated_;
	};

	using FirstOrderLiteralPtr = std::shared_ptr<FirstOrderLiteral>;

	/**
	 * Apply a substitution to a FOL literal.
	 * @param lit the FOL literal.
	 * @param bindings the substitution.
	 * @return the literal with the substitution applied.
	 */
	FirstOrderLiteralPtr applyBindings(const FirstOrderLiteralPtr &lit, const Bindings &bindings);

} // knowrob

#endif //KNOWROB_FIRST_ORDER_LITERAL_H
