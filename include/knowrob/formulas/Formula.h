/*
 * This file is part of KnowRob, please consult
 * https://github.com/knowrob/knowrob for license details.
 */

#ifndef KNOWROB_FORMULA_H_
#define KNOWROB_FORMULA_H_

#include <memory>
#include <ostream>
#include "knowrob/Printable.h"

namespace knowrob {
	/**
	 * The type of a formula.
	 */
	enum class FormulaType {
		// A formula of the form `P(t_1,..,t_n)` where each ti is a term
		// and "P" is a n-ary predicate symbol (or functor).
		PREDICATE,
		// A formula of the form `phi_1 AND ... AND phi_n` where each phi_i is a formula.
		CONJUNCTION,
		// A formula of the form `phi_1 OR ... OR phi_n` where each phi_i is a formula.
		DISJUNCTION,
		NEGATION,
		IMPLICATION,
		MODAL
	};

	/**
	 * A propositional formula.
	 * Note that all formulas are immutable.
	 */
	class Formula : public Printable {
	public:
		/**
		 * @param type the type of the formula.
		 */
		explicit Formula(const FormulaType &type);

		virtual ~Formula() = default;

		/**
		 * @param other another formula
		 * @return true if both formulas are syntactically equal
		 */
		bool operator==(const Formula &other) const;

		/**
		 * @return the type of this formula.
		 */
		FormulaType type() const { return type_; }

		/**
		 * Is this formula free of subformulas?
		 *
		 * @return true if this formula is atomic.
		 */
		bool isAtomic() const;

		/**
		 * @return true if this formula isMoreGeneralThan no free variables.
		 */
		bool isGround() const { return isGround_; }

		/**
		 * @return true if this is the top concept.
		 */
		bool isTop() const;

		/**
		 * @return true if this is the bottom concept.
		 */
		bool isBottom() const;

	protected:
		const FormulaType type_;
		bool isGround_ = true;

		virtual bool isEqual(const Formula &other) const = 0;
	};

	/**
	 * A label for a formula.
	 */
	class FormulaLabel {
	public:
		FormulaLabel() = default;

		bool operator==(const FormulaLabel &other);

	protected:
		virtual bool isEqual(const FormulaLabel &other) const = 0;
	};

	// alias declaration
	using FormulaPtr = std::shared_ptr<Formula>;
	using FormulaLabelPtr = std::shared_ptr<FormulaLabel>;
}

#endif //KNOWROB_FORMULA_H_
