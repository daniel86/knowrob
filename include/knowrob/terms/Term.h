/*
 * This file is part of KnowRob, please consult
 * https://github.com/knowrob/knowrob for license details.
 */

#ifndef KNOWROB_TERM_H_
#define KNOWROB_TERM_H_

#include <set>
#include <memory>
#include <ostream>
#include "knowrob/Printable.h"

namespace knowrob {
	/**
	 * The type of a term.
	 */
	enum class TermType : uint8_t {
		/** atomic term */
		ATOMIC = 0,
		/** a variable */
		VARIABLE,
		/** compound term with functor and arguments */
		FUNCTION
	};

	/**
	 * Terms are used as components of formulas and are recursively
	 * constructed over the set of constants, variables, and function symbols.
	 */
	class Term : public Printable {
	public:
		explicit Term(TermType termType) : termType_(termType) {};

		virtual ~Term() = default;

		/**
		 * @param other another term
		 * @return true if both terms are equal
		 */
		bool operator==(const Term &other) const;

		/**
		 * @param other another term
		 * @return true if both terms are not equal
		 */
		bool operator!=(const Term &other) const { return !this->operator==(other); }

		/**
		 * @return the type of this term.
		 */
		TermType termType() const { return termType_; }

		/**
		 * @return true if this term has no variables.
		 */
		bool isGround() const { return variables().empty(); }

		/**
		 * @return true if this term is bound and not compound.
		 */
		bool isAtomic() const { return termType_ == TermType::ATOMIC; }

		/**
		 * @return true if this term is an atom.
		 */
		bool isAtom() const;

		/**
		 * @return true if this term is a variable.
		 */
		bool isVariable() const;

		/**
		 * @return true if this term is a function.
		 */
		bool isFunction() const;

		/**
		 * @return true if this term is a numeric.
		 */
		bool isNumeric() const;

		/**
		 * @return true if this term is a string.
		 */
		bool isString() const;

		/**
		 * @return true if this term is an IRI.
		 */
		bool isIRI() const { return isIRI_; }

		/**
		 * @return true if this term is a blank node.
		 */
		bool isBlank() const { return isBlank_; }

		/**
		 * @return the hash of this.
		 */
		size_t hash() const;

		/**
		 * @return set of variables of this term.
		 */
		virtual const std::set<std::string_view> &variables() const = 0;

	protected:
		static const std::set<std::string_view> noVariables_;
		const TermType termType_;
		bool isBlank_ = false;
		bool isIRI_ = false;
	};

	// alias declaration
	using TermPtr = std::shared_ptr<Term>;
}

#endif //KNOWROB_TERM_H_
