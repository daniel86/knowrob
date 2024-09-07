/*
 * This file is part of KnowRob, please consult
 * https://github.com/knowrob/knowrob for license details.
 */

#ifndef KNOWROB_GRAPH_TERM_H
#define KNOWROB_GRAPH_TERM_H

#include <iostream>
#include <knowrob/terms/Bindings.h>

namespace knowrob {
	/**
	 * The type of a graph term.
	 */
	enum class GraphTermType {
		Sequence,
		Union,
		Pattern,
		Builtin
	};

	/**
	 * A term in a graph query.
	 */
	class GraphTerm : public Printable {
	public:
		virtual ~GraphTerm() = default;

		/**
		 * @return true if the term is a pattern term.
		 */
		bool isPattern() const { return termType_ == GraphTermType::Pattern; }

		/**
		 * @return true if the term is a builtin term.
		 */
		bool isBuiltin() const { return termType_ == GraphTermType::Builtin; }

		/**
		 * @return the type of this graph term.
		 */
		auto termType() const { return termType_; }

		virtual void write(std::ostream &os) const = 0;

	protected:
		GraphTermType termType_;

		explicit GraphTerm(GraphTermType termType) : termType_(termType) {}

		friend class GraphQuery;
	};

} // knowrob

namespace knowrob {
	std::shared_ptr<GraphTerm> applyBindings(const std::shared_ptr<GraphTerm> &term, const Bindings &bindings);

	std::shared_ptr<GraphTerm> operator&(const std::shared_ptr<GraphTerm> &a, const std::shared_ptr<GraphTerm> &b);

	std::shared_ptr<GraphTerm> operator|(const std::shared_ptr<GraphTerm> &a, const std::shared_ptr<GraphTerm> &b);
}

#endif //v
