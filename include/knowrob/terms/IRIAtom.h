/*
 * This file is part of KnowRob, please consult
 * https://github.com/knowrob/knowrob for license details.
 */

#ifndef KNOWROB_IRI_ATOM_H
#define KNOWROB_IRI_ATOM_H

#include "Atom.h"
#include "RDFNode.h"
#include "knowrob/formulas/Predicate.h"

namespace knowrob {
	/**
	 * An IRI (Internationalized Resource Identifier) within an RDF graph is a Unicode string
	 * that conforms to the syntax defined in RFC 3987.
	 */
	class IRIAtom : public Atom, public RDFNode {
	public:
		/**
		 * Constructs an IRI atom from a string.
		 * @param stringForm the string form of the IRI
		 */
		explicit IRIAtom(std::string_view stringForm)
				: Atom(stringForm, AtomType::IRI),
				  RDFNode(RDFNodeType::IRI) {
			isIRI_ = true;
		}

		/**
		 * @param stringForm the string form of the IRI
		 * @return a shared pointer to an IRI atom
		 */
		static std::shared_ptr<IRIAtom> Tabled(std::string_view stringForm);

		/**
		 * Constructs a predicate from this IRI atom and the given terms.
		 * @param s the subject term
		 * @param o the object term
		 * @return a shared pointer to a predicate
		 */
		PredicatePtr operator()(const TermPtr &s, const TermPtr &o) const;

		/**
		 * Constructs a predicate from this IRI atom and the given term.
		 * @param s the subject term
		 * @return a shared pointer to a predicate
		 */
		PredicatePtr operator()(const TermPtr &s) const;

		// override Printable
		void write(std::ostream &os) const override;

	protected:
	};

	using IRIAtomPtr = std::shared_ptr<IRIAtom>;

	/**
	 * Create an IRI atom.
	 * @param ns the namespace of the IRI
	 * @param name the name of the IRI
	 * @return the IRI atom
	 */
	IRIAtomPtr iri(std::string_view ns, std::string_view name);

} // knowrob


#endif //KNOWROB_IRI_ATOM_H
