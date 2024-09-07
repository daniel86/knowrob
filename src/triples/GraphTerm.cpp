/*
 * This file is part of KnowRob, please consult
 * https://github.com/knowrob/knowrob for license details.
 */

#include <boost/python/suite/indexing/vector_indexing_suite.hpp>
#include "knowrob/triples/GraphTerm.h"
#include "knowrob/integration/python/utils.h"
#include "knowrob/triples/GraphSequence.h"
#include "knowrob/triples/GraphUnion.h"
#include "knowrob/triples/GraphPattern.h"
#include "knowrob/integration/python/converter/vector.h"
#include "knowrob/triples/GraphBuiltin.h"

using namespace knowrob;

namespace knowrob {
	std::shared_ptr<GraphTerm> applyBindings(const std::shared_ptr<GraphTerm> &term, const Bindings &bindings) {
		switch (term->termType()) {
			case GraphTermType::Pattern: {
				auto pattern = std::static_pointer_cast<GraphPattern>(term);
				auto orig = pattern->value();
				auto substituted = applyBindings(orig, bindings);
				if (orig != substituted) {
					return std::make_shared<GraphPattern>(substituted);
				}
			}
			case GraphTermType::Builtin: {
				auto builtin = std::static_pointer_cast<GraphBuiltin>(term);
				auto args = builtin->arguments();
				std::vector<TermPtr> newArgs;
				for (const auto &arg: args) {
					newArgs.push_back(applyBindings(arg, bindings));
				}
				return std::make_shared<GraphBuiltin>(builtin->builtinType(),
													  builtin->functor(),
													  newArgs,
													  builtin->bindVar());
			}
			case GraphTermType::Sequence: {
				auto sequence = std::static_pointer_cast<GraphSequence>(term);
				std::vector<std::shared_ptr<GraphTerm>> newTerms;
				for (const auto &subTerm: sequence->terms()) {
					newTerms.push_back(applyBindings(subTerm, bindings));
				}
				return std::make_shared<GraphSequence>(newTerms);
			}
			case GraphTermType::Union: {
				auto unionTerm = std::static_pointer_cast<GraphUnion>(term);
				std::vector<std::shared_ptr<GraphTerm>> newTerms;
				for (const auto &subTerm: unionTerm->terms()) {
					newTerms.push_back(applyBindings(subTerm, bindings));
				}
				return std::make_shared<GraphUnion>(newTerms);
			}
		}
		return term;
	}

	std::shared_ptr<GraphTerm> operator&(const std::shared_ptr<GraphTerm> &a, const std::shared_ptr<GraphTerm> &b) {
		if (a->termType() == GraphTermType::Sequence) {
			auto sequence = std::static_pointer_cast<GraphSequence>(a);
			auto terms = sequence->terms();
			terms.push_back(b);
			return std::make_shared<GraphSequence>(terms);
		} else {
			return std::make_shared<GraphSequence>(std::vector<std::shared_ptr<GraphTerm>>{a, b});
		}
	}

	std::shared_ptr<GraphTerm> operator|(const std::shared_ptr<GraphTerm> &a, const std::shared_ptr<GraphTerm> &b) {
		if (a->termType() == GraphTermType::Union) {
			auto unionTerm = std::static_pointer_cast<GraphUnion>(a);
			auto terms = unionTerm->terms();
			terms.push_back(b);
			return std::make_shared<GraphUnion>(terms);
		} else {
			return std::make_shared<GraphUnion>(std::vector<std::shared_ptr<GraphTerm>>{a, b});
		}
	}
}

namespace knowrob::py {
	std::shared_ptr<GraphTerm> applyBindings_graph(const std::shared_ptr<GraphTerm> &term, const Bindings &bindings) {
		return applyBindings(term, bindings);
	}

	template<>
	void createType<GraphTerm>() {
		using namespace boost::python;

		enum_<GraphTermType>("GraphTermType")
				.value("Sequence", GraphTermType::Sequence)
				.value("Union", GraphTermType::Union)
				.value("Pattern", GraphTermType::Pattern)
				.value("Builtin", GraphTermType::Builtin)
				.export_values();

		class_<GraphTerm, std::shared_ptr<GraphTerm>, boost::noncopyable>
				("GraphTerm", no_init)
				.def("isPattern", &GraphTerm::isPattern)
				.def("isBuiltin", &GraphTerm::isBuiltin)
				.def("termType", &GraphTerm::termType);

		class_<GraphPattern, bases<GraphTerm>, std::shared_ptr<GraphPattern>, boost::noncopyable>
				("GraphPattern", init<FramedTriplePatternPtr>())
				.def(init<const TermPtr &, const TermPtr &, const TermPtr &>())
				.def("value", &GraphPattern::value, return_value_policy<copy_const_reference>());

		createType<GraphUnion>();
		createType<GraphSequence>();
		createType<GraphBuiltin>();

		def("applyBindings", applyBindings_graph);
		// allow conversion between std::vector and python::list for FirstOrderLiteral objects.
		typedef std::vector<std::shared_ptr<GraphTerm>> GraphTermList;
		py::custom_vector_from_seq<std::shared_ptr<GraphTerm>>();
		boost::python::class_<GraphTermList>("GraphTermList").def(
				boost::python::vector_indexing_suite<GraphTermList, true>());
	}
}
