/*
 * This file is part of KnowRob, please consult
 * https://github.com/knowrob/knowrob for license details.
 */

#include "knowrob/formulas/FirstOrderLiteral.h"
#include "knowrob/integration/python/utils.h"

using namespace knowrob;

FirstOrderLiteral::FirstOrderLiteral(const PredicatePtr &predicate, bool isNegative)
		: predicate_(predicate),
		  isNegated_(isNegative) {}

/*
FirstOrderLiteral::FirstOrderLiteral(const FirstOrderLiteral &other, const Substitution &sub)
		: predicate_(std::static_pointer_cast<Predicate>(applyBindings(other.predicate_, sub))),
		  isNegated_(other.isNegated_) {}
*/

void FirstOrderLiteral::write(std::ostream &os) const {
	if (isNegated()) {
		os << "not(" << *predicate_ << ")";
	} else {
		os << *predicate_;
	}
}

namespace knowrob {
	FirstOrderLiteralPtr applyBindings(const FirstOrderLiteralPtr &lit, const Bindings &bindings) {
		auto predicate = std::static_pointer_cast<Predicate>(applyBindings(lit->predicate(), bindings));
		if (predicate != lit->predicate()) {
			return std::make_shared<FirstOrderLiteral>(predicate, lit->isNegated());
		}
		else {
			return lit;
		}
	}
}

namespace knowrob::py {
	template<>
	void createType<FirstOrderLiteral>() {
		using namespace boost::python;
		class_<FirstOrderLiteral, std::shared_ptr<FirstOrderLiteral>>
				("FirstOrderLiteral", init<const PredicatePtr &, bool>())
				.def("predicate", &FirstOrderLiteral::predicate, return_value_policy<copy_const_reference>())
				.def("isNegated", &FirstOrderLiteral::isNegated)
				.def("functor", &FirstOrderLiteral::functor, return_value_policy<copy_const_reference>())
				.def("arity", &FirstOrderLiteral::arity)
				.def("numVariables", &FirstOrderLiteral::numVariables);
	}
}
