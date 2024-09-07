/*
 * This file is part of KnowRob, please consult
 * https://github.com/knowrob/knowrob for license details.
 */

#include <knowrob/formulas/Formula.h>
#include "knowrob/formulas/Top.h"
#include "knowrob/formulas/Bottom.h"
#include "knowrob/integration/python/utils.h"
#include "knowrob/formulas/CompoundFormula.h"
#include "knowrob/formulas/Negation.h"
#include "knowrob/formulas/Implication.h"
#include "knowrob/formulas/Disjunction.h"
#include "knowrob/formulas/ModalFormula.h"
#include "knowrob/formulas/FirstOrderLiteral.h"
#include "knowrob/formulas/PredicateIndicator.h"
#include "knowrob/formulas/Conjunction.h"
#include "knowrob/knowrob.h"

using namespace knowrob;

Formula::Formula(const FormulaType &type)
		: type_(type) {}

bool Formula::operator==(const Formula &other) const {
	// note: isEqual can safely perform static cast as type id's do match
	return typeid(*this) == typeid(other) && isEqual(other);
}

bool Formula::isAtomic() const {
	return type() == FormulaType::PREDICATE;
}

bool Formula::isBottom() const {
	return (this == Bottom::get().get());
}

bool Formula::isTop() const {
	return (this == Top::get().get());
}

bool FormulaLabel::operator==(const FormulaLabel &other) {
	return typeid(*this) == typeid(other) && isEqual(other);
}

namespace knowrob::py {
	template<>
	void createType<Formula>() {
		using namespace boost::python;
		enum_<FormulaType>("FormulaType")
				.value("PREDICATE", FormulaType::PREDICATE)
				.value("CONJUNCTION", FormulaType::CONJUNCTION)
				.value("DISJUNCTION", FormulaType::DISJUNCTION)
				.value("NEGATION", FormulaType::NEGATION)
				.value("IMPLICATION", FormulaType::IMPLICATION)
				.value("MODAL", FormulaType::MODAL)
				.export_values();
		class_<Formula, std::shared_ptr<Formula>, boost::noncopyable>
				("Formula", no_init)
				.def("type", &Formula::type)
				.def("__eq__", &Formula::operator==)
				.def("__repr__", &Formula::format)
				.def("isGround", &Formula::isGround)
				.def("isAtomic", &Formula::isAtomic)
				.def("isTop", &Formula::isTop)
				.def("isBottom", &Formula::isBottom);

		py::createType<CompoundFormula>();
		py::createType<Negation>();
		py::createType<Conjunction>();
		py::createType<Disjunction>();
		py::createType<Implication>();
		py::createType<Predicate>();
		py::createType<Bottom>();
		py::createType<Top>();
		py::createType<ModalFormula>();
		py::createType<FirstOrderLiteral>();
		py::createType<PredicateIndicator>();
	}
}
