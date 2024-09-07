/*
 * This file is part of KnowRob, please consult
 * https://github.com/knowrob/knowrob for license details.
 */

#include "knowrob/reasoner/Goal.h"
#include "knowrob/integration/python/utils.h"
#include "knowrob/queries/AnswerYes.h"
#include "knowrob/reasoner/RDFGoal.h"

using namespace knowrob;

// make sure bindings only contains variables that are in vars
static BindingsPtr includeOnly(const BindingsPtr &bindings, const std::set<std::string_view> &vars) {
	// test if bindings has variables that are not in vars
	bool hasExtraVars = bindings->size() > vars.size();
	if (!hasExtraVars) {
		for (const auto &var : *bindings) {
			if (vars.find(var.first) == vars.end()) {
				hasExtraVars = true;
				break;
			}
		}
	}
	if (hasExtraVars) {
		// bindings has extra variables, filter them
		auto filtered = std::make_shared<Bindings>();
		for (const auto &var : vars) {
			auto it = bindings->find(var);
			if (it != bindings->end()) {
				filtered->set(it->second.first, it->second.second);
			}
		}
		return filtered;
	} else {
		return bindings;
	}
}

static BindingsPtr includeOnly(const BindingsPtr &bindings, const SimpleConjunctionPtr &formula) {
	std::set<std::string_view> vars;
	for (const auto &lit : formula->literals()) {
		for (const auto &var : lit->predicate()->variables()) {
			vars.insert(var);
		}
	}
	return includeOnly(bindings, vars);
}

Goal::Goal(SimpleConjunctionPtr formula, const Goal &goal)
		: Query(goal.ctx_),
		  formula_(std::move(formula)),
		  ctx_(goal.ctx_),
		  answerBuffer_(goal.answerBuffer_),
		  outputChannel_(goal.outputChannel_) {}

Goal::Goal(SimpleConjunctionPtr formula, QueryContextPtr ctx)
		: Query(ctx),
		  formula_(std::move(formula)),
		  ctx_(std::move(ctx)),
		  answerBuffer_(std::make_shared<TokenBuffer>()),
		  outputChannel_(TokenStream::Channel::create(answerBuffer_)) {}

Goal::Goal(const FirstOrderLiteralPtr &literal, QueryContextPtr ctx)
		: Query(ctx),
		  formula_(std::make_shared<SimpleConjunction>(literal)),
		  ctx_(std::move(ctx)),
		  answerBuffer_(std::make_shared<TokenBuffer>()),
		  outputChannel_(TokenStream::Channel::create(answerBuffer_)) {}

Goal::~Goal() {
	outputChannel_->close();
}

void Goal::push(const AnswerPtr &answer) {
	outputChannel_->push(answer);
}

void Goal::push(const BindingsPtr &bindings) {
	auto filteredBindings = includeOnly(bindings, formula_);
	auto yes = std::make_shared<AnswerYes>(filteredBindings);
	for (const auto &lit : formula_->literals()) {
		auto instance = applyBindings(lit->predicate(), *filteredBindings);
		yes->addGrounding(std::static_pointer_cast<Predicate>(instance), lit->isNegated());
	}
	push(yes);
}

namespace knowrob::py {
	template<>
	void createType<Goal>() {
		using namespace boost::python;

		using Push1 = void (Goal::*)(const AnswerPtr &);
		using Push2 = void (Goal::*)(const BindingsPtr &);

		class_<Goal, std::shared_ptr<Goal>, boost::noncopyable>
				("Goal", init<FramedTriplePatternPtr, QueryContextPtr>())
				.def("formula", &Goal::formula, return_value_policy<copy_const_reference>())
				.def("answerBuffer", &Goal::answerBuffer, return_value_policy<copy_const_reference>())
				.def("ctx", &Query::ctx, return_value_policy<copy_const_reference>())
				.def("push", with<no_gil>(static_cast<Push1>(&Goal::push)))
				.def("push", with<no_gil>(static_cast<Push2>(&Goal::push)));
		createType<RDFGoal>();
	}
}
