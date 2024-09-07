/*
 * This file is part of KnowRob, please consult
 * https://github.com/knowrob/knowrob for license details.
 */

#include "iomanip"
#include "knowrob/triples/GraphSelector.h"
#include "knowrob/knowrob.h"
#include "knowrob/integration/python/utils.h"

using namespace knowrob;

bool GraphSelector::mergeWith(const GraphSelector &other) {
	uncertain = uncertain || other.uncertain;
	occasional = occasional || other.occasional;

	// graph selector changes to wildcard if graph of the other selector is different
	if (!graph || !other.graph || *graph != *other.graph) {
		graph = nullptr;
	}

	// agent cannot be changed in merge operation.
	// So GraphSelector can only be merged within a modal in which both are embedded.
	if (perspective) {
		if (other.perspective) {
			if (perspective->iri() != other.perspective->iri()) {
				return false;
			}
		} else {
			return false;
		}
	} else if (other.perspective) {
		return false;
	}

	// later begin time is more restrictive
	if (other.begin.has_value() && (!begin.has_value() || other.begin.value() > begin.value())) {
		begin = other.begin;
	}

	// earlier end time is more restrictive
	if (other.end.has_value() && (!end.has_value() || other.end.value() > end.value())) {
		end = other.end;
	}

	// smaller confidence is more restrictive
	if (other.confidence.has_value() && (!confidence.has_value() || other.confidence.value() < confidence.value())) {
		confidence = other.confidence;
	}

	return true;
}

size_t GraphSelector::hash() const {
	size_t val = 0;
	if (graph) {
		hashCombine(val, graph->hash());
	} else {
		hashCombine(val, 0);
	}
	if (perspective) {
		hashCombine(val, std::hash<std::string_view>{}(perspective->iri()));
	} else {
		hashCombine(val, 0);
	}
	hashCombine(val, std::hash<bool>{}(occasional));
	hashCombine(val, std::hash<bool>{}(uncertain));
	hashCombine(val, std::hash<std::optional<double>>{}(end));
	hashCombine(val, std::hash<std::optional<double>>{}(begin));
	hashCombine(val, std::hash<std::optional<double>>{}(confidence));
	return val;
}

void GraphSelector::write(std::ostream &os) const {
	os << std::setprecision(1);

	bool hasEpistemicOperator = false;
	if (confidence.has_value()) {
		hasEpistemicOperator = true;
		if (confidence.value() > 0.999) {
			os << 'K';
		} else {
			os << "B[" << confidence.value() << "]";
		}
	} else if (uncertain) {
		hasEpistemicOperator = true;
		os << 'B';
	}
	if (perspective && !Perspective::isEgoPerspective(perspective->iri())) {
		if (!hasEpistemicOperator) {
			os << 'K';
		}
		os << '[' << perspective->iri() << ']';
	}

	bool hasTemporalOperator = false;
	if (occasional) {
		hasTemporalOperator = true;
		os << 'P';
	}
	if (begin.has_value() || end.has_value()) {
		if (!hasTemporalOperator) {
			os << 'H';
		}
		os << '[';
		if (begin.has_value()) {
			os << begin.value();
		}
		os << '-';
		if (end.has_value()) {
			os << end.value();
		}
		os << ']';
	}
}

void GraphSelector::set(const boost::property_tree::ptree &config) {
	uncertain = config.get<bool>("uncertain", false);
	occasional = config.get<bool>("occasional", false);
	if (config.count("graph")) {
		graph = Atom::Tabled(config.get<std::string>("graph"));
	}
	if (config.count("perspective")) {
		perspective = std::make_shared<Perspective>(config.get<std::string>("perspective"));
	}
	if (config.count("begin")) {
		begin = config.get<double>("begin");
	}
	if (config.count("end")) {
		end = config.get<double>("end");
	}
	if (config.count("confidence")) {
		confidence = config.get<double>("confidence");
	}
}

// optional member must be added with add_property
#define BOOST_PYTHON_ADD_OPTIONAL(X, Y) add_property(X, \
    make_getter(Y, return_value_policy<return_by_value>()), \
    make_setter(Y, return_value_policy<return_by_value>()))

namespace knowrob::py {
	template<>
	void createType<GraphSelector>() {
		using namespace boost::python;
		class_<GraphSelector, std::shared_ptr<GraphSelector>>
				("GraphSelector", init<>())
				.def_readwrite("graph", &GraphSelector::graph)
				.def_readwrite("uncertain", &GraphSelector::uncertain)
				.def_readwrite("occasional", &GraphSelector::occasional)
				.BOOST_PYTHON_ADD_OPTIONAL("perspective", &GraphSelector::perspective)
				.BOOST_PYTHON_ADD_OPTIONAL("begin", &GraphSelector::begin)
				.BOOST_PYTHON_ADD_OPTIONAL("end", &GraphSelector::end)
				.BOOST_PYTHON_ADD_OPTIONAL("confidence", &GraphSelector::confidence);
	}
}
