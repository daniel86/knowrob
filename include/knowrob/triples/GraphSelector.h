/*
 * This file is part of KnowRob, please consult
 * https://github.com/knowrob/knowrob for license details.
 */

#ifndef KNOWROB_GRAPH_SELECTOR_H
#define KNOWROB_GRAPH_SELECTOR_H

#include "optional"
#include "Perspective.h"
#include <boost/property_tree/ptree.hpp>

namespace knowrob {
	/**
	 * The data base can contain multiple graphs, and this selector
	 * is used to select a subset of them.
	 * For example, each point in time is conceptually a separate graph, and
	 * a query may only address a specific point in time, or time interval.
	 */
	struct GraphSelector : public Printable {
		GraphSelector() = default;

		/**
		 * The name of the graph, usually reflects the name of an ontology.
		 */
		AtomPtr graph;
		/**
		 * The perspective of statement.
		 */
		PerspectivePtr perspective;
		/**
		 * True if occasional triples are considered.
		 */
		bool occasional = false;
		/**
		 * True if uncertain triples are considered.
		 */
		bool uncertain = false;
		/**
		 * The begin of the time interval of consideration.
		 */
		std::optional<double> begin;
		/**
		 * The end of the time interval of consideration.
		 */
		std::optional<double> end;
		/**
		 * The minimum confidence threshold for statements.
		 */
		std::optional<double> confidence;

		/**
		 * Compute the hash value of this selector.
		 * @return the hash value
		 */
		size_t hash() const;

		/**
		 * Merge this selector with another selector.
		 * @param other another selector.
		 * @return true if the merge was successful.
		 */
		bool mergeWith(const GraphSelector &other);

		/**
		 * Set the selector from a property tree.
		 * @param config the property tree
		 */
		void set(const boost::property_tree::ptree &config);

		// Override Printable::write
		void write(std::ostream &os) const override;
	};

	// alias
	using GraphSelectorPtr = std::shared_ptr<const GraphSelector>;

	/**
	 * @return the default graph selector
	 */
	static GraphSelectorPtr DefaultGraphSelector() {
		static auto defaultSelector = std::make_shared<const GraphSelector>();
		return defaultSelector;
	}
}

#endif //KNOWROB_GRAPH_SELECTOR_H
