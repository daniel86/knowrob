/*
 * This file is part of KnowRob, please consult
 * https://github.com/knowrob/knowrob for license details.
 */

#include "knowrob/TimeInterval.h"

using namespace knowrob;

TimeInterval::TimeInterval(const std::optional<TimePoint> &since, const std::optional<TimePoint> &until)
		: since_(since),
		  until_(until) {}

bool TimeInterval::operator==(const TimeInterval &other) const {
	return since_ == other.since_ && until_ == other.until_;
}

const TimeInterval &TimeInterval::anytime() {
	static const TimeInterval timeInterval(std::nullopt, std::nullopt);
	return timeInterval;
}

TimeInterval TimeInterval::currently() {
	TimePoint now = time::now();
	return {now, now};
}

TimeInterval TimeInterval::during(const TimePoint &begin, const TimePoint &end) {
	return {begin, end};
}

std::shared_ptr<TimeInterval> TimeInterval::intersectWith(const TimeInterval &other) const {
	return std::make_shared<TimeInterval>(std::max(since_, other.since_), std::min(until_, other.until_));
}

void TimeInterval::write(std::ostream &os) const {
	os << '[';
	if (since().has_value()) time::write(since().value(), os);
	else os << '_';
	os << ",";
	if (until().has_value()) time::write(until().value(), os);
	else os << '_';
	os << ']';
}
