#include "EntrySolver.hpp"
#include "trace_exception.hpp"
#include "../../EqualityChecker.h"

namespace VerifyTAPN
{
	std::vector<decimal> EntrySolver::CalculateDelays(const std::vector<TraceInfo::Invariant>& lastInvariant)
	{
		CreateLastResetAtLookupTable();
		CreateEntryTimeDBM(lastInvariant);
		return FindSolution();
	}

	// See CTU - DCCreator.cpp for details!
	void EntrySolver::CreateLastResetAtLookupTable()
	{

		unsigned int locations = traceInfos.size()+1;

		if(lraTable != 0) delete[] lraTable;
		lraTable = new unsigned int[locations*clocks]; // TODO: check that this gives correct number of places

		for(unsigned int i = 0; i < clocks; i++)
		{
			lraTable[i] = 0;
		}
		for(unsigned int loc = 1; loc < locations; loc++)
		{
			unsigned int index = loc-1;
			for(unsigned int clock = 0; clock < clocks; clock++)
			{
				bool isClockUsed = IsClockResetInStep(clock, traceInfos[index]);
				if(isClockUsed)
					lraTable[loc*clocks+clock] = loc;
				else
					lraTable[loc*clocks+clock] = lraTable[(loc-1)*clocks+clock];
			}
		}
	}



	bool EntrySolver::IsClockResetInStep(unsigned int clock, const TraceInfo& traceInfo) const
	{
		const std::vector<Participant>& participants = traceInfo.Participants();
		for(std::vector<Participant>::const_iterator it = participants.begin(); it != participants.end(); it++)
		{
			const Participant& participant = *it;
			assert(participant.TokenIndex() != -1);

			unsigned int index = participant.TokenIndex();
			unsigned int mapped_token_index = RemapTokenIndex(traceInfo, index);
			assert(mapped_token_index >= 0);
			if((mapped_token_index+1) == clock)
			{
				return participant.GetArcType() == NORMAL_ARC;
			}
		}
		return false;
	}

	unsigned int EntrySolver::RemapTokenIndex(const TraceInfo & traceInfo, unsigned int index) const
	{
		unsigned int indexAfterFiring = traceInfo.GetTransitionFiringMapping().MapForward(index);
		unsigned int symmetric_index = traceInfo.GetSymmetricMapping().MapForward(indexAfterFiring);
		unsigned int mapped_token_index = traceInfo.GetOriginalMapping()[symmetric_index];
		return mapped_token_index;
	}

	// See CTU - DCCreator.cpp for details!
	// Algorithm:
	// For i = 0 to trace.length+1 do
	//		For each place invariant inv which applies to a token and is not [0,inf)
	//			compute AfterAction(i, inv), add to DBM
	//
	// For each step i in the trace do
	// 		For each time interval ti in the guards of step i
	//			let ti_low be constraint representing lower bound
	//			let ti_up be constraint representing upper bound
	//			compute AfterDelay(i, ti_low), add to DBM
	// 			compute AfterDelay(i, ti_up), add to DBM
	//		For each place invariant inv which is not [0,inf)
	//			compute AfterDelay(i, inv), add to DBM
	//
	// For each step i in the trace do
	// 		add e_i - e_{i+1} <= 0 to DBM
	void EntrySolver::CreateEntryTimeDBM(const std::vector<TraceInfo::Invariant>& lastInvariant)
	{
		unsigned int dim = traceInfos.size();
		entryTimeDBM.setInit();

		for(unsigned int i = 0; i < dim; i++)
		{
			const TraceInfo& traceInfo = traceInfos[i];
			const std::vector<TraceInfo::Invariant>& invariants = traceInfo.GetInvariants();
			for(std::vector<TraceInfo::Invariant>::const_iterator it = invariants.begin(); it != invariants.end(); it++)
			{
				const TraceInfo::Invariant& inv = *it;
				assert(inv.second != TAPN::TimeInvariant::LS_INF);

				unsigned int mapped_index = RemapTokenIndex(traceInfo, inv.first);
				constraint_t bound(mapped_index+1, 0, dbm_boundbool2raw(inv.second.GetBound(), inv.second.IsBoundStrict()));
				entryTimeDBM.constrain(AfterAction(i, bound));

				dbm2::bound_t bound2(inv.second.GetBound(), inv.second.IsBoundStrict());

				auto constraint = AfterAction2(i, mapped_index+1, 0, bound2);
				entryTimeDBM2.restrict(constraint.first.first, constraint.first.second, constraint.second);
				EqualityChecker::assertEqualDbms(entryTimeDBM, entryTimeDBM2);
			}
		}

		// Apply invariants from final marking
		for(std::vector<TraceInfo::Invariant>::const_iterator it = lastInvariant.begin(); it != lastInvariant.end(); it++)
		{
			const TraceInfo::Invariant& inv = *it;
			assert(inv.second != TAPN::TimeInvariant::LS_INF);

			unsigned int mapped_index = traceInfos[traceInfos.size()-1].GetOriginalMapping()[inv.first];
			constraint_t bound(mapped_index+1, 0, dbm_boundbool2raw(inv.second.GetBound(), inv.second.IsBoundStrict()));
			entryTimeDBM.constrain(AfterAction(dim, bound));

			dbm2::bound_t bound2(inv.second.GetBound(), inv.second.IsBoundStrict());
			auto constraint = AfterAction2(dim, mapped_index+1, 0, bound2);
			entryTimeDBM2.restrict(constraint.first.first, constraint.first.second, constraint.second);

			EqualityChecker::assertEqualDbms(entryTimeDBM, entryTimeDBM2);
		}


		for(unsigned int i = 0; i < dim; i++)
		{
			const TraceInfo& traceInfo = traceInfos[i];
			typedef std::vector<Participant>::const_iterator const_iterator;
			const_iterator begin = traceInfo.Participants().begin();
			const_iterator end = traceInfo.Participants().end();
			for(const_iterator it = begin;it != end;it++){
				const TAPN::TimeInterval & interval = it->GetTimeInterval();
				unsigned int mapped_token_index = RemapTokenIndex(traceInfo, it->TokenIndex());

				constraint_t lower(0, mapped_token_index + 1, interval.LowerBoundToDBMRaw());
				constraint_t entryLower(AfterDelay(i, lower));
				entryTimeDBM.constrain(entryLower);

				auto constraint = AfterDelay2(i, 0, mapped_token_index + 1, interval.LowerBoundToDBM2Bound());
				entryTimeDBM2.restrict(constraint.first.first, constraint.first.second, constraint.second);

				if(interval.UpperBoundToDBMRaw() != dbm_LS_INFINITY)
				{
					constraint_t upper(mapped_token_index + 1, 0, interval.UpperBoundToDBMRaw());
					constraint_t entryUpper(AfterDelay(i, upper));
					entryTimeDBM.constrain(entryUpper);

					constraint = AfterDelay2(i, mapped_token_index + 1, 0, interval.UpperBoundToDBM2Bound());
					entryTimeDBM2.restrict(constraint.first.first, constraint.first.second, constraint.second);
				}
			}

			const std::vector<TraceInfo::Invariant>& invariants = traceInfo.GetInvariants();
			for(std::vector<TraceInfo::Invariant>::const_iterator it = invariants.begin(); it != invariants.end(); it++)
			{
				const TraceInfo::Invariant& inv = *it;
				assert(inv.second != TAPN::TimeInvariant::LS_INF);

				unsigned int mapped_index = RemapTokenIndex(traceInfo, inv.first);
				constraint_t bound(mapped_index+1, 0, dbm_boundbool2raw(inv.second.GetBound(), inv.second.IsBoundStrict()));
				entryTimeDBM.constrain(AfterDelay(i, bound));

				auto constraint = AfterDelay2(i, mapped_index + 1, 0, dbm2::bound_t(inv.second.GetBound(), inv.second.IsBoundStrict()));
				entryTimeDBM2.restrict(constraint.first.first, constraint.first.second, constraint.second);
			}

			EqualityChecker::assertEqualDbms(entryTimeDBM, entryTimeDBM2);
		}

		// add constraints e_i - e_i+1 <= 0
		for(unsigned int i = 0;i < dim;i++){
			entryTimeDBM.constrain(i, i + 1, 0, false);
			entryTimeDBM2.restrict(i, i + 1, dbm2::bound_t(0, false));
		}

		if(entryTimeDBM.isEmpty()) throw VerifyTAPN::trace_exception("entry time dbm empty");
		if(entryTimeDBM2.is_empty()) throw VerifyTAPN::trace_exception("entry time dbm empty");

		EqualityChecker::assertEqualDbms(entryTimeDBM, entryTimeDBM2);
	}

	//TODO: I need a structure to store two clock indexes and a bound_t
	// implement such a structure perhaps, instead of this monster: pair<pair<int, int>, bound_t>.
	std::pair<std::pair<dbm2::dim_t, dbm2::dim_t>, dbm2::bound_t>
	EntrySolver::AfterAction2(unsigned int locationIndex, dbm2::dim_t i, dbm2::dim_t j, dbm2::bound_t constraint) const {
		if(j == 0 && i != 0)
			return std::make_pair(std::make_pair(locationIndex, LastResetAt(locationIndex, i)), constraint);

		else
		if(i == 0 && j != 0)
			return std::make_pair(std::make_pair(LastResetAt(locationIndex, j), locationIndex), constraint);

		else
			return std::make_pair(std::make_pair(LastResetAt(locationIndex, j), LastResetAt(locationIndex, i)), constraint);
	}
	std::pair<std::pair<dbm2::dim_t, dbm2::dim_t>, dbm2::bound_t>
	EntrySolver::AfterDelay2(unsigned int locationIndex, dbm2::dim_t i, dbm2::dim_t j, dbm2::bound_t constraint) const {
		if(i != 0 && j == 0)
			return std::make_pair(std::make_pair(locationIndex + 1, LastResetAt(locationIndex, i)), constraint);

		else
		if(i == 0 && j != 0)
			return std::make_pair(std::make_pair(LastResetAt(locationIndex, j), locationIndex + 1), constraint);

		else
			return std::make_pair(std::make_pair(LastResetAt(locationIndex, j), LastResetAt(locationIndex, i)), constraint);
	}

	// Theory: AfterAction(Trace, index, guard/invariant)
	constraint_t EntrySolver::AfterAction(unsigned int locationIndex, const constraint_t & constraint) const
	{
		if(constraint.j == 0 && constraint.i != 0) //TODO: is it correct that i and j are not switched?
			return constraint_t(locationIndex, LastResetAt(locationIndex, constraint.i), constraint.value);

		else
			if(constraint.i == 0 && constraint.j != 0)
				return constraint_t(LastResetAt(locationIndex, constraint.j), locationIndex, constraint.value);

			else
				return constraint_t(LastResetAt(locationIndex, constraint.j), LastResetAt(locationIndex, constraint.i), constraint.value);


	}
	// Theory: AfterDelay(Trace, index, guard/invariant)
	constraint_t EntrySolver::AfterDelay(unsigned int locationIndex, const constraint_t & constraint) const
	{
		if(constraint.i != 0 && constraint.j == 0)
			return constraint_t(locationIndex + 1, LastResetAt(locationIndex, constraint.i), constraint.value);

		else
			if(constraint.i == 0 && constraint.j != 0)
				return constraint_t(LastResetAt(locationIndex, constraint.j), locationIndex + 1, constraint.value);

			else
				return constraint_t(LastResetAt(locationIndex, constraint.j), LastResetAt(locationIndex, constraint.i), constraint.value);


	}
	// This is straight port from CTU implementation. See CTU -- SolutionFinder.cpp for details
	std::vector<decimal> EntrySolver::FindSolution() const
	{
		assert(!entryTimeDBM.isEmpty());
		assert(!entryTimeDBM2.is_empty());
		unsigned int dim = entryTimeDBM.getDimension();
		assert(dim == entryTimeDBM2._bounds_table._number_of_clocks);
		std::vector<decimal> entry_times(dim);
		bool restricted[dim];
		for(unsigned int i = 0;i < dim;i++){
			restricted[i] = false;
		}
		// make sure we start at time 0
		entry_times[0] = decimal(0);
		restricted[0] = true; // ensure time 0 is final
		for(unsigned int i = 1;i < dim;i++){
			if(!restricted[i]){
				bool lowerStrict = dbm_rawIsStrict(entryTimeDBM(0, i));
				assert(lowerStrict == entryTimeDBM2._bounds_table.at(0, i)._strict);

				decimal lower = decimal(-dbm_raw2bound(entryTimeDBM(0, i)));
				assert(lower == decimal(entryTimeDBM2._bounds_table.at(0, i)._n));

				bool upperStrict = dbm_rawIsStrict(entryTimeDBM(i, 0));
				assert(upperStrict == entryTimeDBM2._bounds_table.at(i, 0)._strict);

				decimal upper = decimal(dbm_raw2bound(entryTimeDBM(i, 0)));
				assert(upper == decimal(entryTimeDBM2._bounds_table.at(i, 0)._n));
				// try to derive tighter bounds
				for(unsigned int j = 1;j < dim;j++){
					if(restricted[j] && i != j){
						bool strict = dbm_rawIsStrict(entryTimeDBM(i, j));
						assert(strict == entryTimeDBM2._bounds_table.at(i, j)._strict);

						decimal bound = decimal(dbm_raw2bound(entryTimeDBM(i, j))) + entry_times[j];
						assert(bound == decimal(entryTimeDBM2._bounds_table.at(i, j)._n));

						if(bound < upper || (bound == upper && strict)){
							upperStrict = strict;
							upper = bound;
						}
						strict = dbm_rawIsStrict(entryTimeDBM(j, i));
						assert(strict == entryTimeDBM2._bounds_table.at(j, i)._strict);

						bound = decimal(-dbm_raw2bound(entryTimeDBM(j, i))) + entry_times[j];
						assert(bound == decimal(entryTimeDBM2._bounds_table.at(j, i)._n));

						if(bound > lower || (bound == lower && strict)){
							lowerStrict = strict;
							lower = bound;
						}
					}

				}

				// These are the tightest bounds so we find a value in this range
				entry_times[i] = FindValueInRange(lowerStrict, lower, upper, upperStrict, entry_times[i - 1]);
				restricted[i] = true;
			}

		}

		std::vector<decimal> delays(entry_times.size());
		ConvertEntryTimesToDelays(entry_times, delays);
		return delays;
	}

	decimal EntrySolver::FindValueInRange(bool lowerStrict, decimal lower, decimal upper, bool upperStrict, decimal lastEntryTime) const
	{
		decimal diff = upper - lower;
		assert(lower <= upper);
		assert((!lowerStrict && !upperStrict) || diff > 0);

		if(!lowerStrict)
		{
			return lower; // Safe due to assert above
		}
		else if(lowerStrict && diff > 1)
		{
			return lower + decimal(1);
		}
		else // diff <= 1 && lowerStrict
		{
			if(!upperStrict)
			{
				return upper;
			}
			else
			{
				return (lower + upper) / 2; // return mean
			}
		}
	}

	void EntrySolver::ConvertEntryTimesToDelays(const std::vector<decimal>& entry_times, std::vector<decimal>& delays) const
	{
		for(unsigned int i = 0; i < entry_times.size()-1; i++)
		{
			delays[i] = entry_times[i+1] - entry_times[i];
		}
	}
}
