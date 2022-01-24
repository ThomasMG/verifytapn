#ifndef ENTRYSOLVER_HPP_
#define ENTRYSOLVER_HPP_

#include "TraceInfo.hpp"
#include <deque>
#include <vector>
#include "../../typedefs.hpp"
#include <dbm/fed.h>
#include <dbm2/DBM.h>

namespace VerifyTAPN
{
	class EntrySolver
	{
	public:
		EntrySolver(unsigned int tokens, const std::deque<TraceInfo>& traceInfos) : lraTable(0), entryTimeDBM(traceInfos.size()+1), entryTimeDBM2(traceInfos.size()+1), clocks(tokens+1), traceInfos(traceInfos), EPSILON(0.1) { };
		virtual ~EntrySolver() { delete[] lraTable; };

		std::vector<decimal> CalculateDelays(const std::vector<TraceInfo::Invariant>& lastInvariant);
	private:
		inline unsigned int LastResetAt(unsigned int location, unsigned int clock) const { return lraTable[location*clocks+clock]; };

		void CreateLastResetAtLookupTable();
		void CreateEntryTimeDBM(const std::vector<TraceInfo::Invariant>& lastInvariant);
		std::vector<decimal> FindSolution() const;

		bool IsClockResetInStep(unsigned int clock, const TraceInfo& traceInfo) const;

		constraint_t AfterAction(unsigned int locationIndex, const constraint_t& constraint) const;

        std::pair<std::pair<dbm2::dim_t, dbm2::dim_t>, dbm2::bound_t>
        AfterAction2(unsigned int locationIndex, dbm2::dim_t i, dbm2::dim_t j, dbm2::bound_t constraint) const;

		constraint_t AfterDelay(unsigned int locationIndex, const constraint_t& constraint) const;

        std::pair<std::pair<dbm2::dim_t, dbm2::dim_t>, dbm2::bound_t>
        AfterDelay2(unsigned int locationIndex, dbm2::dim_t i, dbm2::dim_t j, dbm2::bound_t constraint) const;

		decimal FindValueInRange(bool lowerStrict, decimal lower, decimal upper, bool upperStrict, decimal lastEntryTime) const;
		void ConvertEntryTimesToDelays(const std::vector<decimal>& entry_times, std::vector<decimal>& delays) const;
	    unsigned int RemapTokenIndex(const TraceInfo & traceInfo, unsigned int index) const;
	private:
		unsigned int* lraTable;
		dbm::dbm_t entryTimeDBM;
		dbm2::DBM entryTimeDBM2;

		unsigned int clocks;
		const std::deque<TraceInfo>& traceInfos;

		const decimal EPSILON;
	};
}

#endif /* ENTRYSOLVER_HPP_ */
