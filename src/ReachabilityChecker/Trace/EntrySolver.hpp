#ifndef ENTRYSOLVER_HPP_
#define ENTRYSOLVER_HPP_

#include "TraceInfo.hpp"
#include <deque>
#include <vector>
#include "../../typedefs.hpp"
#include <pardibaal/DBM.h>

namespace VerifyTAPN
{
	class EntrySolver
	{
	public:
		EntrySolver(unsigned int tokens, const std::deque<TraceInfo>& traceInfos) : lraTable(0), entryTimeDBM2(traceInfos.size()+1), clocks(tokens+1), traceInfos(traceInfos), EPSILON(0.1) { };
		virtual ~EntrySolver() { delete[] lraTable; };

		std::vector<decimal> CalculateDelays(const std::vector<TraceInfo::Invariant>& lastInvariant);
	private:
		inline unsigned int LastResetAt(unsigned int location, unsigned int clock) const { return lraTable[location*clocks+clock]; };

		void CreateLastResetAtLookupTable();
		void CreateEntryTimeDBM(const std::vector<TraceInfo::Invariant>& lastInvariant);
		std::vector<decimal> FindSolution() const;

		bool IsClockResetInStep(unsigned int clock, const TraceInfo& traceInfo) const;

		std::pair<std::pair<pardibaal::dim_t, pardibaal::dim_t>, pardibaal::bound_t>
		AfterAction2(unsigned int locationIndex, pardibaal::dim_t i, pardibaal::dim_t j, pardibaal::bound_t constraint) const;

		std::pair<std::pair<pardibaal::dim_t, pardibaal::dim_t>, pardibaal::bound_t>
		AfterDelay2(unsigned int locationIndex, pardibaal::dim_t i, pardibaal::dim_t j, pardibaal::bound_t constraint) const;

		decimal FindValueInRange(bool lowerStrict, decimal lower, decimal upper, bool upperStrict, decimal lastEntryTime) const;
		void ConvertEntryTimesToDelays(const std::vector<decimal>& entry_times, std::vector<decimal>& delays) const;
		unsigned int RemapTokenIndex(const TraceInfo & traceInfo, unsigned int index) const;
	private:
		unsigned int* lraTable;
		pardibaal::DBM entryTimeDBM2;

		unsigned int clocks;
		const std::deque<TraceInfo>& traceInfos;

		const decimal EPSILON;
	};
}

#endif /* ENTRYSOLVER_HPP_ */
