#ifndef DBMMARKING_HPP_
#define DBMMARKING_HPP_

#include "DiscreteMarking.hpp"
#include "StoredMarking.hpp"
#include "TokenMapping.hpp"
#include "MarkingFactory.hpp"
#include "../TAPN/TimedArcPetriNet.hpp"
#include <iosfwd>
#include <vector>

#include <pardibaal/DBM.h>

namespace VerifyTAPN {

	class DBMMarking: public DiscreteMarking, public StoredMarking {
		friend class UppaalDBMMarkingFactory;
		friend class DiscreteInclusionMarkingFactory;
	public:
		static const TAPN::TimedArcPetriNet* tapn;
	public:
		DBMMarking(const DiscretePart& dp, const pardibaal::DBM& new_dbm) : DiscreteMarking(dp), new_dbm(new_dbm), mapping() {InitMapping(); assert(IsConsistent()); };
		DBMMarking(const DiscretePart& dp, const TokenMapping& mapping, const pardibaal::DBM& new_dbm) : DiscreteMarking(dp), new_dbm(new_dbm), mapping(mapping) { assert(IsConsistent()); };
		DBMMarking(const DBMMarking& dm) : DiscreteMarking(dm), new_dbm(dm.new_dbm), mapping(dm.mapping) { };
		// DBMMarking(const DiscretePart& dp, const TokenMapping& mapping,  const dbm::dbm_t& dbm) : DiscreteMarking(dp), dbm(dbm), new_dbm(0), mapping(mapping) { assert(IsConsistent()); };

		virtual ~DBMMarking() { };

		virtual id_type UniqueId() const { return id; };
		virtual size_t HashKey() const { return VerifyTAPN::hash()(dp); };

		virtual void Reset(int token) {
			new_dbm.assign(mapping.GetMapping(token), 0);
		};

		virtual bool IsEmpty() const { return new_dbm.is_empty(); };
		virtual void Delay()
		{
			new_dbm.future();
			for(unsigned int i = 0; i < NumberOfTokens(); i++)
			{
				const TAPN::TimeInvariant& invariant = tapn->GetPlace(GetTokenPlacement(i)).GetInvariant();
				Constrain(i, invariant);
				assert(!IsEmpty()); // this should not be possible
			}
		};
		virtual void Constrain(int token, const TAPN::TimeInterval& interval)
		{
			int clock = mapping.GetMapping(token);

			new_dbm.restrict(0,clock, interval.LowerBoundToDBM2Bound());
			new_dbm.restrict(clock, 0, interval.UpperBoundToDBM2Bound());
		};

		virtual void Constrain(int token, const TAPN::TimeInvariant& invariant)
		{
			if(invariant.GetBound() != std::numeric_limits<int>::max())
			{
				new_dbm.restrict(mapping.GetMapping(token), 0, pardibaal::bound_t(invariant.GetBound(), invariant.IsBoundStrict()));
			}
		};

		virtual bool PotentiallySatisfies(int token, const TAPN::TimeInterval& interval) const
		{
			int clock = mapping.GetMapping(token);
			bool isLowerBoundSat = new_dbm.is_satisfying(0, clock, interval.LowerBoundToDBM2Bound());

			bool isUpperBoundSat = new_dbm.is_satisfying(clock, 0, interval.UpperBoundToDBM2Bound());

			bool inappropriateAge = !isLowerBoundSat || !isUpperBoundSat;
			return !inappropriateAge;
		};

		virtual relation Relation(const StoredMarking& other) const
		{
			auto relation = new_dbm.relation(static_cast<const DBMMarking&>(other).new_dbm);
			return ConvertToRelation(relation);
		}

		virtual void Extrapolate(const int* maxConstants) {
			new_dbm.extrapolate_diagonal(std::vector<pardibaal::val_t>(maxConstants, maxConstants + new_dbm.dimension()));
		};
		virtual unsigned int GetClockIndex(unsigned int token) const { return mapping.GetMapping(token); };

		virtual void AddTokens(const std::list<int>& placeIndices);
		virtual void RemoveTokens(const std::set<int>& tokenIndices);

		// raw_t GetLowerBound(int clock) const { return dbm(0,clock); };
		pardibaal::bound_t GetLowerBound2(int clock) const { return new_dbm.at(0,clock); };

		// const dbm::dbm_t& GetDBM() const { return dbm; };
		const pardibaal::DBM& GetDBM2() const { return new_dbm; };

		virtual void Print(std::ostream& out) const;

	private:
		void InitMapping();

		bool IsConsistent() const
		{
			if (dp.size() != new_dbm.dimension() -1) return false;
			if(mapping.size() != dp.size()) return false;

			for(unsigned int i = 0; i < dp.size(); i++)
			{
				unsigned int mappedIndex = mapping.GetMapping(i);
				if(mappedIndex == 0 || mappedIndex >= new_dbm.dimension())
					return false;
			}
			return true;
		};

	protected:
		virtual void Swap(int i, int j);
		virtual bool IsUpperPositionGreaterThanPivot(int upper, int pivotIndex) const;
		relation ConvertToRelation(pardibaal::relation_t rel) const;

	protected: // data
		pardibaal::DBM new_dbm;
		TokenMapping mapping;
		id_type id;

	};

}

#endif /* DBMMARKING_HPP_ */
