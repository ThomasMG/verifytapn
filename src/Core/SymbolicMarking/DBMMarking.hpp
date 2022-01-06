#ifndef DBMMARKING_HPP_
#define DBMMARKING_HPP_

#include "DiscreteMarking.hpp"
#include "StoredMarking.hpp"
#include "TokenMapping.hpp"
#include "MarkingFactory.hpp"
#include "../TAPN/TimedArcPetriNet.hpp"
#include <dbm/fed.h>
#include <iosfwd>
#include <vector>

#include <dbm2/DBM.h>

namespace VerifyTAPN {

	class DBMMarking: public DiscreteMarking, public StoredMarking {
		friend class UppaalDBMMarkingFactory;
		friend class DiscreteInclusionMarkingFactory;
	public:
		static std::shared_ptr<TAPN::TimedArcPetriNet> tapn;
	public:
		DBMMarking(const DiscretePart& dp,  const dbm::dbm_t& dbm, const dbm2::DBM& new_dbm) : DiscreteMarking(dp), dbm(dbm), new_dbm(new_dbm), mapping() {InitMapping(); assert(IsConsistent()); };
		DBMMarking(const DiscretePart& dp, const TokenMapping& mapping,  const dbm::dbm_t& dbm, const dbm2::DBM& new_dbm) : DiscreteMarking(dp), dbm(dbm), new_dbm(new_dbm), mapping(mapping) { assert(IsConsistent()); };
		DBMMarking(const DBMMarking& dm) : DiscreteMarking(dm), dbm(dm.dbm), new_dbm(dm.new_dbm), mapping(dm.mapping) { };

        DBMMarking(const DiscretePart& dp,  const dbm::dbm_t& dbm) : DiscreteMarking(dp), dbm(dbm), new_dbm(0), mapping() {InitMapping(); assert(IsConsistent()); };
        DBMMarking(const DiscretePart& dp, const TokenMapping& mapping,  const dbm::dbm_t& dbm) : DiscreteMarking(dp), dbm(dbm), new_dbm(0), mapping(mapping) { assert(IsConsistent()); };

		virtual ~DBMMarking() { };

		virtual id_type UniqueId() const { return id; };
		virtual size_t HashKey() const { return VerifyTAPN::hash()(dp); };

		virtual void Reset(int token) {
		    dbm(mapping.GetMapping(token)) = 0;
		    new_dbm.assign(mapping.GetMapping(token), 0);
		};
		virtual bool IsEmpty() const { return dbm.isEmpty(); };
        virtual bool NewIsEmpty() const { return new_dbm.is_empty(); };
		virtual void Delay()
		{
			dbm.up();
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
			dbm.constrain(0, clock, interval.LowerBoundToDBMRaw());
            dbm.constrain(clock, 0, interval.UpperBoundToDBMRaw());

			new_dbm.restrict(0,clock, interval.LowerBoundToDBM2Bound());
			new_dbm.restrict(clock, 0, interval.UpperBoundToDBM2Bound());
		};

		virtual void Constrain(int token, const TAPN::TimeInvariant& invariant)
		{
			if(invariant.GetBound() != std::numeric_limits<int>::max())
			{
				dbm.constrain(mapping.GetMapping(token), 0, dbm_boundbool2raw(invariant.GetBound(), invariant.IsBoundStrict()));
                new_dbm.restrict(mapping.GetMapping(token), 0, dbm2::bound_t(invariant.GetBound(), invariant.IsBoundStrict()));
			}
		};

		virtual bool PotentiallySatisfies(int token, const TAPN::TimeInterval& interval) const
		{
			int clock = mapping.GetMapping(token);
			bool isLowerBoundSat = dbm.satisfies(0, clock, interval.LowerBoundToDBMRaw());
			bool isLowerBoundSat2 = new_dbm.is_satisfied(0, clock, interval.LowerBoundToDBM2Bound());
			assert(isLowerBoundSat = isLowerBoundSat2);

			bool isUpperBoundSat = dbm.satisfies(clock, 0, interval.UpperBoundToDBMRaw());
			bool isUpperBoundSat2 = new_dbm.is_satisfied(clock, 0, interval.UpperBoundToDBM2Bound());
			assert(isUpperBoundSat = isUpperBoundSat2);

			bool inappropriateAge = !isLowerBoundSat || !isUpperBoundSat;
			return !inappropriateAge;
		};

		//TODO: Maybe implement some fancy relation thing in dbm2?
		virtual relation Relation(const StoredMarking& other) const
		{
			relation_t relation = dbm.relation(static_cast<const DBMMarking&>(other).dbm);
			return ConvertToRelation(relation);
		}

		virtual void Extrapolate(const int* maxConstants) {
		    dbm.diagonalExtrapolateMaxBounds(maxConstants);

		    //TODO: I'm gonna (probably wrongfully) assume that this is the same as a regular delay and normalisation
		    new_dbm.future();
		    std::vector<dbm2::val_t> vec;
		    for (int i = 0; i < new_dbm._bounds_table._number_of_clocks; i++)
		        vec.push_back((dbm2::val_t) maxConstants[i]);
		    new_dbm.norm(vec);
		};
		virtual unsigned int GetClockIndex(unsigned int token) const { return mapping.GetMapping(token); };

		virtual void AddTokens(const std::list<int>& placeIndices);
		virtual void RemoveTokens(const std::set<int>& tokenIndices);

		raw_t GetLowerBound(int clock) const { return dbm(0,clock); };
        dbm2::bound_t GetLowerBound2(int clock) const { return new_dbm._bounds_table.at(0,clock); };

		const dbm::dbm_t& GetDBM() const { return dbm; };
        const dbm2::DBM& GetDBM2() const { return new_dbm; };

		virtual void Print(std::ostream& out) const;
	private:
		void InitMapping();

		bool IsConsistent() const
		{
			if(dp.size() != dbm.getDimension()-1)
			{
				return false;
			}
            if(dp.size() != new_dbm._bounds_table._number_of_clocks - 1)
                return false;

			if(mapping.size() != dp.size()) return false;

			for(unsigned int i = 0; i < dp.size(); i++)
			{
				unsigned int mappedIndex = mapping.GetMapping(i);
				if(mappedIndex == 0 || mappedIndex >= dbm.getDimension())
					return false;
                if(mappedIndex == 0 || mappedIndex >= new_dbm._bounds_table._number_of_clocks)
                    return false;
			}
			return true;
		};

	protected:
		virtual void Swap(int i, int j);
		virtual bool IsUpperPositionGreaterThanPivot(int upper, int pivotIndex) const;
		relation ConvertToRelation(relation_t relation) const;

	protected: // data
	    dbm::dbm_t dbm;
		dbm2::DBM new_dbm;
		TokenMapping mapping;
		id_type id;

	};

}

#endif /* DBMMARKING_HPP_ */
