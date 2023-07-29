#ifndef DISCRETEINCLUSIONMARKINGFACTORY_HPP_
#define DISCRETEINCLUSIONMARKINGFACTORY_HPP_

#include "UppaalDBMMarkingFactory.hpp"
#include "DiscretePartInclusionMarking.hpp"

#include <iostream>

#include <pardibaal/DBM.h>

#include "../VerificationOptions.hpp"

namespace VerifyTAPN {

class DiscreteInclusionMarkingFactory : public UppaalDBMMarkingFactory {
public:
	DiscreteInclusionMarkingFactory(const TAPN::TimedArcPetriNet* tapn, const VerificationOptions& options)
		: UppaalDBMMarkingFactory(tapn), tapn(tapn), inc_places(tapn->NumberOfPlaces(), false), empty_inc(options.GetFactory() == DEFAULT) { MarkPlacesForInclusion(options.GetIncPlaces()); };
	virtual ~DiscreteInclusionMarkingFactory() {};

	virtual StoredMarking* Convert(SymbolicMarking* marking) const // TODO: who should clean up marking?
	{
		DBMMarking* dbmMarking = static_cast<DBMMarking*>(marking);
		std::vector<int> eq;
		std::vector<int> inc(tapn->NumberOfPlaces(), 0);
		TokenMapping mapping;

		for(unsigned int i = 0; i < marking->NumberOfTokens(); i++)
		{
			int place = marking->GetTokenPlacement(i);
			if(BelongsToINC(i, *dbmMarking))
				inc[place]++;
			else
			{
				int newIndex = eq.size();
				eq.push_back(place);
				mapping.SetMapping(newIndex, marking->GetClockIndex(i));
			}
		}
		pardibaal::DBM new_dbm = projectToEQPartDbm2(eq, mapping, dbmMarking->GetDBM2());

		return new DiscretePartInclusionMarking(dbmMarking->id, eq, inc, mapping, new_dbm);
	};

	virtual SymbolicMarking* Convert(StoredMarking* marking) const
	{
		DiscretePartInclusionMarking* dpiMarking = static_cast<DiscretePartInclusionMarking*>(marking);

		TokenMapping mapping;
		std::vector<int> dpVec;

		unsigned int nextIncIndex = dpiMarking->eq.size()+1;

		unsigned int i = 0, place_j = 0;
		while(i < dpiMarking->eq.size() || place_j < dpiMarking->inc.size())
		{
			unsigned int place_i = i < dpiMarking->eq.size() ? dpiMarking->eq[i] : std::numeric_limits<int>::max();

			if(i < dpiMarking->eq.size() && place_i <= place_j)
			{
				int newIndex = dpVec.size();
				dpVec.push_back(place_i);
				mapping.SetMapping(newIndex, dpiMarking->GetClockIndex(i));
				i++;
				continue;
			}
			else if(place_j < place_i && dpiMarking->inc[place_j] > 0)
			{
				for(int t = 0; t < dpiMarking->inc[place_j]; t++)
				{
					int newIndex = dpVec.size();
					dpVec.push_back(place_j);
					mapping.SetMapping(newIndex, nextIncIndex);
					assert(mapping.GetMapping(newIndex) == nextIncIndex);
					nextIncIndex++;
				}
			}
			place_j++;
		}

		for(unsigned int i = 0; i < dpVec.size(); i++)
		{
			assert(mapping.GetMapping(i) <= dpiMarking->size()+1);
		}


		DiscretePart dp(dpVec);
		pardibaal::DBM new_dbm = ProjectToAllClocksDbm2(dp, mapping, dpiMarking->new_dbm);

		TokenMapping identity_mapping;
		for(unsigned int i = 0; i < dp.size(); i++)
		{
			identity_mapping.SetMapping(i,i+1);
		}

		assert(dp.size()+1 == new_dbm.dimension());

		DBMMarking* result =  new DBMMarking(dp, identity_mapping, new_dbm);
		result->id = dpiMarking->id;

		return result;
	};

	virtual void Release(SymbolicMarking* marking)
	{
		if(marking != 0) delete marking;
	};

	virtual void Release(StoredMarking* marking)
	{
		if(marking != 0) delete marking;
	};

private:
	bool BelongsToINC(int token, const DBMMarking& marking) const
	{
		if(empty_inc) return false;

		int placeIndex = marking.GetTokenPlacement(token);
		if(!inc_places[placeIndex]) return false;

		const auto& place = tapn->GetPlace(placeIndex);

		assert(placeIndex != TAPN::TimedPlace::BottomIndex());
		if(place.GetInvariant() != TAPN::TimeInvariant::LS_INF) return false;
		if(place.HasInhibitorArcs()) return false;
		if(place.IsUntimed()) return true;

		pardibaal::bound_t lowerBound2 = marking.GetLowerBound2(marking.GetClockIndex(token));

		if(lowerBound2 == pardibaal::bound_t(-place.GetMaxConstant(), true)) return true;

		return false;
	};

	pardibaal::DBM projectToEQPartDbm2(const std::vector<int>& eq, TokenMapping& mapping, const pardibaal::DBM& dbm) const
	{
		unsigned int dim = dbm.dimension();
		if(eq.size()+1 == dim) return pardibaal::DBM(dbm);

		unsigned int bitArraySize = (dim % 32 == 0 ? dim/32 : dim/32+1);
		unsigned int bitSrc[bitArraySize];
		unsigned int bitDst[bitArraySize];

		for(unsigned int i = 0; i < bitArraySize; i++)
		{
			if(i == 0){
				bitSrc[i] = 1;
				bitDst[i] = 1;
			}else{
				bitSrc[i] = 0;
				bitDst[i] = 0;
			}
		}

		for(unsigned int i = 0; i < dim; i++)
		{
			bitSrc[i/32] |= (1 << (i % 32));
		}

		for(unsigned int i = 0; i < eq.size(); i++)
		{
			unsigned int arrayIndex = mapping.GetMapping(i)/32;
			unsigned int offset = mapping.GetMapping(i) % 32;
			bitDst[arrayIndex] |= (1 << offset);
		}

		// Translate bit arrays to vector<bool> (also compact)
		std::vector<bool> src_vec(dim);
		for (unsigned int i = 0; i < dim; i++)
			src_vec[i] = (bitSrc[i/32] & (1 << (i%32) )) != 0;

		std::vector<bool> dst_vec(dim);
		for (unsigned int i = 0; i < eq.size(); i++)
			dst_vec[i] = (bitDst[i/32] & (1 << (i%32) )) != 0;

		pardibaal::DBM copy(dbm);
		std::vector<pardibaal::dim_t> table = copy.resize(src_vec, dst_vec);

		assert(dbm.dimension() == dim);
		assert(eq.size()+1 == copy.dimension());

		for(unsigned int i = 0; i < dim; ++i)
		{
			if(table[i] != i)
			{
				for(unsigned int j = 0; j < mapping.size(); ++j)
				{
					if(mapping.GetMapping(j) == i)
						mapping.SetMapping(j, table[i]);
				}
			}
		}

		return copy;
	}

	pardibaal::DBM ProjectToAllClocksDbm2(const DiscretePart& dp, const TokenMapping& mapping, const pardibaal::DBM& dbm) const
	{
		unsigned int dim = dbm.dimension();
		unsigned int totalClocks = dp.size()+1;
		std::vector<pardibaal::dim_t> map(totalClocks);
		map[0] = 0;

		bool fromInc[totalClocks];
		fromInc[0] = false;
		for(unsigned int i = 1; i < totalClocks; i++)
		{
			unsigned int target = mapping.GetMapping(i-1);
			if(target >= dim)
			{
				map[i] = ~0;
				fromInc[i] = true;
			}
			else
			{
				map[i] = target;
				fromInc[i] = false;
			}
		}

		pardibaal::DBM copy(dbm);
		//copy.reorder(map, totalClocks);

		for(unsigned int i = 0; i < dp.size(); i++)
		{
			if(fromInc[i+1])
			{
				const TimedPlace& place = tapn->GetPlace(dp.GetTokenPlacement(i));
				if(!place.IsUntimed()) copy.restrict(0, i+1, pardibaal::bound_t(-place.GetMaxConstant(), true));
			}
		}

		return copy;
	};

	void MarkPlacesForInclusion(const std::vector<std::string>& places)
	{
		if((places.size() == 1 && places[0] == "*NONE*") || places.size() == 0)
		{
			return;
		}
		else if(places.size() == 1 && places[0] == "*ALL*")
		{
			for(unsigned int i = 0; i < inc_places.size(); i++)
			{
				inc_places[i] = true;
			}
		}
		else
		{
			for(std::vector<std::string>::const_iterator it = places.begin(); it != places.end(); it++)
			{
				int index = tapn->GetPlaceIndex(*it);
				if(index != TimedPlace::BottomIndex())
				{
					inc_places[index] = true;
				}
			}
		}
	};
private:
	const TAPN::TimedArcPetriNet* tapn;
	std::vector<bool> inc_places;
	bool empty_inc;
};

}

#endif /* DISCRETEINCLUSIONMARKINGFACTORY_HPP_ */
