#include "DBMMarking.hpp"
#include <iostream>

namespace VerifyTAPN
{
	const TAPN::TimedArcPetriNet* DBMMarking::tapn;

	// Add a token in each output place of placesOfTokensToAdd
	// and add placesOfTokensToAdd.size() clocks to the DBM.
	// The DBM library requires arrays of bitvectors indicating
	// which tokens are in the original dbm (bitSrc) and which are in the resulting DBM (bitDst).
	void DBMMarking::AddTokens(const std::list<int>& placeIndices)
	{
		unsigned int tokens = NumberOfTokens();
		unsigned int nAdditionalTokens = placeIndices.size();
		unsigned int oldDimension = new_dbm.dimension();
		unsigned int newDimension = oldDimension + nAdditionalTokens;

		//TODO: Use add_clock instead
		pardibaal::DBM resized_new_dbm(newDimension);
		for (int i = 0; i < oldDimension; i++)
			for (int j = 0; j < oldDimension; j++)
				resized_new_dbm.set(i, j, new_dbm.at(i, j));
		new_dbm = std::move(resized_new_dbm);

		for (int i = oldDimension; i < newDimension; i++) {
			new_dbm.free(i);
			new_dbm.assign(i, 0);
		}

		unsigned int i = 0;
		unsigned int newTokenIndex = tokens;
		for(std::list<int>::const_iterator iter = placeIndices.begin(); iter != placeIndices.end(); ++iter)
		{
			// dbm(oldDimension+i) = 0; // reset new clocks to zero
			mapping.SetMapping(newTokenIndex, oldDimension+i);
			dp.AddTokenInPlace(*iter);
			i++;newTokenIndex++;
		}

		assert(IsConsistent());
	}

	// Remove each token in tokensToRemove from the placement vector and from the DBM.
	// These tokens represent tokens that are moving to BOTTOM.
	// The DBM library requires arrays of bitvectors indicating which tokens are in
	// the original dbm (bitSrc) and which are in the resulting DBM (bitDst).
	void DBMMarking::RemoveTokens(const std::set<int>& tokenIndices)
	{
		std::set<int> dbmTokensToRemove;
		for (const auto &e : tokenIndices)
			dbmTokensToRemove.insert(mapping.GetMapping(e));

		unsigned int oldDimension = new_dbm.dimension();
		unsigned int table[oldDimension];

		for(unsigned int i = 0; i < oldDimension; ++i)
		{
			table[i] = std::numeric_limits<unsigned int>().max();
		}

		for (std::set<int>::const_reverse_iterator it = dbmTokensToRemove.rbegin(); it != dbmTokensToRemove.rend(); it++) {
			new_dbm.remove_clock(*it);
			for (int k = *it; k < oldDimension; k++)
				if (table[k] == std::numeric_limits<unsigned int>().max())
					table[k] = k-1;
				else
					table[k] -= 1;
		}


		assert(oldDimension-dbmTokensToRemove.size() > 0); // should at least be the zero clock left in the DBM

		// fix token mapping according to new DBM:
		for(unsigned int i = 0; i < oldDimension; ++i)
		{
			if(table[i] != std::numeric_limits<unsigned int>().max())
			{
				for(unsigned int j = 0; j < mapping.size(); ++j)
				{
					if(mapping.GetMapping(j) == i)
						mapping.SetMapping(j, table[i]);
				}
			}
		}

		// remove tokens from mapping and placement
		for(std::set<int>::const_reverse_iterator it = tokenIndices.rbegin(); it != tokenIndices.rend(); it++)
		{
			mapping.RemoveToken(*it);
			dp.RemoveToken(*it);
		}

		assert(IsConsistent());
	}

	void DBMMarking::InitMapping()
	{
		for(unsigned int i = 0; i < dp.size(); i++)
		{
			mapping.SetMapping(i, i+1);
		}
	}

	relation DBMMarking::ConvertToRelation(pardibaal::relation_t rel) const
	{
		return rel.is_equal() ? EQUAL : rel.is_subset() ? SUBSET : rel.is_superset() ? SUPERSET : DIFFERENT;
	}

	bool DBMMarking::IsUpperPositionGreaterThanPivot(int upper, int pivotIndex) const
	{
		int placeUpper = dp.GetTokenPlacement(upper);
		int pivot = dp.GetTokenPlacement(pivotIndex);
		unsigned int mapUpper = mapping.GetMapping(upper);
		unsigned int mapPivot = mapping.GetMapping(pivotIndex);
		if(mapPivot > dp.size()+1){
			std::cout << "*";
		}

		auto l_mapUpper = new_dbm.at(0,mapUpper),
		     l_mapPivot = new_dbm.at(0,mapPivot),
			 u_mapUpper = new_dbm.at(mapUpper,0),
			 u_mapPivot = new_dbm.at(mapPivot,0),
			 pivot_upper = new_dbm.at(mapPivot,mapUpper),
			 upper_pivot = new_dbm.at(mapUpper,mapPivot);


		return DiscreteMarking::IsUpperPositionGreaterThanPivot(upper, pivotIndex)
			|| (placeUpper == pivot && l_mapUpper >  l_mapPivot)
			|| (placeUpper == pivot && l_mapUpper == l_mapPivot && u_mapUpper > u_mapPivot)
			|| (placeUpper == pivot && l_mapUpper == l_mapPivot && u_mapUpper == u_mapPivot && (mapPivot > mapUpper ? pivot_upper > upper_pivot : upper_pivot > pivot_upper));
	}

	void DBMMarking::Swap(int i, int j)
	{
		DiscreteMarking::Swap(i,j);
		new_dbm.swap_clocks(mapping.GetMapping(i), mapping.GetMapping(j));
	}

	void DBMMarking::Print(std::ostream& out) const
	{
		out << "Placement: ";
		for(unsigned int i = 0; i < NumberOfTokens(); i++)
		{
			out << GetTokenPlacement(i) << ", ";
		}
		out << std::endl;
		out << "Mapping (token:clock): ";
		for(unsigned int i = 0; i < NumberOfTokens(); i++)
		{
			out << i << ":" << GetClockIndex(i) << ", ";
		}
		out << std::endl;
		out << "DBM:" << std::endl;
		out << new_dbm;
		out << "FIXME" << std::endl;
	};
}
