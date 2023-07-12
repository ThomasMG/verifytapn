#ifndef DISCRETEPARTINCLUSIONMARKING_HPP_
#define DISCRETEPARTINCLUSIONMARKING_HPP_

#include "StoredMarking.hpp"
#include <vector>
#include "boost/functional/hash.hpp"
#include <algorithm>
#include "TokenMapping.hpp"
#include "../../typedefs.hpp"
#include <iosfwd>
#include <pardibaal/DBM.h>

namespace VerifyTAPN {

class DiscretePartInclusionMarking : public StoredMarking {
	friend class DiscreteInclusionMarkingFactory;
public:
	DiscretePartInclusionMarking(const DiscretePartInclusionMarking& dm) : eq(dm.eq), inc(dm.inc), mapping(dm.mapping), new_dbm(dm.new_dbm), id(dm.id) { };

	DiscretePartInclusionMarking(id_type id, const std::vector<int>& eq, const std::vector<int>& inc, const TokenMapping& mapping, const pardibaal::DBM new_dbm) : eq(eq), inc(inc), mapping(mapping), new_dbm(new_dbm), id(id) { };

	virtual ~DiscretePartInclusionMarking() { };

	virtual size_t HashKey() const { return boost::hash_range(eq.begin(), eq.end()); };

	virtual relation Relation(const StoredMarking& stored) const
	{
		const DiscretePartInclusionMarking& other = static_cast<const DiscretePartInclusionMarking&>(stored);

		if(eq != other.eq) return DIFFERENT; // Not sure we need to check this, the hashing ensures that we get a list with the same eq part?

		unsigned int place = inc.size();
		bool checkSuperset = false;
		relation result = EQUAL;

		assert(inc.size() == other.inc.size());
		for(unsigned int i = 0; i < inc.size(); i++)
		{
			if(inc[i] != other.inc[i])
			{
				if(inc[i] > other.inc[i]) checkSuperset = true;
				place = i;
				break;
			}
		}

		if(place != inc.size())
		{
			if(checkSuperset)
			{
				for(unsigned int i = place+1; i < inc.size(); i++)
				{
					if(inc[i] < other.inc[i]) return DIFFERENT;
				}
				result = SUPERSET;
			}
			else
			{
				for(unsigned int i = place+1; i < inc.size(); i++)
				{
					if(inc[i] > other.inc[i]) return DIFFERENT;
				}
				result = SUBSET;
			}
		}
		//TODO: do dmb2 relation stuff as well
		auto dbm_rel = new_dbm.relation(other.new_dbm);
		relation rel = dbm_rel.is_equal() ? EQUAL : dbm_rel.is_subset() ? SUBSET : dbm_rel.is_superset() ? SUPERSET : DIFFERENT;

		if(result == rel) return result;
		if(result == EQUAL) return rel;
		if(result == SUBSET && rel == EQUAL) return SUBSET;
		if(result == SUPERSET && rel == EQUAL) return SUPERSET;

		return DIFFERENT;
	}

	unsigned int GetClockIndex(unsigned int index) { return mapping.GetMapping(index); };

	unsigned int size() const
	{
		int size = eq.size();
		for(unsigned int i = 0; i < inc.size(); i++)
		{
			size += inc[i];
		}

		return size;
	};

	virtual unsigned int UniqueId() const { return id; };
	virtual void Print(std::ostream& out) const;

	virtual const std::vector<int>& inclusionTokens() const { return inc; };
private:
	relation ConvertToRelation(pardibaal::relation_t rel) const
	{
		return rel.is_equal() ? EQUAL : rel.is_subset() ? SUBSET : rel.is_superset() ? SUPERSET : DIFFERENT;
	}

private:
	std::vector<int> eq;
	std::vector<int> inc;
	TokenMapping mapping;
	pardibaal::DBM new_dbm;
	id_type id;
};

}

#endif /* DISCRETEPARTINCLUSIONMARKING_HPP_ */
