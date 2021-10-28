/*
 * PWList.cpp
 *
 *  Created on: 01/03/2012
 *      Author: MathiasGS
 */

#include "PWList.hpp"

namespace VerifyTAPN {
namespace DiscreteVerification {

bool PWList::add(NonStrictMarking* marking){
	discoveredMarkings++;
	NonStrictMarkingList& m = markings_storage[marking->getHashKey()];
	for(NonStrictMarkingList::const_iterator iter = m.begin();
			iter != m.end();
			iter++){
		if((*iter)->equals(*marking)){
                    if(isLiveness){
                        marking->meta = (*iter)->meta;
                        if(!marking->meta->passed){
                                (*iter)->setGeneratedBy(marking->getGeneratedBy());
                                waiting_list->add(*iter, *iter);
                                return true;
                        }
                    }
                    return false;
		}
	}
        stored++;
	m.push_back(marking);
        marking->meta = new MetaData();
	waiting_list->add(marking, marking);
	return true;
}

NonStrictMarking* PWList::getNextUnexplored(){
	return waiting_list->pop();
}

PWList::~PWList() {
    // We don't care, it is deallocated on program execution done
}

std::ostream& operator<<(std::ostream& out, PWList& x){
	out << "Passed and waiting:" << std::endl;
	for(PWList::HashMap::iterator iter = x.markings_storage.begin(); iter != x.markings_storage.end(); iter++){
		for(PWList::NonStrictMarkingList::iterator m_iter = iter->second.begin(); m_iter != iter->second.end(); m_iter++){
			out << "- "<< *m_iter << std::endl;
		}
	}
	out << "Waiting:" << std::endl << x.waiting_list;
	return out;
}

        bool PWListHybrid::add(NonStrictMarking* marking) {

            discoveredMarkings++;

            bool res = passed->add(marking);
            if(res){
             //   this->waiting_list->add(marking, marking);
                return true;
            }
            return false;
        }

        NonStrictMarking* PWListHybrid::getNextUnexplored() {
            return (NonStrictMarking*)passed->getNextUnexplored();
        }

        PWListHybrid::~PWListHybrid() {
            // We don't care, it is deallocated on program execution done
        }


} /* namespace DiscreteVerification */
} /* namespace VerifyTAPN */
