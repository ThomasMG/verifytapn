/* 
 * File:   PData.h
 * Author: Peter Gjøl Jensen
 *
 * Created on 5. november 2012, 10:22
 */


#include "NonStrictMarking.hpp"
#include "EncodingStructure.h"
#include "TimeDart.hpp"
#include <bdd.h>

#ifndef PDATA_H
#define	PDATA_H
namespace VerifyTAPN {
    namespace DiscreteVerification {

        // pointer containing enough data to reconstruct the stored data at any time!
        template<typename T>
        struct EncodingPointer {
            // The part of the encoding not being represented by the path in the PTrie
            EncodingStructure<T*> encoding;
            // The coresponding node in the PTrie
            unsigned int node;

            // empty constructor
            EncodingPointer() {
            };
            
            // Construct a pointer with enough (persistent) data to recreate the marking. 
            // The encoding is cloned as it is not persistant in the PTrie
            EncodingPointer(EncodingStructure<T*> &en, unsigned int n) : encoding(en.clone()), node(n) {
            }
            
            ~EncodingPointer(){

            }
            
        };
        
        template<typename T>
        class PTrie {
        public:
            typedef unsigned int uint;
            typedef EncodingStructure<T*> MarkingEncoding;

            struct Result {
                bool isNew;
                MarkingEncoding encoding;
                uint pos;

                Result(bool ex, MarkingEncoding en, uint node) : isNew(ex), encoding(en), pos(node) {
                };
            };

            class PNode {
            public:
               
                
                PNode() : highpos(0), lowpos(0), highCount(-1), lowCount(-1), parent(0), data(NULL) {
                }
                
                inline void replaceData(MarkingEncoding* newData){
                    delete[] data;
                    data = newData;
                }
                inline MarkingEncoding* getData(){
                    return data;
                }
                
                uint highpos;
                uint lowpos;
                short int highCount;
                short int lowCount;
                uint parent;
            private:
                MarkingEncoding* data;
            };


            PTrie(TAPN::TimedArcPetriNet& tapn, int knumber, int nplaces, int mage) :
            maxNumberOfTokens(knumber),
            maxAge(mage + 1),
            numberOfPlaces(nplaces),
            countBitSize(ceil(log2((knumber ? knumber : 1)) + 1)),
            offsetBitSize(ceil(log2((nplaces * (mage + 1))) + 1) + countBitSize),
            markingBitSize(offsetBitSize * (knumber ? knumber : 1)),
            blockSize(128),
            tapn(tapn) {
                bdd_init(10000,10000);
                theBDD = bddfalse;
                waiting = bddfalse;
                stored = 0;
                totalSize = blockSize;
                this->pnodeArray.push_back(new PNode[this->totalSize]);
                pnodeArray[0][0].highCount = pnodeArray[0][0].lowCount = 0;
                pnodeArray[0][0].lowpos = pnodeArray[0][0].highpos = 0;
                pnodeArray[0][0].parent = 0;
                nextFree = 1;
                encoding = MarkingEncoding(this->markingBitSize);
                overhead = MarkingEncoding::overhead(this->markingBitSize);
                
                this->markingBitSize += overhead;
                bdd_setvarnum(this->markingBitSize);
                blockCount = 0;
                splitThreshold = sizeof (PNode) * 8;
                //+ sizeof (std::list<PNode, allocator<PNode> >) * 4;

            };
            virtual ~PTrie();

            uint splitThreshold;

            bool search(MarkingEncoding* arr, MarkingEncoding en, int size) {
                for (int i = 0; i < size; i++) {
                    if (arr[i] == en)
                        return true;
                }
                return false;
            }

            bool add(NonStrictMarkingBase* marking);

            unsigned int size() {
                return stored;
            }
            void printMemStats();
            void printEncoding(bool* encoding, int length);

            inline PNode* fetchNode(uint i) {
                return &pnodeArray[i / blockSize][i % blockSize];
            }
            NonStrictMarkingBase* enumerateDecode(const EncodingPointer<T>& pointer);
            bool hasWaitingStates(){return !(waiting == bddfalse);};
            NonStrictMarkingBase* getNextUnexplored();

            int enumeratedEncoding(NonStrictMarkingBase* marking);
            const uint maxNumberOfTokens;
            const uint maxAge;
            const uint numberOfPlaces;
            const uint countBitSize;
            const uint offsetBitSize;
            uint markingBitSize;
            const uint blockSize;

            TAPN::TimedArcPetriNet& tapn;

            MarkingEncoding encoding;
            vector<PNode*> pnodeArray;
            uint totalSize;
            uint stored;
            uint nextFree;
            uint overhead;
            uint blockCount;
            bdd theBDD;
            bdd waiting;
        };

        template<typename T>
        PTrie<T>::~PTrie() {
        }


        template<typename T>
        int PTrie<T>::enumeratedEncoding(NonStrictMarkingBase* marking) {
            encoding.zero();

            int tc = 0;
            uint bitcount = 0;

            for (vector<Place>::const_iterator pi = marking->getPlaceList().begin();
                    pi != marking->getPlaceList().end();
                    pi++) { // for each place

                int pc = pi->place->getIndex();

                for (TokenList::const_iterator ti = pi->tokens.begin(); // for each token-element
                        ti != pi->tokens.end();
                        ti++) {


                    int offset = tc * this->offsetBitSize; // the offset of the variables for this token
                    uint number = ti->getCount();
                    bitcount = 0;
                    while (number) { // set the vars while there are bits left
                        if (number & 1) {
                            this->encoding.set(overhead + offset + bitcount, true);
                        }
                        bitcount++;
                        number = number >> 1;
                    }
                    uint pos = pc + this->numberOfPlaces * ti->getAge(); // the enumerated configuration of the token
                    bitcount = countBitSize;
                    /* binary */
                    while (pos) { // set the vars while there are bits left
                        if (pos & 1) {
                            this->encoding.set(overhead + offset + bitcount, true);
                        }
                        bitcount++;
                        pos = pos >> 1;
                    }
                    tc++;
                }
            }
            if (tc == 0)
                return 0;
            else
                return ((tc - 1) * this->offsetBitSize) + bitcount;
        }

        template<typename T>
        NonStrictMarkingBase* PTrie<T>::enumerateDecode(const EncodingPointer<T> &pointer) {
            NonStrictMarkingBase* m = new NonStrictMarkingBase();


            uint var = 0;

            var += this->overhead;


            uint nbits = (var - (var % 8)) + pointer.encoding.Size()*8;


            var = this->markingBitSize - 1;
            // foreach token
            uint data = 0;
            uint count = 0;
            for (int i = this->maxNumberOfTokens - 1; i >= 0; i--) {
                uint offset = (this->offsetBitSize * i) + this->overhead + this->countBitSize;
                while (nbits >= offset) {
                    data = data << 1;

                    if (encoding.at(nbits)) {
                        data = data | 1;
                    }
                    if (nbits == 0) {
                        break;
                    }
                    nbits--;
                }
                offset -= this->countBitSize;
                while (nbits >= offset) {
                    count = count << 1;

                    if (encoding.at(nbits)) {
                        count = count | 1;
                    }
                    if (nbits == 0) {
                        break;
                    }
                    nbits--;
                }

                if (count) {
                    int age = floor(data / this->numberOfPlaces);
                    uint place = (data % this->numberOfPlaces);
                    Token t = Token(age, count);
                    m->addTokenInPlace(tapn.getPlace(place), t);
                    data = 0;
                    count = 0;
                }
            }
            return m;
        }

        template<typename T>
        bool PTrie<T>::add(NonStrictMarkingBase* marking) {
            bdd toAdd = bddtrue;
            enumeratedEncoding(marking);
           
            for(uint i = 0; i < this->markingBitSize; ++i){
                if(encoding.at(i)) {
                    toAdd &= bdd_ithvar(i);
                } else {
                    toAdd &= ! bdd_ithvar(i);
                }
            }
            bdd conjunction = (this->theBDD & toAdd);
            if(conjunction == bddfalse){
                this->theBDD = this->theBDD | toAdd;
                this->waiting = this->waiting | toAdd;
                return true;
            }
            return false;

        }
        
        template<typename T>
        NonStrictMarkingBase* PTrie<T>::getNextUnexplored(){
            encoding.zero();
            bdd toRemove = bdd_fullsatone(this->waiting);
            bdd tmpBDD = toRemove;
            for(uint i = 0; i < this->markingBitSize; ++i){
                if(tmpBDD == bddtrue){
                    break;
                } else {
                    if(bdd_high(tmpBDD) != bddfalse) {
                        tmpBDD = bdd_high(tmpBDD);
                        encoding.set(i,true);
                    } else if(bdd_low(tmpBDD) != bddfalse) {
                        tmpBDD = bdd_low(tmpBDD);
                    }
                }
            }
            this->waiting &= (! toRemove);
            bdd_gbc();
            EncodingPointer<T> e;
            e.encoding = encoding;
            e.node = 0;
            NonStrictMarkingBase* m = this->enumerateDecode(e);

            return m;
        }

        template<typename T>
        void PTrie<T>::printMemStats() {
            cout << endl << "Encoding size;" << endl <<
                    "\t\t\t" << this->markingBitSize << endl;
            cout << "Lists:" << endl <<
                    "\t count \t\t" << this->blockCount << endl;
            cout << "Nodes:" << endl <<
                    "\t count \t\t" << this->nextFree - 1 << endl;
        }

        template<typename T>
        void PTrie<T>::printEncoding(bool* encoding, int length) {
            for (int i = 0; i < length; i++)
                cout << encoding[i];
            cout << endl;
        }
    }
}
#endif	/* PDATA_H */

