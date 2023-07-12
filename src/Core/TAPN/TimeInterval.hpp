#ifndef VERIFYTAPN_TAPN_TIMEINTERVAL_HPP_
#define VERIFYTAPN_TAPN_TIMEINTERVAL_HPP_

#include <limits>
#include <iostream>
#include <pardibaal/bound_t.h>

namespace VerifyTAPN {
	namespace TAPN {

		class TimeInterval
		{
		public: // Construction
			TimeInterval() : leftStrict(false), lowerBound(0), upperBound(std::numeric_limits<int>::max()), rightStrict(true){ };
			TimeInterval(bool leftStrict, int lowerBound, int upperBound, bool rightStrict) : leftStrict(leftStrict), lowerBound(lowerBound), upperBound(upperBound), rightStrict(rightStrict) { };
			TimeInterval(const TimeInterval& ti) : leftStrict(ti.leftStrict), lowerBound(ti.lowerBound), upperBound(ti.upperBound), rightStrict(ti.rightStrict) {};
			TimeInterval& operator=(const TimeInterval& ti)
			{
				leftStrict = ti.leftStrict;
				lowerBound = ti.lowerBound;
				upperBound = ti.upperBound;
				rightStrict = ti.rightStrict;
				return *this;
			}

			virtual ~TimeInterval() { /* empty */ }

		public: // inspectors
			void Print(std::ostream& out) const;
			inline const int GetLowerBound() const { return lowerBound; }
			inline const int GetUpperBound() const { return upperBound; }
			inline const bool IsLowerBoundStrict() const { return leftStrict; }
			inline const bool IsUpperBoundStrict() const { return rightStrict; }

			inline pardibaal::bound_t LowerBoundToDBM2Bound() const
			{
			    return pardibaal::bound_t(-lowerBound, leftStrict);
			};

            inline pardibaal::bound_t UpperBoundToDBM2Bound() const
            {
                if(upperBound == std::numeric_limits<int>().max())
                {
                    return pardibaal::bound_t::inf();
                }
                else
                {
                    return pardibaal::bound_t(upperBound, rightStrict);
                }
            };

			inline const bool IsZeroInfinity() const { return !leftStrict && lowerBound == 0 && upperBound == std::numeric_limits<int>().max() && rightStrict; }

		public: // statics
			static TimeInterval CreateFor(const std::string& interval);


		private: // data
			bool leftStrict;
			int lowerBound;
			int upperBound;
			bool rightStrict;
		};

		inline std::ostream& operator<<(std::ostream& out, const TimeInterval& interval)
		{
			interval.Print(out);
			return out;
		}
	}
}

#endif /* VERIFYTAPN_TAPN_TIMEINTERVAL_HPP_ */
