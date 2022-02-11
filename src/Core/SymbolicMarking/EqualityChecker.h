/*
 * Copyright Thomas Møller Grosen 
 * Created on 10/02/2022
 */

/*
 * This file is part of verifytapn
 *
 * verifytapn is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published by
 * the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * verifytapn is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with verifytapn. If not, see <https://www.gnu.org/licenses/>.
 */
#ifndef VERIFYTAPN_NEWDBMEQUALITY_H
#define VERIFYTAPN_NEWDBMEQUALITY_H
#include <dbm/fed.h>
#include <dbm/print.h>
#include <dbm2/DBM.h>
namespace VerifyTAPN {
    class EqualityChecker {
    public:
        static bool dbm_equal_dbm2(dbm::dbm_t dbm, dbm2::DBM dbm2) {
            if (dbm.getDimension() != dbm2._bounds_table._number_of_clocks)
                return false;

            if (!dbm.isEmpty() && !dbm2.is_empty()) {
                for (int i = 0; i < dbm.getDimension(); i++) {
                    for (int j = 0; j < dbm.getDimension(); j++) {
                        if (dbm_raw2bound(dbm(i, j)) != dbm2._bounds_table.at(i, j)._n ||
                            dbm_raw2strict(dbm(i, j)) == dbm2._bounds_table.at(i, j)._strict) {
                            if (dbm_raw2bound(dbm(i, j)) == dbm_INFINITY && !dbm2._bounds_table.at(i, j)._inf ||
                                dbm_raw2bound(dbm(i, j)) != dbm_INFINITY && dbm2._bounds_table.at(i, j)._inf)
                                return false;
                        }
                    }
                }
            }
            return true;
        }

        static void assertEqualDbms(dbm::dbm_t dbm, dbm2::DBM dbm2) {
            if (!dbm_equal_dbm2(dbm, dbm2)) {
                std::cout << "ERROR: DBM inconsistency!\nDBM:\n" << dbm << "New DBM:\n" << dbm2;
            }

            assert(dbm_equal_dbm2(dbm, dbm2));
        }
    };
}
#endif //VERIFYTAPN_NEWDBMEQUALITY_H
