/*******************************************************************************
 *  Copyright by the contributors to the Dafny Project
 *  SPDX-License-Identifier: MIT
 *******************************************************************************/

var DafnyLibraries = DafnyLibraries || {};
DafnyLibraries.Random = (function () {
    let $module = {};

    $module.nextBool = function () {
        try {
        return Math.random() < 0.5;
        } catch (e) {
            throw "nextBool failed";
        }
    }

    $module.nextInt = function (bound) {
        bound = bound > 0 ? bound : Number.MAX_SAFE_INTEGER;
        return new BigNumber(Math.floor(Math.random() * bound));
    }

    $module.nextReal = function () {
        num = Math.floor(Math.random() * Number.MAX_SAFE_INTEGER);
        den = Number.MAX_SAFE_INTEGER;
        return new _dafny.BigRational(new BigNumber(num), new BigNumber(den));
    }

    return $module;
})();
