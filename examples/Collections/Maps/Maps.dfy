// RUN: %verify "%s"

/*******************************************************************************
 * Copyright by the contributors to the Dafny Project
 * SPDX-License-Identifier: MIT
 *******************************************************************************/

include "../../../src/Functions.dfy"
include "../../../src/Collections/Maps/Maps.dfy"

module {:options "--function-syntax:4"} MapsExamples {
  import Functions
  import Maps

  function ByteKeyMapToIntKeys<Y>(m: map<bv8, Y>): (m': map<int, Y>)
  {
    Maps.MapKeys(b => b as int, m)
  }

  function ByteValueMapToIntValues<X>(m: map<X, bv8>): (m': map<X, int>)
  {
    Maps.MapValues(b => b as int, m)
  }
}
