/*******************************************************************************
*  Copyright by the contributors to the Dafny Project
*  SPDX-License-Identifier: MIT
*******************************************************************************/

// RUN: %dafny /compile:0 "%s"

module {:options "/functionSyntax:4"} MutableMap {
    class MutableMap<K,V> {
      function {:extern} content(): map<K, V>

      constructor {:extern} ()
        ensures this.content() == map[]

      method {:extern} Add(k: K, v: V)
        modifies this 
        ensures k in content().Keys && v in content().Values

      function {:extern} Keys(): (keys: set<K>)
        reads this
        ensures keys == content().Keys

      function {:extern} Values(): (values: set<V>)
        reads this
        ensures values == content().Values

      function {:extern} Find(k: K): (v: V)
        reads this
        requires k in this.Keys()
        ensures v in content().Values
      
      method {:extern} Remove(k: K)
        modifies this
        ensures this.content().Keys == old(this.content)().Keys - {k}

      function {:extern} Size(): (size: int)
        reads this
        ensures size == |content().Values|
    }
}