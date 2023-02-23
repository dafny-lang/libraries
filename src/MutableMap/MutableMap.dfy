/*******************************************************************************
*  Copyright by the contributors to the Dafny Project
*  SPDX-License-Identifier: MIT
*******************************************************************************/

// RUN: %verify "%s"

include "../../examples/Mutablemap/MutableMapTrait.dfy"

/**
  *  Implements mutable maps by interfacing with external code, e.g. 
  *  "MutableMap.java".
  */
module {:extern "DafnyLibraries"} {:options "-functionSyntax:4"} MutableMap {
  import opened MutableMapTrait

  class {:extern "MutableMap"} MutableMap<K(==),V(==)> extends MutableMapTrait<K,V> {
    constructor {:extern} ()
      ensures this.content() == map[]

    function {:extern} content(): map<K, V>
      reads this

    method {:extern} Put(k: K, v: V)
      modifies this
      ensures this.content() == old(this.content())[k := v]   
      ensures k in old(this.content()).Keys ==> this.content().Values + {old(this.content())[k]} == old(this.content()).Values + {v}
      ensures k !in old(this.content()).Keys ==> this.content().Values == old(this.content()).Values + {v}

    function {:extern} Keys(): (keys: set<K>)
      reads this
      ensures keys == this.content().Keys

    predicate {:extern} HasKey(k: K)
      reads this
      ensures HasKey(k) <==> k in this.content().Keys

    function {:extern} Values(): (values: set<V>)
      reads this
      ensures values == this.content().Values

    function {:extern} Items(): (items: set<(K,V)>)
      reads this
      ensures items == this.content().Items
      ensures items == set k | k in this.content().Keys :: (k, this.content()[k])

    function {:extern} Select(k: K): (v: V)
      reads this
      requires this.HasKey(k)
      ensures v in this.content().Values
      ensures this.content()[k] == v
    
    method {:extern} Remove(k: K)
      modifies this
      ensures this.content() == old(this.content()) - {k}
      ensures k in old(this.content()).Keys ==> this.content().Values + {old(this.content())[k]} == old(this.content()).Values

    function {:extern} Size(): (size: int)
      reads this
      ensures size == |this.content().Items|
  }
}