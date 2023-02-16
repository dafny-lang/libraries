/*******************************************************************************
*  Copyright by the contributors to the Dafny Project
*  SPDX-License-Identifier: MIT
*******************************************************************************/

// RUN: %dafny /compile:0 "%s"

module {:extern "MutableMap"} {:options "/functionSyntax:4"} MutableMap {
  class {:extern "MutableMap"} MutableMap<K(==),V(==)> {
    function {:extern "content"} content(): map<K, V>
      reads this

    constructor {:extern "MutableMap"} ()
      ensures this.content() == map[]

    method {:extern "put"} Put(k: K, v: V)
      modifies this
      ensures this.content() == old(this.content())[k := v]    

    function {:extern "keys"} Keys(): (keys: set<K>)
      reads this
      ensures keys == this.content().Keys

    function {:extern "values"} Values(): (values: set<V>)
      reads this
      ensures values == this.content().Values

    function {:extern "items"} Items(): (items: set<(K,V)>)
      reads this
      ensures items == this.content().Items
      ensures items == set k | k in this.content().Keys :: (k, this.content()[k])

    function {:extern "find"} Find(k: K): (v: V)
      reads this
      requires k in this.Keys()
      ensures v in this.content().Values
      ensures this.content()[k] == v
    
    method {:extern "remove"} Remove(k: K)
      modifies this
      ensures forall k' | k' in old(this.content)().Keys :: k' != k ==> (k' in this.content().Keys && old(this.content)()[k'] == this.content()[k'])
      ensures forall k' | k' in this.content().Keys :: k' in old(this.content)().Keys && k' != k
      ensures k in old(this.content)().Keys ==> k !in this.content().Keys
      ensures this.content().Values == set k' | k' in old(this.content)().Keys && k' != k :: this.content()[k']

    function {:extern "size"} Size(): (size: int)
      reads this
      ensures size == |this.content().Items|
  }
}