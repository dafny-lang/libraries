include "MutableMap.dfy"

/*******************************************************************************
*  Copyright by the contributors to the Dafny Project
*  SPDX-License-Identifier: MIT
*******************************************************************************/

// RUN: %dafny /compile:0 "%s"

module {:options "/functionSyntax:4"} MutableMapTrait {
  trait MutableMapTrait<K(==),V(==)> {
    function content(): map<K, V>
      reads this

    method Put(k: K, v: V)
      modifies this
      ensures this.content() == old(this.content())[k := v]    

    function Keys(): (keys: set<K>)
      reads this
      ensures keys == this.content().Keys

    function Values(): (values: set<V>)
      reads this
      ensures values == this.content().Values

    function Items(): (items: set<(K,V)>)
      reads this
      ensures items == this.content().Items
      ensures items == set k | k in this.content().Keys :: (k, this.content()[k])

    function Find(k: K): (v: V)
      reads this
      requires k in this.Keys()
      ensures v in this.content().Values
      ensures this.content()[k] == v
    
    method Remove(k: K)
      modifies this
      ensures this.content() == old(this.content()) - {k}

    function Size(): (size: int)
      reads this
      ensures size == |this.content().Items|
  }
}

module {:options "/functionSyntax:4"} MutableMapFeasability refines MutableMapTrait {
  class MutableMap<K(==),V(==)> extends MutableMapTrait<K,V> {
    var m: map<K,V>

    function content(): map<K, V> 
      reads this
    {
      m
    }

    constructor ()
    {
      m := map[];
    }

    method Put(k: K, v: V) 
      modifies this
      ensures this.content() == old(this.content())[k := v] 
    {
      m := m[k := v];
    }

    function Keys(): (keys: set<K>)
      reads this
      ensures keys == this.content().Keys
    {
      m.Keys
    }

    function Values(): (values: set<V>)
      reads this
      ensures values == this.content().Values
    {
      m.Values
    }

    function Items(): (items: set<(K,V)>)
      reads this
      ensures items == this.content().Items
      ensures items == set k | k in this.content().Keys :: (k, this.content()[k])
    {
      var items := set k | k in m.Keys :: (k, m[k]);
      assert items == m.Items by {
        forall k | k in m.Keys ensures (k, m[k]) in m.Items {
          assert (k, m[k]) in m.Items;
        }
        assert items <= m.Items;
        forall x | x in m.Items ensures x in items {
          assert (x.0, m[x.0]) in items;
        }
        assert m.Items <= items;
      }
      items
    }

    function Find(k: K): (v: V)
      reads this
      requires k in this.Keys()
      ensures v in this.content().Values
      ensures this.content()[k] == v
    {
      m[k]
    }

    method Remove(k: K)
      modifies this
      ensures this.content() == old(this.content()) - {k}
    {
      m := map k' | k' in m.Keys && k' != k :: m[k'];
    }

    function Size(): (size: int)
      reads this
      ensures size == |this.content().Items|
    {
      |m|
    }
  }
}