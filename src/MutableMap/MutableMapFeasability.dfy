include "MutableMap.dfy"

module {:options "/functionSyntax:4"} MutableMapFeasability refines MutableMap {
  class MutableMap<K(==),V(==)> ... {
    var m: map<K,V>

    function content(): map<K, V> {
      m
    }

    constructor ()
    {
      m := map[];
    }

    method Put(k: K, v: V) 
    {
      m := m[k := v];
    }

    function Keys(): set<K>
    {
      m.Keys
    }

    function Values(): set<V>
    {
      m.Values
    }

    function Items(): set<(K,V)>
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
    {
      m[k]
    }

    method Remove(k: K)
    {
      m := map k' | k' in m.Keys && k' != k :: m[k'];
    }

    function Size(): (size: int)
    {
      |m|
    }
  }
}