include "MutableMap.dfy"

module {:options "/functionSyntax:4"} MutableMapFeasability refines MutableMap {
  class MutableMap<K(==),V> ... {
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

    function Keys(): (keys: set<K>)
    {
      m.Keys
    }

    function Values(): (values: set<V>)
    {
      m.Values
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