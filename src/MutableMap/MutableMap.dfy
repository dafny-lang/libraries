/*******************************************************************************
*  Copyright by the contributors to the Dafny Project
*  SPDX-License-Identifier: MIT
*******************************************************************************/

// RUN: %dafny /compile:0 "%s"

module {:extern "MutableMap"} {:options "/functionSyntax:4"} MutableMap {
  class {:extern} MutableMap<K(==),V> {
    function {:extern} content(): map<K, V>
      reads this

    constructor {:extern} ()
      ensures this.content() == map[]
      ensures |this.content()| == 0

    method {:extern} Put(k: K, v: V)
      modifies this 
      ensures k in this.content().Keys
      ensures v in this.content().Values
      ensures this.content()[k] == v
      ensures 
        if k !in old(this.content)() then  
          |this.content()| == |old(this.content)()| + 1 
        else 
          |this.content()| == |old(this.content)()|

    function {:extern} Keys(): (keys: set<K>)
      reads this
      ensures keys == this.content().Keys

    function {:extern} Values(): (values: set<V>)
      reads this
      ensures values == this.content().Values

    function {:extern} Find(k: K): (v: V)
      reads this
      requires k in this.Keys()
      ensures v in this.content().Values
      ensures this.content()[k] == v
    
    method {:extern} Remove(k: K)
      modifies this
      ensures this.content().Keys == old(this.content)().Keys - {k}
      ensures 
        if k in old(this.content)() then 
          && |this.content()| == |old(this.content)()| - 1 
          && this.content().Values == old(this.content)().Values - { old(this.content)()[k] }
        else 
          |this.content()| == |old(this.content)()|

    function {:extern} Size(): (size: int)
      reads this
      ensures size == |this.content()|
  }
}

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
      m := (map k' | k' in m && k' != k :: m[k']);
    }

    function Size(): (size: int)
    {
      |m|
    }
  }
}

module Program {
  import opened MutableMapFeasability

  method Main() {
    var m := new MutableMap<string,string>();
    assert m.Size() == 0;
    assert "testkey" !in m.Keys();
    m.Put("testkey", "testvalue");
    //assert m.Size() == 1;
    assert "testkey" in m.Keys();
    assert "testvalue" in m.Values();
    assert m.Find("testkey") == "testvalue";
    m.Remove("testkey");
    assert "testkey" !in m.Keys();
    m.Put("testkey", "testvalue");
    assert "testkey" in m.Keys();
    //assert m.Size() == 1;
  }
}