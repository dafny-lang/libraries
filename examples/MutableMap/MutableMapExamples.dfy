/*******************************************************************************
*  Copyright by the contributors to the Dafny Project
*  SPDX-License-Identifier: MIT
*******************************************************************************/

// RUN: %dafny /compile:0 "%s"

include "../../src/MutableMap/MutableMap.dfy"

module MutableMapExamples {
  import opened MutableMap

  method Main() {
    var m := new MutableMap<string,string>();
    assert m.Keys() == {};
    assert m.Values() == {};
    assert m.Items() == {};
    assert m.Size() == 0;
    m.Put("testkey", "testvalue");
    assert m.Find("testkey") == "testvalue";
    assert m.Keys() == {"testkey"};
    assert m.Values() == {"testvalue"};
    assert m.Items() == {("testkey", "testvalue")};
    assert m.Size() == 1;
    m.Put("testkey", "testvalue2");
    assert m.Keys() == {"testkey"};
    assert m.Values() == {"testvalue2"};
    assert m.Items() == {("testkey", "testvalue2")};
    m.Put("testkey2", "testvalue2");
    assert m.Keys() == {"testkey", "testkey2"};
    assert m.Values() == {"testvalue2"};
    assert m.Items() == {("testkey", "testvalue2"), ("testkey2", "testvalue2")};
    assert m.Size() == 2;
    assert "testkey" in m.Keys();
    assert "testkey2" in m.Keys();
    m.Remove("testkey");
    assert "testkey" !in m.Keys();
/*  assert "testkey2" in m.Keys();
    assert m.Keys() == {"testkey2"};
    assert m.Values() == {"testvalue2"};
    assert m.Items() == {("testkey2", "testvalue2")}; */
  }
}