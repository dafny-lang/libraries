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