/*******************************************************************************
*  Copyright by the contributors to the Dafny Project
*  SPDX-License-Identifier: MIT
*******************************************************************************/

// RUN: %run -t:java "%s" --input ../../src/MutableMap/MutableMap.java

include "../../src/MutableMap/MutableMap.dfy"
include "../../src/Wrappers.dfy"

module {:options "-functionSyntax:4"} MutableMapExamples {
  import opened MutableMap
  import opened Wrappers

  method AssertAndExpect(p: bool, maybeMsg: Option<string> := None) requires p {
    match maybeMsg {
      case None => {
          expect p;
      }
      case Some(msg) => {
          expect p, msg;
      }
    }
  }

  method Main() {
    var m := new MutableMap<string,string>();
    AssertAndExpect(m.Keys() == {});
    assert m.Values() == {};
    assert m.Items() == {};
    assert m.Size() == 0;
    m.Put("testkey", "testvalue");
    assert m.Select("testkey") == "testvalue";
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
    print m.Select("testkey"), "\n";
    print m.Select("testkey2"), "\n";
    m.Remove("testkey");
    assert m.SelectOpt("testkey").None?;
    assert m.SelectOpt("testkey2").Some? && m.SelectOpt("testkey2").value == "testvalue2";
    assert m.Keys() == {"testkey2"};
    assert m.Values() == {"testvalue2"};
    assert m.Items() == {("testkey2", "testvalue2")};
  }
}