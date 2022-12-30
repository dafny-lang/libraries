include "Utils/Unicode.dfy"
include "Errors.dfy"
include "API.dfy"
include "ZeroCopy/API.dfy"
include "../Collections/Sequences/Seq.dfy"

abstract module JSON.Tests.Wrapper {
  import Utils.Str
  import Utils.Unicode
  import opened BoundedInts

  import opened Errors

  type JSON
  method Deserialize(bs: bytes) returns (js: DeserializationResult<JSON>)
  method SpecSerialize(js: JSON) returns (bs: SerializationResult<bytes>)
  method Serialize(js: JSON) returns (bs: SerializationResult<bytes>)
  method Check(bs: bytes, js: JSON, bs': bytes, sbs': bytes, js': JSON)

  method TestBytestring(bs: bytes, indent: string) {
    var js  :- expect Deserialize(bs);
    // print indent, "=> ", js, "\n";
    var bs'  :- expect Serialize(js);
    print indent, "=> " + Unicode.Transcode8To16(bs') + "\n";
    var sbs' :- expect SpecSerialize(js);
    print indent, "=> " + Unicode.Transcode8To16(sbs') + "\n";
    var js'  :- expect Deserialize(bs');
    Check(bs, js, bs', sbs', js');
  }

  method TestString(str: string, indent: string) {
    var bs := Unicode.Transcode16To8(str);
    TestBytestring(bs, indent);
  }

  method TestStrings(vectors: seq<string>) {
    for i := 0 to |vectors| {
      var input := vectors[i];
      var idx := Str.OfInt(i);
      var indent := seq(|idx| + 1, _ => ' ');
      print "[", idx, "]: ", input, "\n";
      TestString(input, indent);
      print "\n";
    }
  }
}

module JSON.Tests.ZeroCopyWrapper refines Wrapper {
  import opened Wrappers
  import Grammar
  import ZeroCopy.API
  import ConcreteSyntax.Spec

  type JSON = Grammar.JSON

  method Deserialize(bs: bytes) returns (js: DeserializationResult<JSON>) {
    js := API.Deserialize(bs);
  }

  method Serialize(js: JSON) returns (bs: SerializationResult<bytes>) {
    // print "Count: ", wr.chain.Count(), "\n";
    bs := API.Serialize(js);
  }

  method SpecSerialize(js: JSON) returns (bs: SerializationResult<bytes>) {
    bs := Success(Spec.JSON(js));
  }

  method Check(bs: bytes, js: JSON, bs': bytes, sbs': bytes, js': JSON) {
    expect sbs' == bs' == bs;
    expect js' == js; // This doesn't hold in general, since the views could be different
  }
}

module JSON.Tests.AbstractSyntaxWrapper refines Wrapper {
  import opened Wrappers
  import Grammar
  import API
  import AST
  import Spec

  type JSON = AST.JSON

  method Deserialize(bs: bytes) returns (js: DeserializationResult<JSON>) {
    js := API.Deserialize(bs);
  }

  method Serialize(js: JSON) returns (bs: SerializationResult<bytes>) {
    bs := API.Serialize(js);
  }

  method SpecSerialize(js: JSON) returns (bs: SerializationResult<bytes>) {
    bs := Success(Spec.JSON(js));
  }

  method Check(bs: bytes, js: JSON, bs': bytes, sbs': bytes, js': JSON) {
    expect sbs' == bs'; // Serializing changes number representations, escapes, and spacing, so no == bs
    expect js' == js;
  }
}

module JSON.Tests {
  const VECTORS := [
    "true",
    "false",
    "null",
    "\"\"",
    "\"string\"",
    "[\"A\"]",
    "-123.456e-18",
    "[]",
    "[ ]",
    "[1]",
    "[1, 2]",
    "{}",
    "{ \"a\": 1 }",
    "{ \"a\": \"b\" }",
    "{ \"some\" : \"string\", \"and\": [ \"a number\", -123.456e-18 ] }",

    "  true  ",
    " {  } ",
    "\"\\t\\r\\n\\f\"",
    "\"\u2200ABC // \\u2200ABC\"", // ∀
    "\"\uD83C\uDDEB\uD83C\uDDF7ABC // \\ud83c\\udDeB\\ud83c\\uDDF7ABC\"", // 🇫🇷

    "[true, false , null, { \"some\" : \"string\", \"and\": [ \"a number\", -123.456e-18 ] } ]  "
  ];

  method Main() {
    ZeroCopyWrapper.TestStrings(VECTORS);
    AbstractSyntaxWrapper.TestStrings(VECTORS);
  }
}
