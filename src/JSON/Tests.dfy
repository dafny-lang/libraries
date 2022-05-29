include "Grammar.dfy"
include "Deserializer.dfy"
include "../Collections/Sequences/Seq.dfy"

import opened BoundedInts

import opened Vs = Views.Core

import opened JSON.Grammar
import opened JSON.Deserializer

function method bytes_of_ascii(s: string) : bytes {
  Seq.Map((c: char) requires c in s => if c as int < 256 then c as byte else 0 as byte, s)
}

function method ascii_of_bytes(bs: bytes) : string {
  Seq.Map((b: byte) requires b in bs => b as char, bs)
}

const VECTORS := [
  "true",
  "false",
  "null",
  "\"\"",
  "\"string\"",
  "[\"A\"]",
  "-123.456e-18",
  "[]",
  "[1]",
  "[1, 2]",
  "{}",
  "{ \"a\": 1 }",
  "{ \"a\": \"b\" }",
  "{ \"some\" : \"string\", \"and\": [ \"a number\", -123.456e-18 ] }",
  "[true, false , null, { \"some\" : \"string\", \"and\": [ \"a number\", -123.456e-18 ] } ]  "
];

method Main() {
  for i := 0 to |VECTORS| {
    var input := VECTORS[i];
    expect |input| < 0x1_00000000;

    print input, "\n";
    var bytes := bytes_of_ascii(input);
    match Deserializer.Top.Text(View.OfBytes(bytes)) {
      case Failure(msg) =>
        print "Parse error: " + msg.ToString((e: Deserializer.Core.JSONError) => e.ToString()) + "\n";
        expect false;
      case Success(js) =>
        var bytes' := Grammar.Bytes(js);
        print "=> " + ascii_of_bytes(bytes') + "\n";
        expect bytes' == bytes;
    }
    print "\n";
  }
}
