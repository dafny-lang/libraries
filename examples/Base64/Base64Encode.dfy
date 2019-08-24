include "../../src/Base64.dfy"

module Demo {
    method TestBase64(msg: string, expected: string)
         requires forall k :: 0 <= k < |msg| ==> 0 <= msg[k] as int < 0x100
     {
         print "The message is: ", msg, "\n";

         var byteMsg: seq<byte> := [];
         var i := 0;
         while i < |msg| {
             byteMsg := byteMsg + [msg[i] as int as byte];
             i := i + 1;
         }
         var encoded := Encode(byteMsg);
         print "The encoding is: ", encoded, "\n";
         print "The expected is: ", expected, "\n";
         print "The encoding ", (if encoded == expected then "matches" else "doesn't match"), " the expected.\n";

         var decoded := Decode(encoded);
         assert decoded.value == byteMsg;

         var dmsg := "";
         i := 0;
         while i < |decoded.value| {
             dmsg := dmsg + [decoded.value[i] as int as char];
             i := i + 1;
         }
         print "The decoded message is: ", dmsg, "\n\n";
     }

     method Main() {
         // TEST 0: No padding
         TestBase64("Hello I am a string with no padding.", "SGVsbG8gSSBhbSBhIHN0cmluZyB3aXRoIG5vIHBhZGRpbmcu");
         // TEST 1: One padding
         TestBase64("Hi, I am a string with one padding.", "SGksIEkgYW0gYSBzdHJpbmcgd2l0aCBvbmUgcGFkZGluZy4=");
         // TEST 2: Two paddings
         TestBase64("Hello I'm a string with two paddings.", "SGVsbG8gSSdtIGEgc3RyaW5nIHdpdGggdHdvIHBhZGRpbmdzLg==");
     }
}
