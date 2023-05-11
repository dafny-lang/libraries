
include "../../src/Unicode/UnicodeStringsWithUnicodeChar.dfy"
include "../../src/JSON/API.dfy"

module UnicodeTests {

  import JSON
  import opened UnicodeStrings

  method {:test} LongString() {
    var s :=
      "AaaaaaaaaaAaaaaaaaaaAaaaaaaaaaAaaaaaaaaaAaaaaaaaaaAaaaaaaaaaAaaaaaaaaaAaaaaaaaaaAaaaaaaaaaAaaaaaaaaa" +
      "AaaaaaaaaaAaaaaaaaaaAaaaaaaaaaAaaaaaaaaaAaaaaaaaaaAaaaaaaaaaAaaaaaaaaaAaaaaaaaaaAaaaaaaaaaAaaaaaaaaa" +
      "AaaaaaaaaaAaaaaaaaaaAaaaaaaaaaAaaaaaaaaaAaaaaaaaaaAaaaaaaaaaAaaaaaaaaaAaaaaaaaaaAaaaaaaaaaAaaaaaaaaa" +
      "AaaaaaaaaaAaaaaaaaaaAaaaaaaaaaAaaaaaaaaaAaaaaaaaaaAaaaaaaaaaAaaaaaaaaaAaaaaaaaaaAaaaaaaaaaAaaaaaaaaa" +
      "AaaaaaaaaaAaaaaaaaaaAaaaaaaaaaAaaaaaaaaaAaaaaaaaaaAaaaaaaaaaAaaaaaaaaaAaaaaaaaaaAaaaaaaaaaAaaaaaaaaa" +
      "AaaaaaaaaaAaaaaaaaaaAaaaaaaaaaAaaaaaaaaaAaaaaaaaaaAaaaaaaaaaAaaaaaaaaaAaaaaaaaaaAaaaaaaaaaAaaaaaaaaa" +
      "AaaaaaaaaaAaaaaaaaaaAaaaaaaaaaAaaaaaaaaaAaaaaaaaaaAaaaaaaaaaAaaaaaaaaaAaaaaaaaaaAaaaaaaaaaAaaaaaaaaa" +
      "AaaaaaaaaaAaaaaaaaaaAaaaaaaaaaAaaaaaaaaaAaaaaaaaaaAaaaaaaaaaAaaaaaaaaaAaaaaaaaaaAaaaaaaaaaAaaaaaaaaa" +
      "AaaaaaaaaaAaaaaaaaaaAaaaaaaaaaAaaaaaaaaaAaaaaaaaaaAaaaaaaaaaAaaaaaaaaaAaaaaaaaaaAaaaaaaaaaAaaaaaaaaa" +
      "AaaaaaaaaaAaaaaaaaaaAaaaaaaaaaAaaaaaaaaaAaaaaaaaaaAaaaaaaaaaAaaaaaaaaaAaaaaaaaaaAaaaaaaaaaAaaaaaaaaa";
    var S := s + s + s + s + s + s + s + s + s + s;
    var utf8 :- expect ToUTF8Checked("\"" + S + "\"");
    var json :- expect JSON.API.Deserialize(utf8);
  }
}