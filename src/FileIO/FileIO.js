const fs = require("fs");
const buffer = require("buffer");
var DafnyLibraries = DafnyLibraries || {};
DafnyLibraries.FileIO = (function() {
  let $module = {};

  /**
   * Attempts to read all bytes from the file at the given `path`, and returns an array of the following values:
   *
   *   - `isError`: true iff an error was thrown during path string conversion or when reading the file
   *   - `bytesRead`: the sequence of bytes from the file, or an empty sequence if `isError` is true
   *   - `errorMsg`: the error message of the thrown error if `isError` is true, or an empty sequence otherwise
   *
   * We return these values individually because `Result` is not defined in the runtime but instead in library code.
   * It is the responsibility of library code to construct an equivalent `Result` value.
   */
  $module.INTERNAL_ReadBytesFromFile = function(path) {
    const emptySeq = _dafny.Seq.of();
    try {
      const readOpts = { encoding: null };  // read as buffer, not string
      const buf = fs.readFileSync(path, readOpts);
      const readBytes = _dafny.Seq.from(buf.valueOf(), byte => new BigNumber(byte));
      return [false, readBytes, emptySeq];
    } catch (e) {
      const errorMsg = _dafny.Seq.from(e.toString());
      return [true, emptySeq, errorMsg];
    }
  }

  /**
   * Attempts to write all given `bytes` to the file at the given `path`, and returns an array of the following values:
   *
   *   - `isError`: true iff an error was thrown during path string conversion or when writing to the file
   *   - `errorMsg`: the error message of the thrown error if `isError` is true, or an empty sequence otherwise
   *
   * We return these values individually because `Result` is not defined in the runtime but instead in library code.
   * It is the responsibility of library code to construct an equivalent `Result` value.
   */
  $module.INTERNAL_WriteBytesToFile = function(path, bytes) {
    try {
      const buf = buffer.Buffer.from(bytes);
      fs.writeFileSync(path, buf);  // no need to specify encoding because data is a Buffer
      return [false, _dafny.Seq.of()];
    } catch (e) {
      const errorMsg = _dafny.Seq.from(e.toString());
      return [true, errorMsg];
    }
  }

  return $module;
})();
