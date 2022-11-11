"""
/*******************************************************************************
*  Copyright by the contributors to the Dafny Project
*  SPDX-License-Identifier: MIT
*******************************************************************************/
"""

import traceback

from _dafny import Seq, string_of

assert "DafnyLibraries" == __name__
DafnyLibraries = sys.modules[__name__]

class FileIO:
    @staticmethod
    def INTERNAL_ReadBytesFromFile(path: Seq) -> (bool, Seq, Seq):
        """Attempt to read all bytes from the file at the given path, and return the following values:

        * ``isError``: ``True`` iff an exception was raised during path string conversion or when reading the file
        * ``bytesRead``: the sequence of bytes read from the file, or an empty sequence if ``isError`` is ``True``
        * ``errorMsg``: the error message of the raised exception if ``isError`` is ``True``, or an empty sequence otherwise

        We return these values individually because ``Result`` is not defined in the runtime but instead in library code.
        It is the responsibility of library code to construct an equivalent ``Result`` value.
        """
        try:
            with open(string_of(path), "rb") as file:
                return False, Seq(file.read()), Seq()
        except Exception:
            return True, Seq(), Seq(traceback.format_exc())

    @staticmethod
    def INTERNAL_WriteBytesToFile(path: Seq, bytes_: Seq) -> (bool, Seq):
        """Attempt to write all given bytes to the file at the given path, and return the following values:

        * ``isError``: ``True`` iff an exception was raised during path string conversion or when writing to the file
        * ``errorMsg``: the error message of the raised exception if ``isError`` is ``True``, or an empty sequence otherwise

        We return these values individually because ``Result`` is not defined in the runtime but instead in library code.
        It is the responsibility of library code to construct an equivalent ``Result`` value.
        """
        try:
            with open(string_of(path), "wb") as file:
                file.write(bytes(bytes_))
                return False, Seq()
        except Exception:
            return True, Seq(traceback.format_exc())
