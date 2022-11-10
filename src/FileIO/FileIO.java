package DafnyLibraries;

import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.Paths;

import dafny.DafnySequence;
import dafny.Tuple2;
import dafny.Tuple3;
import dafny.TypeDescriptor;

public class FileIO {
    /**
     * Attempts to read all bytes from the file at {@code path}, and returns a tuple of the following values:
     * <dl>
     *     <dt>{@code isError}</dt>
     *     <dd>true iff an exception was thrown during path string conversion or when reading the file</dd>
     *     <dt>{@code bytesRead}</dt>
     *     <dd>the sequence of bytes read from the file, or an empty sequence if {@code isError} is true</dd>
     *     <dt>{@code errorMsg}</dt>
     *     <dd>the error message of the thrown exception if {@code isError} is true, or an empty sequence otherwise</dd>
     * </dl>
     * <p>
     * We return these values individually because {@code Result} is not defined in the runtime but instead in library code.
     * It is the responsibility of library code to construct an equivalent {@code Result} value.
     */
    public static Tuple3<Boolean, DafnySequence<? extends Byte>, DafnySequence<? extends Character>>
        INTERNAL_ReadBytesFromFile(DafnySequence<? extends Character> path) {
        try {
            final String pathStr = new String((char[]) path.toArray().unwrap());
            final Path pathObj = Paths.get(pathStr);
            final DafnySequence<Byte> readBytes = DafnySequence.fromBytes(Files.readAllBytes(pathObj));
            return Tuple3.create(false, readBytes, DafnySequence.empty(TypeDescriptor.CHAR));
        } catch (Exception ex) {
            final DafnySequence<Character> errorMsg = DafnySequence.of(ex.toString().toCharArray());
            return Tuple3.create(true, DafnySequence.empty(TypeDescriptor.BYTE), errorMsg);
        }
    }

    /**
     * Attempts to write {@code bytes} to the file at {@code path}, and returns a tuple of the following values:
     * <dl>
     *     <dt>{@code isError}</dt>
     *     <dd>true iff an exception was thrown during path string conversion or when writing to the file</dd>
     *     <dt>{@code errorMsg}</dt>
     *     <dd>the error message of the thrown exception if {@code isError} is true, or an empty sequence otherwise</dd>
     * </dl>
     * <p>
     * We return these values individually because {@code Result} is not defined in the runtime but instead in library code.
     * It is the responsibility of library code to construct an equivalent {@code Result} value.
     */
    public static Tuple2<Boolean, DafnySequence<? extends Character>>
        INTERNAL_WriteBytesToFile(DafnySequence<? extends Character> path, DafnySequence<? extends Byte> bytes) {
        try {
            final String pathStr = new String((char[]) path.toArray().unwrap());
            final Path pathObj = Paths.get(pathStr);

            // It's safe to cast `bytes` to `DafnySequence<Byte>` since the cast value is immediately consumed
            @SuppressWarnings("unchecked")
            final byte[] byteArr = DafnySequence.toByteArray((DafnySequence<Byte>) bytes);

            Files.write(pathObj, byteArr);
            return Tuple2.create(false, DafnySequence.empty(TypeDescriptor.CHAR));
        } catch (Exception ex) {
            final DafnySequence<Character> errorMsg = DafnySequence.of(ex.toString().toCharArray());
            return Tuple2.create(true, errorMsg);
        }
    }
}
