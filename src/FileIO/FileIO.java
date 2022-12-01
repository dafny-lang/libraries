/*******************************************************************************
*  Copyright by the contributors to the Dafny Project
*  SPDX-License-Identifier: MIT
*******************************************************************************/

package DafnyLibraries;

import java.io.IOException;
import java.io.PrintWriter;
import java.io.StringWriter;
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
            final Path pathObj = dafnyStringToPath(path);
            final DafnySequence<Byte> readBytes = DafnySequence.fromBytes(Files.readAllBytes(pathObj));
            return Tuple3.create(false, readBytes, DafnySequence.empty(TypeDescriptor.CHAR));
        } catch (Exception ex) {
            return Tuple3.create(true, DafnySequence.empty(TypeDescriptor.BYTE), stackTraceToDafnyString(ex));
        }
    }

    /**
     * Attempts to write {@code bytes} to the file at {@code path}, creating nonexistent parent directories as necessary,
     * and returns a tuple of the following values:
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
            final Path pathObj = dafnyStringToPath(path);
            createParentDirs(pathObj);

            // It's safe to cast `bytes` to `DafnySequence<Byte>` since the cast value is immediately consumed
            @SuppressWarnings("unchecked")
            final byte[] byteArr = DafnySequence.toByteArray((DafnySequence<Byte>) bytes);

            Files.write(pathObj, byteArr);
            return Tuple2.create(false, DafnySequence.empty(TypeDescriptor.CHAR));
        } catch (Exception ex) {
            return Tuple2.create(true, stackTraceToDafnyString(ex));
        }
    }

    /**
     * Returns a Path constructed from the given Dafny string.
     */
    private static final Path dafnyStringToPath(final DafnySequence<? extends Character> path) {
        return Paths.get(new String((char[]) path.toArray().unwrap()));
    }

    /**
     * Creates the nonexistent parent directory(-ies) of the given path.
     */
    private static final void createParentDirs(final Path path) throws IOException {
        final Path parentDir = path.toAbsolutePath().getParent();
        if (parentDir == null) {
            return;
        }
        Files.createDirectories(parentDir);
    }

    private static final DafnySequence<Character> stackTraceToDafnyString(final Throwable t) {
        final StringWriter stringWriter = new StringWriter();
        final PrintWriter printWriter = new PrintWriter(stringWriter);
        t.printStackTrace(printWriter);
        final String str = stringWriter.toString();
        return DafnySequence.of(str.toCharArray());
    }
}
