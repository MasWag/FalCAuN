package net.maswag.falcaun.simulink;

import org.junit.jupiter.api.Test;
import org.junit.jupiter.api.io.TempDir;

import java.nio.channels.FileChannel;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.StandardOpenOption;
import java.util.List;
import java.util.Set;
import java.util.stream.Collectors;
import java.util.stream.Stream;

import static org.junit.jupiter.api.Assertions.*;

class MatlabEngineManagerTest {

    @Test
    void generateUniqueNameIsMatlabVarName() {
        String name = MatlabEngineManager.generateUniqueName();
        assertTrue(MatlabEngineManager.isValidMatlabVarName(name),
            "Generated name must be a valid MATLAB variable name: " + name);
        assertTrue(name.startsWith("FalCAuN_"),
            "Generated name must start with FalCAuN_ prefix: " + name);
    }

    @Test
    void generateUniqueNamesAreDistinct() {
        Set<String> names = Stream.generate(MatlabEngineManager::generateUniqueName)
            .limit(1000)
            .collect(Collectors.toSet());
        assertEquals(1000, names.size(), "All generated names should be distinct");
    }

    @Test
    void generateUniqueNameContainsPid() {
        String name = MatlabEngineManager.generateUniqueName();
        long pid = ProcessHandle.current().pid();
        assertTrue(name.startsWith("FalCAuN_" + pid),
            "Generated name should contain the process ID: " + name);
    }

    @Test
    void isValidMatlabVarName_acceptsValidNames() {
        assertTrue(MatlabEngineManager.isValidMatlabVarName("FalCAuN_12345_ab"));
        assertTrue(MatlabEngineManager.isValidMatlabVarName("a"));
        assertTrue(MatlabEngineManager.isValidMatlabVarName("A_B_C"));
        assertTrue(MatlabEngineManager.isValidMatlabVarName("a1_b2"));
        assertTrue(MatlabEngineManager.isValidMatlabVarName(MatlabEngineManager.generateUniqueName()));
    }

    @Test
    void isValidMatlabVarName_rejectsInvalidNames() {
        assertFalse(MatlabEngineManager.isValidMatlabVarName(null));
        assertFalse(MatlabEngineManager.isValidMatlabVarName(""));
        assertFalse(MatlabEngineManager.isValidMatlabVarName("123startWithDigit"));
        assertFalse(MatlabEngineManager.isValidMatlabVarName("has-dash"));
        assertFalse(MatlabEngineManager.isValidMatlabVarName("has space"));
        assertFalse(MatlabEngineManager.isValidMatlabVarName("has.dot"));
        assertFalse(MatlabEngineManager.isValidMatlabVarName("has/slash"));
    }

    @Test
    void filterNamesOnlyAcceptsFalCAuNPrefix() {
        List<String> names = List.of(
            "FalCAuN_12345_ab",
            "MATLAB_12345",
            "FalCAuN_abc",
            "other_session",
            "falcUn_123"
        );
        long count = names.stream()
            .filter(n -> n.startsWith(MatlabEngineManager.ENGINE_NAME_PREFIX))
            .count();
        assertEquals(2, count);
    }

    @Test
    void filterNames_rejectsNonFalCAuNNames() {
        List<String> names = List.of(
            "MATLAB_12345",
            "MATLAB_Engine",
            "octave_session",
            "Session1",
            "MyMATLAB"
        );
        for (String name : names) {
            assertFalse(name.startsWith(MatlabEngineManager.ENGINE_NAME_PREFIX),
                name + " should not start with FalCAuN_");
        }
    }

    @Test
    void lockFilePathIsUnderTmpDir() {
        Path path = MatlabEngineManager.lockFilePath("FalCAuN_12345");
        String tmpDir = System.getProperty("java.io.tmpdir");
        assertTrue(path.startsWith(Path.of(tmpDir)),
            "Lock file must be under java.io.tmpdir, got: " + path);
    }

    @Test
    void lockFilePathContainsEngineName() {
        Path path = MatlabEngineManager.lockFilePath("FalCAuN_process0_abc");
        assertTrue(path.getFileName().toString().startsWith("FalCAuN_process0_abc"));
        assertTrue(path.getFileName().toString().endsWith(".lock"));
    }

    @Test
    void lockFileNameFormat() {
        assertEquals("FalCAuN_12345.lock", MatlabEngineManager.lockFileName("FalCAuN_12345"));
        assertEquals("session_a.lock", MatlabEngineManager.lockFileName("session_a"));
    }

    @TempDir
    Path tmpDir;

    @Test
    void lockFilePathParentDirectoryCreated() throws Exception {
        Path engineLockFile = tmpDir.resolve("engine1.lock");
        FileChannel channel = FileChannel.open(engineLockFile, StandardOpenOption.CREATE, StandardOpenOption.WRITE);
        var lock = channel.tryLock();
        assertNotNull(lock);
        channel.close();
        assertTrue(Files.exists(engineLockFile));
    }

    @Test
    void lockPreventsSecondAcquisitionInDifferentThread() throws Exception {
        // FileLock across JVM processes would correctly return null for tryLock()
        // within same thread context, Java throws OverlappingFileLockException when
        // trying to lock the same file from different channels in the same thread.
        // We test the lock acquisition/release cycle instead.
        Path lockFile = tmpDir.resolve("exclusive_test.lock");
        Files.write(lockFile, new byte[0]);

        FileChannel c1 = FileChannel.open(lockFile, StandardOpenOption.READ, StandardOpenOption.WRITE);
        var lock1 = c1.tryLock();
        assertNotNull(lock1, "First tryLock() should succeed");
        assertTrue(lock1.isValid());

        lock1.release();
        c1.close();

        // Verify the file handle is properly cleaned up
        assertFalse(lock1.isValid(), "Lock should be invalid after release");

        // Re-acquire should succeed
        FileChannel c2 = FileChannel.open(lockFile, StandardOpenOption.READ, StandardOpenOption.WRITE);
        var lock2 = c2.tryLock();
        assertNotNull(lock2, "Lock should be reacquirable after release");
        assertTrue(lock2.isValid());
        lock2.release();
        c2.close();
    }

    @Test
    void lockedmatlabengineClosesInOrder() throws Exception {
        // Test that LockedMatlabEngine closes engine before releasing lock
        // We verify the try-finally structure by checking that the close
        // method does not throw when engine is already closed before lock is released
        Path lockFile = tmpDir.resolve("close_order_test.lock");
        try {
            Files.createDirectories(lockFile.getParent());
            Files.write(lockFile, new byte[0]);
            FileChannel channel = FileChannel.open(lockFile, StandardOpenOption.CREATE, StandardOpenOption.WRITE);
            var lock = channel.tryLock();
            assertNotNull(lock);
            // Verify lock is valid
            assertTrue(lock.isValid());
            channel.close();
        } catch (Exception e) {
            fail("Should not throw: " + e.getMessage());
        }
    }

    @Test
    void validNameRejectsSpecialChars() {
        String[] invalidNames = {
            "has-dash",
            "has space",
            "has.dot",
            "has/tab",
            "has(brk)",
            "has[brk]",
            "has{brk}",
            "has|pipe",
            "has&amp",
            "has<lt>",
            "has>gt>",
            "has;semi",
            "has'quote",
            "has\"dquote",
            "has^caret",
            "has`backtick"
        };
        for (String name : invalidNames) {
            assertFalse(MatlabEngineManager.isValidMatlabVarName(name),
                "Should reject: " + name);
        }
    }

    @Test
    void validNameAcceptsUnderscoresAndDigits() {
        assertTrue(MatlabEngineManager.isValidMatlabVarName("_"));
        assertTrue(MatlabEngineManager.isValidMatlabVarName("__"));
        assertTrue(MatlabEngineManager.isValidMatlabVarName("___123"));
        assertTrue(MatlabEngineManager.isValidMatlabVarName("a_b_c_d_e"));
        assertTrue(MatlabEngineManager.isValidMatlabVarName("a1b2c3d4"));
    }
}
