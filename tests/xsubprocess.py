"""
Enhanced subprocess.Popen subclass, supporting:
    * .communicate() with timeout

Sample usage:
    out, err = Popen(...).communicate(input, timeout=300)
"""

# --------------------------------------------------------------------
import os, subprocess

if subprocess.mswindows:
    import threading
else:
    import select, errno

# --------------------------------------------------------------------
__all__ = subprocess.__all__[:]

# --------------------------------------------------------------------
def __import():
    for i in subprocess.__all__:
        globals()[i] = getattr(subprocess, i)

__import()

# --------------------------------------------------------------------
class Popen(subprocess.Popen):
    def _fo_read_no_intr(self, obj):
        """Like obj.read(), but retries on EINTR"""
        while True:
            try:
                return obj.read()
            except IOError, e:
                if e.errno == errno.EINTR:
                    continue
                else:
                    raise

    def _fo_write_no_intr(self, obj, data):
        """Like obj.write(), but retries on EINTR"""
        while True:
            try:
                return obj.write(data)
            except IOError, e:
                if e.errno == errno.EINTR:
                    continue
                else:

                    raise
    def _fo_write_no_intr(self, obj, data):
        """Like obj.write(), but retries on EINTR"""
        while True:
            try:
                return obj.write(data)
            except IOError, e:
                if e.errno == errno.EINTR:
                    continue
                else:
                    raise

    def communicate(self, input=None, timeout=None):
        self.timeout = timeout

        # If we are only using one pipe, or no pipe at all, using
        # select() or threads is unnecessary.
        if [self.stdin, self.stdout, self.stderr].count(None) >= 2:
            stdout = None
            stderr = None
            if self.stdin:
                if input:
                    self._fo_write_no_intr(self.stdin, input)
                self.stdin.close()
            elif self.stdout:
                stdout = self._fo_read_no_intr(self.stdout)
                self.stdout.close()
            elif self.stderr:
                stderr = self._fo_read_no_intr(self.stderr)
                self.stderr.close()
            self.wait()
            return (stdout, stderr)

        return self._communicate(input)

    if subprocess.mswindows:
        def _communicate(self, input):
            stdout = None # Return
            stderr = None # Return

            if self.stdout:
                stdout = []
                stdout_thread = threading.Thread(target=self._readerthread,
                                                 args=(self.stdout, stdout))
                stdout_thread.setDaemon(True)
                stdout_thread.start()
            if self.stderr:
                stderr = []
                stderr_thread = threading.Thread(target=self._readerthread,
                                                 args=(self.stderr, stderr))
                stderr_thread.setDaemon(True)
                stderr_thread.start()

            if self.stdin:
                if input is not None:
                    self.stdin.write(input)
                self.stdin.close()

            if self.stdout:
                stdout_thread.join(self.timeout)
            if self.stderr:
                stderr_thread.join(self.timeout)

            # if the threads are still alive, that means the thread join timed out
            timed_out = (self.stdout and stdout_thread.isAlive() or
                         self.stderr and stderr_thread.isAlive())
            if timed_out:
                self.kill()
            else:
                self.wait()

            # All data exchanged.  Translate lists into strings.
            if stdout is not None:
                stdout = ''.join(stdout)
            if stderr is not None:
                stderr = ''.join(stderr)

            # Translate newlines, if requested.  We cannot let the file
            # object do the translation: It is based on stdio, which is
            # impossible to combine with select (unless forcing no
            # buffering).
            if self.universal_newlines and hasattr(file, 'newlines'):
                if stdout:
                    stdout = self._translate_newlines(stdout)
                if stderr:
                    stderr = self._translate_newlines(stderr)

            return (stdout, stderr)

    else: # POSIX
        def _communicate(self, input):
            timed_out = False
            read_set = []
            write_set = []
            stdout = None # Return
            stderr = None # Return

            if self.stdin:
                # Flush stdio buffer.  This might block, if the user has
                # been writing to .stdin in an uncontrolled fashion.
                self.stdin.flush()
                if input:
                    write_set.append(self.stdin)
                else:
                    self.stdin.close()
            if self.stdout:
                read_set.append(self.stdout)
                stdout = []
            if self.stderr:
                read_set.append(self.stderr)
                stderr = []

            input_offset = 0
            while read_set or write_set:
                try:
                    rlist, wlist, xlist = select.select(read_set, write_set, [], self.timeout)
                except select.error, e:
                    if e.args[0] == errno.EINTR:
                        continue
                    raise

                timed_out = not (rlist or wlist or xlist)
                if timed_out:
                    break

                if self.stdin in wlist:
                    # When select has indicated that the file is writable,
                    # we can write up to PIPE_BUF bytes without risk
                    # blocking.  POSIX defines PIPE_BUF >= 512
                    chunk = input[input_offset:input_offset + 512]
                    bytes_written = os.write(self.stdin.fileno(), chunk)
                    input_offset += bytes_written
                    if input_offset >= len(input):
                        self.stdin.close()
                        write_set.remove(self.stdin)

                if self.stdout in rlist:
                    data = os.read(self.stdout.fileno(), 1024)
                    if data == "":
                        self.stdout.close()
                        read_set.remove(self.stdout)
                    stdout.append(data)

                if self.stderr in rlist:
                    data = os.read(self.stderr.fileno(), 1024)
                    if data == "":
                        self.stderr.close()
                        read_set.remove(self.stderr)
                    stderr.append(data)

            # All data exchanged.  Translate lists into strings.
            if stdout is not None:
                stdout = ''.join(stdout)
            if stderr is not None:
                stderr = ''.join(stderr)

            # Translate newlines, if requested.  We cannot let the file
            # object do the translation: It is based on stdio, which is
            # impossible to combine with select (unless forcing no
            # buffering).
            if self.universal_newlines and hasattr(file, 'newlines'):
                if stdout:
                    stdout = self._translate_newlines(stdout)
                if stderr:
                    stderr = self._translate_newlines(stderr)

            if timed_out:
                self.kill()
            else:
                self.wait()
            return (stdout, stderr)
