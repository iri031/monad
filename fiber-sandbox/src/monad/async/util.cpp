#include "monad/async/util.h"

#include <cerrno>
#include <cstring>
#include <filesystem>

#include <fcntl.h> // for open
#include <unistd.h> // for unlink

static std::filesystem::path const &working_temporary_directory()
{
    static std::filesystem::path const v = [] {
        std::filesystem::path ret;
        auto test_path = [&](const std::filesystem::path path) -> bool {
            int fd = ::open(path.c_str(), O_RDWR | O_DIRECT | O_TMPFILE, 0600);
            if (-1 == fd && ENOTSUP == errno) {
                auto path2 = path / "monad_XXXXXX";
                fd = mkostemp(
                    const_cast<char *>(path2.native().c_str()), O_DIRECT);
                if (-1 != fd) {
                    unlink(path2.c_str());
                }
            }
            if (-1 != fd) {
                ret = path;
                ::close(fd);
                return true;
            }
            return false;
        };
        // Only observe environment variables if not a SUID or SGID situation
        // FIXME? Is this actually enough? What about the non-standard saved
        // uid/gid? Should I be checking if my executable is SUGID and its
        // owning user is not mine?
        if (getuid() == geteuid() && getgid() == getegid()) {
            // Note that XDG_RUNTIME_DIR is the systemd runtime directory for
            // the current user, usually mounted with tmpfs XDG_CACHE_HOME  is
            // the systemd cache directory for the current user, usually at
            // $HOME/.cache
            static const char *variables[] = {
                "TMPDIR",
                "TMP",
                "TEMP",
                "TEMPDIR",
                "XDG_RUNTIME_DIR",
                "XDG_CACHE_HOME"};
            for (const auto *variable : variables) {
                const char *env = getenv(variable);
                if (env != nullptr) {
                    if (test_path(env)) {
                        return ret;
                    }
                }
            }
            // Also try $HOME/.cache
            const char *env = getenv("HOME");
            if (env != nullptr) {
                std::filesystem::path buffer(env);
                buffer /= ".cache";
                if (test_path(buffer)) {
                    return ret;
                }
            }
        }
        // TODO: Use getpwent_r() to extract current effective user home
        // directory Hardcoded fallbacks in case environment is not available to
        // us
        if (test_path("/tmp")) {
            return ret;
        }
        if (test_path("/var/tmp")) {
            return ret;
        }
        if (test_path("/run/user/" + std::to_string(geteuid()))) {
            return ret;
        }
        // Some systems with no writable hardcode fallbacks may have shared
        // memory configured
        if (test_path("/run/shm")) {
            return ret;
        }
        // On some Docker images this is the only writable path anywhere
        if (test_path("/")) {
            return ret;
        }
        throw std::runtime_error(
            "This system appears to have no writable temporary files location, "
            "please set one using any of the usual environment variables e.g. "
            "TMPDIR");
    }();
    return v;
}

extern "C" char const *monad_async_working_temporary_directory()
{
    return working_temporary_directory().c_str();
}

extern "C" int monad_async_make_temporary_file(char *buffer, size_t buffer_len)
{
    auto scratch = working_temporary_directory() / "monad_XXXXXX";
    if (scratch.native().size() > buffer_len - 1) {
        errno = ENOSPC;
        return -1;
    }
    memcpy(buffer, scratch.c_str(), scratch.native().size() + 1);
    return mkstemp(buffer);
}

extern "C" int monad_async_make_temporary_inode()
{
    int fd =
        ::open(working_temporary_directory().c_str(), O_RDWR | O_TMPFILE, 0600);
    if (-1 == fd && ENOTSUP == errno) {
        // O_TMPFILE is not supported on ancient Linux kernels
        // of the kind apparently Github like to run :(
        auto buffer = working_temporary_directory() / "monad_XXXXXX";
        fd = mkstemp(const_cast<char *>(buffer.native().c_str()));
        if (-1 != fd) {
            unlink(buffer.c_str());
        }
    }
    if (fd == -1) {
        fprintf(
            stderr,
            "FATAL: Failed to make temporary inode due to '%s'\n",
            strerror(errno));
        abort();
    }
    return fd;
}
