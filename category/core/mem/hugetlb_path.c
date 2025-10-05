// Copyright (C) 2025 Category Labs, Inc.
//
// This program is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.
//
// This program is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU General Public License for more details.
//
// You should have received a copy of the GNU General Public License
// along with this program.  If not, see <http://www.gnu.org/licenses/>.

#include <category/core/cleanup.h> // NOLINT(misc-include-cleaner)
#include <category/core/format_err.h>
#include <category/core/mem/hugetlb_path.h>
#include <category/core/srcloc.h>

//#include <hugetlbfs.h>

#include <errno.h>
#include <fcntl.h>
#include <limits.h>
#include <linux/limits.h>
#include <stdlib.h>
#include <string.h>
#include <sys/stat.h>
#include <sys/types.h>
#include <unistd.h>

thread_local char g_error_buf[PATH_MAX];

#define FORMAT_ERRC(...)                                                       \
    monad_format_err(                                                          \
        g_error_buf,                                                           \
        sizeof g_error_buf,                                                    \
        &MONAD_SOURCE_LOCATION_CURRENT(),                                      \
        __VA_ARGS__)

int monad_hugetlbfs_open_dir_fd(
    struct monad_hugetlbfs_resolve_params const *, int *,
    char *, size_t )
{
    return 0;
}

char const *monad_hugetlbfs_get_last_error()
{
    return g_error_buf;
}
