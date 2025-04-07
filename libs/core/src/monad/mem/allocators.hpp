#pragma once

#include <monad/core/assert.h>
#include <monad/core/cmemory.hpp>

#include <concepts>
#include <memory>
#include <span>
#include <stdexcept>
#include <vector>

MONAD_NAMESPACE_BEGIN

namespace allocators
{
    namespace detail
    {
        template <class T>
        struct is_unique_ptr : public std::false_type
        {
        };

        template <class T, class Deleter>
        struct is_unique_ptr<std::unique_ptr<T, Deleter>>
            : public std::true_type
        {
        };
    }

    //! \brief Concept matching a STL allocator.
    template <class T>
    concept allocator =
        requires(T a, size_t n) { a.deallocate(a.allocate(n), n); };

    //! \brief Concept matching a Deleter template parameter for a `unique_ptr`.
    template <class T, class U>
    concept unique_ptr_deleter = requires(T x, U *p) { x(p); };

    //! \brief Concept matching a `unique_ptr`.
    template <class T>
    concept unique_ptr = detail::is_unique_ptr<std::decay_t<T>>::value;

    //! \brief If a type opts into this, `calloc_free_allocator` and `calloc` is
    //! used and constructors are NOT called. Only opt into this if your type is
    //! happy seeing all bytes zero as if it had been constructed, this can be a
    //! win for same use cases (`calloc` may be able to avoid zeroing memory if
    //! it knows its source is already zeroed) but can also be a loss if zeroing
    //! bytes is more expensive than calling the constructor.
    //!
    //! \warning Be SURE to specialise this before instantiating any code which
    //! instantiates allocator code! Otherwise it will have no effect.
    template <class T>
    struct construction_equals_all_bits_zero : std::false_type
    {
    };

    //! \brief Injects a noop `construct()` into a STL allocator.
    template <allocator Base>
    struct disable_construct_in_allocator : public Base
    {
        template <class U, class... Args>
        void construct(U *, Args &&...)
        {
        }
    };

    /**************************************************************************/
    //! \brief A STL allocator which uses `malloc`-`free`.
    template <class T>
    struct malloc_free_allocator
    {
        using value_type = T;

        [[nodiscard]] constexpr T *allocate(size_t const no)
        {
            MONAD_ASSERT(no < size_t(-1) / sizeof(T));
            if constexpr (alignof(T) > alignof(max_align_t)) {
                return reinterpret_cast<T *>(
                    std::aligned_alloc(alignof(T), no * sizeof(T)));
            }
            return reinterpret_cast<T *>(std::malloc(no * sizeof(T)));
        }

        template <class U>
        [[nodiscard]] constexpr T *allocate_overaligned(size_t const no)
        {
            MONAD_ASSERT(no < size_t(-1) / sizeof(T));
            if constexpr (alignof(U) > alignof(max_align_t)) {
                return reinterpret_cast<T *>(
                    std::aligned_alloc(alignof(U), no * sizeof(T)));
            }
            return reinterpret_cast<T *>(std::malloc(no * sizeof(T)));
        }

        constexpr void deallocate(T *const p, size_t const)
        {
            std::free(p);
        }
    };

    //! \brief A STL allocator which uses `calloc`-`free` (i.e. allocated bytes
    //! are returned zeroed)
    template <class T>
    struct calloc_free_allocator
    {
        using value_type = T;

        [[nodiscard]] constexpr T *allocate(size_t const no)
        {
            MONAD_ASSERT(no < size_t(-1) / sizeof(T));
            if constexpr (alignof(T) > alignof(max_align_t)) {
                char *ret = reinterpret_cast<char *>(
                    std::aligned_alloc(alignof(T), no * sizeof(T)));
                cmemset(ret, char(0), no * sizeof(T));
                return reinterpret_cast<T *>(ret);
            }
            return reinterpret_cast<T *>(std::calloc(no, sizeof(T)));
        }

        template <class U>
        [[nodiscard]] constexpr T *allocate_overaligned(size_t const no)
        {
            MONAD_ASSERT(no < size_t(-1) / sizeof(T));
            if constexpr (alignof(U) > alignof(max_align_t)) {
                char *ret = reinterpret_cast<char *>(
                    std::aligned_alloc(alignof(U), no * sizeof(T)));
                cmemset(ret, char(0), no * sizeof(T));
                return reinterpret_cast<T *>(ret);
            }
            return reinterpret_cast<T *>(std::calloc(no, sizeof(T)));
        }

        constexpr void deallocate(T *const p, size_t const)
        {
            std::free(p);
        }
    };

    //! \brief Chooses `calloc_free_allocator` if
    //! `construction_equals_all_bits_zero<T>` is true, else
    //! `malloc_free_allocator`
    template <class T, class U = T>
    using calloc_free_allocator_if_opted_in = std::conditional_t<
        construction_equals_all_bits_zero<T>::value, calloc_free_allocator<U>,
        malloc_free_allocator<U>>;

    /**************************************************************************/
    //! \brief A unique ptr deleter for a STL allocator
    template <allocator Alloc, Alloc &(*GetAllocator)()>
    struct unique_ptr_allocator_deleter
    {
        using allocator_type = Alloc;
        using value_type = typename Alloc::value_type;

        constexpr unique_ptr_allocator_deleter() = default;

        constexpr void operator()(value_type *const p) const
        {
            using allocator_traits = std::allocator_traits<allocator_type>;
            Alloc &alloc = GetAllocator();
            allocator_traits::destroy(alloc, p);
            allocator_traits::deallocate(alloc, p, 1);
        }
    };

    namespace detail
    {
        template <allocator TypeAlloc, allocator RawAlloc>
        struct type_raw_alloc_pair
        {
            using type_allocator = TypeAlloc;
            using raw_bytes_allocator = RawAlloc;

            TypeAlloc &type_alloc;
            RawAlloc &raw_alloc;
        };

        template <class T>
        inline type_raw_alloc_pair<
            std::allocator<T>, calloc_free_allocator_if_opted_in<T, std::byte>>
        GetStdAllocatorPair()
        {
            static std::allocator<T> a;
            static calloc_free_allocator_if_opted_in<T, std::byte> b;
            return {a, b};
        }
    }

    //! \brief A unique ptr deleter for a STL allocator where underlying storage
    //! exceeds type
    template <
        allocator TypeAlloc, allocator RawAlloc,
        detail::type_raw_alloc_pair<TypeAlloc, RawAlloc> (*GetAllocator)(),
        size_t (*GetSize)(typename TypeAlloc::value_type *)>
    struct unique_ptr_aliasing_allocator_deleter
    {
        using allocator_type = TypeAlloc;
        using value_type = typename TypeAlloc::value_type;

        constexpr unique_ptr_aliasing_allocator_deleter() {}

        constexpr void operator()(value_type *const p1) const
        {
            using allocator1_traits = std::allocator_traits<allocator_type>;
            using allocator2_traits = std::allocator_traits<RawAlloc>;
            // Use all bits one for the number of items to deallocate in
            // order to trap use of unsuitable user supplied allocators
            using size_type2 = allocator2_traits::size_type;
            auto no = static_cast<size_type2>(-1);
#pragma GCC diagnostic push
#pragma GCC diagnostic ignored                                                 \
    "-Waddress" // warns about GetSize never being null
            if (GetSize != nullptr) {
                no = GetSize(p1);
            }
#pragma GCC diagnostic pop
            auto [alloc1, alloc2] = GetAllocator();
            allocator1_traits::destroy(alloc1, p1);
            auto *p2 = reinterpret_cast<std::byte *>(p1);
            allocator2_traits::deallocate(alloc2, p2, no);
        }
    };

    //! \brief An implementation of proposed `allocate_unique`, a STL allocator
    //! aware `unique_ptr`.
    template <allocator Alloc, Alloc &(*GetAllocator)(), class... Args>
        requires(std::is_constructible_v<typename Alloc::value_type, Args...>)
    inline constexpr std::unique_ptr<
        typename Alloc::value_type,
        unique_ptr_allocator_deleter<Alloc, GetAllocator>>
    allocate_unique(Args &&...args)
    {
        using allocator_traits = std::allocator_traits<Alloc>;
        Alloc &alloc = GetAllocator();
        auto *p = allocator_traits::allocate(alloc, 1);
        try {
            if constexpr (
                sizeof...(args) > 0 || !construction_equals_all_bits_zero<
                                           typename Alloc::value_type>::value) {
                allocator_traits::construct(
                    alloc, p, static_cast<Args &&>(args)...);
            }
            return std::unique_ptr<
                typename Alloc::value_type,
                unique_ptr_allocator_deleter<Alloc, GetAllocator>>(p);
        }
        catch (...) {
            allocator_traits::deallocate(alloc, p, 1);
            throw;
        }
    }

    //! \brief A STL allocator aware unique ptr whose storage is larger than its
    //! type. Useful for variably lengthed types. Needs a raw storage allocator
    //! capable of deallocating without being told how many bytes to deallocate.
    template <
        allocator TypeAlloc, allocator RawAlloc,
        detail::type_raw_alloc_pair<TypeAlloc, RawAlloc> (*GetAllocator)(),
        size_t (*GetSize)(typename TypeAlloc::value_type *) = nullptr,
        class... Args>
        requires(
            std::is_same_v<typename RawAlloc::value_type, std::byte> &&
            std::is_constructible_v<typename TypeAlloc::value_type, Args...>)
    inline constexpr std::unique_ptr<
        typename TypeAlloc::value_type,
        unique_ptr_aliasing_allocator_deleter<
            TypeAlloc, RawAlloc, GetAllocator, GetSize>>
    allocate_aliasing_unique(size_t const storagebytes, Args &&...args)
    {
        MONAD_ASSERT(storagebytes >= sizeof(typename TypeAlloc::value_type));
        using allocator1_traits = std::allocator_traits<TypeAlloc>;
        using allocator2_traits = std::allocator_traits<RawAlloc>;
        auto [alloc1, alloc2] = GetAllocator();
        std::byte *p2;
        if constexpr (
            alignof(typename TypeAlloc::value_type) > alignof(max_align_t)) {
            p2 = alloc2.template allocate_overaligned<
                typename TypeAlloc::value_type>(storagebytes);
        }
        else {
            p2 = allocator2_traits::allocate(alloc2, storagebytes);
        }
#ifndef NDEBUG
        if constexpr (!construction_equals_all_bits_zero<
                          typename TypeAlloc::value_type>::value) {
            // Trap use of region after end of type
            cmemset(p2, std::byte{0xff}, storagebytes);
        }
#endif
        try {
            auto *p1 = reinterpret_cast<typename TypeAlloc::value_type *>(p2);
            if constexpr (
                sizeof...(args) > 0 ||
                !construction_equals_all_bits_zero<
                    typename TypeAlloc::value_type>::value) {
                allocator1_traits::construct(
                    alloc1, p1, static_cast<Args &&>(args)...);
            }
            using deleter_type = unique_ptr_aliasing_allocator_deleter<
                TypeAlloc,
                RawAlloc,
                GetAllocator,
                GetSize>;
            return std::
                unique_ptr<typename TypeAlloc::value_type, deleter_type>(p1);
        }
        catch (...) {
            allocator2_traits::deallocate(alloc2, p2, storagebytes);
            throw;
        }
    }

    // todo: verify this actually allocates correctly
    //! naive shared ptr alloc aware of storage pool
    template <
        allocator TypeAlloc, allocator RawAlloc,
        detail::type_raw_alloc_pair<TypeAlloc, RawAlloc> (*GetAllocator)(),
        size_t (*GetSize)(typename TypeAlloc::value_type *) = nullptr,
        class... Args>
        requires(
            std::is_same_v<typename RawAlloc::value_type, std::byte> &&
            std::is_constructible_v<typename TypeAlloc::value_type, Args...>)
    inline constexpr std::shared_ptr<typename TypeAlloc::value_type>
    allocate_aliasing_shared(size_t const storagebytes, Args &&...args)
    {
        MONAD_ASSERT(storagebytes >= sizeof(typename TypeAlloc::value_type));
        using allocator1_traits = std::allocator_traits<TypeAlloc>;
        using allocator2_traits = std::allocator_traits<RawAlloc>;
        auto [alloc1, alloc2] = GetAllocator();
        std::byte *p2;
        if constexpr (
            alignof(typename TypeAlloc::value_type) > alignof(max_align_t)) {
            p2 = alloc2.template allocate_overaligned<
                typename TypeAlloc::value_type>(storagebytes);
        }
        else {
            p2 = allocator2_traits::allocate(alloc2, storagebytes);
        }
#ifndef NDEBUG
        if constexpr (!construction_equals_all_bits_zero<
                          typename TypeAlloc::value_type>::value) {
            // Trap use of region after end of type
            cmemset(p2, std::byte{0xff}, storagebytes);
        }
#endif
        try {
            auto *p1 = reinterpret_cast<typename TypeAlloc::value_type *>(p2);
            if constexpr (
                sizeof...(args) > 0 ||
                !construction_equals_all_bits_zero<
                    typename TypeAlloc::value_type>::value) {
                allocator1_traits::construct(
                    alloc1, p1, static_cast<Args &&>(args)...);
            }

            return std::shared_ptr<typename TypeAlloc::value_type>(p1);
        }
        catch (...) {
            allocator2_traits::deallocate(alloc2, p2, storagebytes);
            throw;
        }
    }

    //! \brief A unique ptr whose storage is larger than its type, using
    //! `std::allocator`.
    template <class T, class... Args>
    inline constexpr std::unique_ptr<
        T, unique_ptr_aliasing_allocator_deleter<
               std::allocator<T>, malloc_free_allocator<std::byte>,
               detail::GetStdAllocatorPair<T>, nullptr>>
    make_aliasing_unique(size_t const storagebytes, Args &&...args)
    {
        return allocate_aliasing_unique<
            std::allocator<T>,
            malloc_free_allocator<std::byte>,
            detail::GetStdAllocatorPair<T>>(
            storagebytes, static_cast<Args &&>(args)...);
    }

    /**************************************************************************/

    namespace detail
    {
        // The clang 16 on CI is just plain broken here. clang 14 on my machine
        // is not broken.
#if defined(__clang__) && (__clang_major__ >= 16 && __clang_major__ <= 18)
        template <class T>
        constexpr bool is_array_v = true;
#else
        template <class T>
        constexpr bool is_array_v = std::is_array_v<T>;
#endif
    }

    struct unique_ptr_free_deleter
    {
        template <class T>
        constexpr void operator()(T *const p) const
        {
            MONAD_ASSERT(p == nullptr);
        }
    };

    //! \brief A unique ptr whose pointee can be resized. Requires `T[0]` to be
    //! trivially copyable so storage overhead can be avoided. `owning_span` is
    //! suitable for more complex types.
    //!
    //! \note Any custom constructor you might have gets ignored!
    //! `construction_equals_all_bits_zero<T>` is respected however.
    template <class T>
    class resizeable_unique_ptr;
    template <class T>
        requires(detail::is_array_v<T> && std::is_trivially_copyable_v<T>)
    inline constexpr resizeable_unique_ptr<T>
    make_resizeable_unique_for_overwrite(size_t no);

    template <class T>
    class resizeable_unique_ptr<T[]>
        : protected std::unique_ptr<T[], unique_ptr_free_deleter>
    {
        friend constexpr resizeable_unique_ptr<T[]>
        make_resizeable_unique_for_overwrite<T[]>(size_t const no);

        using _base = std::unique_ptr<T[], unique_ptr_free_deleter>;

        explicit constexpr resizeable_unique_ptr(size_t const no)
            : _base([no] {
                MONAD_ASSERT(no < size_t(-1) / sizeof(T));
                calloc_free_allocator_if_opted_in<T> alloc;
                T *ret = alloc.allocate(no);
                if (ret == nullptr) {
                    throw std::bad_alloc();
                }
                return ret;
            }())
        {
        }

    public:
        resizeable_unique_ptr() = default;
        resizeable_unique_ptr(resizeable_unique_ptr const &) = delete;
        resizeable_unique_ptr(resizeable_unique_ptr &&) = default;
        resizeable_unique_ptr &
        operator=(resizeable_unique_ptr const &) = delete;

        resizeable_unique_ptr &operator=(resizeable_unique_ptr &&o) noexcept
        {
            if (this != &o) {
                this->~resizeable_unique_ptr();
                new (this) resizeable_unique_ptr(
                    static_cast<resizeable_unique_ptr &&>(o));
            }
            return *this;
        }

        ~resizeable_unique_ptr()
        {
            reset();
        }

        using _base::get;
        using _base::release;
        using _base::operator bool;
        using _base::operator[];

        template <class U>
            requires(
                !std::is_same_v<U, std::nullptr_t> &&
                requires(_base x, U y) { x.reset(y); })
        void reset(U ptr) noexcept
        {
            if (_base::get() != nullptr) {
                std::free(_base::get());
                _base::release();
            }
            _base::reset(ptr);
        }

        void reset(std::nullptr_t const = nullptr) noexcept
        {
            if (_base::get() != nullptr) {
                std::free(_base::get());
                _base::release();
            }
        }

        void swap(resizeable_unique_ptr &o) noexcept
        {
            _base::swap(o);
        }

        //! Try to resize the pointee, returning false if was unable
        bool try_resize(size_t const no) noexcept
        {
            MONAD_ASSERT(no < size_t(-1) / sizeof(T));
            auto *ret = (T *)std::realloc(_base::get(), no * sizeof(T));
            if (ret == nullptr) {
                return false;
            }
            _base::release();
            _base::reset(ret);
            return true;
        }

        //! Resize the pointer, throwing `bad_alloc` if failed. Returns true if
        //! pointee moved in memory.
        bool resize(size_t const no)
        {
            MONAD_ASSERT(no < size_t(-1) / sizeof(T));
            auto *ret = (T *)std::realloc(_base::get(), no * sizeof(T));
            if (ret == nullptr) {
                throw std::bad_alloc();
            }
            auto *old = _base::release();
            _base::reset(ret);
            return old != ret;
        }
    };

    template <class T>
    struct detail::is_unique_ptr<resizeable_unique_ptr<T[]>>
        : public std::true_type
    {
    };

    //! \brief Use this function to create a `resizeable_unique_ptr<T>`.
    template <class T>
        requires(detail::is_array_v<T> && std::is_trivially_copyable_v<T>)
    inline constexpr resizeable_unique_ptr<T>
    make_resizeable_unique_for_overwrite(size_t const no)
    {
        return resizeable_unique_ptr<T>(no);
    }

    /**************************************************************************/

    //! \brief An owning span, as we don't have `static_vector` yet.
    template <class T, allocator Alloc = std::allocator<T>>
    class owning_span : public std::span<T>
    {
        using _base = std::span<T>;
        using _size_type = typename _base::size_type;
        [[no_unique_address]] Alloc _alloc;

        template <class... Args>
        static _base _allocate(Alloc alloc, _size_type const no, Args &&...args)
        {
            using allocator_traits = std::allocator_traits<Alloc>;
            auto *p = allocator_traits::allocate(alloc, no);
            for (_size_type n = 0; n < no; n++) {
                try {
                    if constexpr (
                        sizeof...(args) > 0 ||
                        !construction_equals_all_bits_zero<T>::value) {
                        allocator_traits::construct(
                            alloc, &p[n], static_cast<Args &&>(args)...);
                    }
                }
                catch (...) {
                    while (n > 0) {
                        allocator_traits::destroy(alloc, &p[--n]);
                    }
                    allocator_traits::deallocate(alloc, p, no);
                    throw;
                }
            }
            return _base(p, no);
        }

    public:
        using size_type = _size_type;
        owning_span() = default;

        constexpr explicit owning_span(Alloc const &alloc)
            : _alloc(alloc)
        {
        }

        constexpr explicit owning_span(
            size_type no, T const &v, Alloc const &alloc = Alloc())
            : _base(_allocate(alloc, no, v))
            , _alloc(alloc)
        {
        }

        constexpr owning_span(size_type const no, Alloc const &alloc = Alloc())
            : _base(_allocate(alloc, no))
            , _alloc(alloc)
        {
        }

        owning_span(owning_span const &) = delete;
        owning_span &operator=(owning_span const &) = delete;

        owning_span(owning_span &&o) noexcept
            : _base(static_cast<_base &&>(o))
            , _alloc(static_cast<Alloc &&>(o._alloc))
        {
            auto &&other = static_cast<_base &&>(o);
            other = {};
        }

        owning_span &operator=(owning_span &&o) noexcept
        {
            if (this != &o) {
                this->~owning_span();
                new (this) owning_span(static_cast<owning_span &&>(o));
            }
            return *this;
        }

        ~owning_span()
        {
            using allocator_traits = std::allocator_traits<Alloc>;
            for (auto &i : *this) {
                allocator_traits::destroy(_alloc, &i);
            }
            if (_base::data() != nullptr) {
                allocator_traits::deallocate(
                    _alloc, _base::data(), _base::size());
            }
        }
    };

    /**************************************************************************/

    //! \brief A span referring to either in-object storage, or dynamically
    //! allocated storage
    template <
        class T, size_t inline_buffer_bytes = 1024,
        allocator Alloc = std::allocator<T>>
    class inline_owning_span final : protected std::span<T>
    {
        using _base = std::span<T>;
        static constexpr size_t _max_inline_items =
            (inline_buffer_bytes >= sizeof(T)) ? inline_buffer_bytes / sizeof(T)
                                               : 1;

    public:
        using element_type = typename _base::element_type;
        using value_type = typename _base::value_type;
        using size_type = typename _base::size_type;
        using difference_type = typename _base::difference_type;
        using pointer = typename _base::pointer;
        using const_pointer = typename _base::const_pointer;
        using reference = typename _base::reference;
        using const_reference = typename _base::const_reference;
        using iterator = typename _base::iterator;
        using reverse_iterator = typename _base::reverse_iterator;

        using _base::begin;
        using _base::end;
        using _base::rbegin;
        using _base::rend;

        using _base::back;
        using _base::front;
        using _base::operator[];
        using _base::data;

        using _base::empty;
        using _base::size;
        using _base::size_bytes;

    protected:
        [[no_unique_address]] Alloc _alloc;

        union _inline_buffer_t
        {
            std::byte _rawbytes[inline_buffer_bytes];
            value_type p[_max_inline_items];

            _inline_buffer_t()
            {
                /* do not initialise anything */
            }

            _inline_buffer_t(_inline_buffer_t const &) = delete;
            _inline_buffer_t(_inline_buffer_t &&) = delete;

            ~_inline_buffer_t() {}
        } _inline_buffer;

        // The above MUST be the last member in the object if the compiler is to
        // have the power to optimise it away if it can statically prove it will
        // never be used.

        template <class... Args>
        _base _allocate(Alloc alloc, size_type const no, Args &&...args)
        {
            using allocator_traits = std::allocator_traits<Alloc>;
            auto *p = (no <= _max_inline_items)
                          ? _inline_buffer.p
                          : allocator_traits::allocate(alloc, no);
            for (size_type n = 0; n < no; n++) {
                try {
                    if constexpr (
                        sizeof...(args) > 0 ||
                        !construction_equals_all_bits_zero<T>::value) {
                        allocator_traits::construct(
                            alloc, &p[n], static_cast<Args &&>(args)...);
                    }
                    else if (no <= _max_inline_items) {
                        cmemset(
                            _inline_buffer._rawbytes,
                            std::byte{0},
                            no * sizeof(value_type));
                    }
                }
                catch (...) {
                    while (n > 0) {
                        allocator_traits::destroy(alloc, &p[--n]);
                    }
                    if (no > _max_inline_items) {
                        allocator_traits::deallocate(alloc, p, no);
                    }
                    throw;
                }
            }
            return _base(p, no);
        }

    public:
        inline_owning_span() = default;

        constexpr explicit inline_owning_span(Alloc const &alloc)
            : _alloc(alloc)
        {
        }

        constexpr explicit inline_owning_span(
            size_type no, T const &v, Alloc const &alloc = Alloc())
            : _alloc(alloc)
        {
            _base::operator=(_allocate(_alloc, no, v));
        }

        constexpr inline_owning_span(
            size_type const no, Alloc const &alloc = Alloc())
            : _alloc(alloc)
        {
            _base::operator=(_allocate(_alloc, no));
        }

        inline_owning_span(inline_owning_span const &) = delete;
        inline_owning_span &operator=(inline_owning_span const &) = delete;

        inline_owning_span(inline_owning_span &&o) noexcept(
            std::is_nothrow_move_constructible_v<value_type>)
            : _base(static_cast<_base &&>(o))
            , _alloc(static_cast<Alloc &&>(o._alloc))
        {
            auto &&other = static_cast<_base &&>(o);
            if (other.size() <= _max_inline_items) {
                using allocator_traits = std::allocator_traits<Alloc>;
                auto *p = _inline_buffer.p;
                for (size_type n = 0; n < other.size(); n++) {
                    try {
                        allocator_traits::construct(
                            _alloc, &p[n], std::move(o._inline_buffer.p[n]));
                    }
                    catch (...) {
                        while (n > 0) {
                            allocator_traits::destroy(_alloc, &p[--n]);
                        }
                        throw;
                    }
                }
                static_cast<_base *>(this)->operator=(_base(p, other.size()));
                for (size_type n = 0; n < other.size(); n++) {
                    allocator_traits::destroy(_alloc, &o._inline_buffer.p[n]);
                }
            }
            other = {};
        }

        inline_owning_span &operator=(inline_owning_span &&o) noexcept(
            std::is_nothrow_move_constructible_v<value_type>)
        {
            if (this != &o) {
                this->~inline_owning_span();
                new (this)
                    inline_owning_span(static_cast<inline_owning_span &&>(o));
            }
            return *this;
        }

        ~inline_owning_span()
        {
            using allocator_traits = std::allocator_traits<Alloc>;
            for (auto &i : *this) {
                allocator_traits::destroy(_alloc, &i);
            }
            if (_base::data() != nullptr) {
                if (_base::size() > _max_inline_items) {
                    allocator_traits::deallocate(
                        _alloc, _base::data(), _base::size());
                }
            }
        }
    };

    /**************************************************************************/

    template <unique_ptr T>
    void delayed_reset(T &&ptr);

    /*! \class thread_local_delayed_unique_ptr_resetter
    \brief Collects unique ptrs upon whom `delayed_reset()` is called into
    a thread local list. When the resetter is reset, destroys those unique ptrs.
    */
    template <unique_ptr T>
    class thread_local_delayed_unique_ptr_resetter
    {
        friend void delayed_reset<T>(T &&ptr);
        thread_local_delayed_unique_ptr_resetter *_prev{nullptr};
        std::vector<T> _ptrs;

        static thread_local_delayed_unique_ptr_resetter *&_inst()
        {
            static thread_local thread_local_delayed_unique_ptr_resetter *v;
            return v;
        }

        void _add(T &&v)
        {
            _ptrs.push_back(std::move(v));
        }

    public:
        using unique_ptr_type = T;

        thread_local_delayed_unique_ptr_resetter()
            : _prev(_inst())
        {
            _inst() = this;
            _ptrs.reserve(256);
        }

        thread_local_delayed_unique_ptr_resetter(
            thread_local_delayed_unique_ptr_resetter const &) = delete;
        thread_local_delayed_unique_ptr_resetter(
            thread_local_delayed_unique_ptr_resetter &&) = delete;
        thread_local_delayed_unique_ptr_resetter &
        operator=(thread_local_delayed_unique_ptr_resetter const &) = delete;
        thread_local_delayed_unique_ptr_resetter &
        operator=(thread_local_delayed_unique_ptr_resetter &&) = delete;

        ~thread_local_delayed_unique_ptr_resetter()
        {
            reset();
            _inst() = _prev;
        }

        //! Returns a pointer to the instance for the calling thread, if any
        static thread_local_delayed_unique_ptr_resetter *thread_instance()
        {
            return _inst();
        }

        //! Executes destructing all the enqueued unique ptrs.
        void reset()
        {
            _ptrs.clear();
        }
    };

    //! \brief Delay the reset of the specified unique ptr. If there is not a
    //! `thread_local_delayed_unique_ptr_resetter` instance earlier in the
    //! calling thread's stack, terminates the process.
    template <unique_ptr T>
    void delayed_reset(T &&ptr)
    {
        using resetter_type = thread_local_delayed_unique_ptr_resetter<T>;
        MONAD_ASSERT(resetter_type::thread_instance() != nullptr);
        resetter_type::thread_instance()->_add(std::move(ptr));
    }
}

MONAD_NAMESPACE_END
