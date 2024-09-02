#include <errno.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>

#include <dlfcn.h>
#include <pthread.h>
#include <sys/signal.h>

/* /usr/lib/x86_64-linux-gnu/libthread_db.so exports the following symbols:

td_init
td_log
td_symbol_list
td_ta_clear_event
td_ta_delete
td_ta_enable_stats
td_ta_event_addr
td_ta_event_getmsg
td_ta_get_nthreads
td_ta_get_ph
td_ta_get_stats
td_ta_map_id2thr
td_ta_map_lwp2thr
td_ta_new
td_ta_reset_stats
td_ta_set_event
td_ta_setconcurrency
td_ta_thr_iter
td_ta_tsd_iter
td_thr_clear_event
td_thr_dbresume
td_thr_dbsuspend
td_thr_event_enable
td_thr_event_getmsg
td_thr_get_info
td_thr_getfpregs
td_thr_getgregs
td_thr_getxregs
td_thr_getxregsize
td_thr_set_event
td_thr_setfpregs
td_thr_setgregs
td_thr_setprio
td_thr_setsigpending
td_thr_setxregs
td_thr_sigsetmask
td_thr_tls_get_addr
td_thr_tlsbase
td_thr_tsd
td_thr_validate

GLIBC_2.2.5
GLIBC_2.3
GLIBC_2.3.3
*/

/* gdb/linux-thread-db.cc appears to only require this of libthread_db.so:

Essential:

td_init
td_ta_map_lwp2thr
td_ta_new
td_ta_thr_iter (but not used if /proc/pid/task exists!)
td_thr_get_info

Non-essential:

td_ta_delete
td_thr_tlsbase
td_thr_tls_get_addr
*/

/* gdbserver/thread-db.cc appears to only require this of libthread_db.so:

Essential:

td_ta_map_lwp2thr
td_ta_new
td_ta_thr_iter
td_thr_get_info
td_symbol_list

Non-essential:

td_thr_tlsbase
td_thr_tls_get_addr
*/

typedef pthread_t thread_t;

typedef struct td_thragent td_thragent_t;

typedef void *psaddr_t;

typedef unsigned lwpid_t;

typedef struct td_thrhandle
{
    td_thragent_t *th_ta_p;
    psaddr_t th_unique;
} td_thrhandle_t;

typedef struct td_thr_events
{
    uint32_t event_bits[2];
} td_thr_events_t;

typedef int td_thr_iter_f(td_thrhandle_t const *, void *);

struct ps_prochandle;

// clang-format off

/* Error codes of the library.  */
typedef enum
{
  TD_OK,	  /* No error.  */
  TD_ERR,	  /* No further specified error.  */
  TD_NOTHR,	  /* No matching thread found.  */
  TD_NOSV,	  /* No matching synchronization handle found.  */
  TD_NOLWP,	  /* No matching light-weighted process found.  */
  TD_BADPH,	  /* Invalid process handle.  */
  TD_BADTH,	  /* Invalid thread handle.  */
  TD_BADSH,	  /* Invalid synchronization handle.  */
  TD_BADTA,	  /* Invalid thread agent.  */
  TD_BADKEY,	  /* Invalid key.  */
  TD_NOMSG,	  /* No event available.  */
  TD_NOFPREGS,	  /* No floating-point register content available.  */
  TD_NOLIBTHREAD, /* Application not linked with thread library.  */
  TD_NOEVENT,	  /* Requested event is not supported.  */
  TD_NOCAPAB,	  /* Capability not available.  */
  TD_DBERR,	  /* Internal debug library error.  */
  TD_NOAPLIC,	  /* Operation is not applicable.  */
  TD_NOTSD,	  /* No thread-specific data available.  */
  TD_MALLOC,	  /* Out of memory.  */
  TD_PARTIALREG,  /* Not entire register set was read or written.  */
  TD_NOXREGS,	  /* X register set not available for given thread.  */
  TD_TLSDEFER,	  /* Thread has not yet allocated TLS for given module.  */
  TD_NOTALLOC = TD_TLSDEFER,
  TD_VERSION,	  /* Version if libpthread and libthread_db do not match.  */
  TD_NOTLS	  /* There is no TLS segment in the given module.  */
} td_err_e;

/* Possible thread states.  TD_THR_ANY_STATE is a pseudo-state used to
   select threads regardless of state in td_ta_thr_iter().  */
typedef enum
{
  TD_THR_ANY_STATE,
  TD_THR_UNKNOWN,
  TD_THR_STOPPED,  // specifically, stopped by thr_suspend
  TD_THR_RUN,  // runnable, but not on a LWP yet
  TD_THR_ACTIVE, // running on a LWP right now
  TD_THR_ZOMBIE, // exited, but not joined yet
  TD_THR_SLEEP, // not currently runnable
  TD_THR_STOPPED_ASLEEP // blocked by TD_THR_SLEEP and stopped by td_thr_dbsuspend
} td_thr_state_e;

/* Thread type: user or system.  TD_THR_ANY_TYPE is a pseudo-type used
   to select threads regardless of type in td_ta_thr_iter().  */
typedef enum
{
  TD_THR_ANY_TYPE,
  TD_THR_USER,
  TD_THR_SYSTEM
} td_thr_type_e;

typedef struct td_thrinfo {
  void             *ti_ta_p;          /* internal process handle */
  unsigned         ti_user_flags;     /* value of flags parameter */
  thread_t         ti_tid;            /* thread identifier */ 
  char             *ti_tls;           /* pointer to thread-local storage*/
  psaddr_t         ti_startfunc;      /* address of function at which thread 
                                         execution began*/
  psaddr_t         ti_stkbase;        /* base of thread's stack area*/
  long             ti_stksize;        /* size in bytes of thread's allocated
                                         stack region*/
  psaddr_t         ti_ro_area;        /* address of ulwp_t structure*/
  int              ti_ro_size;         /* size of the ulwp_t structure in 
                                         bytes */
  td_thr_state_e   ti_state;           /* state of the thread */
  unsigned char    ti_db_suspended;    /* non-zero if thread suspended by 
                                         td_thr_dbsuspend*/
  td_thr_type_e    ti_type;            /* type of the thread*/
  intptr_t         ti_pc;              /* value of thread's program counter*/
  intptr_t         ti_sp;              /* value of thread's stack counter*/
  short            ti_flags;           /* set of special flags used by 
                                         libc*/
  int              ti_pri;             /* priority of thread returned by 
                                         thr_getprio(3T)*/
  lwpid_t          ti_lid;             /* id of light weight process (LWP) 
                                         executing this thread*/
  sigset_t         ti_sigmask;         /* thread's signal mask.  See 
                                         thr_sigsetmask(3T)*/
  unsigned char    ti_traceme;         /* non-zero if event tracing is on*/
  unsigned char    ti_preemptflag;     /* non-zero if thread preempted when 
                                         last active*/
  unsigned char    ti_pirecflag;       /* non-zero if thread runs priority 
                                        beside regular */
  sigset_t         ti_pending;        /* set of signals pending for this 
                                        thread*/
  td_thr_events_t  ti_events;         /* bitmap of events enabled for this 
                                        thread*/
} td_thrinfo_t;

// clang-format on

#define LIBTHREAD_DB_EXTERN extern __attribute__((visibility("default")))

// These get intercepted by our functions below
#define LIBTHREAD_DB_FUNCTION(symbol) static void *symbol##_orig;
LIBTHREAD_DB_FUNCTION(td_init)
LIBTHREAD_DB_FUNCTION(td_ta_map_lwp2thr)
LIBTHREAD_DB_FUNCTION(td_ta_new)
LIBTHREAD_DB_FUNCTION(td_ta_thr_iter)
LIBTHREAD_DB_FUNCTION(td_thr_get_info)
#undef LIBTHREAD_DB_FUNCTION

// These get forwarded to libthreaddb.so
#define LIBTHREAD_DB_FUNCTION(symbol)                                          \
    LIBTHREAD_DB_EXTERN void *symbol;                                          \
    void *symbol = nullptr;
LIBTHREAD_DB_FUNCTION(td_log)
LIBTHREAD_DB_FUNCTION(td_symbol_list)
LIBTHREAD_DB_FUNCTION(td_ta_clear_event)
LIBTHREAD_DB_FUNCTION(td_ta_delete)
LIBTHREAD_DB_FUNCTION(td_ta_enable_stats)
LIBTHREAD_DB_FUNCTION(td_ta_event_addr)
LIBTHREAD_DB_FUNCTION(td_ta_event_getmsg)
LIBTHREAD_DB_FUNCTION(td_ta_get_nthreads)
LIBTHREAD_DB_FUNCTION(td_ta_get_ph)
LIBTHREAD_DB_FUNCTION(td_ta_get_stats)
LIBTHREAD_DB_FUNCTION(td_ta_map_id2thr)
LIBTHREAD_DB_FUNCTION(td_ta_reset_stats)
LIBTHREAD_DB_FUNCTION(td_ta_set_event)
LIBTHREAD_DB_FUNCTION(td_ta_setconcurrency)
LIBTHREAD_DB_FUNCTION(td_ta_tsd_iter)
LIBTHREAD_DB_FUNCTION(td_thr_clear_event)
LIBTHREAD_DB_FUNCTION(td_thr_dbresume)
LIBTHREAD_DB_FUNCTION(td_thr_dbsuspend)
LIBTHREAD_DB_FUNCTION(td_thr_event_enable)
LIBTHREAD_DB_FUNCTION(td_thr_event_getmsg)
LIBTHREAD_DB_FUNCTION(td_thr_getfpregs)
LIBTHREAD_DB_FUNCTION(td_thr_getgregs)
LIBTHREAD_DB_FUNCTION(td_thr_getxregs)
LIBTHREAD_DB_FUNCTION(td_thr_getxregsize)
LIBTHREAD_DB_FUNCTION(td_thr_set_event)
LIBTHREAD_DB_FUNCTION(td_thr_setfpregs)
LIBTHREAD_DB_FUNCTION(td_thr_setgregs)
LIBTHREAD_DB_FUNCTION(td_thr_setprio)
LIBTHREAD_DB_FUNCTION(td_thr_setsigpending)
LIBTHREAD_DB_FUNCTION(td_thr_setxregs)
LIBTHREAD_DB_FUNCTION(td_thr_sigsetmask)
LIBTHREAD_DB_FUNCTION(td_thr_tls_get_addr)
LIBTHREAD_DB_FUNCTION(td_thr_tlsbase)
LIBTHREAD_DB_FUNCTION(td_thr_tsd)
LIBTHREAD_DB_FUNCTION(td_thr_validate)
#undef LIBTHREAD_DB_FUNCTION

static void *base_so;

static void __attribute__((destructor)) base_so_cleanup()
{
    if (base_so != nullptr) {
        dlclose(base_so);
        base_so = nullptr;
    }
}

// https://docs.oracle.com/cd/E86824_01/html/E54766/td-init-3c-db.html
LIBTHREAD_DB_EXTERN td_err_e td_init()
{
    base_so = dlopen(
        "/usr/lib/x86_64-linux-gnu/libthread_db.so", RTLD_LAZY | RTLD_LOCAL);
    if (base_so == nullptr) {
        fprintf(
            stderr,
            "FATAL: Failed to load '/usr/lib/x86_64-linux-gnu/libthread_db.so' "
            "due to '%s'.\n",
            dlerror());
        abort();
    }
#define LIBTHREAD_DB_FUNCTION(symbol)                                          \
    symbol##_orig = dlsym(base_so, #symbol);                                   \
    if (symbol##_orig == nullptr) {                                            \
        fprintf(                                                               \
            stderr,                                                            \
            "FATAL: Failed to resolve symbol '" #symbol "' due to '%s'.\n",    \
            dlerror());                                                        \
        abort();                                                               \
    }
    LIBTHREAD_DB_FUNCTION(td_init)
    LIBTHREAD_DB_FUNCTION(td_ta_map_lwp2thr)
    LIBTHREAD_DB_FUNCTION(td_ta_new)
    LIBTHREAD_DB_FUNCTION(td_ta_thr_iter)
    LIBTHREAD_DB_FUNCTION(td_thr_get_info)
#undef LIBTHREAD_DB_FUNCTION
#define LIBTHREAD_DB_FUNCTION(symbol)                                          \
    symbol = dlsym(base_so, #symbol);                                          \
    if (symbol == nullptr) {                                                   \
        fprintf(                                                               \
            stderr,                                                            \
            "FATAL: Failed to resolve symbol '" #symbol "' due to '%s'.\n",    \
            dlerror());                                                        \
        abort();                                                               \
    }
    LIBTHREAD_DB_FUNCTION(td_log)
    LIBTHREAD_DB_FUNCTION(td_symbol_list)
    LIBTHREAD_DB_FUNCTION(td_ta_clear_event)
    LIBTHREAD_DB_FUNCTION(td_ta_delete)
    LIBTHREAD_DB_FUNCTION(td_ta_enable_stats)
    LIBTHREAD_DB_FUNCTION(td_ta_event_addr)
    LIBTHREAD_DB_FUNCTION(td_ta_event_getmsg)
    LIBTHREAD_DB_FUNCTION(td_ta_get_nthreads)
    LIBTHREAD_DB_FUNCTION(td_ta_get_ph)
    LIBTHREAD_DB_FUNCTION(td_ta_get_stats)
    LIBTHREAD_DB_FUNCTION(td_ta_map_id2thr)
    LIBTHREAD_DB_FUNCTION(td_ta_reset_stats)
    LIBTHREAD_DB_FUNCTION(td_ta_set_event)
    LIBTHREAD_DB_FUNCTION(td_ta_setconcurrency)
    LIBTHREAD_DB_FUNCTION(td_ta_tsd_iter)
    LIBTHREAD_DB_FUNCTION(td_thr_clear_event)
    LIBTHREAD_DB_FUNCTION(td_thr_dbresume)
    LIBTHREAD_DB_FUNCTION(td_thr_dbsuspend)
    LIBTHREAD_DB_FUNCTION(td_thr_event_enable)
    LIBTHREAD_DB_FUNCTION(td_thr_event_getmsg)
    LIBTHREAD_DB_FUNCTION(td_thr_getfpregs)
    LIBTHREAD_DB_FUNCTION(td_thr_getgregs)
    LIBTHREAD_DB_FUNCTION(td_thr_getxregs)
    LIBTHREAD_DB_FUNCTION(td_thr_getxregsize)
    LIBTHREAD_DB_FUNCTION(td_thr_set_event)
    LIBTHREAD_DB_FUNCTION(td_thr_setfpregs)
    LIBTHREAD_DB_FUNCTION(td_thr_setgregs)
    LIBTHREAD_DB_FUNCTION(td_thr_setprio)
    LIBTHREAD_DB_FUNCTION(td_thr_setsigpending)
    LIBTHREAD_DB_FUNCTION(td_thr_setxregs)
    LIBTHREAD_DB_FUNCTION(td_thr_sigsetmask)
    LIBTHREAD_DB_FUNCTION(td_thr_tls_get_addr)
    LIBTHREAD_DB_FUNCTION(td_thr_tlsbase)
    LIBTHREAD_DB_FUNCTION(td_thr_tsd)
    LIBTHREAD_DB_FUNCTION(td_thr_validate)
#undef LIBTHREAD_DB_FUNCTION
    return ((td_err_e(*)())td_init_orig)();
}

// https://docs.oracle.com/cd/E86824_01/html/E54766/td-ta-map-lwp2thr-3c-db.html
LIBTHREAD_DB_EXTERN td_err_e td_ta_map_lwp2thr(
    td_thragent_t const *ta_p, lwpid_t lwpid, td_thrhandle_t *th_p)
{
    /* If the lwpid_t is currently running one of our contexts, return that
     * context.
     */
    return ((td_err_e(*)(
        td_thragent_t const *ta_p, lwpid_t lwpid, td_thrhandle_t *th_p))
                td_ta_map_lwp2thr_orig)(ta_p, lwpid, th_p);
}

// https://docs.oracle.com/cd/E86824_01/html/E54766/td-ta-new-3c-db.html
LIBTHREAD_DB_EXTERN td_err_e
td_ta_new(const struct ps_prochandle *ph_p, td_thragent_t **ta_pp)
{
    /* Use psaddr_t symbol_addr; ps_pglobal_lookup(ph_p, nullptr, "symbol",
    &symbol_addr); to look up our debugging access function in the inferior.

    Store td_thragent_t* in an array mapping it to our state.
    */
    return ((td_err_e(*)(
        const struct ps_prochandle *ph_p,
        td_thragent_t **ta_pp))td_ta_new_orig)(ph_p, ta_pp);
}

// https://docs.oracle.com/cd/E86824_01/html/E54766/td-ta-thr-iter-3c-db.html
LIBTHREAD_DB_EXTERN td_err_e td_ta_thr_iter(
    td_thragent_t const *ta_p, td_thr_iter_f *cb, void *cbdata_p,
    td_thr_state_e state, int ti_pri, sigset_t *ti_sigmask_p,
    unsigned ti_user_flags)
{
#if 0
    for (size_t n = 0; n != 0; n++) {
        if (state == TD_THR_SLEEP) {
            td_thrhandle_t *th;
            if (cb(th, cbdata_p) != 0) {
                return TD_OK;
            }
        }
    }
#endif
    return ((td_err_e(*)(
        td_thragent_t const *ta_p,
        td_thr_iter_f *cb,
        void *cbdata_p,
        td_thr_state_e state,
        int ti_pri,
        sigset_t *ti_sigmask_p,
        unsigned ti_user_flags))td_ta_thr_iter_orig)(
        ta_p, cb, cbdata_p, state, ti_pri, ti_sigmask_p, ti_user_flags);
}

// https://docs.oracle.com/cd/E86824_01/html/E54766/td-thr-get-info-3c-db.html
LIBTHREAD_DB_EXTERN td_err_e
td_thr_get_info(td_thrhandle_t const *th_p, td_thrinfo_t *ti_p)
{
    /* Is th_p one of our contexts? If so:

    Fetch the td_thrinfo_t for the underlying kernel thread and replace:

    ti_startfunc
    ti_stkbase
    ti_stksize
    ti_state
    ti_type = TD_THR_USER (maint info sol-threads) will show "Solaris user
    threads"
    ti_pc ti_sp

    If not one our contexts, but it is currently running our context,
    we need to set ti_state from TD_THR_ACTIVE to TD_THR_RUN.
    */
    return ((td_err_e(*)(td_thrhandle_t const *th_p, td_thrinfo_t *ti_p))
                td_thr_get_info_orig)(th_p, ti_p);
}
