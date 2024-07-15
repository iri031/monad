include! {"async_raw_bindings.rs"}
include! {"../../rust/monad_rust_utils.rs"}

use std::{
    cell::RefCell,
    ffi::CStr,
    future::Future,
    pin::Pin,
    rc::Rc,
    task::{Context, Poll, Waker},
};

unsafe extern "C" {
    pub fn abort() -> !;
}

// Helper function to form a Rust atomic from what bindgen emits
unsafe fn to_atomic_ptr<'a, T>(p: *const *mut T) -> &'a std::sync::atomic::AtomicPtr<T> {
    &*(p as *const std::sync::atomic::AtomicPtr<T>)
}

#[allow(dead_code)]
#[derive(Debug)]
/// \brief A smart pointer to an executor
pub struct monad_async_executor_ptr {
    pub head: monad_async_executor,
}

impl Default for monad_async_executor_ptr {
    fn default() -> Self {
        let mut s = ::std::mem::MaybeUninit::<Self>::uninit();
        unsafe {
            ::std::ptr::write_bytes(s.as_mut_ptr(), 0, 1);
            s.assume_init()
        }
    }
}

impl monad_async_executor_ptr {
    #[allow(dead_code)]
    pub fn new(ex_attr: &mut monad_async_executor_attr) -> MonadCResult<monad_async_executor_ptr> {
        let mut ret = monad_async_executor_ptr {
            ..Default::default()
        };
        unsafe {
            to_result(monad_async_executor_create(&mut ret.head, ex_attr))?;
        }
        Ok(ret)
    }
}

impl Drop for monad_async_executor_ptr {
    fn drop(&mut self) {
        unsafe {
            if self.head.as_ref().is_some() {
                to_result(monad_async_executor_destroy(self.head)).unwrap();
            }
        }
    }
}

#[allow(dead_code)]
#[derive(Debug)]
/// \brief A smart pointer to a context switcher
pub struct monad_context_switcher_ptr {
    pub head: monad_context_switcher,
}

impl Default for monad_context_switcher_ptr {
    fn default() -> Self {
        let mut s = ::std::mem::MaybeUninit::<Self>::uninit();
        unsafe {
            ::std::ptr::write_bytes(s.as_mut_ptr(), 0, 1);
            s.assume_init()
        }
    }
}

impl monad_context_switcher_ptr {
    #[allow(dead_code)]
    pub fn new(implem: &monad_context_switcher_impl) -> MonadCResult<monad_context_switcher_ptr> {
        let mut ret = monad_context_switcher_ptr {
            ..Default::default()
        };
        unsafe {
            to_result(implem.create.unwrap()(&mut ret.head))?;
        }
        Ok(ret)
    }
}

impl Drop for monad_context_switcher_ptr {
    fn drop(&mut self) {
        unsafe {
            if self.head.as_ref().is_some() {
                to_result((*self.head).self_destroy.unwrap()(self.head)).unwrap();
            }
        }
    }
}

#[allow(dead_code)]
#[derive(Debug)]
/// \brief A smart pointer to a task
pub struct monad_async_task_ptr {
    pub head: monad_async_task,
}

impl Default for monad_async_task_ptr {
    fn default() -> Self {
        let mut s = ::std::mem::MaybeUninit::<Self>::uninit();
        unsafe {
            ::std::ptr::write_bytes(s.as_mut_ptr(), 0, 1);
            s.assume_init()
        }
    }
}

impl monad_async_task_ptr {
    #[allow(dead_code)]
    pub fn new(
        switcher: monad_context_switcher,
        attr: *mut monad_async_task_attr,
    ) -> MonadCResult<monad_async_task_ptr> {
        let mut ret = monad_async_task_ptr {
            ..Default::default()
        };
        unsafe {
            to_result(monad_async_task_create(&mut ret.head, switcher, attr))?;
        }
        Ok(ret)
    }
}

impl Drop for monad_async_task_ptr {
    fn drop(&mut self) {
        unsafe {
            if self.head.as_ref().is_some() {
                to_result(monad_async_task_destroy(self.head)).unwrap();
            }
        }
    }
}

#[allow(dead_code)]
#[derive(Debug)]
/// \brief A smart pointer to an open file
pub struct monad_async_task_file_ptr {
    pub head: monad_async_file,
    pub task: monad_async_task,
}

impl Default for monad_async_task_file_ptr {
    fn default() -> Self {
        let mut s = ::std::mem::MaybeUninit::<Self>::uninit();
        unsafe {
            ::std::ptr::write_bytes(s.as_mut_ptr(), 0, 1);
            s.assume_init()
        }
    }
}

impl monad_async_task_file_ptr {
    #[allow(dead_code)]
    pub fn new(
        task: monad_async_task,
        base: monad_async_file,
        subpath: *const ::std::os::raw::c_char,
        how: *mut open_how,
    ) -> MonadCResult<monad_async_task_file_ptr> {
        let mut ret = monad_async_task_file_ptr {
            ..Default::default()
        };
        unsafe {
            to_result(monad_async_task_file_create(
                &mut ret.head,
                task,
                base,
                subpath,
                how,
            ))?;
        }
        ret.task = task;
        Ok(ret)
    }
}

impl Drop for monad_async_task_file_ptr {
    fn drop(&mut self) {
        unsafe {
            if self.head.as_ref().is_some() {
                to_result(monad_async_task_file_destroy(self.task, self.head)).unwrap();
            }
        }
    }
}

#[allow(dead_code)]
#[derive(Debug)]
/// \brief A smart pointer to an open socket
pub struct monad_async_task_socket_ptr {
    pub head: monad_async_socket,
    pub task: monad_async_task,
}

impl Default for monad_async_task_socket_ptr {
    fn default() -> Self {
        let mut s = ::std::mem::MaybeUninit::<Self>::uninit();
        unsafe {
            ::std::ptr::write_bytes(s.as_mut_ptr(), 0, 1);
            s.assume_init()
        }
    }
}

impl monad_async_task_socket_ptr {
    #[allow(dead_code)]
    pub fn new(
        task: monad_async_task,
        domain: ::std::os::raw::c_int,
        type_: ::std::os::raw::c_int,
        protocol: ::std::os::raw::c_int,
        flags: ::std::os::raw::c_uint,
    ) -> MonadCResult<monad_async_task_socket_ptr> {
        let mut ret = monad_async_task_socket_ptr {
            ..Default::default()
        };
        unsafe {
            to_result(monad_async_task_socket_create(
                &mut ret.head,
                task,
                domain,
                type_,
                protocol,
                flags,
            ))?;
        }
        ret.task = task;
        Ok(ret)
    }
}

impl Drop for monad_async_task_socket_ptr {
    fn drop(&mut self) {
        unsafe {
            if self.head.as_ref().is_some() {
                to_result(monad_async_task_socket_destroy(self.task, self.head)).unwrap();
            }
        }
    }
}

// Teaches Rust about a monad async task
#[allow(dead_code)]
#[derive(Debug)]
struct MonadAsyncTaskInner<T>
where
    T: FnOnce(monad_async_task) -> monad_c_result,
{
    func: Option<T>,
    waker: Option<Waker>,
    retval: monad_c_result,
    owned_task: monad_async_task_ptr,
}

/// \brief A Rust async wrapper of an async task executing a Rust closure
#[derive(Clone)]
pub struct MonadAsyncTask {
    inner: Option<Rc<RefCell<Box<dyn MonadAsyncTaskErased>>>>,
    ex: monad_async_executor,
    task: monad_async_task,
    is_cancelled: bool
}

impl MonadAsyncTask {
    fn new_internal<T>(
        ex: monad_async_executor,
        task: monad_async_task,
        owned_task: monad_async_task_ptr,
        func: T,
    ) -> MonadCResult<MonadAsyncTask>
    where
        T: FnOnce(monad_async_task) -> monad_c_result + 'static,
    {
        let inner: Rc<RefCell<Box<dyn MonadAsyncTaskErased>>> =
            Rc::new(RefCell::new(Box::new(MonadAsyncTaskInner {
                func: Some(func),
                waker: None,
                retval: monad_c_result {
                    ..Default::default()
                },
                owned_task,
            })));
        // Clone the Rc, and release its pointer to MonadAsyncTaskWrapperFunction
        let inner_copy = inner.clone();
        let inner_copy_ptr = Rc::into_raw(inner_copy);
        unsafe {
            (*task).derived.user_code = Some(MonadAsyncTaskWrapperFunction);
            (*task).derived.user_ptr = inner_copy_ptr as *mut ::std::os::raw::c_void;
        }
        to_result(unsafe { monad_async_task_attach(ex, task, std::ptr::null_mut()) })?;
        Ok(MonadAsyncTask {
            inner: Some(inner),
            ex,
            task,
            is_cancelled: false
        })
    }

    pub fn new_using_external_task<T>(
        ex: monad_async_executor,
        task: monad_async_task,
        func: T,
    ) -> MonadCResult<MonadAsyncTask>
    where
        T: FnOnce(monad_async_task) -> monad_c_result + 'static,
    {
        MonadAsyncTask::new_internal(
            ex,
            task,
            monad_async_task_ptr {
                ..Default::default()
            },
            func,
        )
    }

    pub fn new_using_internal_task<T>(
        ex: monad_async_executor,
        switcher: monad_context_switcher,
        func: T,
    ) -> MonadCResult<MonadAsyncTask>
    where
        T: FnOnce(monad_async_task) -> monad_c_result + 'static,
    {
        let mut t_attr = monad_async_task_attr {
            ..Default::default()
        };
        let task = monad_async_task_ptr::new(switcher, &mut t_attr)?;
        MonadAsyncTask::new_internal(ex, task.head, task, func)
    }

    pub fn is_valid(&self) -> bool {
        self.inner.is_some()
    }

    pub fn executor(&self) -> monad_async_executor {
        self.ex
    }

    pub fn task(&self) -> monad_async_task {
        self.task
    }

    pub fn has_exited(&self) -> bool {
        if self.task == std::ptr::null_mut() {
            panic!("MonadAsyncTask's task not set");
        }
        unsafe { monad_async_task_has_exited(self.task) }
    }

    pub fn get_exit_result(&self) -> Option<monad_c_result> {
        if self.has_exited() {
            return Some(self.inner.as_ref().unwrap().borrow().value());
        }
        None
    }

    pub fn is_cancelled(&self) -> bool {
        self.is_cancelled
    }

    pub fn initiate_cancel(&mut self) -> MonadCResult<isize>
    {
        self.is_cancelled = true;
        to_result(unsafe { monad_async_task_cancel(self.ex, self.task) })
    }

    #[allow(dead_code)]
    pub fn as_fut(self) -> impl Future<Output = monad_c_result> {
        self
    }

    pub fn detach(mut self) {
        // Disable blocking drop
        self.ex = std::ptr::null_mut();
        drop(self)
    }
}

impl Drop for MonadAsyncTask {
    fn drop(&mut self) {
        if self.ex != std::ptr::null_mut() {
            loop {
                if self.has_exited() {
                    break;
                }
                unsafe { monad_async_executor_run(self.ex, 1, std::ptr::null_mut()) };
            }
        }
    }
}

impl Default for MonadAsyncTask {
    fn default() -> MonadAsyncTask {
        MonadAsyncTask {
            inner: None,
            ex: std::ptr::null_mut(),
            task: std::ptr::null_mut(),
            is_cancelled : false
        }
    }
}

trait MonadAsyncTaskErased {
    #[allow(dead_code)]
    fn func(&mut self, task: monad_async_task) -> monad_c_result;
    fn set_waker(&mut self, waker: Waker);
    fn value(&self) -> monad_c_result;
}

impl<T> MonadAsyncTaskErased for MonadAsyncTaskInner<T>
where
    T: FnOnce(monad_async_task) -> monad_c_result,
{
    #[allow(dead_code)]
    fn func(&mut self, task: monad_async_task) -> monad_c_result {
        let func = self.func.take().unwrap();
        let ret = (func)(task);
        self.retval = ret;
        let waker = self.waker.take();
        match waker {
            None => (),
            Some(waker) => waker.wake(),
        };
        ret
    }
    fn set_waker(&mut self, waker: Waker) {
        self.waker = Some(waker);
    }
    fn value(&self) -> monad_c_result {
        self.retval
    }
}

unsafe extern "C" fn MonadAsyncTaskWrapperFunction(task_: monad_context_task) -> monad_c_result {
    let task = task_ as monad_async_task;
    // It would appear Rust demands mutex protection for values which traverse catch_unwind().
    let r = std::sync::Mutex::new(monad_c_result {
        ..Default::default()
    });
    match std::panic::catch_unwind(|| {
        let parent: Rc<RefCell<Box<dyn MonadAsyncTaskErased>>> = unsafe {
            Rc::from_raw((*task).derived.user_ptr as *mut RefCell<Box<dyn MonadAsyncTaskErased>>)
        };
        *r.lock().unwrap() = parent.as_ref().borrow_mut().func(task);
        // When the Rc drops, it _may_ cause the `MonadAsyncTaskInner` to get dropped
    }) {
        Ok(_) => *r.lock().unwrap(),
        Err(err) => {
            if let Some(s) = err.downcast_ref::<String>() {
                eprintln!(
                    "FATAL: Rust panic reached MonadAsyncTaskWrapperFunction: '{}'",
                    s
                );
            } else if let Some(s) = err.downcast_ref::<&str>() {
                eprintln!(
                    "FATAL: Rust panic reached MonadAsyncTaskWrapperFunction: '{}'",
                    s
                );
            } else {
                eprintln!("FATAL: Rust panic reached MonadAsyncTaskWrapperFunction: unknown");
            }
            abort()
        }
    }
}

impl Future for MonadAsyncTask {
    type Output = monad_c_result;

    fn poll(self: Pin<&mut Self>, cx: &mut Context<'_>) -> Poll<Self::Output> {
        if unsafe { monad_async_task_has_exited(self.task) } {
            return Poll::Ready(self.inner.as_ref().unwrap().borrow().value());
        }
        let mut ts = timespec {
            ..Default::default()
        };
        match unsafe { to_result(monad_async_executor_run(self.ex, 1, &mut ts)) } {
            Err(err) => {
                if unsafe {
                    outcome_status_code_equal_generic(
                        &err as *const cxx_status_code_system as *const ::std::os::raw::c_void,
                        62, /*ETIME*/
                    )
                } == 0
                {
                    panic!("{}", err);
                }
            }
            Ok(_) => {}
        };
        if unsafe { monad_async_task_has_exited(self.task) } {
            return Poll::Ready(self.inner.as_ref().unwrap().borrow().value());
        }
        Pin::into_inner(self)
            .inner
            .as_ref()
            .unwrap()
            .borrow_mut()
            .set_waker(cx.waker().clone());
        Poll::Pending
    }
}

impl std::fmt::Debug for MonadAsyncTask {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("MonadAsyncTask")
            .field("ex", &self.ex)
            .field("task", &self.task)
            .finish()
    }
}

impl std::fmt::Debug for monad_async_io_status {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("monad_async_io_status")
            .field("ticks_when_initiated", &self.ticks_when_initiated)
            .field("ticks_when_completed", &self.ticks_when_completed)
            .field("ticks_when_reaped", &self.ticks_when_reaped)
            .finish()
    }
}
