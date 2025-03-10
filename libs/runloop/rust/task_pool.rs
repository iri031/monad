#![allow(non_upper_case_globals)]
#![allow(non_camel_case_types)]
#![allow(non_snake_case)]
#![allow(unused)]

include! {"async.rs"}

use std::{ffi::c_void, mem, pin::pin, time::Duration};

pub trait LinkedListItem<T> {
    fn prev(&self) -> &Option<*mut T>;
    fn next(&self) -> &Option<Pin<Box<T>>>;
    fn prev_mut(&mut self) -> &mut Option<*mut T>;
    fn next_mut(&mut self) -> &mut Option<Pin<Box<T>>>;
}

#[derive(Debug)]
pub struct LinkedList<T> {
    front: Option<Pin<Box<T>>>,
    back: Option<*mut T>,
}

// Stable Rust doesn't implement `.as_mut_ptr()` yet
fn box_as_mut_ptr<T>(val: Pin<Box<T>>) -> (Box<T>, *mut T) {
    let mut ptr: *mut T = Box::into_raw(unsafe { Pin::into_inner_unchecked(val) });
    let val_ = unsafe { Box::from_raw(ptr) };
    (val_, ptr)
}

impl<T: LinkedListItem<T>> LinkedList<T> {
    pub fn new() -> LinkedList<T> {
        LinkedList {
            front: None,
            back: None,
        }
    }
    fn check_for_correctness(&mut self, desc: &'static str) {
        if cfg!(debug_assertions) {
            //println!("   Checking for correctness after {} ...", desc);
            let mut p: Option<&mut Pin<Box<T>>> = self.front.as_mut();
            if p.is_none() {
                debug_assert!(self.back.is_none());
                return;
            }
            let mut p_addr: *mut T =
                unsafe { Pin::into_inner_unchecked(p.as_mut().unwrap().as_mut()) } as *mut T;
            let p_inner: &mut T = unsafe { &mut *p_addr };
            /*println!(
                "      Front is {:#?}, back is {:#?}",
                p_addr,
                self.back.as_ref().unwrap()
            );*/
            debug_assert!(p_inner.prev_mut().is_none());
            let mut prev_addr = p_addr;
            p = p_inner.next_mut().as_mut();
            while p.is_some() {
                p_addr =
                    unsafe { Pin::into_inner_unchecked(p.as_mut().unwrap().as_mut()) } as *mut T;
                let p_inner: &mut T = unsafe { &mut *p_addr };
                debug_assert!(p_inner.prev_mut().unwrap() as *const T == prev_addr);
                debug_assert!(p_addr != prev_addr);
                prev_addr = p_addr;
                //println!("      Item is {:#?}", prev_addr);
                p = p_inner.next_mut().as_mut();
            }
            debug_assert!(unsafe { (*prev_addr).next_mut() }.is_none());
        }
    }
    pub fn empty(&self) -> bool {
        self.front.is_none() && self.back.is_none()
    }
    pub fn front(&self) -> Option<Pin<&'static mut T>> {
        if self.front.is_none() {
            return None;
        }
        let front: &Pin<Box<T>> = self.front.as_ref().unwrap();
        if front.next().is_some() {
            let ptr: *mut T = front
                .next()
                .as_ref()
                .unwrap()
                .prev()
                .as_ref()
                .unwrap()
                .clone();
            return Some(unsafe { Pin::new_unchecked(&mut *ptr) });
        }
        let ptr: *mut T = self.back.as_ref().unwrap().clone();
        Some(unsafe { Pin::new_unchecked(&mut *ptr) })
    }
    pub fn push_back(&mut self, val_: Pin<Box<T>>) -> Pin<&'static mut T> {
        let (mut val, mut ptr) = box_as_mut_ptr(val_);
        if self.front.is_none() {
            // List is empty
            assert_eq!(self.back.is_none(), true);
            self.front = Some(Box::into_pin(val));
            self.back = Some(ptr);
        } else {
            *val.prev_mut() = self.back;
            unsafe { *(*(*self.back.as_mut().unwrap())).next_mut() = Some(Box::into_pin(val)) };
            self.back = Some(ptr);
        }
        self.check_for_correctness("push back");
        unsafe { Pin::new_unchecked(&mut *ptr) }
    }
    pub fn pop(&mut self) -> Option<Pin<Box<T>>> {
        if self.front.is_some() {
            let (mut front, mut ptr) = box_as_mut_ptr(self.front.take().unwrap());
            let mut next = front.next_mut().take();
            if next.is_some() {
                *unsafe { Pin::into_inner_unchecked(next.as_mut().unwrap().as_mut()) }.prev_mut() =
                    None;
                self.front = next;
            } else {
                self.front = None;
                self.back = None;
            }
            *front.prev_mut() = None;
            *front.next_mut() = None;
            self.check_for_correctness("pop");
            return Some(Box::into_pin(front));
        }
        None
    }
    pub fn remove_by_ref(&mut self, val: &mut T) -> Pin<Box<T>> {
        if (*val).prev_mut().is_none() && (*val).next_mut().is_none() {
            // One item in the list
            let (mut front, mut ptr) = box_as_mut_ptr(self.front.take().unwrap());
            if ptr != val {
                panic!("pointer values don't match");
            }
            if self.back.unwrap() != val {
                panic!("pointer values don't match");
            }
            self.front = None;
            self.back = None;
            self.check_for_correctness("remove from single item list");
            return Box::into_pin(front);
        }
        if (*val).prev_mut().is_none() {
            // Item is at front of list
            let (mut front, mut ptr) = box_as_mut_ptr(self.front.take().unwrap());
            if ptr != val {
                panic!("pointer values don't match");
            }
            self.front = front.next_mut().take();
            *unsafe { Pin::into_inner_unchecked(self.front.as_mut().unwrap().as_mut()) }
                .prev_mut() = None;
            self.check_for_correctness("remove when item front of list");
            return Box::into_pin(front);
        }
        if (*val).next_mut().is_none() {
            // Item is at back of list
            if self.back.unwrap() != val {
                panic!("pointer values don't match");
            }
            let mut ret: Pin<Box<T>> = unsafe {
                (*(*(*val).prev_mut().as_ref().unwrap()))
                    .next_mut()
                    .take()
                    .unwrap()
            };
            unsafe {
                *(*Pin::into_inner_unchecked(ret.as_mut()).prev_mut().unwrap()).next_mut() = None
            };
            self.back = unsafe { *(*self.back.unwrap()).prev_mut() };
            *unsafe { Pin::into_inner_unchecked(ret.as_mut()).prev_mut() } = None;
            self.check_for_correctness("remove when item back of list");
            return ret;
        }
        // Item is in middle of list
        let this_as_box = unsafe { (*(*(*val).prev_mut().as_ref().unwrap())).next_mut() };
        debug_assert!(this_as_box.is_some());
        let (mut ret, mut ptr) = box_as_mut_ptr(this_as_box.take().unwrap());
        if ptr != val {
            panic!("pointer values don't match");
        }
        *(*unsafe { Pin::into_inner_unchecked(ret.next_mut().as_mut().unwrap().as_mut()) })
            .prev_mut() = *ret.prev_mut();
        unsafe { *(*(*ret.prev_mut().as_ref().unwrap())).next_mut() = ret.next_mut().take() };
        *ret.prev_mut() = None;
        self.check_for_correctness("remove when item middle of list");
        Box::into_pin(ret)
    }
    pub fn remove(&mut self, val: Pin<&mut T>) -> Pin<Box<T>> {
        self.remove_by_ref(unsafe { Pin::into_inner_unchecked(val) })
    }
}

#[derive(Debug)]
struct MonadAsyncIo {
    prev: Option<*mut MonadAsyncIo>,
    next: Option<Pin<Box<MonadAsyncIo>>>,
    parent: Option<MonadAsyncTaskPool>,

    iostatus: monad_async_io_status,
    buffer: monad_async_task_registered_io_buffer,
    msghdr: msghdr,
    is_done: bool,
    waker: Option<Waker>,
    pub user_value: usize,
}

impl MonadAsyncIo {
    fn from_io_status(iostatus: *mut monad_async_io_status) -> &'static mut MonadAsyncIo {
        let addr = iostatus as usize;
        let addr2 = addr - mem::offset_of!(MonadAsyncIo, iostatus);
        let addr3 = addr2 as *mut MonadAsyncIo;
        unsafe { &mut *addr3 }
    }

    fn as_io_status(&mut self) -> *mut monad_async_io_status {
        &mut self.iostatus as *mut monad_async_io_status
    }

    fn as_io_buffer(&mut self) -> *mut monad_async_task_registered_io_buffer {
        &mut self.buffer as *mut monad_async_task_registered_io_buffer
    }

    fn as_msghdr(&mut self) -> *mut msghdr {
        &mut self.msghdr as *mut msghdr
    }

    fn as_pin<'a>(&'a self) -> Pin<&'static MonadAsyncIo> {
        Pin::static_ref(unsafe {
            std::mem::transmute::<&'a MonadAsyncIo, &'static MonadAsyncIo>(self)
        })
    }

    fn as_mut_pin<'a>(&'a mut self) -> Pin<&'static mut MonadAsyncIo> {
        Pin::static_mut(unsafe {
            std::mem::transmute::<&'a mut MonadAsyncIo, &'static mut MonadAsyncIo>(self)
        })
    }

    fn new(parent: MonadAsyncTaskPool) -> MonadAsyncIo {
        MonadAsyncIo {
            prev: None,
            next: None,
            parent: Some(parent),
            iostatus: monad_async_io_status {
                ..Default::default()
            },
            buffer: monad_async_task_registered_io_buffer {
                ..Default::default()
            },
            msghdr: msghdr {
                ..Default::default()
            },
            is_done: false,
            waker: None,
            user_value: 0,
        }
    }
}

impl LinkedListItem<MonadAsyncIo> for MonadAsyncIo {
    fn prev(&self) -> &Option<*mut MonadAsyncIo> {
        &self.prev
    }
    fn next(&self) -> &Option<Pin<Box<MonadAsyncIo>>> {
        &self.next
    }
    fn prev_mut(&mut self) -> &mut Option<*mut MonadAsyncIo> {
        &mut self.prev
    }
    fn next_mut(&mut self) -> &mut Option<Pin<Box<MonadAsyncIo>>> {
        &mut self.next
    }
}

#[derive(Debug)]
pub struct MonadAsyncIoRef {
    inner: Option<Pin<&'static mut MonadAsyncIo>>,
}

impl MonadAsyncIoRef {
    pub fn as_fut(self) -> impl Future<Output = monad_c_result> {
        self
    }

    /// \brief Sets the user defined value
    pub fn set_user_value(&mut self, user_value: usize) {
        self.inner.as_mut().unwrap().user_value = user_value;
    }

    /// \brief Gets the user defined value
    pub fn user_value(&self) -> usize {
        self.inner.as_ref().unwrap().user_value
    }

    /// \brief True if i/o has been initiated and has not completed yet.
    pub fn is_in_progress(&self) -> bool {
        unsafe {
            monad_async_is_io_in_progress(
                &self.inner.as_ref().unwrap().iostatus as *const monad_async_io_status,
            )
        }
    }

    /// \brief True if i/o has been initiated, has completed, and has been reaped by the dispatcher
    /// task (i.e. you can read the result now).
    pub fn is_done(&self) -> bool {
        self.inner.as_ref().unwrap().is_done
    }

    /// \brief The result of the i/o, if it is completed.
    pub fn result(&self) -> Option<monad_c_result> {
        if self.is_in_progress() {
            return None;
        }
        Some(unsafe {
            *self
                .inner
                .as_ref()
                .unwrap()
                .iostatus
                .__bindgen_anon_1
                .result
                .as_ref()
        })
    }

    /// \brief A pointer to `monad_async_io_status` ready for passing to an i/o initiation operation
    pub fn iostatus(&mut self) -> *mut monad_async_io_status {
        &mut self.inner.as_mut().unwrap().iostatus as *mut monad_async_io_status
    }

    /// \brief A pointer to `monad_async_task_registered_io_buffer` ready for passing to an i/o initiation operation
    pub fn tofill(&mut self) -> *mut monad_async_task_registered_io_buffer {
        &mut self.inner.as_mut().unwrap().buffer as *mut monad_async_task_registered_io_buffer
    }

    /// \brief The buffer `tofill()` filled as a Rust slice. Returns None if no result set or the result indicates failure.
    pub fn result_as_slice(&self) -> Option<&[u8]> {
        match to_result(self.result()?) {
            Ok(bytes_read) => Some(unsafe {
                std::slice::from_raw_parts(
                    self.inner.as_ref().unwrap().buffer.iov[0].iov_base as *const u8,
                    bytes_read as usize,
                )
            }),
            Err(_) => None,
        }
    }

    /// \brief Initiate cancellation of this i/o.
    pub fn cancel(&self) -> MonadCResult<()> {
        self.inner
            .as_ref()
            .unwrap()
            .parent
            .as_ref()
            .unwrap()
            .cancel_io(self)
    }

    /// \brief Release all resources back to the task pool. This will block if the i/o is not done yet.
    pub fn reset(mut self) -> MonadCResult<()> {
        if self.is_in_progress() {
            self.cancel()?;
        }
        let mut parent = self
            .inner
            .as_ref()
            .unwrap()
            .parent
            .as_ref()
            .unwrap()
            .clone();
        let mut pin = parent.reset_io(self.inner.take().unwrap())?;
        pin.iostatus = monad_async_io_status {
            ..Default::default()
        };
        pin.buffer = monad_async_task_registered_io_buffer {
            ..Default::default()
        };
        pin.msghdr = msghdr {
            ..Default::default()
        };
        pin.is_done = false;
        pin.waker = None;
        Ok(())
    }

    /// \brief Release management of this reference
    pub unsafe fn release(mut self) {
        self.inner = None
    }
}

impl Clone for MonadAsyncIoRef {
    fn clone(&self) -> Self {
        if self.inner.is_none() {
            MonadAsyncIoRef { inner: None }
        } else {
            /* Annoyingly, there appears to be no way of getting a &mut MonadAsyncIo
            from a Pin if that Pin is an immutable reference. I therefore can only
            clone a &MonadAsyncIo without this hackery. */
            let iostatus = &self.inner.as_ref().unwrap().iostatus as *const monad_async_io_status
                as *mut monad_async_io_status;
            let this: &mut MonadAsyncIo = MonadAsyncIo::from_io_status(iostatus);
            MonadAsyncIoRef {
                inner: Some(Pin::static_mut(this)),
            }
        }
    }
}

impl Drop for MonadAsyncIoRef {
    fn drop(&mut self) {
        if self.inner.is_some() {
            panic!("An MonadAsyncIo was not reset before drop!");
        }
    }
}

impl Future for MonadAsyncIoRef {
    type Output = monad_c_result;

    fn poll(self: Pin<&mut Self>, cx: &mut Context<'_>) -> Poll<Self::Output> {
        if self.is_done() {
            return Poll::Ready(self.result().unwrap());
        }
        Pin::into_inner(self).inner.as_mut().unwrap().waker = Some(cx.waker().clone());
        Poll::Pending
    }
}

struct MonadAsyncTaskPoolInner {
    ex_ptr: monad_async_executor_ptr,
    switcher_ptr: monad_context_switcher_ptr,

    switcher: monad_context_switcher,
    io_sleeping: LinkedList<MonadAsyncIo>,
    io_initiated: LinkedList<MonadAsyncIo>,
    io_awaiting_reap: LinkedList<MonadAsyncIo>,
    dispatcher: MonadAsyncTask,
    tasks_sleeping: Vec<monad_async_task_ptr>,
    tasks_inuse: i32,
    io_awaiting_reap_callback: Option<Box<dyn FnMut()>>,
}

impl std::fmt::Debug for MonadAsyncTaskPoolInner {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("MonadAsyncTaskPoolInner")
            .field("ex_ptr", &self.ex_ptr)
            .field("switcher_ptr", &self.switcher_ptr)
            .field("switcher", &self.switcher)
            .field("io_sleeping", &self.io_sleeping)
            .field("io_initiated", &self.io_initiated)
            .field("io_awaiting_reap", &self.io_awaiting_reap)
            .field("dispatcher", &self.dispatcher)
            .field("tasks_sleeping", &self.tasks_sleeping)
            .field("tasks_inuse", &self.tasks_inuse)
            .finish()
    }
}

impl MonadAsyncTaskPoolInner {
    fn launch_tasks(&mut self, ex: monad_async_executor, tasks: usize) -> MonadCResult<()> {
        let mut t_attr = monad_async_task_attr {
            ..Default::default()
        };
        for n in 0..tasks {
            let task = monad_async_task_ptr::new(self.switcher, &mut t_attr)?;
            self.tasks_sleeping.push(task);
        }
        Ok(())
    }

    fn get_sleeping_task(&mut self) -> MonadCResult<monad_async_task_ptr> {
        let task: monad_async_task_ptr = match self.tasks_sleeping.pop() {
            Some(task) => task,
            None => {
                let mut t_attr = monad_async_task_attr {
                    ..Default::default()
                };
                monad_async_task_ptr::new(self.switcher, &mut t_attr)?
            }
        };
        self.tasks_inuse += 1;
        Ok(task)
    }
}

impl Drop for MonadAsyncTaskPoolInner {
    fn drop(&mut self) {
        if !self.io_initiated.empty() || !self.io_awaiting_reap.empty() {
            panic!("MonadAsyncTaskPool dropped with i/o still in flight, this should never occur");
        }
        if self.tasks_inuse > 0 {
            panic!("MonadAsyncTaskPool dropped with tasks still running, this should never occur");
        }
    }
}

#[derive(Debug, Clone)]
pub struct MonadAsyncTaskPool {
    inner: Rc<RefCell<MonadAsyncTaskPoolInner>>,
}

impl MonadAsyncTaskPool {
    fn complete_init(
        self,
        ex: monad_async_executor,
        tasks: usize,
        ios: usize,
    ) -> MonadCResult<MonadAsyncTaskPool> {
        {
            let mut this = self.clone();
            let mut inner = self.inner.borrow_mut();
            inner.dispatcher = MonadAsyncTask::new_using_internal_task(
                ex,
                inner.switcher,
                move |task: monad_async_task| this.dispatch_task_impl(task),
            )?;
            inner.launch_tasks(ex, tasks)?;
            for n in 0..ios {
                inner
                    .io_sleeping
                    .push_back(Box::pin(MonadAsyncIo::new(self.clone())));
            }
        }
        Ok(self)
    }

    // This dispatch function very closely resembles the one in AsyncIO. If unexpected
    // behaviour appears here, it might be worth comparing implementations.
    fn dispatch_task_impl(&mut self, task: monad_async_task) -> monad_c_result {
        let mut have_been_cancelled = false;
        let mut reaped_count = 0;
        loop {
            let mut completed: *mut monad_async_io_status =
                unsafe { monad_async_task_completed_io(task) };
            println!("Dispatcher task sees completed i/o {:?}", completed);
            if completed != std::ptr::null_mut() {
                let mut state = MonadAsyncIo::from_io_status(completed);
                let mut inner = self.inner.borrow_mut();
                let mut box_ = inner.io_initiated.remove_by_ref(state);
                let mut s = inner.io_awaiting_reap.push_back(box_);
                s.is_done = true;
                reaped_count += 1;
                if let Some(waker) = s.waker.take() {
                    waker.wake();
                }
            } else {
                if self.inner.borrow().io_awaiting_reap_callback.is_some() {
                    (self
                        .inner
                        .borrow_mut()
                        .io_awaiting_reap_callback
                        .as_mut()
                        .unwrap())();
                }
                if have_been_cancelled {
                    println!("Dispatcher task exits due to cancellation");
                    return success(0);
                }
                println!("Dispatcher task begins suspend for duration");
                match to_result(unsafe {
                    monad_async_task_suspend_for_duration(
                        &mut completed as *mut *mut monad_async_io_status,
                        task,
                        monad_async_duration_infinite_cancelling,
                    )
                }) {
                    Ok(_) => (),
                    Err(err) => {
                        if unsafe {
                            outcome_status_code_equal_generic(
                                &err as *const cxx_status_code_system as *const c_void,
                                125, /*ECANCELED*/
                            )
                        } != 0
                        {
                            // Clear all pending completions before we exit
                            have_been_cancelled = true;
                            continue;
                        }
                        panic!("monad_async_task_suspend_for_duration failed with {}", err);
                    }
                }
                println!("Dispatcher task ends suspend for duration");
            }
        }
    }

    fn cancel_io(&self, state: &MonadAsyncIoRef) -> MonadCResult<()> {
        panic!("cancel_io() not implemented yet");
    }

    fn reset_io(&mut self, state: Pin<&mut MonadAsyncIo>) -> MonadCResult<Pin<&mut MonadAsyncIo>> {
        while !state.is_done {
            self.run(1, None)?;
        }
        if state.buffer.index != 0 {
            let index = state.buffer.index;
            let fut = self.execute_on_task(move |task: monad_async_task| -> monad_c_result {
                unsafe { monad_async_task_release_registered_io_buffer(task, index) }
            })?;
            self.join(&[fut])?;
        }
        let mut inner = self.inner.borrow_mut();
        let mut box_ = inner.io_awaiting_reap.remove(state);
        box_.parent = None;
        Ok(inner.io_sleeping.push_back(box_))
    }

    /// \brief Create a task pool using an external executor and context switcher
    pub fn with_existing_executor(
        ex: monad_async_executor,
        switcher: monad_context_switcher,
        tasks: usize,
        ios: usize,
    ) -> MonadCResult<MonadAsyncTaskPool> {
        let mut ret = MonadAsyncTaskPoolInner {
            ex_ptr: monad_async_executor_ptr {
                ..Default::default()
            },
            switcher_ptr: monad_context_switcher_ptr {
                ..Default::default()
            },
            switcher: switcher,
            io_sleeping: LinkedList::<MonadAsyncIo>::new(),
            io_initiated: LinkedList::<MonadAsyncIo>::new(),
            io_awaiting_reap: LinkedList::<MonadAsyncIo>::new(),
            dispatcher: MonadAsyncTask::default(),
            tasks_sleeping: Vec::with_capacity(tasks),
            tasks_inuse: 0,
            io_awaiting_reap_callback: None,
        };
        MonadAsyncTaskPool {
            inner: Rc::new(RefCell::new(ret)),
        }
        .complete_init(ex, tasks, ios)
    }

    /// \brief Create a task pool using an internal executor and context switcher
    pub fn new(
        tasks: usize,
        ios: usize,
        ex_attr_: Option<monad_async_executor_attr>,
    ) -> MonadCResult<MonadAsyncTaskPool> {
        let mut ex_attr = monad_async_executor_attr {
            ..Default::default()
        };
        ex_attr.io_uring_ring.entries = 64;
        if ex_attr_.is_some() {
            ex_attr = ex_attr_.unwrap();
        }
        let ex = monad_async_executor_ptr::new(&mut ex_attr)?;
        let ex_ptr = ex.head;
        let switcher =
            monad_context_switcher_ptr::new(unsafe { &monad_context_switcher_fcontext })?;
        let switcher_ptr = switcher.head;
        let mut ret = MonadAsyncTaskPoolInner {
            ex_ptr: ex,
            switcher_ptr: switcher,
            switcher: switcher_ptr,
            io_sleeping: LinkedList::<MonadAsyncIo>::new(),
            io_initiated: LinkedList::<MonadAsyncIo>::new(),
            io_awaiting_reap: LinkedList::<MonadAsyncIo>::new(),
            dispatcher: MonadAsyncTask::default(),
            tasks_sleeping: Vec::with_capacity(tasks),
            tasks_inuse: 0,
            io_awaiting_reap_callback: None,
        };
        MonadAsyncTaskPool {
            inner: Rc::new(RefCell::new(ret)),
        }
        .complete_init(ex_ptr, tasks, ios)
    }

    /// \brief Run completions on the task pool, blocking for the timeout given
    pub fn run(&self, max_items: usize, timeout: Option<Duration>) -> MonadCResult<isize> {
        let ex = self.inner.borrow().ex_ptr.head;
        let mut timeout_: *const timespec = std::ptr::null_mut();
        let mut timeout__ = timespec {
            ..Default::default()
        };
        if let Some(ts) = timeout {
            timeout__ = timespec {
                tv_sec: ts.as_secs() as i64,
                tv_nsec: ts.subsec_nanos() as i64,
            };
            timeout_ = &timeout__ as *const timespec;
        }
        to_result(unsafe { monad_async_executor_run(ex, max_items, timeout_) })
    }

    /// \brief Run completions on the task pool, returning if max items reached or no more completions
    pub fn run_without_sleeping(&self, max_items: usize) -> MonadCResult<isize> {
        let ex = self.inner.borrow().ex_ptr.head;
        let timeout = timespec {
            tv_sec: 0,
            tv_nsec: 0,
        };
        match to_result(unsafe { monad_async_executor_run(ex, max_items, &timeout) }) {
            Ok(v) => Ok(v),
            Err(err) => {
                if unsafe {
                    outcome_status_code_equal_generic(
                        &err as *const cxx_status_code_system as *const c_void,
                        62, /*ETIME*/
                    )
                } != 0
                {
                    return Ok(0);
                }
                Err(err)
            }
        }
    }

    /// \brief Asynchronously execute the closure on a free task in the pool.
    /// Note that `MonadAsyncTask` implements `Future`, though not efficiently.
    /// It is more efficient to use `join()` and `select()` below.
    pub fn execute_on_task<T>(&mut self, func: T) -> MonadCResult<MonadAsyncTask>
    where
        T: FnOnce(monad_async_task) -> monad_c_result + 'static,
    {
        let mut inner = self.inner.borrow_mut();
        let task = inner.get_sleeping_task()?;
        let mut this = self.inner.clone();
        let ex = inner.ex_ptr.head;
        mem::drop(inner);
        Ok(MonadAsyncTask::new_using_external_task(
            ex,
            task.head,
            move |task_raw: monad_async_task| -> monad_c_result {
                unsafe { (*task_raw).io_recipient_task = task_raw };
                let ret = func(task_raw);
                let mut inner = this.borrow_mut();
                inner.tasks_sleeping.push(task);
                inner.tasks_inuse -= 1;
                ret
            },
        )?)
    }

    /// \brief More efficiently wait until all `MonadAsyncTasks` are done. Like `join!`,
    /// but you call it from non-async code.
    pub fn join(&self, tasks: &[MonadAsyncTask]) -> MonadCResult<Vec<MonadCResult<isize>>> {
        let mut states: Vec<Option<MonadCResult<isize>>> =
            tasks.into_iter().map(|_| None).collect();
        loop {
            let mut done = true;
            for n in 0..tasks.len() {
                if states[n].is_none() {
                    if let Some(res) = tasks[n].get_exit_result() {
                        states[n] = Some(to_result(res));
                    } else {
                        done = false;
                    }
                }
            }
            if done {
                return Ok(states.into_iter().map(|res| res.unwrap()).collect());
            }
            /* Sleep until something happens rather than spin */
            self.run(1, None)?;
        }
    }

    /// \brief More efficiently wait until the first `MonadAsyncTask` is done. Like `select!`,
    /// but you call it from non-async code.
    pub fn select(&self, tasks: &[MonadAsyncTask]) -> MonadCResult<(usize, MonadCResult<isize>)> {
        loop {
            for n in 0..tasks.len() {
                if let Some(res) = tasks[n].get_exit_result() {
                    return Ok((n, to_result(res)));
                }
            }
            /* Sleep until something happens rather than spin */
            self.run(1, None)?;
        }
    }

    /// \brief Initiate an i/o status based operation, signalling the returned pinned Future
    /// when the i/o completes.
    pub fn initiate_io<T>(&mut self, func: T) -> MonadCResult<MonadAsyncIoRef>
    where
        T: FnOnce(
                *mut monad_async_io_status,
                monad_async_task,
                *mut monad_async_task_registered_io_buffer,
                *mut msghdr,
            ) -> ()
            + 'static,
    {
        let mut io_box = match self.inner.borrow_mut().io_sleeping.pop() {
            Some(mut io) => {
                io.parent = Some(self.clone());
                io
            }
            None => Box::pin(MonadAsyncIo::new(self.clone())),
        };
        let dispatcher_task: monad_async_task = self.inner.borrow().dispatcher.task();
        let iostatus: *mut monad_async_io_status = io_box.as_io_status();
        let buf: *mut monad_async_task_registered_io_buffer = io_box.as_io_buffer();
        let msghdr: *mut msghdr = io_box.as_msghdr();
        self.execute_on_task(move |task: monad_async_task| -> monad_c_result {
            unsafe { (*task).io_recipient_task = dispatcher_task };
            func(iostatus, task, buf, msghdr);
            success(0)
        })?
        .detach();
        Ok(MonadAsyncIoRef {
            inner: Some(self.inner.borrow_mut().io_initiated.push_back(io_box)),
        })
    }

    /// \brief Set a callback to be invoked after i/o reaping has finished
    pub fn set_io_awaiting_reap_notify(&mut self, callback: Option<Box<dyn FnMut()>>) {
        self.inner.borrow_mut().io_awaiting_reap_callback = callback;
    }

    /// \brief Return the first item in the i/o reaping list, if any
    pub fn first_io_awaiting_reap(&self) -> Option<MonadAsyncIoRef> {
        Some(MonadAsyncIoRef {
            inner: Some(self.inner.borrow().io_awaiting_reap.front()?),
        })
    }

    /// \brief Visit all items in the i/o reaping list, starting with most recent first
    pub fn visit_io_awaiting_reap<T: FnMut(MonadAsyncIoRef) -> bool>(&self, mut func: T) {
        let mut ptr = self
            .inner
            .borrow()
            .io_awaiting_reap
            .back
            .unwrap_or(std::ptr::null_mut() as *mut MonadAsyncIo);
        loop {
            if ptr == std::ptr::null_mut() {
                break;
            }
            if !func(MonadAsyncIoRef {
                inner: Some(unsafe { Pin::new_unchecked(&mut *ptr) }),
            }) {
                return;
            }
            ptr = unsafe { &*ptr }.prev().unwrap_or(std::ptr::null_mut());
        }
    }
}

/// \brief Claim a registered write buffer and configure a msghdr to point into it
pub fn claim_registered_socket_io_write_buffer(
    task: monad_async_task,
    buffer: *mut monad_async_task_registered_io_buffer,
    msghdr: *mut msghdr,
    bytes: usize,
) -> MonadCResult<()> {
    let flags = monad_async_task_claim_registered_io_buffer_flags {
        ..Default::default()
    };
    to_result(unsafe {
        monad_async_task_claim_registered_socket_io_write_buffer(buffer, task, bytes, flags)
    })?;
    unsafe {
        *msghdr = msghdr {
            ..Default::default()
        };
        (*msghdr).msg_iov = (*buffer).iov.as_mut_ptr();
        (*msghdr).msg_iovlen = 1;
    }
    Ok(())
}

/// \brief The buffer as a mutable slide. Returns None if no buffer present yet.
pub fn buffer_as_slice_mut<'a>(
    buffer: *mut monad_async_task_registered_io_buffer,
) -> Option<&'a mut [u8]> {
    unsafe {
        if (*buffer).iov[0].iov_base == std::ptr::null_mut() {
            return None;
        }
        Some(std::slice::from_raw_parts_mut(
            (*buffer).iov[0].iov_base as *mut u8,
            (*buffer).iov[0].iov_len,
        ))
    }
}
