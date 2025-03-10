use std::{
    cell::RefCell,
    future::Future,
    pin::{pin, Pin},
    rc::Rc,
    sync::{
        atomic::{AtomicUsize, Ordering},
        Arc,
    },
    task::{Context, Poll, Wake, Waker},
};

mod task_pool;
use task_pool::*;

// std::net is surprisingly useless to us :(
const AF_INET: u16 = 2;
const SOCK_STREAM: i32 = 0x1;
const SOCK_CLOEXEC: i32 = 0x80000;
const INADDR_LOOPBACK: u32 = 0x7f000001;

const fn htonl(u: u32) -> u32 {
    u.to_be()
}
const fn htons(u: u16) -> u16 {
    u.to_be()
}
const fn ntohs(u: u16) -> u16 {
    u16::from_be(u)
}

#[cfg(test)]
mod tests {
    use super::*;

    struct MyLinkedListItem {
        prev: Option<*mut MyLinkedListItem>,
        next: Option<Pin<Box<MyLinkedListItem>>>,

        value: i32,
    }

    impl LinkedListItem<MyLinkedListItem> for MyLinkedListItem {
        fn prev(&self) -> &Option<*mut MyLinkedListItem> {
            &self.prev
        }
        fn next(&self) -> &Option<Pin<Box<MyLinkedListItem>>> {
            &self.next
        }
        fn prev_mut(&mut self) -> &mut Option<*mut MyLinkedListItem> {
            &mut self.prev
        }
        fn next_mut(&mut self) -> &mut Option<Pin<Box<MyLinkedListItem>>> {
            &mut self.next
        }
    }

    #[test]
    fn test_linked_list_works() {
        let mut list = LinkedList::<MyLinkedListItem>::new();
        println!("   Pushing item 5 ...");
        let item_5a = list.push_back(Box::pin(MyLinkedListItem {
            prev: None,
            next: None,
            value: 5,
        }));
        println!("   Pushing item 6 ...");
        let item_6a = list.push_back(Box::pin(MyLinkedListItem {
            prev: None,
            next: None,
            value: 6,
        }));
        println!("   Pushing item 7 ...");
        let item_7a = list.push_back(Box::pin(MyLinkedListItem {
            prev: None,
            next: None,
            value: 7,
        }));
        println!("   Pushing item 8 ...");
        let item_8a = list.push_back(Box::pin(MyLinkedListItem {
            prev: None,
            next: None,
            value: 8,
        }));
        println!("   Removing item 6 ...");
        let item_6b = list.remove(item_6a);
        println!("   Removing item 5 ...");
        let item_5b = list.remove(item_5a);
        println!("   Removing item 8 ...");
        let item_8b = list.remove(item_8a);
        println!("   Removing item 7 ...");
        let item_7b = list.remove(item_7a);
        assert_eq!(item_6b.value, 6);
        assert_eq!(item_5b.value, 5);
        assert_eq!(item_8b.value, 8);
        assert_eq!(item_7b.value, 7);
    }

    #[test]
    fn test_task_pool_works() {
        let mut pool = MonadAsyncTaskPool::new(1, 0, None).unwrap();
        static COUNT: AtomicUsize = AtomicUsize::new(0);
        {
            // Schedule the tasks for execution
            let tasks: Vec<_> = (0..10)
                .map(|_| {
                    pool.execute_on_task(|_task: monad_async_task| -> monad_c_result {
                        let i = COUNT.fetch_add(1, Ordering::Relaxed);
                        println!("   Task {} executes!", i + 1);
                        success(0)
                    })
                    .unwrap()
                })
                .collect();
            assert_eq!(COUNT.load(Ordering::Relaxed), 0);
            // MonadAsyncTask meets Future concept, if we were within an async
            // function we could await or join!, but we are not so pump these
            // manually
            for mut task in tasks {
                loop {
                    let is_ready = pin!(&mut task)
                        .poll(&mut Context::from_waker(Waker::noop()))
                        .is_ready();
                    if is_ready {
                        break;
                    }
                }
            }
            assert_eq!(COUNT.load(Ordering::Relaxed), 10);
        }

        // Also test detached tasks
        for _ in 0..10 {
            pool.execute_on_task(|_task: monad_async_task| -> monad_c_result {
                let i = COUNT.fetch_add(1, Ordering::Relaxed);
                println!("   Detached task {} executes!", i + 1);
                success(0)
            })
            .unwrap()
            .detach();
        }
        while COUNT.load(Ordering::Relaxed) < 20 {
            pool.run(1, None).unwrap();
        }
    }

    struct MyWaker {
        count: AtomicUsize,
    }

    impl Wake for MyWaker {
        fn wake(self: Arc<Self>) {
            self.count.fetch_add(1, Ordering::Relaxed);
        }
    }

    async fn rust_async_func<T>(pool: &RefCell<MonadAsyncTaskPool>, func: T) -> monad_c_result
    where
        T: FnOnce(monad_async_task) -> monad_c_result + 'static,
    {
        println!("   Suspending Rust async func until a task pool task completes ...");
        let fut = pool.borrow_mut().execute_on_task(func).unwrap();
        let ret = fut.await;
        println!(
            "   Rust async func has been woken by completion of task pool task, which returned {}",
            ret.value
        );
        ret
    }

    #[test]
    fn test_task_pool_waker() {
        let pool = RefCell::new(MonadAsyncTaskPool::new(1, 0, None).unwrap());
        let fut = rust_async_func(&pool, |task: monad_async_task| -> monad_c_result {
            println!("      Task suspends ...");
            unsafe { monad_async_task_suspend_for_duration(std::ptr::null_mut(), task, 0) };
            println!("      Task resumes!");
            success(43)
        });
        let count = Arc::new(MyWaker { count: 0.into() });
        let waker = count.clone().into();
        let mut cx = Context::from_waker(&waker);
        let mut fut_pin = pin!(fut);
        match fut_pin.as_mut().poll(&mut cx) {
            Poll::Ready(_res) => panic!("Future should not have been ready"),
            Poll::Pending => (),
        }
        while count.count.load(Ordering::Relaxed) == 0 {
            pool.borrow().run(1, None).unwrap();
        }
        match fut_pin.as_mut().poll(&mut cx) {
            Poll::Ready(res) => assert_eq!(res.value, 43),
            Poll::Pending => panic!("Future was not ready"),
        };
    }

    #[test]
    fn test_task_pool_io_works() {
        // Create a new task pool
        let mut ex_attr = monad_async_executor_attr {
            ..Default::default()
        };
        // Ring entries
        ex_attr.io_uring_ring.entries = 64;
        // Number of registered i/o buffers
        ex_attr.io_uring_ring.registered_buffers.small_count = 4;
        // Number of kernel allocated registered i/o buffers
        ex_attr
            .io_uring_ring
            .registered_buffers
            .small_kernel_allocated_count = 1;
        // Create the task pool with this io_uring configuration
        let mut pool = MonadAsyncTaskPool::new(1, 0, Some(ex_attr)).unwrap();
        // Create some reference counted shared state to keep Rust happy about lifetimes
        struct SharedState {
            server_socket: monad_async_task_socket_ptr,
            client_socket: monad_async_task_socket_ptr,
            localhost_port: u16,
        }
        let shared: Rc<RefCell<SharedState>> = Rc::new(RefCell::new(SharedState {
            server_socket: monad_async_task_socket_ptr::default(),
            client_socket: monad_async_task_socket_ptr::default(),
            localhost_port: 0,
        }));
        // Create server and client sockets. They must be created within a task, otherwise
        // there is nothing to suspend and resume.
        {
            let server_socket_shared = shared.clone();
            let client_socket_shared = shared.clone();
            let create_sockets_tasks = [
                pool.execute_on_task(move |task: monad_async_task| -> monad_c_result {
                    // Create the socket
                    server_socket_shared.borrow_mut().server_socket =
                        monad_async_task_socket_ptr::new(
                            task,
                            AF_INET as i32,
                            SOCK_STREAM | SOCK_CLOEXEC,
                            0,
                            0,
                        )
                        .unwrap();
                    let server_socket = server_socket_shared.borrow().server_socket.head;
                    // Bind the socket to localhost
                    const LOCALHOST: sockaddr_in = sockaddr_in {
                        sin_family: AF_INET,
                        sin_port: 0, /* any */
                        sin_addr: in_addr {
                            s_addr: htonl(INADDR_LOOPBACK),
                        },
                        ..unsafe { std::mem::zeroed() }
                    };
                    to_result(unsafe {
                        monad_async_task_socket_bind(
                            server_socket,
                            &LOCALHOST as *const sockaddr_in as *const sockaddr,
                            std::mem::size_of::<sockaddr_in>() as u32,
                        )
                    })
                    .unwrap();
                    // Put the socket into a listening state
                    to_result(unsafe { monad_async_task_socket_listen(server_socket, 0) }).unwrap();
                    server_socket_shared.borrow_mut().localhost_port = unsafe {
                        ntohs(
                            (*(&(*server_socket).addr as *const sockaddr as *const sockaddr_in))
                                .sin_port,
                        )
                    };
                    println!(
                        "   Server socket listens on port {}",
                        server_socket_shared.borrow().localhost_port
                    );
                    // And finally, transfer the socket to exclusively io_uring, ending its
                    // conventional syscall based representation
                    to_result(unsafe {
                        monad_async_task_socket_transfer_to_uring(task, server_socket)
                    })
                    .unwrap();
                    success(0)
                })
                .unwrap(),
                pool.execute_on_task(move |task: monad_async_task| -> monad_c_result {
                    // Create the socket
                    client_socket_shared.borrow_mut().client_socket =
                        monad_async_task_socket_ptr::new(
                            task,
                            AF_INET as i32,
                            SOCK_STREAM | SOCK_CLOEXEC,
                            0,
                            0,
                        )
                        .unwrap();
                    // Transfer the socket to exclusively io_uring, ending its
                    // conventional syscall based representation
                    to_result(unsafe {
                        monad_async_task_socket_transfer_to_uring(
                            task,
                            client_socket_shared.borrow().client_socket.head,
                        )
                    })
                    .unwrap();
                    success(0)
                })
                .unwrap(),
            ];
            // Efficiently wait until all tasks exit. MonadAsyncTask is also a Rust Future,
            // so it can be waited upon directly from within a Rust async function. This
            // function is for non-async code to efficiently wait for MonadAsyncTasks to complete.
            pool.join(&create_sockets_tasks).unwrap();
        }
        // Connect the client socket to the server socket, and have the server socket accept
        // that connection and close the listening socket
        {
            let server_socket_shared = shared.clone();
            let client_socket_shared = shared.clone();
            let connect_sockets_tasks = [
                pool.execute_on_task(move |task: monad_async_task| -> monad_c_result {
                    let server_socket = server_socket_shared.borrow().server_socket.head;
                    // Accept new connections, suspending until a new one appears
                    let mut conn: monad_async_socket = std::ptr::null_mut();
                    to_result(unsafe {
                        monad_async_task_socket_accept(
                            &mut conn as *mut monad_async_socket,
                            task,
                            server_socket,
                            0,
                        )
                    })
                    .unwrap();
                    // Swap the server sockets, and close the listening one
                    let listening_socket = server_socket_shared.borrow().server_socket.head;
                    server_socket_shared.borrow_mut().server_socket.head = conn;
                    to_result(unsafe { monad_async_task_socket_destroy(task, listening_socket) })
                        .unwrap();
                    let peer: *const sockaddr_in =
                        unsafe { &(*conn).addr as *const sockaddr as *const sockaddr_in };
                    println!(
                        "   Server accepts new connection from {:#x}:{}",
                        unsafe { (*peer).sin_addr.s_addr },
                        unsafe { (*peer).sin_port }
                    );
                    success(0)
                })
                .unwrap(),
                pool.execute_on_task(move |task: monad_async_task| -> monad_c_result {
                    let client_socket = client_socket_shared.borrow().client_socket.head;
                    // Initiate connecting to the socket. This doesn't suspend-resume and
                    // cannot fail as it doesn't do anything yet.
                    let mut iostatus = monad_async_io_status {
                        ..Default::default()
                    };
                    let addr = sockaddr_in {
                        sin_family: AF_INET,
                        sin_port: htons(client_socket_shared.borrow().localhost_port),
                        sin_addr: in_addr {
                            s_addr: htonl(INADDR_LOOPBACK),
                        },
                        ..unsafe { std::mem::zeroed() }
                    };
                    unsafe {
                        monad_async_task_socket_connect(
                            &mut iostatus as *mut monad_async_io_status,
                            task,
                            client_socket,
                            &addr as *const sockaddr_in as *const sockaddr,
                            std::mem::size_of::<sockaddr_in>() as u32,
                        )
                    }
                    // Having initiated the socket connect, now suspend until it completes.
                    let mut completed: *mut monad_async_io_status = std::ptr::null_mut();
                    to_result(unsafe {
                        monad_async_task_suspend_until_completed_io(
                            &mut completed as *mut *mut monad_async_io_status,
                            task,
                            monad_async_duration_infinite_cancelling,
                        )
                    })
                    .unwrap();
                    if completed != &mut iostatus {
                        panic!("Completed did not equal the i/o initiated");
                    }
                    println!("   Client has connected!");
                    success(0)
                })
                .unwrap(),
            ];
            pool.join(&connect_sockets_tasks).unwrap();
        }
        // Test the pool's i/o functions
        {
            let client_socket_shared = shared.clone();
            // Initiate a read of the client socket. MonadAsyncIo is also a Rust Future
            // and if we were in Rust async, we could await it.
            let readfut = pool
                .initiate_io(
                    move |iostatus: *mut monad_async_io_status,
                          task: monad_async_task,
                          buffer: *mut monad_async_task_registered_io_buffer,
                          _msghdr: *mut msghdr| {
                        let client_socket = client_socket_shared.borrow().client_socket.head;
                        unsafe {
                            // io_uring allocates the buffer for socket receive
                            println!("   Initiate socket receive ...");
                            monad_async_task_socket_receive(
                                iostatus,
                                task,
                                client_socket,
                                buffer,
                                1024,
                                0,
                            )
                        };
                    },
                )
                .unwrap();
            assert_eq!(readfut.is_in_progress(), false);
            assert_eq!(readfut.is_done(), false);
            pool.run_without_sleeping(100).unwrap();
            assert_eq!(readfut.is_in_progress(), true);
            assert_eq!(readfut.is_done(), false);

            let server_socket_shared = shared.clone();
            // Initiate a write of the server socket.
            let writefut = pool
                .initiate_io(
                    move |iostatus: *mut monad_async_io_status,
                          task: monad_async_task,
                          buffer: *mut monad_async_task_registered_io_buffer,
                          msghdr: *mut msghdr| {
                        let server_socket = server_socket_shared.borrow().server_socket.head;
                        unsafe {
                            // We must allocate the buffer for socket send
                            println!("   Claim a registered i/o buffer for the write ...");
                            claim_registered_socket_io_write_buffer(task, buffer, msghdr, 1024)
                                .unwrap();
                            // Say what we shall send
                            let outbuf = buffer_as_slice_mut(buffer).unwrap();
                            outbuf[0..11].copy_from_slice(b"hello world");
                            (*buffer).iov[0].iov_len = 11;
                            // Initiate the send
                            println!("   Initiate socket send of {:?} ...", &outbuf[0..11]);
                            monad_async_task_socket_send(
                                iostatus,
                                task,
                                server_socket,
                                (*buffer).index,
                                msghdr,
                                0,
                            )
                            // WARNING: The buffer you send MUST outlive this closure.
                            // By using a registered buffer, we are safe here -- if you used
                            // a stack allocated buffer, you would not be safe.
                        };
                    },
                )
                .unwrap();
            assert_eq!(writefut.is_in_progress(), false);
            assert_eq!(writefut.is_done(), false);

            // The socket write should cause both i/o to become done
            while !writefut.is_done() || !readfut.is_done() {
                pool.run_without_sleeping(1).unwrap();
            }
            assert_eq!(writefut.is_in_progress(), false);
            assert_eq!(writefut.is_done(), true);
            assert_eq!(readfut.is_done(), true);

            // The write operation can be recycled now. Rust consumes writefut,
            // after this it is dead. If you forget to do this (a) this i/o state can't
            // be used for other i/o, wasting resources (b) if it is dropped before it
            // is reset, panic is called.
            writefut.reset().unwrap();

            // Make sure buffer read has the right contents
            match to_result(readfut.result().unwrap()) {
                Ok(bytes_read) => assert_eq!(bytes_read, 11),
                Err(err) => panic!("{}", err),
            }
            let data = readfut.result_as_slice().unwrap();
            println!("   Client socket receives {:?}", data);
            assert_eq!(data, b"hello world");

            // Release readfut
            readfut.reset().unwrap();
        }
        // Destroy server and client sockets, which also must be done within a task
        {
            let destroy_sockets_tasks = [pool
                .execute_on_task(move |task: monad_async_task| -> monad_c_result {
                    // shared was moved into this closure, and no longer exists outside it
                    // Reset task to current task before drop
                    shared.borrow_mut().server_socket.task = task;
                    shared.borrow_mut().client_socket.task = task;
                    // This will be the last copy, so this will destroy the sockets
                    drop(shared);
                    success(0)
                })
                .unwrap()];
            pool.join(&destroy_sockets_tasks).unwrap();
        }
    }
}
