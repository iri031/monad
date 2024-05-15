include!{"async.rs"}

impl Drop for monad_async_executor_head {
  fn drop(&mut self) {
    unsafe { monad_async_executor_destroy(self); }
  }
}