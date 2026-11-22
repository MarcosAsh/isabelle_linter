//! Work on several files at once, with the results handed back in file order.

use std::collections::BTreeMap;
use std::sync::atomic::{AtomicUsize, Ordering};
use std::sync::mpsc;

/// Two cores stay free for the desktop.
pub fn default_jobs() -> usize {
    std::thread::available_parallelism()
        .map(|n| n.get().saturating_sub(2))
        .unwrap_or(1)
        .max(1)
}

/// `emit` gets an item's result once every earlier item's is out.
pub fn in_order<T: Sync, R: Send>(
    items: &[T],
    jobs: usize,
    work: impl Fn(usize, &T) -> R + Sync,
    mut emit: impl FnMut(usize, R),
) {
    let next = AtomicUsize::new(0);
    let (sender, receiver) = mpsc::channel();
    std::thread::scope(|scope| {
        for _ in 0..jobs.clamp(1, items.len().max(1)) {
            let sender = sender.clone();
            let (next, work) = (&next, &work);
            scope.spawn(move || {
                loop {
                    let index = next.fetch_add(1, Ordering::SeqCst);
                    let Some(item) = items.get(index) else { break };
                    if sender.send((index, work(index, item))).is_err() {
                        break;
                    }
                }
            });
        }
        drop(sender);
        let mut waiting = BTreeMap::new();
        let mut due = 0;
        for (index, result) in receiver {
            waiting.insert(index, result);
            while let Some(result) = waiting.remove(&due) {
                emit(due, result);
                due += 1;
            }
        }
    });
}
