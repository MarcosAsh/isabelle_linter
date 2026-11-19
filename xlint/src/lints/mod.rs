pub mod unused;

use crate::lint::Lint;

pub fn all() -> Vec<Box<dyn Lint>> {
    vec![Box::new(unused::Unused)]
}
