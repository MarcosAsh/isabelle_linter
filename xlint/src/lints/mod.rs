pub mod diagnostic_commands;
pub mod faster_step;
pub mod unused;

use crate::lint::Lint;

pub fn all() -> Vec<Box<dyn Lint>> {
    vec![
        Box::new(unused::Unused),
        Box::new(faster_step::FasterStep),
        Box::new(diagnostic_commands::DiagnosticCommands),
    ]
}
