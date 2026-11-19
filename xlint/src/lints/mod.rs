pub mod definitions;
pub mod diagnostic_commands;
pub mod faster_step;
pub mod simp_hygiene;
pub mod simp_scope;
pub mod unused;

use crate::lint::Lint;

pub fn all() -> Vec<Box<dyn Lint>> {
    vec![
        Box::new(unused::Unused),
        Box::new(unused::UnusedImports),
        Box::new(faster_step::FasterStep),
        Box::new(diagnostic_commands::DiagnosticCommands),
        Box::new(simp_hygiene::SimpHygiene),
        Box::new(simp_scope::SimpScope),
        Box::new(definitions::Definitions),
    ]
}
