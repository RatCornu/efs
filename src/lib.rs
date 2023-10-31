//! Extended fs
//!
//! An OS and architecture independent implementation of some Unix filesystems in Rust.

#![cfg_attr(all(not(test), feature = "no_std"), no_std)]
#![deny(
    clippy::complexity,
    clippy::correctness,
    clippy::nursery,
    clippy::pedantic,
    clippy::perf,
    clippy::restriction,
    clippy::style,
    missing_docs
)]
#![allow(
    clippy::absolute_paths,
    clippy::arithmetic_side_effects,
    clippy::as_conversions,
    clippy::blanket_clippy_restriction_lints,
    clippy::else_if_without_else,
    clippy::exhaustive_enums,
    clippy::exhaustive_structs,
    clippy::expect_used,
    clippy::implicit_return,
    clippy::integer_division,
    clippy::match_same_arms,
    clippy::match_wildcard_for_single_variants,
    clippy::missing_trait_methods,
    clippy::mod_module_files,
    clippy::panic,
    clippy::panic_in_result_fn,
    clippy::pattern_type_mismatch,
    clippy::question_mark_used,
    clippy::separated_literal_suffix,
    clippy::shadow_reuse,
    clippy::shadow_unrelated,
    clippy::todo,
    clippy::unreachable,
    clippy::use_debug,
    clippy::unwrap_in_result,
    clippy::wildcard_in_or_patterns,
    const_item_mutation
)]
#![cfg_attr(
    test,
    allow(
        clippy::assertions_on_result_states,
        clippy::collection_is_never_read,
        clippy::enum_glob_use,
        clippy::indexing_slicing,
        clippy::non_ascii_literal,
        clippy::too_many_lines,
        clippy::unwrap_used,
        clippy::wildcard_imports
    )
)]
#![feature(const_mut_refs)]
#![feature(error_in_core)]
#![feature(iter_advance_by)]
#![feature(let_chains)]
#![feature(step_trait)]
#![feature(trait_upcasting)]

extern crate alloc;
extern crate core;
#[cfg(not(no_std))]
extern crate std;

pub mod error;
pub mod file;
pub mod fs;
pub mod path;
pub mod types;

pub mod dev;

pub mod ext2;
