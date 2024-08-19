#![allow(unexpected_cfgs)]

#[cfg(not(all(target_os = "zkvm", target_vendor = "succinct")))]
mod arithmetic;

#[cfg(not(all(target_os = "zkvm", target_vendor = "succinct")))]
mod fr;
#[cfg(all(target_os = "zkvm", target_vendor = "succinct"))]
mod fr_sp1;

#[cfg(feature = "asm")]
mod assembly;

#[macro_use]
mod derive;

pub mod serde;

// Re-export ff and group to simplify down stream dependencies
#[cfg(feature = "reexport")]
pub use ff;
#[cfg(not(feature = "reexport"))]
use ff;

#[cfg(not(all(target_os = "zkvm", target_vendor = "succinct")))]
pub use fr::Fr;
#[cfg(all(target_os = "zkvm", target_vendor = "succinct"))]
pub use fr_sp1::Fr;