//! Compile-time registry geometry shared with the host capacity regression.
//! All firmware configurations use this bound for the resident compact image.
pub const CAPACITY: usize = 63;

/// Physical header preceding object payloads in the current flash format.
pub const OBJECT_BLOCK_HEADER_LEN: usize = 32;
