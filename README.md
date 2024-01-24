[![Build][build-badge]][build-link]
[![Documentation][documentation-badge]][documentation-link]
[![crates.io-badge]][crates.io-link]

[build-badge]: https://github.com/RatCornu/efs/actions/workflows/build.yml/badge.svg?branch=master
[build-link]: https://github.com/RatCornu/efs/actions/workflows/build.yml

[documentation-badge]: https://github.com/RatCornu/efs/actions/workflows/doc.yml/badge.svg?branch=master
[documentation-link]: https://github.com/RatCornu/efs/actions/workflows/doc.yml

[crates.io-badge]: https://img.shields.io/crates/v/efs.svg
[crates.io-link]: https://crates.io/crates/efs

# Extended fs

An OS and architecture independent implementation of some Unix filesystems in Rust.

## Features

* `no_std` support (enabled by default)

* General interface for UNIX filesystems

* `read`/`write` regular files

* Read directories content

## Supported filesystems

* [`ext2`](https://en.wikipedia.org/wiki/Ext2): ✅

* [`ext4`](https://en.wikipedia.org/wiki/Ext2): ❌

* [`fatfs`](https://en.wikipedia.org/wiki/FatFs): ❌

## Usage

Add this to your `Cargo.toml`:

```
[dependencies]
efs = "0.2"
```

<!-- Add examples on 0.3 release --> 

## Features

* `ext2`: enable the `ext2` filesystem support

* `std`: enable the features depending on the standard library

By default, only the `ext2` feature is set.
