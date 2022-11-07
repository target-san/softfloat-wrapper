# softfloat-wrapper
softfloat-wrapper is a safe wrapper of [Berkeley SoftFloat](https://github.com/ucb-bar/berkeley-softfloat-3) based on [softfloat-sys](https://crates.io/crates/softfloat-sys).

[![Actions Status](https://github.com/dalance/softfloat-wrapper/workflows/Regression/badge.svg)](https://github.com/dalance/softfloat-wrapper/actions)
[![Crates.io](https://img.shields.io/crates/v/softfloat-wrapper.svg)](https://crates.io/crates/softfloat-wrapper)
[![Docs.rs](https://docs.rs/softfloat-wrapper/badge.svg)](https://docs.rs/softfloat-wrapper)

# Requirements

* Rust 1.64 - `core::ffi` types in stable
* `rustfmt` - used by `bindgen` to format bindings
* `clang` and `libclang` - used by `bindgen` to generate some bindings

## Usage

```Cargo.toml
[dependencies.softfloat-wrapper]
git = "https://github.com/tacanslabs/softfloat-sys.git"
```

## Example

```rust
use softfloat_wrapper::{Float, F16, RoundingMode};

fn main() {
    let a = 0x1234;
    let b = 0x1479;

    let a = F16::from_bits(a);
    let b = F16::from_bits(b);
    let d = a.add(b, RoundingMode::TiesToEven);

    let a = f32::from_bits(a.to_f32(RoundingMode::TiesToEven).to_bits());
    let b = f32::from_bits(b.to_f32(RoundingMode::TiesToEven).to_bits());
    let d = f32::from_bits(d.to_f32(RoundingMode::TiesToEven).to_bits());

    println!("{} + {} = {}", a, b, d);
}
```

## Features

Compared to 0.3.x, architecture specializations are chosen through target triple.
Architectures properly supported ATM:

* Linux x86-64
* Wasm32

Actual feature gates:

* `concordium` - Tweaks to make softfloat usable with `concordium` blockchain, where hardware floats are not supported. Disables conversions from and to platform float types (VM doesn't even have instructions for such values)
and `F128` type. The latter is disabled due to ABI issues when building for `Wasm32`.
Also implements traits `Serial` and `Deserial` for concordium-std.

## License

Licensed under either of

 * Apache License, Version 2.0, ([LICENSE-APACHE](LICENSE-APACHE) or http://www.apache.org/licenses/LICENSE-2.0)
 * MIT license ([LICENSE-MIT](LICENSE-MIT) or http://opensource.org/licenses/MIT)

at your option.

### Contribution

Unless you explicitly state otherwise, any contribution intentionally
submitted for inclusion in the work by you, as defined in the Apache-2.0
license, shall be dual licensed as above, without any additional terms or
conditions.
