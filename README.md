# alfred-json

## Introduction

Heavily inspired by [lilyball/alfred-rs](https://github.com/lilyball/alfred-rs), this crate defines helpers for writing script filters and JSON configs of [Alfred](https://www.alfredapp.com/)(>=5).

## Example usage

```rust
use alfred_json::scriptfilter::{ItemBuilder, ScriptFilterOutputBuilder, IntoJson};
fn main() {
    let output = ScriptFilterOutputBuilder::from_items([
        ItemBuilder::new("Item 1").subtitle("subtitle").into_item(),
        ItemBuilder::new("Item 2").valid(false).into_item(),
    ]).into_output();
    print!("{}", output.into_json());
}
```
