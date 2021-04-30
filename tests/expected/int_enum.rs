// cargo-deps: flagset
extern crate flagset;
use flagset::flags;
use std::collections::HashMap;
use std::os::raw::c_int;

#[derive(Clone, Eq, Hash, PartialEq)]
enum Colors {
    RED,
    GREEN,
    BLUE,
}

flags! {
    enum Permissions: c_int {
        R = 1,
        W = 2,
        X = 16,
    }
}

fn show() {
    let color_map: &HashMap<Colors, &str> = &[
        (Colors::RED, "red"),
        (Colors::GREEN, "green"),
        (Colors::BLUE, "blue"),
    ]
    .iter()
    .cloned()
    .collect::<HashMap<_, _>>();
    let a: Colors = Colors::GREEN;
    if a == Colors::GREEN {
        println!("{}", "green");
    } else {
        println!("{}", "Not green");
    }
    let b: Permissions = Permissions::R;
    if b == Permissions::R {
        println!("{}", "R");
    } else {
        println!("{}", "Not R");
    }
    assert!(color_map.len() as i32 != 0);
}

fn main() {
    show();
}
