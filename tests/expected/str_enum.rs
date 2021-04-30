// cargo-deps: strum,strum_macros
extern crate strum;
extern crate strum_macros;
use std::collections::HashMap;
use strum_macros::EnumString;

#[derive(Clone, Debug, Eq, Hash, PartialEq, EnumString)]
enum Colors {
    #[strum(serialize = "red")]
    RED,
    #[strum(serialize = "green")]
    GREEN,
    #[strum(serialize = "blue")]
    BLUE,
}

fn show() {
    let color_map: &HashMap<Colors, &str> = &[
        (Colors::RED, "1"),
        (Colors::GREEN, "2"),
        (Colors::BLUE, "3"),
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
    println!("{}", color_map.len());
}

fn main() {
    show();
}
