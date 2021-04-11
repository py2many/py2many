// cargo-deps: flagset
use flagset::flags;
use flagset::FlagSet;
use std::os::raw::c_int;

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
