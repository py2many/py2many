//! ```cargo
//! [package]
//! edition = "2021"
//! [dependencies]
//! anyhow = "*"
//! ```

#![allow(clippy::assertions_on_constants)]
#![allow(clippy::bool_comparison)]
#![allow(clippy::collapsible_else_if)]
#![allow(clippy::comparison_to_empty)]
#![allow(clippy::double_parens)] // https://github.com/adsharma/py2many/issues/17
#![allow(clippy::eq_op)]
#![allow(clippy::let_with_type_underscore)]
#![allow(clippy::map_identity)]
#![allow(clippy::needless_return)]
#![allow(clippy::nonminimal_bool)]
#![allow(clippy::partialeq_to_none)]
#![allow(clippy::print_literal)]
#![allow(clippy::ptr_arg)]
#![allow(clippy::redundant_static_lifetimes)] // https://github.com/adsharma/py2many/issues/266
#![allow(clippy::unnecessary_cast)]
#![allow(clippy::upper_case_acronyms)]
#![allow(clippy::useless_vec)]
#![allow(non_camel_case_types)]
#![allow(non_snake_case)]
#![allow(non_upper_case_globals)]
#![allow(unused_imports)]
#![allow(unused_mut)]
#![allow(unused_parens)]

extern crate anyhow;
use anyhow::Result;

pub struct Packet {
    pub val: f64,
}

impl Packet {}
enum Register {
    PACKET(Packet),
    VALUE(i32),
}

impl Register {
    fn packet(&self) -> Option<&Packet> {
        if let Register::PACKET(val) = self {
            Some(val)
        } else {
            None
        }
    }

    fn value(&self) -> Option<&i32> {
        if let Register::VALUE(val) = self {
            Some(val)
        } else {
            None
        }
    }

    fn is_packet(&self) -> bool {
        matches!(*self, Register::PACKET(_))
    }

    fn is_value(&self) -> bool {
        matches!(*self, Register::VALUE(_))
    }
}

pub fn main() -> Result<()> {
    let a = Register::VALUE(10);
    assert!(a.is_value());
    a.value();
    let b = Register::PACKET(Packet { val: 1.3 });
    assert!(b.is_packet());
    b.packet();
    println!("{}", "OK");
    Ok(())
}
