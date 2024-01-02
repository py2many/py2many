//! ```cargo
//! [package]
//! edition = "2021"
//! [dependencies]
//! anyhow = "*"
//! pylib = "*"
//! tempfile = "*"
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
extern crate pylib;
extern crate tempfile;
use anyhow::Result;
use pylib::FileReadBytes;
use pylib::FileReadString;
use pylib::FileWriteString;
use std::fs::File;
use std::fs::OpenOptions;

use tempfile::NamedTempFile;
pub fn main() -> Result<()> {
    ({
        let temp_file = NamedTempFile::new()?;
        let file_path = temp_file.path();
        ({
            let mut f = OpenOptions::new().write(true).open(file_path)?;
            f.write_string("hello")?;
        });
        ({
            let mut f = OpenOptions::new().read(true).open(file_path)?;
            assert!(std::str::from_utf8(&f.read_bytes(1)?)? == "h");
            assert!(f.read_string()? == "ello");
            println!("{}", "OK");
        });
    });
    Ok(())
}
