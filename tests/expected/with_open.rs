
//! ```cargo
//! [package]
//! edition = "2018"
//! [dependencies]
//! anyhow = "*"
//! pylib = "*"
//! tempfile = "*"
//! ```

#![allow(clippy::collapsible_else_if)]
#![allow(clippy::double_parens)] // https://github.com/adsharma/py2many/issues/17
#![allow(clippy::map_identity)]
#![allow(clippy::needless_return)]
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
        let temp_file: _ = NamedTempFile::new()?;
        let file_path: _ = temp_file.path();
        ({
            let mut f: _ = OpenOptions::new().write(true).open(file_path)?;
            f.write_string("hello")?;
        });
        ({
            let mut f: _ = OpenOptions::new().read(true).open(file_path)?;
            assert!(std::str::from_utf8(&f.read_bytes(1)?)? == "h");
            assert!(f.read_string()? == "ello");
            println!("{}", "OK");
        });
    });
    Ok(())
}
