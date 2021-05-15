
//! ```cargo
//! [package]
//! edition = "2018"
//! [dependencies]
//! pyo3 = "*"
//! ```

#![allow(clippy::upper_case_acronyms)]
#![allow(non_camel_case_types)]
#![allow(non_snake_case)]
#![allow(non_upper_case_globals)]
#![allow(unused_imports)]
#![allow(unused_mut)]
#![allow(unused_parens)]

extern crate pyo3;
use pyo3::prelude::*;
use pyo3::wrap_pyfunction;

/* This file implements a rectangle class  */

#[pyclass]
pub struct Rectangle {
    pub height: i32,
    pub length: i32,
}

#[pymethods]
impl Rectangle {
    #[pyfunction]
    pub fn is_square(&self) -> bool {
        return Ok(self.height == self.length);
    }
}

#[pymodule]
fn rect(_py: Python, m: &PyModule) -> PyResult<()> {
    Ok(())
}
