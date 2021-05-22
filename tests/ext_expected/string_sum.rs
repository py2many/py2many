
//! ```cargo
//! [package]
//! edition = "2018"
//! [dependencies]
//! pyo3 = "*"
//! ```

#![allow(clippy::redundant_static_lifetimes)]
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

#[pyfunction]
pub fn sum_as_string(a: i8, b: i8) -> PyResult<String> {
    return Ok(((a as i16) + (b as i16)).to_string());
}

#[pyfunction]
pub fn add_key(d: &PyDict) -> PyResult<()> {
    d[1] = 2;
    return Ok(());
}

#[pymodule]
fn string_sum(_py: Python, m: &PyModule) -> PyResult<()> {
    m.add_function(wrap_pyfunction!(sum_as_string, m)?)?;
    m.add_function(wrap_pyfunction!(add_key, m)?)?;

    Ok(())
}
