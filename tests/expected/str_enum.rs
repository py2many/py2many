// cargo-deps: strum,strum_macros
use strum;
use strum_macros::EnumString;

#[derive(Debug, PartialEq, EnumString)]
enum Colors {
    RED,
    GREEN,
    #[strum(serialize = "blue")]
    BLUE,
}
