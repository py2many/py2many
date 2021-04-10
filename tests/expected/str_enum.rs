// cargo-deps: strum,strum_macros
use strum;
use strum_macros::EnumString;

#[derive(Debug, PartialEq, EnumString)]
enum Colors {
    #[strum(serialize = "red")]
    RED,
    #[strum(serialize = "green")]
    GREEN,
    #[strum(serialize = "blue")]
    BLUE,
}
