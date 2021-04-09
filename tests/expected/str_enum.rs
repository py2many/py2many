use strum_macros::EnumString;

#[derive(Debug, PartialEq, EnumString)]
enum Colors {
    RED,
    GREEN,
    BLUE = "blue",
}
