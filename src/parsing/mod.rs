// parser for the Technique language
use std::path::Path;

pub mod parser;

pub fn load(source: &Path) {
    // read source to a str
    let content = std::fs::read_to_string(source).expect("Failed to read the source file");

    parser::parse_via_pest(content.as_str());
}