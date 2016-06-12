extern crate gcc;

fn main() {
    gcc::compile_library("libpicosat.a", &["src/picosat.c"]);
}