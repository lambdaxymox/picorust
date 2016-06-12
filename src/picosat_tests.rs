use super::picosat;

#[test]
fn test_picosat_copyright() {
    let copyright = picosat::copyright();

    assert!(true);
}

#[test]
fn test_picosat_init_reset() {
    let mut picosat = picosat::init();

    picosat::reset(&mut picosat);
}

#[test]
fn test_picosat_time_stamp() {
    let time_stamp = picosat::time_stamp();

    println!("{}", time_stamp);
}

#[test]
fn test_picosat_variables() {
    let mut picosat = picosat::init();
    let variables = picosat::variables(&picosat);

    println!("variables: {:b}", variables);

    picosat::reset(&mut picosat);
}

#[test]
fn test_picosat_added_original_clauses() {
    let mut picosat = picosat::init();
    let clauses = picosat::added_original_clauses(&picosat);

    println!("clauses: {}", clauses);

    picosat::reset(&mut picosat);
}

#[test]
fn test_picosat_max_bytes_allocated() {
    let mut picosat = picosat::init();
    let bytes = picosat::max_bytes_allocated(&picosat);

    println!("bytes: {}", bytes);

    picosat::reset(&mut picosat);
}

#[test]
fn test_picosat_seconds() {
    let mut picosat = picosat::init();
    let seconds = picosat::seconds(&picosat);
    
    picosat::reset(&mut picosat);

    println!("seconds: {}", seconds);
}