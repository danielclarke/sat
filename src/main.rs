extern crate minisat;

mod master_key;
mod master_key_2;
mod solver;
mod sudoku;
mod sudoku_2;

fn main() {
    let s = String::from(
        "52...6.........7.13...........4..8..6......5...........418.........3..2...87.....",
    );
    let b = sudoku_2::Board::from_string(s);
    println!("{}", b);

    let mut s = sudoku_2::Solver::new(b);
    if let Some(solution) = s.solve() {
        print!("{}", solution);
    }

    println!();

    let lock_sheet = master_key_2::LockSheet::load("data/mk2/lock_sheet.txt").expect("Error:");
    println!("{}", lock_sheet);
    let geometry = master_key_2::Geometry::load("data/mk2/geometry.txt").expect("Error:");
    println!("{}", geometry);
    let mut solver = master_key_2::Solver::new(geometry, lock_sheet);
    solver.solve();

    // let lock_sheet = master_key::LockSheet::load("data/mk0/lock_sheet.txt").expect("Error:");
    // println!("{}", lock_sheet);
    // let geometry = master_key::Geometry::load("data/mk0/geometry.txt").expect("Error:");
    // println!("{}", geometry);
    // let mut solver = master_key::Solver::new(geometry, lock_sheet);
    // solver.solve();
}
