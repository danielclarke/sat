use festival_scheduler::Scheduler;

use utils::read_lines;

mod adjaceny_list;
mod fixed_size_stack;
mod slot_map;
mod utils;

mod festival_scheduler;
mod master_key;
mod solver;
mod sudoku;

fn main() {
    festival_scheduler::load_venues("./_data/venues.csv");

    let mut scheduler = Scheduler::new();
    scheduler.solve();

    let lines = if let Ok(lines) = read_lines("example_data/sudoku/95_hard_sudokus.txt") {
        lines
    } else {
        return;
    };
    for (i, sudoku) in lines.enumerate() {
        match sudoku {
            Ok(sudoku) => {
                let board = sudoku::Board::from_string(sudoku);
                println!("Sudoku: {}", i);
                println!("{}", board);

                let mut solver = sudoku::Solver::new(board);
                match solver.solve() {
                    Some(solution) => print!("{}", solution),
                    None => print!("Sudoku not solvable!"),
                }

                println!();
            }
            Err(e) => println!("Error reading sudoku: {}", e),
        }
    }

    let lock_sheet =
        master_key::LockSheet::load("example_data/mk2/lock_sheet.txt").expect("Error:");
    println!("{}", lock_sheet);
    let geometry = master_key::Geometry::load("example_data/mk2/geometry.txt").expect("Error:");
    println!("{}", geometry);
    let mut solver = master_key::Solver::new(geometry, lock_sheet);
    solver.solve();

    let lock_sheet =
        master_key::LockSheet::load("example_data/mk2/lock_sheet.txt").expect("Error:");
    println!("{}", lock_sheet);
    let geometry = master_key::Geometry::load("example_data/mk2/geometry.txt").expect("Error:");
    println!("{}", geometry);
    let mut solver = master_key::Solver::new(geometry, lock_sheet);
    solver.solve();

    let lock_sheet =
        master_key::LockSheet::load("example_data/mk1/lock_sheet.txt").expect("Error:");
    println!("{}", lock_sheet);
    let geometry = master_key::Geometry::load("example_data/mk1/geometry.txt").expect("Error:");
    println!("{}", geometry);
    let mut solver = master_key::Solver::new(geometry, lock_sheet);
    solver.solve();

    // let lock_sheet = master_key::LockSheet::load("example_data/mk1/lock_sheet.txt").expect("Error:");
    // println!("{}", lock_sheet);
    // let geometry = master_key::Geometry::load("example_data/mk1/geometry.txt").expect("Error:");
    // println!("{}", geometry);
    // let mut solver = master_key::Solver::new(geometry, lock_sheet);
    // solver.solve();
}
