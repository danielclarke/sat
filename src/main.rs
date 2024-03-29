extern crate minisat;

use festival_scheduler::Scheduler;

use utils::read_lines;

mod adjaceny_list;
mod fixed_size_stack;
mod master_key_ms;
mod slot_map;
mod utils;

mod festival_scheduler;
mod master_key;
mod solver;
mod sudoku;

fn main() {
    // let venues =
    //     festival_scheduler::load_venues("./data/venues.csv").expect("error reading venues");
    // let events =
    //     festival_scheduler::load_events("./data/sessions.csv").expect("error reading events");
    // let artists =
    //     festival_scheduler::load_artists("./data/sessions.csv").expect("error reading artists");

    // let mut scheduler = Scheduler::new(0, 4, artists, venues, events[0..10].to_vec());
    // scheduler.solve();

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
        master_key_ms::LockSheet::load("example_data/mk2/lock_sheet.txt").expect("Error:");
    println!("{}", lock_sheet);
    let geometry = master_key_ms::Geometry::load("example_data/mk2/geometry.txt").expect("Error:");
    println!("{}", geometry);
    let mut solver = master_key_ms::Solver::new(geometry, lock_sheet);
    solver.solve();

    let lock_sheet =
        master_key::LockSheet::load("example_data/mk2/lock_sheet.txt").expect("Error:");
    println!("{}", lock_sheet);
    let geometry = master_key::Geometry::load("example_data/mk2/geometry.txt").expect("Error:");
    println!("{}", geometry);
    let mut solver = master_key::Solver::new(geometry, lock_sheet);
    solver.solve();

    let lock_sheet =
        master_key_ms::LockSheet::load("example_data/mk1/lock_sheet.txt").expect("Error:");
    println!("{}", lock_sheet);
    let geometry = master_key_ms::Geometry::load("example_data/mk1/geometry.txt").expect("Error:");
    println!("{}", geometry);
    let mut solver = master_key_ms::Solver::new(geometry, lock_sheet);
    solver.solve();

    let lock_sheet =
        master_key::LockSheet::load("example_data/mk1/lock_sheet.txt").expect("Error:");
    println!("{}", lock_sheet);
    let geometry = master_key::Geometry::load("example_data/mk1/geometry.txt").expect("Error:");
    println!("{}", geometry);
    let mut solver = master_key::Solver::new(geometry, lock_sheet);
    solver.solve();
}
