extern crate minisat;

use std::fs::File;
use std::io::{self, BufRead};
use std::path::Path;

use festival_scheduler::Scheduler;

use utils::read_lines;

mod adjaceny_list;
mod fixed_size_stack;
mod slot_map;
mod utils;

mod festival_scheduler;
mod master_key;
mod master_key_2;
mod solver;
mod sudoku;
mod sudoku_2;

fn main() {
    let mut scheduler = Scheduler::new();
    scheduler.solve();

    let lines = if let Ok(lines) = read_lines("data/sudoku/95_hard_sudokus.txt") {
        lines
    } else {
        return;
    };
    for (i, sudoku) in lines.enumerate() {
        match sudoku {
            Ok(sudoku) => {
                let board = sudoku_2::Board::from_string(sudoku);
                println!("Sudoku: {}", i);
                println!("{}", board);

                let mut solver = sudoku_2::Solver::new(board);
                match solver.solve() {
                    Some(solution) => print!("{}", solution),
                    None => print!("Sudoku not solvable!"),
                }

                println!();
            }
            Err(e) => println!("Error reading sudoku: {}", e),
        }
    }

    let lock_sheet = master_key_2::LockSheet::load("data/mk2/lock_sheet.txt").expect("Error:");
    println!("{}", lock_sheet);
    let geometry = master_key_2::Geometry::load("data/mk2/geometry.txt").expect("Error:");
    println!("{}", geometry);
    let mut solver = master_key_2::Solver::new(geometry, lock_sheet);
    solver.solve();

    let lock_sheet = master_key_2::LockSheet::load("data/mk2/lock_sheet.txt").expect("Error:");
    println!("{}", lock_sheet);
    let geometry = master_key_2::Geometry::load("data/mk2/geometry.txt").expect("Error:");
    println!("{}", geometry);
    let mut solver = master_key_2::Solver::new(geometry, lock_sheet);
    solver.solve();

    let lock_sheet = master_key_2::LockSheet::load("data/mk1/lock_sheet.txt").expect("Error:");
    println!("{}", lock_sheet);
    let geometry = master_key_2::Geometry::load("data/mk1/geometry.txt").expect("Error:");
    println!("{}", geometry);
    let mut solver = master_key_2::Solver::new(geometry, lock_sheet);
    solver.solve();

    // let lock_sheet = master_key::LockSheet::load("data/mk1/lock_sheet.txt").expect("Error:");
    // println!("{}", lock_sheet);
    // let geometry = master_key::Geometry::load("data/mk1/geometry.txt").expect("Error:");
    // println!("{}", geometry);
    // let mut solver = master_key::Solver::new(geometry, lock_sheet);
    // solver.solve();
}
