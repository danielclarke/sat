use std::fmt;

use crate::solver::{self, Solution};

const ROWS: usize = 9;
const COLUMNS: usize = 9;
const VALUES: usize = 9;
const BOXES: usize = 3;

pub struct Board {
    board: Vec<Vec<Option<u32>>>,
}

impl Board {
    fn new(rows: usize, columns: usize) -> Board {
        Board {
            board: vec![vec![None; columns]; rows],
        }
    }

    pub fn from_string(s: String) -> Board {
        let mut board = vec![vec![None; COLUMNS]; ROWS];
        for (i, c) in s.chars().enumerate() {
            board[i / ROWS][i % COLUMNS] = c.to_digit(10).map(|d| d - 1);
        }
        Board { board }
    }

    pub fn is_valid(&self) -> bool {
        for i in 0..VALUES {
            for c in 0..COLUMNS {
                match &self.board[i][..].iter().find(|&&v| v == Some(c as u32)) {
                    None => return false,
                    Some(_) => (),
                }
                match &self.board[..][i].iter().find(|&&v| v == Some(c as u32)) {
                    None => return false,
                    Some(_) => (),
                }
            }
        }

        for r in (0..ROWS).step_by(BOXES) {
            for c in (0..COLUMNS).step_by(BOXES) {
                let mut values = vec![];
                for rr in 0..BOXES {
                    for cc in 0..BOXES {
                        values.push(self.board[r + rr][c + cc]);
                    }
                }
                for c in 0..VALUES {
                    match &values.iter().find(|&&v| v == Some(c as u32)) {
                        None => return false,
                        Some(_) => (),
                    }
                }
            }
        }

        true
    }
}

pub struct Solver {
    board: Board,
    formula: solver::Formula,
    vars: Vec<solver::Variable>,
}

impl Solver {
    pub fn new(board: Board) -> Solver {
        Solver {
            board,
            formula: solver::Formula::new(),
            vars: vec![],
        }
    }

    fn init_variables(&mut self) {
        for _r in 0..ROWS {
            for _c in 0..COLUMNS {
                for _v in 0..VALUES {
                    self.vars.push(self.formula.add_var());
                }
            }
        }
    }

    pub fn solve(&mut self) -> Option<Board> {
        self.init_variables();
        self.unique_rows();
        self.unique_columns();
        self.unique_boxes();
        self.one_square_one_value();
        self.apply_board();

        let mut solver = solver::Solver::new(self.formula.clone());

        match solver.solve() {
            Solution::Sat => {
                let mut board = Board::new(ROWS, COLUMNS);
                for r in 0..ROWS {
                    for c in 0..COLUMNS {
                        for v in 0..VALUES {
                            if solver.value(&self.vars[r * COLUMNS * VALUES + c * VALUES + v])
                                == solver::Value::True
                            {
                                board.board[r][c] = Some(v as u32);
                            }
                        }
                    }
                }
                assert!(board.is_valid());
                Some(board)
            }
            Solution::UnSat => None,
            Solution::Unknown => None,
        }
    }

    fn get_var(&self, row: usize, column: usize, value: usize) -> solver::Variable {
        self.vars[row * COLUMNS * VALUES + column * VALUES + value]
    }

    fn exactly_one_true(&mut self, variables: Vec<solver::Variable>) {
        for i in 0..variables.len() {
            for j in i + 1..variables.len() {
                self.formula
                    .add_clause(vec![!variables[i].literal(), !variables[j].literal()]);
            }
        }
        self.formula
            .add_clause(variables.iter().map(|v| v.literal()).collect());
    }

    pub fn apply_board(&mut self) {
        for r in 0..ROWS {
            for c in 0..COLUMNS {
                if let Some(value) = self.board.board[r][c] {
                    self.formula
                        .add_clause(vec![self.get_var(r, c, value as usize).literal()]);
                }
            }
        }
    }

    fn unique_rows(&mut self) {
        for r in 0..ROWS {
            for v in 0..VALUES {
                let variables: Vec<solver::Variable> =
                    (0..COLUMNS).map(|c| self.get_var(r, c, v)).collect();
                self.exactly_one_true(variables);
            }
        }
    }

    fn unique_columns(&mut self) {
        for c in 0..COLUMNS {
            for v in 0..VALUES {
                let variables: Vec<solver::Variable> =
                    (0..ROWS).map(|r| self.get_var(r, c, v)).collect();
                self.exactly_one_true(variables);
            }
        }
    }

    fn unique_boxes(&mut self) {
        for r in (0..ROWS).step_by(BOXES) {
            for c in (0..COLUMNS).step_by(BOXES) {
                for v in 0..VALUES {
                    let mut variables = vec![];
                    for rr in 0..BOXES {
                        for cc in 0..BOXES {
                            variables.push(self.get_var(r + rr, c + cc, v));
                        }
                    }
                    self.exactly_one_true(variables);
                }
            }
        }
    }

    fn one_square_one_value(&mut self) {
        for r in 0..ROWS {
            for c in 0..COLUMNS {
                let variables: Vec<solver::Variable> =
                    (0..VALUES).map(|v| self.get_var(r, c, v)).collect();
                self.exactly_one_true(variables);
            }
        }
    }
}

impl fmt::Display for Board {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let mut result = String::new();
        for (r, row) in self.board.iter().enumerate() {
            for (c, value) in row.iter().enumerate() {
                match value {
                    None => {
                        if c == 2 || c == 5 {
                            result += ".| ";
                        } else {
                            result += ". ";
                        }
                    }
                    Some(value) => {
                        if c == 2 || c == 5 {
                            result += &format!("{}| ", value + 1);
                        } else {
                            result += &format!("{} ", value + 1);
                        }
                    }
                }
            }
            if r == 2 || r == 5 {
                result += "\n";
                result += "-------------------";
                result += "\n";
            } else {
                result += "\n";
            }
        }

        write!(f, "{}", result)
    }
}

#[cfg(test)]
mod test_sudokus {
    use super::*;
    use crate::read_lines;
    use crate::solver::SolutionError;
    use std::error::Error;

    fn test_sudoku_n(n: usize) -> Result<(), Box<dyn Error>> {
        let mut lines = read_lines("example_data/sudoku/95_hard_sudokus.txt")?.collect::<Vec<_>>();
        let sudoku = lines.swap_remove(n)?;
        let board = Board::from_string(sudoku);
        println!("Sudoku: {}", n);
        println!("{}", board);

        let mut solver = Solver::new(board);
        match solver.solve() {
            Some(solution) => print!("{}", solution),
            None => {
                print!("Sudoku not solvable!");
                return Err(Box::new(SolutionError::UnSat));
            }
        }

        println!();
        return Ok(());
    }

    #[test]
    fn test_sudoku_0() -> Result<(), Box<dyn Error>> {
        test_sudoku_n(0)
    }

    #[test]
    fn test_sudoku_1() -> Result<(), Box<dyn Error>> {
        test_sudoku_n(1)
    }

    #[test]
    fn test_sudoku_2() -> Result<(), Box<dyn Error>> {
        test_sudoku_n(2)
    }

    #[test]
    fn test_sudoku_3() -> Result<(), Box<dyn Error>> {
        test_sudoku_n(3)
    }

    #[test]
    fn test_sudoku_4() -> Result<(), Box<dyn Error>> {
        test_sudoku_n(4)
    }

    #[test]
    fn test_sudoku_all() -> Result<(), Box<dyn Error>> {
        for i in 0..95 {
            test_sudoku_n(i)?;
        }
        Ok(())
    }
}
