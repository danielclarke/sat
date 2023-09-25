extern crate minisat;

use std::fmt;

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
            board[i / ROWS][i % COLUMNS] = c.to_digit(10);
        }
        Board { board }
    }
}

pub struct Solver {
    board: Board,
    solver: minisat::Solver,
    vars: Vec<minisat::Bool>,
}

impl Solver {
    pub fn new(board: Board) -> Solver {
        Solver {
            board,
            solver: minisat::Solver::new(),
            vars: vec![],
        }
    }

    fn init_variables(&mut self) {
        for _r in 0..ROWS {
            for _c in 0..COLUMNS {
                for _v in 0..VALUES {
                    self.vars.push(self.solver.new_lit());
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

        if let Ok(solution) = self.solver.solve() {
            let mut board = Board::new(ROWS, COLUMNS);
            for r in 0..ROWS {
                for c in 0..COLUMNS {
                    for v in 0..VALUES {
                        if solution.value(&self.vars[r * COLUMNS * VALUES + c * VALUES + v]) {
                            board.board[r][c] = Some(v as u32);
                        }
                    }
                }
            }

            Some(board)
        } else {
            None
        }
    }

    fn get_var(&self, row: usize, column: usize, value: usize) -> minisat::Bool {
        self.vars[row * COLUMNS * VALUES + column * VALUES + value]
    }

    fn exactly_one_true(&mut self, literals: Vec<minisat::Bool>) {
        for i in 0..literals.len() {
            for j in i + 1..literals.len() {
                self.solver.add_clause(vec![!literals[i], !literals[j]]);
            }
        }
        self.solver.add_clause(literals);
    }

    pub fn apply_board(&mut self) {
        for r in 0..ROWS {
            for c in 0..COLUMNS {
                if let Some(value) = self.board.board[r][c] {
                    self.solver
                        .add_clause(vec![self.get_var(r, c, value as usize)]);
                }
            }
        }
    }

    fn unique_rows(&mut self) {
        for r in 0..ROWS {
            for v in 0..VALUES {
                let literals: Vec<minisat::Bool> =
                    (0..COLUMNS).map(|c| self.get_var(r, c, v)).collect();
                self.exactly_one_true(literals);
            }
        }
    }

    fn unique_columns(&mut self) {
        for c in 0..COLUMNS {
            for v in 0..VALUES {
                let literals: Vec<minisat::Bool> =
                    (0..ROWS).map(|r| self.get_var(r, c, v)).collect();
                self.exactly_one_true(literals);
            }
        }
    }

    fn unique_boxes(&mut self) {
        for r in (0..ROWS).step_by(BOXES) {
            for c in (0..COLUMNS).step_by(BOXES) {
                for v in 0..VALUES {
                    let mut literals = vec![];
                    for rr in 0..BOXES {
                        for cc in 0..BOXES {
                            literals.push(self.get_var(r + rr, c + cc, v));
                        }
                    }
                    self.exactly_one_true(literals);
                }
            }
        }
    }

    fn one_square_one_value(&mut self) {
        for r in 0..ROWS {
            for c in 0..COLUMNS {
                let literals: Vec<minisat::Bool> =
                    (0..VALUES).map(|v| self.get_var(r, c, v)).collect();
                self.exactly_one_true(literals);
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
