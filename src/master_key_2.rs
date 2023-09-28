use std::collections::HashMap;
use std::error;
use std::fmt;
use std::fs::File;
use std::io::{self, BufRead};
use std::path::Path;

use crate::solver::{self, Solution, Value, Variable};

#[derive(Debug, Clone)]
enum DataError {
    MissingHeader,
    IncorrectHeaderFormat,
    IncorrectGeometryFormat,
    IncorrectLockSheetFormat,
}

impl fmt::Display for DataError {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match *self {
            DataError::MissingHeader => write!(f, "Missing header in geometry file"),
            DataError::IncorrectHeaderFormat => write!(
                f,
                "Incorrect format for header in geometry file. Expected e.g. base: 3,6"
            ),
            DataError::IncorrectGeometryFormat => write!(
                f,
                "Incorrect format in geometry file. Expected e.g. G: 1, *, 2"
            ),
            DataError::IncorrectLockSheetFormat => {
                write!(f, "LockSheet contains unexpected charcter. Expected * or .")
            }
        }
    }
}

impl error::Error for DataError {}

type Indices = (usize, usize, usize);

fn read_lines<P>(filename: P) -> io::Result<io::Lines<io::BufReader<File>>>
where
    P: AsRef<Path>,
{
    let file = File::open(filename)?;
    Ok(io::BufReader::new(file).lines())
}

pub struct LockSheet {
    locks: Vec<Vec<bool>>,
    num_locks: usize,
    num_keys: usize,
}

impl LockSheet {
    pub fn load<P>(filename: P) -> Result<LockSheet, Box<dyn error::Error>>
    where
        P: AsRef<Path>,
    {
        let mut locks = vec![];
        let lines = read_lines(filename)?;
        for lock in lines {
            let mut unlocks = vec![];
            match lock {
                Ok(lock) => {
                    for key in lock.chars() {
                        match key {
                            '*' => {
                                unlocks.push(true);
                            }
                            '.' => {
                                unlocks.push(false);
                            }
                            _ => return Err(Box::new(DataError::IncorrectLockSheetFormat)),
                        }
                    }
                }
                Err(e) => return Err(Box::new(e)),
            }
            locks.push(unlocks);
        }

        Ok(LockSheet {
            num_locks: locks.len(),
            num_keys: locks[0].len(),
            locks,
        })
    }
}

impl fmt::Display for LockSheet {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let mut result = String::new();

        for lock in &self.locks {
            for &key in lock {
                if key {
                    result += "*";
                } else {
                    result += ".";
                }
            }
            result += "\n";
        }

        write!(f, "{}", result)
    }
}

pub struct Geometry {
    positions: usize,
    depths: usize,
    gecodes: Vec<Vec<Option<usize>>>,
}

impl Geometry {
    pub fn load<P>(filename: P) -> Result<Geometry, Box<dyn error::Error>>
    where
        P: AsRef<Path>,
    {
        let mut lines = read_lines(filename)?;
        let mut geometry = match lines.next() {
            Some(header) => match header {
                Ok(header) => {
                    if let &[positions, depths] = &header
                        .strip_prefix("base: ")
                        .ok_or(Box::new(DataError::MissingHeader))?
                        .split(',')
                        .map(|s| s.parse::<usize>())
                        .collect::<Result<Vec<_>, _>>()?[..]
                    {
                        Geometry {
                            positions,
                            depths,
                            gecodes: vec![],
                        }
                    } else {
                        return Err(Box::new(DataError::IncorrectHeaderFormat));
                    }
                }
                Err(e) => return Err(Box::new(e)),
            },
            None => return Err(Box::new(DataError::MissingHeader)),
        };
        for line in lines {
            match line {
                Ok(line) => {
                    let codes = line
                        .strip_prefix("G: ")
                        .ok_or(Box::new(DataError::IncorrectGeometryFormat))?
                        .split(", ")
                        .map(|s| {
                            if s == "*" {
                                Ok(None)
                            } else {
                                match s.parse::<usize>() {
                                    Ok(v) => Ok(Some(v)),
                                    Err(e) => Err(Box::new(e)),
                                }
                            }
                        })
                        .collect::<Result<Vec<_>, _>>()?;
                    geometry.gecodes.push(codes);
                }
                Err(e) => return Err(Box::new(e)),
            }
        }
        Ok(geometry)
    }
}

impl fmt::Display for Geometry {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let mut result = String::new();

        result += &format!("base: {},{}\n", self.positions, self.depths);
        for gecodes in &self.gecodes {
            result += "G: ";
            for g in gecodes {
                match g {
                    Some(g) => result += &format!("{}, ", g),
                    None => result += "*, ",
                }
            }
            result += "\n";
        }

        write!(f, "{}", result)
    }
}

pub struct Solver {
    key_vars: HashMap<Indices, Variable>,
    lock_vars: HashMap<Indices, Variable>,
    geometry: Geometry,
    lock_sheet: LockSheet,
    solver: solver::Solver,
}

impl Solver {
    pub fn new(geometry: Geometry, lock_sheet: LockSheet) -> Solver {
        Solver {
            key_vars: HashMap::new(),
            lock_vars: HashMap::new(),
            geometry,
            lock_sheet,
            solver: solver::Solver::new(),
        }
    }

    pub fn solve(&mut self) {
        for lock in 0..self.lock_sheet.num_locks {
            self.add_lock(lock);
        }

        for key in 0..self.lock_sheet.num_keys {
            self.add_key(key);
            self.add_unlock_constraints(key);
            self.add_block_constraints(key);
            self.add_gecodes(key);
        }

        match self.solver.solve() {
            Solution::Sat => {
                println!("SOLVED!");

                for key in 0..self.lock_sheet.num_keys {
                    println!("Key  {}: ", key);
                    for depth in 0..self.geometry.depths {
                        for position in 0..self.geometry.positions {
                            let indices = (position, depth, key);
                            let key_lit = self.key_vars[&indices];
                            match self.solver.value(&key_lit) {
                                Value::True => print!("{} ", depth),
                                Value::Unknown => print!("x "),
                                Value::False => print!(". "),
                            }
                        }
                        println!();
                    }
                    println!();
                }

                for lock in 0..self.lock_sheet.num_locks {
                    println!("Lock {}: ", lock);
                    for depth in 0..self.geometry.depths {
                        for position in 0..self.geometry.positions {
                            let indices = (position, depth, lock);
                            let lock_lit = self.lock_vars[&indices];
                            if self.solver.value(&lock_lit) == Value::True {
                                print!("{} ", depth);
                            } else {
                                print!(". ");
                            }
                        }
                        println!();
                    }
                    println!();
                }
            }
            Solution::UnSat => {
                println!("UNSAT");
            }
            Solution::Unknown => {
                println!("UNSAT");
            }
        }
    }

    fn exactly_one(&mut self, variables: Vec<Variable>) {
        for i in 0..variables.len() {
            for j in i + 1..variables.len() {
                self.solver
                    .add_clause(vec![!variables[i].literal(), !variables[j].literal()]);
            }
        }
        self.solver
            .add_clause(variables.iter().map(|v| v.literal()).collect());
    }

    fn add_key_var(&mut self, position: usize, depth: usize, key: usize) -> Variable {
        let indices = (position, depth, key);
        *self
            .key_vars
            .entry(indices)
            .or_insert(self.solver.add_var())
    }

    fn add_lock_var(&mut self, position: usize, depth: usize, lock: usize) -> Variable {
        let indices = (position, depth, lock);
        *self
            .lock_vars
            .entry(indices)
            .or_insert(self.solver.add_var())
    }

    fn key_var(&self, position: usize, depth: usize, key: usize) -> Variable {
        let indices = (position, depth, key);
        self.key_vars[&indices]
    }

    fn lock_var(&self, position: usize, depth: usize, lock: usize) -> Variable {
        let indices = (position, depth, lock);
        self.lock_vars[&indices]
    }

    fn add_lock(&mut self, lock: usize) {
        for position in 0..self.geometry.positions {
            let mut variables = vec![];
            for depth in 0..self.geometry.depths {
                variables.push(self.add_lock_var(position, depth, lock));
            }
            self.solver
                .add_clause(variables.iter().map(|v| v.literal()).collect());
        }
    }

    fn add_key(&mut self, key: usize) {
        for position in 0..self.geometry.positions {
            let mut variables = vec![];
            for depth in 0..self.geometry.depths {
                variables.push(self.add_key_var(position, depth, key));
            }
            self.exactly_one(variables);
        }
    }

    fn add_unlock_constraints(&mut self, key: usize) {
        for (lock, lock_line) in self.lock_sheet.locks.iter().enumerate() {
            if lock_line[key] {
                for position in 0..self.geometry.positions {
                    for depth in 0..self.geometry.depths {
                        let key_lit = self.key_var(position, depth, key);
                        let lock_lit = self.lock_var(position, depth, lock);
                        self.solver
                            .add_clause(vec![!key_lit.literal(), lock_lit.literal()]);
                    }
                }
            }
        }
    }

    fn add_block_constraints(&mut self, key: usize) {
        for (lock, lock_line) in self.lock_sheet.locks.iter().enumerate() {
            if !lock_line[key] {
                let mut blocking_variables = vec![];

                for position in 0..self.geometry.positions {
                    for depth in 0..self.geometry.depths {
                        let block_variable = self.solver.add_var();
                        let key_variable = self.key_var(position, depth, key);
                        let lock_variable = self.lock_var(position, depth, lock);

                        // block_{p, d} <=> (key_{p, d} && ~lock_{p, d})
                        // 1)   block_{p, d}  => (key_{p, d} && ~lock_{p, d})
                        //     ~block_{p, d}  v  (key_{p, d} && ~lock_{p, d})
                        //    (~block_{p, d} v key_{p, d}) && (~block_{p, d} v ~lock_{p, d})
                        self.solver
                            .add_clause(vec![!block_variable.literal(), key_variable.literal()]);
                        self.solver
                            .add_clause(vec![!block_variable.literal(), !lock_variable.literal()]);

                        // 2)   (key_{p, d} && ~lock_{p, d}) => block_{p, d}
                        //     ~(key_{p, d} && ~lock_{p, d}) v  block_{p, d}
                        //     (~key_{p, d} v   lock_{p, d}) v  block_{p, d}
                        //      ~key_{p, d} v   lock_{p, d}  v block_{p, d}
                        self.solver.add_clause(vec![
                            block_variable.literal(),
                            !key_variable.literal(),
                            lock_variable.literal(),
                        ]);

                        blocking_variables.push(block_variable);
                    }
                }
                self.solver
                    .add_clause(blocking_variables.iter().map(|v| v.literal()).collect());
            }
        }
    }

    fn add_gecodes(&mut self, key: usize) {
        for gecode in &self.geometry.gecodes {
            let mut literals = vec![];
            for (position, &depth) in gecode.iter().enumerate() {
                if let Some(depth) = depth {
                    let key_variable = self.key_var(position, depth, key);
                    literals.push(!key_variable.literal());
                }
            }
            self.solver.add_clause(literals);
        }
    }
}
