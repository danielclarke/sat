use std::collections::HashMap;
use std::error;
use std::fmt;
use std::path::Path;

extern crate minisat;

use crate::utils::read_lines;

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
    key_vars: HashMap<Indices, minisat::Bool>,
    lock_vars: HashMap<Indices, minisat::Bool>,
    geometry: Geometry,
    lock_sheet: LockSheet,
    solver: minisat::Solver,
}

impl Solver {
    pub fn new(geometry: Geometry, lock_sheet: LockSheet) -> Solver {
        Solver {
            key_vars: HashMap::new(),
            lock_vars: HashMap::new(),
            geometry,
            lock_sheet,
            solver: minisat::Solver::new(),
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

        println!(
            "Solving for {} variables with {} clauses",
            self.solver.num_vars(),
            self.solver.num_clauses()
        );

        if let Ok(solution) = self.solver.solve() {
            println!("SOLVED!");

            for key in 0..self.lock_sheet.num_keys {
                println!("Key  {}: ", key);
                for depth in 0..self.geometry.depths {
                    for position in 0..self.geometry.positions {
                        let indices = (position, depth, key);
                        let key_lit = self.key_vars[&indices];
                        if solution.value(&key_lit) {
                            print!("{} ", depth);
                        } else {
                            print!(". ");
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
                        if solution.value(&lock_lit) {
                            print!("{} ", depth);
                        } else {
                            print!(". ");
                        }
                    }
                    println!();
                }
                println!();
            }
        } else {
            println!("NOT SOLVED!");
        }
    }

    fn exactly_one(&mut self, literals: Vec<minisat::Bool>) {
        for i in 0..literals.len() {
            for j in i + 1..literals.len() {
                self.solver.add_clause(vec![!literals[i], !literals[j]]);
            }
        }
        self.solver.add_clause(literals);
    }

    fn add_key_lit(&mut self, position: usize, depth: usize, key: usize) -> minisat::Bool {
        let indices = (position, depth, key);
        *self
            .key_vars
            .entry(indices)
            .or_insert(self.solver.new_lit())
    }

    fn add_lock_lit(&mut self, position: usize, depth: usize, lock: usize) -> minisat::Bool {
        let indices = (position, depth, lock);
        *self
            .lock_vars
            .entry(indices)
            .or_insert(self.solver.new_lit())
    }

    fn key_lit(&self, position: usize, depth: usize, key: usize) -> minisat::Bool {
        let indices = (position, depth, key);
        self.key_vars[&indices]
    }

    fn lock_lit(&self, position: usize, depth: usize, lock: usize) -> minisat::Bool {
        let indices = (position, depth, lock);
        self.lock_vars[&indices]
    }

    fn add_lock(&mut self, lock: usize) {
        for position in 0..self.geometry.positions {
            let mut literals = vec![];
            for depth in 0..self.geometry.depths {
                literals.push(self.add_lock_lit(position, depth, lock));
            }
            self.solver.add_clause(literals);
        }
    }

    fn add_key(&mut self, key: usize) {
        for position in 0..self.geometry.positions {
            let mut literals = vec![];
            for depth in 0..self.geometry.depths {
                literals.push(self.add_key_lit(position, depth, key));
            }
            self.exactly_one(literals);
        }
    }

    fn add_unlock_constraints(&mut self, key: usize) {
        for (lock, lock_line) in self.lock_sheet.locks.iter().enumerate() {
            if lock_line[key] {
                for position in 0..self.geometry.positions {
                    for depth in 0..self.geometry.depths {
                        let key_lit = self.key_lit(position, depth, key);
                        let lock_lit = self.lock_lit(position, depth, lock);
                        self.solver.add_clause([!key_lit, lock_lit]);
                    }
                }
            }
        }
    }

    fn add_block_constraints(&mut self, key: usize) {
        for (lock, lock_line) in self.lock_sheet.locks.iter().enumerate() {
            if !lock_line[key] {
                let mut blocking_literals = vec![];

                for position in 0..self.geometry.positions {
                    for depth in 0..self.geometry.depths {
                        let block_lit = self.solver.new_lit();
                        let key_lit = self.key_lit(position, depth, key);
                        let lock_lit = self.lock_lit(position, depth, lock);

                        // block_{p, d} <=> (key_{p, d} && ~lock_{p, d})
                        // 1)   block_{p, d}  => (key_{p, d} && ~lock_{p, d})
                        //     ~block_{p, d}  v  (key_{p, d} && ~lock_{p, d})
                        //    (~block_{p, d} v key_{p, d}) && (~block_{p, d} v ~lock_{p, d})
                        self.solver.add_clause([!block_lit, key_lit]);
                        self.solver.add_clause([!block_lit, !lock_lit]);

                        // 2)   (key_{p, d} && ~lock_{p, d}) => block_{p, d}
                        //     ~(key_{p, d} && ~lock_{p, d}) v  block_{p, d}
                        //     (~key_{p, d} v   lock_{p, d}) v  block_{p, d}
                        //      ~key_{p, d} v   lock_{p, d}  v block_{p, d}
                        self.solver.add_clause([block_lit, !key_lit, lock_lit]);

                        blocking_literals.push(block_lit);
                    }
                }
                self.solver.add_clause(blocking_literals);
            }
        }
    }

    fn add_gecodes(&mut self, key: usize) {
        for gecode in &self.geometry.gecodes {
            let mut literals = vec![];
            for (position, &depth) in gecode.iter().enumerate() {
                if let Some(depth) = depth {
                    let key_lit = self.key_lit(position, depth, key);
                    literals.push(!key_lit);
                }
            }
            self.solver.add_clause(literals);
        }
    }
}
