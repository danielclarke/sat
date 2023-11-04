use std::ops::Not;
use std::{error, fmt};

use crate::fixed_size_stack::FixedSizeStack;
use crate::slot_map::{SlotKey, SlotMap};

pub enum Solution {
    Sat,
    UnSat,
    Unknown,
}

#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash)]
pub enum Value {
    True,
    False,
    Unknown,
}

impl Value {
    fn or(a: Value, b: Value) -> Value {
        match (a, b) {
            (Value::True, _) => Value::True,
            (_, Value::True) => Value::True,
            (Value::Unknown, _) => Value::Unknown,
            (_, Value::Unknown) => Value::Unknown,
            _ => Value::False,
        }
    }

    fn and(a: Value, b: Value) -> Value {
        match (a, b) {
            (Value::False, _) => Value::False,
            (_, Value::False) => Value::False,
            (Value::Unknown, _) => Value::Unknown,
            (_, Value::Unknown) => Value::Unknown,
            _ => Value::True,
        }
    }
}

impl Not for Value {
    type Output = Value;

    fn not(self) -> <Self as Not>::Output {
        match self {
            Value::True => Value::False,
            Value::False => Value::True,
            Value::Unknown => Value::Unknown,
        }
    }
}

#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash)]
pub struct Variable {
    handle: usize,
}

impl Variable {
    pub fn new(handle: usize) -> Self {
        Self { handle }
    }

    pub fn literal(&self) -> Literal {
        Literal {
            polarity: true,
            handle: self.handle,
        }
    }
}

#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct Literal {
    polarity: bool,
    handle: usize,
}

impl Literal {
    fn value(&self, value: Value) -> Value {
        if self.polarity {
            value
        } else {
            !value
        }
    }
}

impl Not for Literal {
    type Output = Literal;

    fn not(self) -> <Self as Not>::Output {
        Literal {
            polarity: !self.polarity,
            handle: self.handle,
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
struct Clause {
    literals: Vec<Literal>,
}

impl Clause {
    fn new(mut literals: Vec<Literal>) -> Self {
        literals.sort();
        literals.dedup();
        Self { literals }
    }

    fn len(&self) -> usize {
        self.literals.len()
    }

    fn iter(&self) -> ClauseIterator {
        ClauseIterator {
            clause: self,
            index: 0,
        }
    }
}

impl std::ops::Index<usize> for Clause {
    type Output = Literal;

    fn index(&self, index: usize) -> &Self::Output {
        &self.literals[index]
    }
}

struct ClauseIterator<'a> {
    clause: &'a Clause,
    index: usize,
}

impl<'a> Iterator for ClauseIterator<'a> {
    type Item = &'a Literal;

    fn next(&mut self) -> Option<Self::Item> {
        if self.index < self.clause.literals.len() {
            let result = Some(&self.clause.literals[self.index]);
            self.index += 1;
            result
        } else {
            None
        }
    }
}

type DecisionLevel = Option<usize>;
type Antecedant = Option<SlotKey>;
type ClauseIndex = SlotKey;

fn resolve(a: &Clause, b: &Clause) -> Option<Clause> {
    for l_a in a.iter() {
        for l_b in b.iter() {
            if l_a.handle == l_b.handle && l_a.polarity != l_b.polarity {
                let mut resolvent = vec![];
                for ll_a in a.iter() {
                    if ll_a != l_a {
                        resolvent.push(*ll_a);
                    }
                }
                for ll_b in b.iter() {
                    if ll_b != l_b {
                        resolvent.push(*ll_b);
                    }
                }
                return Some(Clause::new(resolvent));
            }
        }
    }
    None
}

#[derive(Debug, Copy, Clone, PartialEq)]
struct VariableAssignment {
    handle: usize,
    index: usize,
    values: [Value; 2],
}

impl VariableAssignment {
    fn new(handle: usize, polarity: bool) -> Self {
        let values = if polarity {
            [Value::True, Value::False]
        } else {
            [Value::False, Value::True]
        };
        Self {
            handle,
            index: 0,
            values,
        }
    }
}

pub struct Solver {
    // problem
    variables: Vec<Variable>,
    clauses: SlotMap<Clause>,

    // lookup
    // variable map to clause
    variable_clauses: Vec<Vec<ClauseIndex>>,
    // variable map to clause where the literal is positive
    positive_literal_clauses: Vec<Vec<ClauseIndex>>,
    // variable map to clause where the literal is negative
    negative_literal_clauses: Vec<Vec<ClauseIndex>>,

    // search
    decisions: FixedSizeStack<VariableAssignment>,
    decision_levels: FixedSizeStack<DecisionLevel>,

    // state
    values: Vec<Value>,
    variable_decision_levels: Vec<DecisionLevel>,
    antecedents: Vec<Antecedant>,

    // implication_vertices:
    watched_literals: SlotMap<[Literal; 2]>,
    unit_clauses: FixedSizeStack<ClauseIndex>,
}

impl Solver {
    pub fn new() -> Self {
        Self {
            variables: vec![],
            clauses: SlotMap::new(),
            variable_clauses: vec![],
            positive_literal_clauses: vec![],
            negative_literal_clauses: vec![],
            decisions: FixedSizeStack::new(0),
            decision_levels: FixedSizeStack::new(0),
            values: vec![],
            variable_decision_levels: vec![],
            antecedents: vec![],
            watched_literals: SlotMap::new(),
            unit_clauses: FixedSizeStack::new(0),
        }
    }

    pub fn add_var(&mut self) -> Variable {
        let var = Variable::new(self.variables.len());
        self.variables.push(var);
        var
    }

    pub fn add_clause(&mut self, literals: Vec<Literal>) -> SlotKey {
        self.clauses.insert(Clause::new(literals))
    }

    pub fn value(&self, variable: &Variable) -> Value {
        self.values[variable.handle]
    }

    fn next_unassigned(&mut self) -> Option<(DecisionLevel, VariableAssignment)> {
        // unassigned variable search order:
        //   1. unit clause
        //   2. pure literal
        //   3. smallest clause

        while let Some(slot_key) = self.unit_clauses.pop() {
            match self.eval_clause(self.clauses.get(&slot_key).unwrap()) {
                // need to continue to avoid "false positive" unit clause which incorrectly triggers a DL backtrack
                Value::True => continue,
                Value::False => unreachable!("False clause not earlier caught"),
                Value::Unknown => (),
            }

            for literal in self.clauses.get(&slot_key).unwrap().iter() {
                if literal.value(self.values[literal.handle]) == Value::Unknown {
                    self.antecedents[literal.handle] = Some(slot_key);
                    let dl = self.decision_levels.last().map_or(Some(0), |&dl| dl);
                    println!("BCP {:#?} {:#?}", literal.handle, dl.unwrap());
                    return Some((
                        dl,
                        VariableAssignment::new(literal.handle, literal.polarity),
                    ));
                }
            }
        }

        let (mut handle, mut min_clause_length) = (None, None);
        for (slot_key, clause) in self.clauses.iter().items() {
            // unit clause propagation
            let clause_length = self.clause_length(clause);

            if clause_length == 0 {
                continue;
            }

            if clause_length == 1 {
                match self.eval_clause(clause) {
                    // need to continue to avoid "false positive" unit clause which incorrectly triggers a DL backtrack
                    Value::True => continue,
                    Value::False => unreachable!("False clause not earlier caught"),
                    Value::Unknown => (),
                }

                for literal in clause.iter() {
                    if literal.value(self.values[literal.handle]) == Value::Unknown {
                        self.antecedents[literal.handle] = Some(slot_key);
                        let dl = self
                            .decision_levels
                            .last()
                            .map_or(Some(0), |&dl| dl.and_then(|dl| Some(dl + 1)));

                        println!("Unit Clause {:#?} {:#?}", literal.handle, dl.unwrap());
                        return Some((
                            dl,
                            VariableAssignment::new(literal.handle, literal.polarity),
                        ));
                    }
                }
            }

            // cache the smallest clause encountered
            match (handle, min_clause_length) {
                (None, None) => {
                    for literal in clause.iter() {
                        if literal.value(self.values[literal.handle]) == Value::Unknown {
                            (handle, min_clause_length) =
                                (Some(literal.handle), Some(clause_length));
                            break;
                        }
                    }
                }
                (Some(_), Some(min_clause_length_)) => {
                    if clause_length < min_clause_length_ {
                        for literal in clause.iter() {
                            if literal.value(self.values[literal.handle]) == Value::Unknown {
                                (handle, min_clause_length) =
                                    (Some(literal.handle), Some(clause_length));
                                break;
                            }
                        }
                    }
                }
                (_, _) => unreachable!(),
            }
        }

        // pure literal elimination
        for (v, clauses) in self.variable_clauses.iter().enumerate() {
            'next_variable: {
                if self.values[v] == Value::Unknown {
                    let mut polarity = None;
                    for &clause in clauses.iter() {
                        if self.eval_clause(self.clauses.get(&clause).unwrap()) == Value::Unknown {
                            for literal in self.clauses.get(&clause).unwrap().iter() {
                                if literal.handle == v {
                                    match polarity {
                                        None => polarity = Some(literal.polarity),
                                        Some(polarity) => {
                                            if polarity == literal.polarity {
                                                continue;
                                            } else {
                                                break 'next_variable;
                                            }
                                        }
                                    }
                                }
                            }
                        }
                    }
                    match polarity {
                        None => (),
                        Some(polarity) => {
                            println!("Polarity {}", v);
                            return Some((
                                self.decision_levels
                                    .last()
                                    .map_or(Some(0), |&dl| dl.and_then(|dl| Some(dl + 1))),
                                VariableAssignment::new(v, polarity),
                            ));
                        }
                    }
                };
            }
        }

        // smallest clause
        handle.map(|handle| {
            println!("Smallest clause {}", handle);
            (
                self.decision_levels
                    .last()
                    .map_or(Some(0), |&dl| dl.and_then(|dl| Some(dl + 1))),
                VariableAssignment::new(handle, false),
            )
        })
    }

    fn clause_length(&self, clause: &Clause) -> usize {
        clause
            .iter()
            .filter(|l| self.values[l.handle] == Value::Unknown)
            .count()
    }

    fn eval_clause(&self, clause: &Clause) -> Value {
        let mut acc = Value::False;
        for literal in clause.iter() {
            acc = Value::or(acc, literal.value(self.values[literal.handle]));
            if acc == Value::True {
                return Value::True;
            }
        }
        acc
    }

    fn print_clause(&self, clause: &Clause) {
        for literal in clause.iter() {
            if !literal.polarity {
                print!("¬");
            }
            print!("x_");
            print!("{}", literal.handle);
            print!(
                "_({}) ",
                self.variable_decision_levels[literal.handle]
                    .map_or("None".to_owned(), |dl| format!("{}", dl))
            );

            // println!(
            //     "Literal Value {} {:#?}",
            //     literal.handle,
            //     literal.value(self.values[literal.handle])
            // );
        }
        println!();
    }

    fn reassign_watched_literal(&mut self) -> Solution {
        if let Some(&va) = self.decisions.last() {
            let false_literal_clauses = match va.values[va.index] {
                Value::True => &self.negative_literal_clauses[va.handle],
                Value::False => &self.positive_literal_clauses[va.handle],
                Value::Unknown => unreachable!("Unknown value on decision stack"),
            };

            // iterate watching clauses and reassign the watched literal to an unset one
            for &slot_key in false_literal_clauses.iter() {
                let watched_literal_index =
                    if va.handle == self.watched_literals.get(&slot_key).unwrap()[0].handle {
                        0
                    } else if va.handle == self.watched_literals.get(&slot_key).unwrap()[1].handle {
                        1
                    } else {
                        continue;
                    };

                match self.clause_length(self.clauses.get(&slot_key).unwrap()) {
                    0 => {
                        if self.eval_clause(self.clauses.get(&slot_key).unwrap()) == Value::False {
                            self.learn_clause(slot_key);
                            return Solution::UnSat;
                        }
                    }
                    1 => {
                        if self.eval_clause(self.clauses.get(&slot_key).unwrap()) == Value::Unknown
                        {
                            self.unit_clauses.push(slot_key);
                        }
                    }
                    _ => {
                        for &l in self.clauses.get(&slot_key).unwrap().iter() {
                            if self.values[l.handle] == Value::Unknown
                                && l != self.watched_literals.get(&slot_key).unwrap()[0]
                                && l != self.watched_literals.get(&slot_key).unwrap()[1]
                            {
                                // replace the watched literal
                                self.watched_literals.get_mut(&slot_key).unwrap()
                                    [watched_literal_index] = l;
                                break;
                            }
                        }
                    }
                }
            }
        }
        Solution::Unknown
    }

    fn check_satisfiability(&self) -> Solution {
        match self
            .clauses
            .iter()
            .map(|clause| self.eval_clause(clause))
            .fold(Value::True, Value::and)
        {
            Value::True => Solution::Sat,
            Value::False => Solution::UnSat,
            Value::Unknown => Solution::Unknown,
        }
    }

    fn backtrack_once(&mut self) -> Option<(DecisionLevel, VariableAssignment)> {
        let variable_assignment = self.decisions.pop()?;

        self.values[variable_assignment.handle] = Value::Unknown;
        self.variable_decision_levels[variable_assignment.handle] = None;

        Some((
            self.decision_levels.pop().and_then(|dl| dl),
            variable_assignment,
        ))
    }

    fn backtrack(&mut self) -> Solution {
        self.unit_clauses.clear();

        let prior_decision_level = self.decision_levels.last().and_then(|&dl| dl);

        let (decision_level, variable_assignment) = 'backtrack: loop {
            let (decision_level, variable_assignment) = if let Some(var) = self.backtrack_once() {
                var
            } else {
                // all variables exhausted
                println!("All backtrack variables exhausted, decision_level");
                return Solution::UnSat;
            };

            // go to the first decision with the same decision level
            if self.decision_levels.last().and_then(|&dl| dl) != prior_decision_level
                || self.decision_levels.len() == 0
            {
                break 'backtrack (decision_level, variable_assignment);
            } else {
                self.antecedents[variable_assignment.handle] = None;
            }
        };

        let (decision_level, variable_assignment) = if variable_assignment.index == 0 {
            (decision_level, variable_assignment)
        } else {
            'backtrack: loop {
                let (decision_level, variable_assignment) = if let Some(var) = self.backtrack_once()
                {
                    var
                } else {
                    // all variables exhausted
                    println!("All backtrack variables exhausted, other assignment");
                    return Solution::UnSat;
                };

                if variable_assignment.index == 0 {
                    break 'backtrack (decision_level, variable_assignment);
                }
            }
        };

        // reached a variable with a remaining assignment, try the other truth value
        self.values[variable_assignment.handle] = variable_assignment.values[1];
        // push it back onto the top of the stack
        self.decisions.push(VariableAssignment {
            index: 1,
            ..variable_assignment
        });
        self.decision_levels.push(decision_level);
        self.variable_decision_levels[variable_assignment.handle] = decision_level;

        println!("Backtracked to {}", variable_assignment.handle);
        Solution::Unknown
    }

    fn get_most_recent_decision_assignment(&self) -> Option<VariableAssignment> {
        let mut variable_assignment: Option<VariableAssignment> = None;
        let decision_level = *self.decision_levels.last()?;
        // println!(
        //     "Decision level {} {} {}",
        //     decision_level.unwrap(),
        //     self.decision_levels.len(),
        //     self.decisions.len()
        // );
        // for va in self.decisions.iter() {
        //     match self.variable_decision_levels[va.handle] {
        //         Some(decision_level) => {
        //             print!("{} ", decision_level);
        //         }
        //         None => print!("None "),
        //     }
        // }
        // println!();
        // for &dl in self.decision_levels.iter() {
        //     match dl {
        //         Some(decision_level) => {
        //             print!("{} ", decision_level);
        //         }
        //         None => print!("None "),
        //     }
        // }
        // println!();

        for va in self.decisions.iter() {
            // match decision_level {
            //     Some(decision_level) => {
            //         println!("Decision level {}", decision_level);
            //     }
            //     None => println!("Decision level None"),
            // }

            // match self.variable_decision_levels[va.handle] {
            //     Some(decision_level) => {
            //         println!("VA Decision level {}", decision_level);
            //     }
            //     None => println!("VA Decision level None"),
            // }

            // match variable_assignment {
            //     Some(variable_assignment) => {
            //         println!("Variable assignment handle {}", variable_assignment.handle);
            //     }
            //     None => {
            //         println!("Variable assignment None");
            //     }
            // }

            // println!("va {}", va.handle);

            // match self.variable_decision_levels[va.handle] {
            //     Some(decision_level) => {
            //         println!("Variable decision level {}", decision_level);
            //     }
            //     None => println!("Variable decision level None"),
            // }

            if self.variable_decision_levels[va.handle] == decision_level {
                variable_assignment = Some(*va);
            } else {
                break;
            }
        }

        variable_assignment
    }

    fn conflict_analysis(&self, clause_index: ClauseIndex) -> Clause {
        let mut clause: Vec<Literal> = vec![];

        let latest_decision_level = *self.decision_levels.last().unwrap();
        let latest_decision = self.get_most_recent_decision_assignment().unwrap();

        let mut literal_queue = self.clauses.get(&clause_index).unwrap().literals.clone();
        let mut visited_list = vec![];
        println!("--------------------------------");
        print!("Conflict clause {} ", clause_index);
        self.print_clause(self.clauses.get(&clause_index).unwrap());
        println!("latest_decision_level {}", latest_decision_level.unwrap());
        println!("latest_decision {}", latest_decision.handle);

        println!("decision levels");
        for &dl in self.decision_levels.iter() {
            match dl {
                Some(decision_level) => {
                    print!("{} ", decision_level);
                }
                None => print!("None "),
            }
        }
        println!();

        println!("va decision levels");
        for va in self.decisions.iter() {
            match self.variable_decision_levels[va.handle] {
                Some(decision_level) => {
                    print!("{} ", decision_level);
                }
                None => print!("None "),
            }
        }
        println!();

        println!("va value");
        for va in self.decisions.iter() {
            match va.values[va.index] {
                Value::True => print!("1 "),
                Value::False => print!("0 "),
                Value::Unknown => (),
            }
        }
        println!();

        println!("va index");
        for va in self.decisions.iter() {
            print!("{} ", va.index)
        }
        println!();

        for va in self.decisions.iter() {
            print!("{} ", va.handle);
        }
        println!();

        for va in self.decisions.iter() {
            match self.antecedents[va.handle] {
                None => println!("antecedent {} None", va.handle),
                Some(antecedent) => {
                    // println!("antecedent {} {:#?}", va.handle, antecedent);
                    print!("antecedent {} ", va.handle);
                    self.print_clause(self.clauses.get(&antecedent).unwrap());
                }
            }
            // println!("DL {} {:#?}", handle, self.variable_decision_levels[handle]);
            // println!("DV {:#?}", handle == latest_decision.handle);
        }

        loop {
            if literal_queue.is_empty() {
                // if clause.is_empty() {
                //     print!("Conflict ");
                //     self.print_clause(self.clauses.get(&clause_index).unwrap());
                //     println!("DL {:#?}", latest_decision_level);
                //     println!("VA {:#?}", latest_decision);
                //     println!("Visited Lits {:#?}", visited_list);
                //     for handle in visited_list {
                //         match self.antecedents[handle] {
                //             None => println!("antecedent {} None", handle),
                //             Some(antecedent) => {
                //                 println!("antecedent {} {:#?}", handle, antecedent);
                //                 print!("antecedent ");
                //                 self.print_clause(self.clauses.get(&antecedent).unwrap());
                //             }
                //         }
                //         println!("DL {} {:#?}", handle, self.variable_decision_levels[handle]);
                //         println!("DV {:#?}", handle == latest_decision.handle);
                //     }
                //     println!("--------------------------------");
                //     // self.print_clause(clause);
                //     println!(
                //         "{:#?}",
                //         clause
                //             .iter()
                //             .map(|&literal| self.variable_decision_levels[literal.handle])
                //             .collect::<Vec<_>>()
                //     );
                //     for &dl in self.decision_levels.iter() {
                //         match dl {
                //             Some(decision_level) => {
                //                 print!("{} ", decision_level);
                //             }
                //             None => print!("None "),
                //         }
                //     }
                //     println!();
                //     for va in self.decisions.iter() {
                //         match self.variable_decision_levels[va.handle] {
                //             Some(decision_level) => {
                //                 print!("{} ", decision_level);
                //             }
                //             None => print!("None "),
                //         }
                //     }
                //     println!();
                //     for va in self.decisions.iter() {
                //         print!("{:#?} ", va.handle);
                //     }
                // }

                println!("--------------------------------");
                return Clause::new(clause);
            }

            println!("  ------------------------------");

            let literal = literal_queue.remove(0);
            visited_list.push(literal.handle);
            if self.variable_decision_levels[literal.handle] == latest_decision_level {
                if literal.handle == latest_decision.handle {
                    clause.push(literal);
                }
                match self.antecedents[literal.handle] {
                    None => (),
                    Some(antecedent) => {
                        let antecedent_clause =
                            &mut self.clauses.get(&antecedent).unwrap().literals.clone();
                        literal_queue.append(
                            &mut antecedent_clause
                                .iter()
                                .filter(|&&l| !visited_list.contains(&l.handle))
                                .map(|&l| l)
                                .collect::<Vec<_>>(),
                        );
                    }
                }
            } else {
                clause.push(literal);
            }
        }
    }

    // fn conflict_analysis(&self, clause_index: ClauseIndex) -> Clause {
    //     let mut clause = self.clauses.get(&clause_index).unwrap().clone();

    //     let latest_decision_level = *self.decision_levels.last().unwrap();

    //     let mut literal_queue = clause
    //         .literals
    //         .clone()
    //         .iter()
    //         .filter(|&l| self.variable_decision_levels[l.handle] == latest_decision_level)
    //         .map(|&l| l)
    //         .collect::<Vec<_>>();
    //     let mut visited_list = vec![];

    //     loop {
    //         if literal_queue.is_empty() {
    //             return clause;
    //         }

    //         let literal = literal_queue.remove(0);
    //         visited_list.push(literal.handle);
    //         match self.antecedents[literal.handle] {
    //             None => (),
    //             Some(slot_key) => {
    //                 let antecedent = &mut self.clauses.get(&slot_key).unwrap().literals.clone();
    //                 literal_queue.append(
    //                     &mut antecedent
    //                         .iter()
    //                         .filter(|&l| {
    //                             self.variable_decision_levels[l.handle] == latest_decision_level
    //                         })
    //                         .filter(|&&l| !visited_list.contains(&l.handle))
    //                         .map(|&l| l)
    //                         .collect::<Vec<_>>(),
    //                 );
    //                 match resolve(&clause, &self.clauses.get(&slot_key).unwrap()) {
    //                     None => (),
    //                     Some(resolvent) => {
    //                         if clause == resolvent {
    //                             return clause;
    //                         }
    //                         clause = resolvent;
    //                     }
    //                 }
    //             }
    //         }
    //     }
    // }

    fn learn_clause(&mut self, c: ClauseIndex) {
        let learned_clause = self.conflict_analysis(c);

        self.print_clause(&learned_clause);
        println!();

        // println!("--------------------------------");
        // self.print_clause(&learned_clause);
        // println!(
        //     "{:#?}",
        //     learned_clause
        //         .iter()
        //         .map(|&literal| self.variable_decision_levels[literal.handle])
        //         .collect::<Vec<_>>()
        // );

        let watched_literals = if learned_clause.len() == 1 {
            [learned_clause[0], learned_clause[0]] // unit clauses watch the only literal twice
        } else {
            let mut watched_literals = [learned_clause[0], learned_clause[1]];
            let decision_variable_watched_literals = watched_literals.iter().any(|&literal| {
                self.variable_decision_levels[literal.handle]
                    == *self.decision_levels.last().unwrap()
            });

            if !decision_variable_watched_literals {
                watched_literals[1] = match learned_clause.iter().find(|&literal| {
                    self.variable_decision_levels[literal.handle]
                        == *self.decision_levels.last().unwrap()
                }) {
                    None => {
                        self.print_clause(&learned_clause);
                        println!(
                            "{:#?}",
                            learned_clause
                                .iter()
                                .map(|&literal| self.variable_decision_levels[literal.handle])
                                .collect::<Vec<_>>()
                        );
                        println!("DL: {:#?}", self.decision_levels.last().unwrap().unwrap());
                        watched_literals[1]
                        // unreachable!("Learned clause does not contain decision variable");
                    }
                    Some(&literal) => literal,
                }
            }
            watched_literals
        };
        self.watched_literals.insert(watched_literals);
        let slot_key = self.clauses.insert(learned_clause);
        for literal in self.clauses.get(&slot_key).unwrap().iter() {
            if literal.polarity {
                self.positive_literal_clauses[literal.handle].push(slot_key);
            } else {
                self.negative_literal_clauses[literal.handle].push(slot_key);
            }
            self.variable_clauses[literal.handle].push(slot_key);
        }
        // a learned clause should have length = 1 after backtrack
        // backtracking which occurs after this will clear the stack anyway
        // if self.clause_length(&self.clauses.get(&slot_key).unwrap()) == 1 {
        //     self.unit_clauses.push(slot_key);
        // }
    }

    fn init(&mut self) {
        self.variable_clauses = vec![vec![]; self.variables.len()];
        self.positive_literal_clauses = vec![vec![]; self.variables.len()];
        self.negative_literal_clauses = vec![vec![]; self.variables.len()];

        for (slot_key, clause) in self.clauses.iter().items() {
            for literal in clause.iter() {
                self.variable_clauses[literal.handle].push(slot_key);
                if literal.polarity {
                    self.positive_literal_clauses[literal.handle].push(slot_key);
                } else {
                    self.negative_literal_clauses[literal.handle].push(slot_key);
                }
            }
        }

        self.values = vec![Value::Unknown; self.variables.len()];
        self.variable_decision_levels = vec![None; self.variables.len()];
        let watched_literals = self
            .clauses
            .iter()
            .map(|c| {
                if c.len() == 1 {
                    [c[0], c[0]] // unit clauses watch the only literal twice
                } else {
                    [c[0], c[1]]
                }
            })
            .collect::<Vec<_>>();

        for watched_literal in watched_literals {
            self.watched_literals.insert(watched_literal);
        }

        self.decisions = FixedSizeStack::new(self.variables.len());
        self.decision_levels = FixedSizeStack::new(self.variables.len());
        self.antecedents = vec![None; self.variables.len()];
        self.unit_clauses = FixedSizeStack::new(self.clauses.len());
    }

    pub fn solve(&mut self) -> Solution {
        self.init();

        println!(
            "Solving for {} variables with {} clauses",
            self.variables.len(),
            self.clauses.len()
        );

        let (decision_level, unassigned) = if let Some(var) = self.next_unassigned() {
            var
        } else {
            println!("All variables assigned!");
            return Solution::Sat;
        };

        self.values[unassigned.handle] = unassigned.values[0];
        self.variable_decision_levels[unassigned.handle] = decision_level;
        self.decisions.push(unassigned);
        self.decision_levels.push(decision_level);

        let mut i = 0;
        loop {
            if self.decisions.len() != self.decision_levels.len() {
                unreachable!(
                    "Decision misalignment! decisions: {}, decision levels: {}",
                    self.decisions.len(),
                    self.decision_levels.len()
                );
            }

            i += 1;
            if i % 100_000 == 0 {
                println!(
                    "{}: Vars: {} / {} DL: {:#?}",
                    i,
                    self.variables.len() - self.decisions.len(),
                    self.variables.len(),
                    self.decision_levels.last().and_then(|&dl| dl)
                );
            }
            match self.reassign_watched_literal() {
                Solution::Sat => {
                    println!("Solved in Iterations: {}", i);
                    return Solution::Sat;
                }
                Solution::UnSat => match self.backtrack() {
                    Solution::Sat => unreachable!("Backtrack found a solution"),
                    Solution::UnSat => return Solution::UnSat,
                    Solution::Unknown => (),
                },
                Solution::Unknown => {
                    if let Some((decision_level, var)) = self.next_unassigned() {
                        self.values[var.handle] = var.values[0];
                        self.variable_decision_levels[var.handle] = decision_level;
                        self.decisions.push(var);
                        self.decision_levels.push(decision_level);
                    } else {
                        match self.check_satisfiability() {
                            Solution::Sat => {
                                println!("Solved in Iterations: {}", i);
                                return Solution::Sat;
                            }
                            Solution::UnSat => return Solution::UnSat,
                            Solution::Unknown => return Solution::Unknown,
                        }
                    };
                }
            }
        }
    }
}

#[derive(Debug, Clone)]
pub enum SolutionError {
    UnSat,
}

impl fmt::Display for SolutionError {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match *self {
            SolutionError::UnSat => write!(f, "Solution unsatisfiable"),
        }
    }
}

impl error::Error for SolutionError {}

#[cfg(test)]
mod test_resolution {
    use super::*;
    use std::error::Error;

    #[test]
    fn test_resolution() -> Result<(), Box<dyn Error>> {
        let vars = vec![Variable::new(0), Variable::new(1), Variable::new(2)];
        let clause_a = Clause::new(vec![vars[0].literal(), vars[1].literal()]);
        let clause_b = Clause::new(vec![!vars[1].literal(), vars[2].literal()]);

        assert_eq!(
            resolve(&clause_a, &clause_b),
            Some(Clause::new(vec![vars[0].literal(), vars[2].literal()]))
        );

        Ok(())
    }

    #[test]
    fn test_resolution_2() -> Result<(), Box<dyn Error>> {
        let v1 = Variable::new(0);
        let v2 = Variable::new(1);
        let v3 = Variable::new(2);
        let v4 = Variable::new(3);
        let v5 = Variable::new(4);
        let v6 = Variable::new(5);
        let v31 = Variable::new(6);
        let v21 = Variable::new(7);

        let c1 = Clause::new(vec![v1.literal(), v31.literal(), !v2.literal()]);
        let c2 = Clause::new(vec![v1.literal(), !v3.literal()]);
        let c3 = Clause::new(vec![v2.literal(), v3.literal(), v4.literal()]);
        let c4 = Clause::new(vec![!v4.literal(), !v5.literal()]);
        let c5 = Clause::new(vec![v21.literal(), !v4.literal(), !v6.literal()]);
        let c6 = Clause::new(vec![v5.literal(), v6.literal()]);

        let resolvent = resolve(&c6, &c4);
        assert_eq!(
            resolvent,
            Some(Clause::new(vec![!v4.literal(), v6.literal()]))
        );

        let resolvent = resolve(&c5, &resolvent.unwrap());
        assert_eq!(
            resolvent,
            Some(Clause::new(vec![v21.literal(), !v4.literal()]))
        );

        let resolvent = resolve(&c3, &resolvent.unwrap());
        assert_eq!(
            resolvent,
            Some(Clause::new(vec![v21.literal(), v2.literal(), v3.literal()]))
        );

        let resolvent = resolve(&c1, &resolvent.unwrap());
        assert_eq!(
            resolvent,
            Some(Clause::new(vec![
                v31.literal(),
                v21.literal(),
                v3.literal(),
                v1.literal()
            ]))
        );

        let resolvent = resolve(&c2, &resolvent.unwrap());
        assert_eq!(
            resolvent,
            Some(Clause::new(vec![
                v31.literal(),
                v21.literal(),
                v1.literal()
            ]))
        );

        Ok(())
    }

    #[test]
    fn test_resolution_3() -> Result<(), Box<dyn Error>> {
        let v1 = Variable::new(0);
        let v2 = Variable::new(1);
        let v3 = Variable::new(2);
        let v4 = Variable::new(3);
        let v5 = Variable::new(4);
        let v6 = Variable::new(5);
        let v21 = Variable::new(21);
        let v31 = Variable::new(31);

        let c1 = Clause::new(vec![v1.literal(), v31.literal(), !v2.literal()]);
        let c2 = Clause::new(vec![v1.literal(), !v3.literal()]);
        let c3 = Clause::new(vec![v2.literal(), v3.literal(), v4.literal()]);
        let c4 = Clause::new(vec![!v4.literal(), !v5.literal()]);
        let c5 = Clause::new(vec![v21.literal(), !v4.literal(), !v6.literal()]);
        let c6 = Clause::new(vec![v5.literal(), v6.literal()]);

        // 5 3 2 1 4
        let resolvent = resolve(&c6, &c5);
        assert_eq!(
            resolvent,
            Some(Clause::new(vec![
                !v4.literal(),
                v5.literal(),
                v21.literal()
            ]))
        );

        let resolvent = resolve(&c3, &resolvent.unwrap());
        assert_eq!(
            resolvent,
            Some(Clause::new(vec![
                v2.literal(),
                v3.literal(),
                v5.literal(),
                v21.literal(),
            ]))
        );

        let resolvent = resolve(&c2, &resolvent.unwrap());
        assert_eq!(
            resolvent,
            Some(Clause::new(vec![
                v1.literal(),
                v2.literal(),
                v5.literal(),
                v21.literal(),
            ]))
        );

        let resolvent = resolve(&c1, &resolvent.unwrap());
        assert_eq!(
            resolvent,
            Some(Clause::new(vec![
                v1.literal(),
                v5.literal(),
                v21.literal(),
                v31.literal(),
            ]))
        );

        let resolvent = resolve(&c4, &resolvent.unwrap());
        assert_eq!(
            resolvent,
            Some(Clause::new(vec![
                v1.literal(),
                !v4.literal(),
                v21.literal(),
                v31.literal(),
            ]))
        );

        Ok(())
    }
}

#[cfg(test)]
mod test_clause_learning {
    use super::*;
    use std::error::Error;

    #[test]
    fn test_clause_learning() -> Result<(), Box<dyn Error>> {
        let mut solver = Solver::new();

        solver.add_var();
        let v1 = solver.add_var();
        let v2 = solver.add_var();
        let v3 = solver.add_var();
        let v4 = solver.add_var();
        let v5 = solver.add_var();
        let v6 = solver.add_var();
        for _ in 7..21 {
            solver.add_var();
        }
        let v21 = solver.add_var();
        for _ in 22..31 {
            solver.add_var();
        }
        let v31 = solver.add_var();

        let c1 = vec![v1.literal(), v31.literal(), !v2.literal()];
        let c2 = vec![v1.literal(), !v3.literal()];
        let c3 = vec![v2.literal(), v3.literal(), v4.literal()];
        let c4 = vec![!v4.literal(), !v5.literal()];
        let c5 = vec![v21.literal(), !v4.literal(), !v6.literal()];
        let c6 = vec![v5.literal(), v6.literal()];

        let sk1 = solver.add_clause(c1);
        let sk2 = solver.add_clause(c2);
        let sk3 = solver.add_clause(c3);
        let sk4 = solver.add_clause(c4);
        let sk5 = solver.add_clause(c5);
        let sk6 = solver.add_clause(c6);

        solver.init();

        solver.values[v21.handle] = Value::False;
        solver.variable_decision_levels[v21.handle] = Some(2);
        solver.decision_levels.push(Some(2));
        solver.decisions.push(VariableAssignment {
            handle: v21.handle,
            index: 0,
            values: [Value::False, Value::True],
        });

        solver.values[v31.handle] = Value::False;
        solver.variable_decision_levels[v31.handle] = Some(3);
        solver.decision_levels.push(Some(3));
        solver.decisions.push(VariableAssignment {
            handle: v31.handle,
            index: 0,
            values: [Value::False, Value::True],
        });

        solver.values[v1.handle] = Value::False;
        solver.variable_decision_levels[v1.handle] = Some(5);
        solver.decision_levels.push(Some(5));
        solver.decisions.push(VariableAssignment {
            handle: v1.handle,
            index: 0,
            values: [Value::False, Value::True],
        });

        solver.values[v2.handle] = Value::False;
        solver.antecedents[v2.handle] = Some(sk1);
        solver.variable_decision_levels[v2.handle] = Some(5);
        solver.decision_levels.push(Some(5));
        solver.decisions.push(VariableAssignment {
            handle: v2.handle,
            index: 0,
            values: [Value::False, Value::True],
        });

        solver.values[v3.handle] = Value::False;
        solver.antecedents[v3.handle] = Some(sk2);
        solver.variable_decision_levels[v3.handle] = Some(5);
        solver.decision_levels.push(Some(5));
        solver.decisions.push(VariableAssignment {
            handle: v3.handle,
            index: 0,
            values: [Value::False, Value::True],
        });

        solver.values[v4.handle] = Value::False;
        solver.antecedents[v4.handle] = Some(sk3);
        solver.variable_decision_levels[v4.handle] = Some(5);
        solver.decision_levels.push(Some(5));
        solver.decisions.push(VariableAssignment {
            handle: v4.handle,
            index: 0,
            values: [Value::False, Value::True],
        });

        solver.values[v5.handle] = Value::False;
        solver.antecedents[v5.handle] = Some(sk4);
        solver.variable_decision_levels[v5.handle] = Some(5);
        solver.decision_levels.push(Some(5));
        solver.decisions.push(VariableAssignment {
            handle: v5.handle,
            index: 0,
            values: [Value::False, Value::True],
        });

        solver.values[v6.handle] = Value::False;
        solver.antecedents[v6.handle] = Some(sk5);
        solver.variable_decision_levels[v6.handle] = Some(5);
        solver.decision_levels.push(Some(5));
        solver.decisions.push(VariableAssignment {
            handle: v6.handle,
            index: 0,
            values: [Value::False, Value::True],
        });

        let learned_clause = solver.conflict_analysis(sk6);

        assert_eq!(
            learned_clause,
            Clause::new(vec![v1.literal(), v21.literal(), v31.literal()])
        );

        assert_eq!(
            solver.get_most_recent_decision_assignment(),
            Some(VariableAssignment {
                handle: v1.handle,
                index: 0,
                values: [Value::False, Value::True]
            })
        );

        Ok(())
    }
}
