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

    fn add(&mut self, literal: Literal) {
        if !self.literals.contains(&literal) {
            self.literals.push(literal);
            self.literals.sort();
        }
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

type DecisionLevel = usize;
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

#[derive(Clone)]
pub struct Formula {
    variables: Option<Vec<Variable>>,
    clauses: Option<SlotMap<Clause>>,
}

impl Formula {
    pub fn new() -> Self {
        Self {
            variables: Some(vec![]),
            clauses: Some(SlotMap::new()),
        }
    }

    pub fn add_var(&mut self) -> Variable {
        let var = Variable::new(self.variables.as_ref().unwrap().len());
        self.variables.as_mut().unwrap().push(var);
        var
    }

    pub fn add_clause(&mut self, literals: Vec<Literal>) -> SlotKey {
        self.clauses.as_mut().unwrap().insert(Clause::new(literals))
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
    variable_decision_levels: Vec<Option<DecisionLevel>>,
    antecedents: Vec<Antecedant>,

    // implication_vertices:
    watched_literals: SlotMap<[Literal; 2]>,
    unit_clauses: FixedSizeStack<ClauseIndex>,
}

impl Solver {
    pub fn new(formula: Formula) -> Self {
        let mut formula = formula;
        let num_variables = formula.variables.as_ref().unwrap().len();
        let num_clauses = formula.clauses.as_ref().unwrap().len();
        let mut variable_clauses = vec![vec![]; num_variables];
        let mut positive_literal_clauses = vec![vec![]; num_variables];
        let mut negative_literal_clauses = vec![vec![]; num_variables];

        for (slot_key, clause) in formula.clauses.as_ref().unwrap().iter().items() {
            for literal in clause.iter() {
                variable_clauses[literal.handle].push(slot_key);
                if literal.polarity {
                    positive_literal_clauses[literal.handle].push(slot_key);
                } else {
                    negative_literal_clauses[literal.handle].push(slot_key);
                }
            }
        }

        let values = vec![Value::Unknown; num_variables];
        let variable_decision_levels = vec![None; num_variables];
        let watched_literals = formula
            .clauses
            .as_ref()
            .unwrap()
            .iter()
            .map(|c| {
                if c.len() == 1 {
                    [c[0], c[0]] // unit clauses watch the only literal twice
                } else {
                    [c[0], c[1]]
                }
            })
            .collect::<SlotMap<_>>();

        let decisions = FixedSizeStack::new(num_variables);
        let decision_levels = FixedSizeStack::new(num_variables);
        let antecedents = vec![None; num_variables];
        let unit_clauses = FixedSizeStack::new(num_clauses);

        Self {
            variables: formula.variables.take().unwrap(),
            clauses: formula.clauses.take().unwrap(),
            variable_clauses,
            positive_literal_clauses,
            negative_literal_clauses,
            decisions,
            decision_levels,
            values,
            variable_decision_levels,
            antecedents,
            watched_literals,
            unit_clauses,
        }
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
                Value::False => unreachable!("False unit clause not earlier caught"),
                Value::Unknown => (),
            }

            for literal in self.clauses.get(&slot_key).unwrap().iter() {
                if literal.value(self.values[literal.handle]) == Value::Unknown {
                    self.antecedents[literal.handle] = Some(slot_key);
                    let dl = self.decision_levels.last().map_or(0, |&dl| dl);
                    // println!("BCP {:#?} {:#?}", literal.handle, dl);
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
                        let dl = self.decision_levels.last().map_or(0, |&dl| dl + 1);

                        // println!("Unit Clause {:#?} {:#?}", literal.handle, dl.unwrap());
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
                            // println!("Polarity {}", v);
                            return Some((
                                self.decision_levels.last().map_or(0, |&dl| dl + 1),
                                VariableAssignment::new(v, polarity),
                            ));
                        }
                    }
                };
            }
        }

        // smallest clause
        handle.map(|handle| {
            // println!("Smallest clause {}", handle);
            (
                self.decision_levels.last().map_or(0, |&dl| dl + 1),
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

    fn print_literal(&self, literal: &Literal) {
        if !literal.polarity {
            print!("¬");
        }
        print!("x_");
        print!("{}", literal.handle);
        print!(
            "_({},{}) ",
            self.variable_decision_levels[literal.handle]
                .map_or("None".to_owned(), |dl| format!("{}", dl)),
            match self.values[literal.handle] {
                Value::True => "T",
                Value::False => "F",
                Value::Unknown => "U",
            }
        );
    }

    fn print_clause(&self, clause: &Clause) {
        for literal in clause.iter() {
            self.print_literal(literal);
        }
        println!();
    }

    fn reassign_watched_literal(&mut self) -> Result<(), DecisionLevel> {
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
                            return Err(self.learn_clause(slot_key));
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
        Ok(())
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
            self.decision_levels.pop().map_or(0, |dl| dl),
            variable_assignment,
        ))
    }

    fn backtrack(&mut self, backtrack_decision_level: DecisionLevel) -> Solution {
        self.unit_clauses.clear();

        let mut backtrack_decision_level_ = backtrack_decision_level;

        let (decision_level, variable_assignment) = 'assignment: loop {
            let (decision_level, variable_assignment) = 'backtrack: loop {
                let (decision_level, variable_assignment) = if let Some(var) = self.backtrack_once()
                {
                    var
                } else {
                    // all variables exhausted
                    return Solution::UnSat;
                };

                if decision_level == backtrack_decision_level_
                    && (self.decision_levels.empty()
                        || self.decision_levels.last().map_or(0, |&dl| dl)
                            != backtrack_decision_level_)
                {
                    break 'backtrack (decision_level, variable_assignment);
                } else {
                    self.antecedents[variable_assignment.handle] = None;
                }
            };

            if variable_assignment.index == 0 {
                break 'assignment (decision_level, variable_assignment);
            } else {
                backtrack_decision_level_ = if decision_level == 0 {
                    decision_level
                } else {
                    decision_level - 1
                };
            }
        };

        // reached a variable with a remaining assignment, try the other truth value
        self.values[variable_assignment.handle] = variable_assignment.values[1];
        // self.values[variable_assignment.handle] =
        //     variable_assignment.values[variable_assignment.index];
        // push it back onto the top of the stack
        self.decisions.push(VariableAssignment {
            index: 1,
            ..variable_assignment
        });
        // self.decisions.push(variable_assignment);
        self.decision_levels.push(decision_level);
        self.variable_decision_levels[variable_assignment.handle] = Some(decision_level);

        Solution::Unknown
    }

    fn get_most_recent_decision_assignment(&self) -> Option<VariableAssignment> {
        let mut variable_assignment: Option<VariableAssignment> = None;
        let decision_level = *self.decision_levels.last()?;

        for va in self.decisions.iter() {
            if self.variable_decision_levels[va.handle] == Some(decision_level) {
                variable_assignment = Some(*va);
            } else {
                break;
            }
        }

        variable_assignment
    }

    fn decision_level_count(&self, clause: &Clause, decision_level: DecisionLevel) -> usize {
        clause
            .literals
            .iter()
            .filter(|&l| self.variable_decision_levels[l.handle] == Some(decision_level))
            .count()
    }

    fn conflict_analysis_last_uip(&self, clause_index: ClauseIndex) -> Clause {
        let mut clause: Vec<Literal> = vec![];

        let latest_decision_level = *self.decision_levels.last().unwrap();
        let latest_decision = self.get_most_recent_decision_assignment().unwrap();

        let mut literal_queue = self.clauses.get(&clause_index).unwrap().literals.clone();
        let mut visited_list = vec![];

        loop {
            if literal_queue.is_empty() {
                return Clause::new(clause);
            }

            let literal = literal_queue.remove(0);
            visited_list.push(literal.handle);
            if self.variable_decision_levels[literal.handle] == Some(latest_decision_level) {
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
                                .copied()
                                .collect::<Vec<_>>(),
                        );
                    }
                }
            } else {
                clause.push(literal);
            }
        }
    }

    fn conflict_analysis_first_uip(&self, clause_index: ClauseIndex) -> Clause {
        let mut clause = self.clauses.get(&clause_index).unwrap().clone();

        let latest_decision_level = *self.decision_levels.last().unwrap();

        let mut literal_queue = clause
            .literals
            .iter()
            .filter(|&l| self.variable_decision_levels[l.handle] == Some(latest_decision_level))
            .copied()
            .collect::<Vec<_>>();
        let mut visited_list = vec![];

        loop {
            if literal_queue.is_empty() {
                return clause;
            }

            if self.decision_level_count(&clause, latest_decision_level) == 1 {
                return clause;
            }

            let literal = literal_queue.remove(0);
            visited_list.push(literal.handle);
            match self.antecedents[literal.handle] {
                None => (),
                Some(slot_key) => {
                    let antecedent = &mut self.clauses.get(&slot_key).unwrap().literals.clone();
                    literal_queue.append(
                        &mut antecedent
                            .iter()
                            .filter(|&l| {
                                self.variable_decision_levels[l.handle]
                                    == Some(latest_decision_level)
                            })
                            .filter(|&&l| !visited_list.contains(&l.handle))
                            .copied()
                            .collect::<Vec<_>>(),
                    );
                    match resolve(&clause, self.clauses.get(&slot_key).unwrap()) {
                        None => (),
                        Some(resolvent) => {
                            if clause == resolvent {
                                return clause;
                            }
                            clause = resolvent;
                        }
                    }
                }
            }
        }
    }

    fn conflict_analysis(&self, clause_index: ClauseIndex) -> Clause {
        self.conflict_analysis_first_uip(clause_index)
    }

    fn learn_clause(&mut self, c: ClauseIndex) -> DecisionLevel {
        let learned_clause = self.conflict_analysis(c);

        let watched_literals = if learned_clause.len() == 1 {
            [learned_clause[0], learned_clause[0]] // unit clauses watch the only literal twice
        } else {
            let mut literals = learned_clause.literals.clone();
            literals.sort_by(|a, b| {
                self.variable_decision_levels[a.handle]
                    .map_or(usize::MAX, |decision_level| decision_level)
                    .partial_cmp(
                        &self.variable_decision_levels[b.handle]
                            .map_or(usize::MAX, |decision_level| decision_level),
                    )
                    .unwrap()
            });
            literals.reverse();

            [literals[0], literals[1]]
        };

        self.watched_literals.insert(watched_literals);

        let decision_level = *self.decision_levels.last().unwrap();

        // let decision_level = learned_clause
        //     .literals
        //     .iter()
        //     .map(|&l| self.variable_decision_levels[l.handle])
        //     .filter(|&l| l.is_some())
        //     .map(|l| l.unwrap())
        //     .min()
        //     .map_or(0, |dl| dl);

        let slot_key = self.clauses.insert(learned_clause);
        for literal in self.clauses.get(&slot_key).unwrap().iter() {
            if literal.polarity {
                self.positive_literal_clauses[literal.handle].push(slot_key);
            } else {
                self.negative_literal_clauses[literal.handle].push(slot_key);
            }
            self.variable_clauses[literal.handle].push(slot_key);
        }

        decision_level
        // a learned clause should have length = 1 after backtrack
        // backtracking which occurs after this will clear the stack anyway
        // if self.clause_length(&self.clauses.get(&slot_key).unwrap()) == 1 {
        //     self.unit_clauses.push(slot_key);
        // }
    }

    pub fn solve(&mut self) -> Solution {
        println!(
            "Solving for {} variables with {} clauses",
            self.variables.len(),
            self.clauses.len()
        );

        let unit_clause_slot_keys = self
            .clauses
            .iter()
            .items()
            .filter(|(_, c)| self.clause_length(c) == 1)
            .map(|(sk, _)| sk)
            .collect::<Vec<_>>();

        for slot_key in unit_clause_slot_keys {
            let clause = self.clauses.get(&slot_key).unwrap();
            let clause_length = self.clause_length(clause);

            if clause_length == 1 {
                let literal = &clause[0];
                self.antecedents[literal.handle] = Some(slot_key);
                let variable_assignment = VariableAssignment::new(literal.handle, literal.polarity);

                self.values[variable_assignment.handle] = variable_assignment.values[0];
                self.variable_decision_levels[variable_assignment.handle] = Some(0);
                self.decisions.push(variable_assignment);
                self.decision_levels.push(0);
            }

            match self.reassign_watched_literal() {
                Ok(_) => (),
                Err(_) => return Solution::UnSat,
            }
        }

        let mut i = 0;
        loop {
            if cfg!(debug_assertions) {
                self.assert_invariances();
            }

            i += 1;
            if i % 100_000 == 0 {
                println!(
                    "{}: Vars: {} / {} DL: {:#?}",
                    i,
                    self.variables.len() - self.decisions.len(),
                    self.variables.len(),
                    self.decision_levels.last()
                );
            }

            match self.reassign_watched_literal() {
                Ok(_) => {
                    if let Some((decision_level, var)) = self.next_unassigned() {
                        self.values[var.handle] = var.values[0];
                        self.variable_decision_levels[var.handle] = Some(decision_level);
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
                Err(decision_level) => match self.backtrack(decision_level) {
                    Solution::Sat => unreachable!("Backtrack found a solution"),
                    Solution::UnSat => return Solution::UnSat,
                    Solution::Unknown => (),
                },
            }
        }
    }

    fn assert_invariances(&self) {
        if self.decisions.len() != self.decision_levels.len() {
            unreachable!(
                "Decision misalignment! decisions: {}, decision levels: {}",
                self.decisions.len(),
                self.decision_levels.len()
            );
        }

        let mut dl_iter = self.decision_levels.iter();
        match dl_iter.next() {
            Some(mut dl) => {
                for dl_ in dl_iter {
                    if dl < dl_ {
                        unreachable!("Decision levels out of order! Decision level {} is a more recent decision than {}", dl, dl_);
                    }
                    dl = dl_;
                }
            }
            None => (),
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
    fn test_conflict_analysis_last_uip() -> Result<(), Box<dyn Error>> {
        let mut formula = Formula::new();

        formula.add_var();
        let v1 = formula.add_var();
        let v2 = formula.add_var();
        let v3 = formula.add_var();
        let v4 = formula.add_var();
        let v5 = formula.add_var();
        let v6 = formula.add_var();
        for _ in 7..21 {
            formula.add_var();
        }
        let v21 = formula.add_var();
        for _ in 22..31 {
            formula.add_var();
        }
        let v31 = formula.add_var();

        let c1 = vec![v1.literal(), v31.literal(), !v2.literal()];
        let c2 = vec![v1.literal(), !v3.literal()];
        let c3 = vec![v2.literal(), v3.literal(), v4.literal()];
        let c4 = vec![!v4.literal(), !v5.literal()];
        let c5 = vec![v21.literal(), !v4.literal(), !v6.literal()];
        let c6 = vec![v5.literal(), v6.literal()];

        let sk1 = formula.add_clause(c1);
        let sk2 = formula.add_clause(c2);
        let sk3 = formula.add_clause(c3);
        let sk4 = formula.add_clause(c4);
        let sk5 = formula.add_clause(c5);
        let sk6 = formula.add_clause(c6);

        let mut solver = Solver::new(formula);

        solver.values[v21.handle] = Value::False;
        solver.variable_decision_levels[v21.handle] = Some(2);
        solver.decision_levels.push(2);
        solver.decisions.push(VariableAssignment {
            handle: v21.handle,
            index: 0,
            values: [Value::False, Value::True],
        });

        solver.values[v31.handle] = Value::False;
        solver.variable_decision_levels[v31.handle] = Some(3);
        solver.decision_levels.push(3);
        solver.decisions.push(VariableAssignment {
            handle: v31.handle,
            index: 0,
            values: [Value::False, Value::True],
        });

        solver.values[v1.handle] = Value::False;
        solver.variable_decision_levels[v1.handle] = Some(5);
        solver.decision_levels.push(5);
        solver.decisions.push(VariableAssignment {
            handle: v1.handle,
            index: 0,
            values: [Value::False, Value::True],
        });

        solver.values[v2.handle] = Value::False;
        solver.antecedents[v2.handle] = Some(sk1);
        solver.variable_decision_levels[v2.handle] = Some(5);
        solver.decision_levels.push(5);
        solver.decisions.push(VariableAssignment {
            handle: v2.handle,
            index: 0,
            values: [Value::False, Value::True],
        });

        solver.values[v3.handle] = Value::False;
        solver.antecedents[v3.handle] = Some(sk2);
        solver.variable_decision_levels[v3.handle] = Some(5);
        solver.decision_levels.push(5);
        solver.decisions.push(VariableAssignment {
            handle: v3.handle,
            index: 0,
            values: [Value::False, Value::True],
        });

        solver.values[v4.handle] = Value::False;
        solver.antecedents[v4.handle] = Some(sk3);
        solver.variable_decision_levels[v4.handle] = Some(5);
        solver.decision_levels.push(5);
        solver.decisions.push(VariableAssignment {
            handle: v4.handle,
            index: 0,
            values: [Value::False, Value::True],
        });

        solver.values[v5.handle] = Value::False;
        solver.antecedents[v5.handle] = Some(sk4);
        solver.variable_decision_levels[v5.handle] = Some(5);
        solver.decision_levels.push(5);
        solver.decisions.push(VariableAssignment {
            handle: v5.handle,
            index: 0,
            values: [Value::False, Value::True],
        });

        solver.values[v6.handle] = Value::False;
        solver.antecedents[v6.handle] = Some(sk5);
        solver.variable_decision_levels[v6.handle] = Some(5);
        solver.decision_levels.push(5);
        solver.decisions.push(VariableAssignment {
            handle: v6.handle,
            index: 0,
            values: [Value::False, Value::True],
        });

        let learned_clause = solver.conflict_analysis_last_uip(sk6);

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

    #[test]
    fn test_conflict_analysis_first_uip() -> Result<(), Box<dyn Error>> {
        let mut formula = Formula::new();

        formula.add_var();
        let v1 = formula.add_var();
        let v2 = formula.add_var();
        let v3 = formula.add_var();
        let v4 = formula.add_var();
        let v5 = formula.add_var();
        let v6 = formula.add_var();
        for _ in 7..21 {
            formula.add_var();
        }
        let v21 = formula.add_var();
        for _ in 22..31 {
            formula.add_var();
        }
        let v31 = formula.add_var();

        let c1 = vec![v1.literal(), v31.literal(), !v2.literal()];
        let c2 = vec![v1.literal(), !v3.literal()];
        let c3 = vec![v2.literal(), v3.literal(), v4.literal()];
        let c4 = vec![!v4.literal(), !v5.literal()];
        let c5 = vec![v21.literal(), !v4.literal(), !v6.literal()];
        let c6 = vec![v5.literal(), v6.literal()];

        let sk1 = formula.add_clause(c1);
        let sk2 = formula.add_clause(c2);
        let sk3 = formula.add_clause(c3);
        let sk4 = formula.add_clause(c4);
        let sk5 = formula.add_clause(c5);
        let sk6 = formula.add_clause(c6);

        let mut solver = Solver::new(formula);

        solver.values[v21.handle] = Value::False;
        solver.variable_decision_levels[v21.handle] = Some(2);
        solver.decision_levels.push(2);
        solver.decisions.push(VariableAssignment {
            handle: v21.handle,
            index: 0,
            values: [Value::False, Value::True],
        });

        solver.values[v31.handle] = Value::False;
        solver.variable_decision_levels[v31.handle] = Some(3);
        solver.decision_levels.push(3);
        solver.decisions.push(VariableAssignment {
            handle: v31.handle,
            index: 0,
            values: [Value::False, Value::True],
        });

        solver.values[v1.handle] = Value::False;
        solver.variable_decision_levels[v1.handle] = Some(5);
        solver.decision_levels.push(5);
        solver.decisions.push(VariableAssignment {
            handle: v1.handle,
            index: 0,
            values: [Value::False, Value::True],
        });

        solver.values[v2.handle] = Value::False;
        solver.antecedents[v2.handle] = Some(sk1);
        solver.variable_decision_levels[v2.handle] = Some(5);
        solver.decision_levels.push(5);
        solver.decisions.push(VariableAssignment {
            handle: v2.handle,
            index: 0,
            values: [Value::False, Value::True],
        });

        solver.values[v3.handle] = Value::False;
        solver.antecedents[v3.handle] = Some(sk2);
        solver.variable_decision_levels[v3.handle] = Some(5);
        solver.decision_levels.push(5);
        solver.decisions.push(VariableAssignment {
            handle: v3.handle,
            index: 0,
            values: [Value::False, Value::True],
        });

        solver.values[v4.handle] = Value::False;
        solver.antecedents[v4.handle] = Some(sk3);
        solver.variable_decision_levels[v4.handle] = Some(5);
        solver.decision_levels.push(5);
        solver.decisions.push(VariableAssignment {
            handle: v4.handle,
            index: 0,
            values: [Value::False, Value::True],
        });

        solver.values[v5.handle] = Value::False;
        solver.antecedents[v5.handle] = Some(sk4);
        solver.variable_decision_levels[v5.handle] = Some(5);
        solver.decision_levels.push(5);
        solver.decisions.push(VariableAssignment {
            handle: v5.handle,
            index: 0,
            values: [Value::False, Value::True],
        });

        solver.values[v6.handle] = Value::False;
        solver.antecedents[v6.handle] = Some(sk5);
        solver.variable_decision_levels[v6.handle] = Some(5);
        solver.decision_levels.push(5);
        solver.decisions.push(VariableAssignment {
            handle: v6.handle,
            index: 0,
            values: [Value::False, Value::True],
        });

        let learned_clause = solver.conflict_analysis_first_uip(sk6);

        assert_eq!(
            learned_clause,
            Clause::new(vec![!v4.literal(), v21.literal()])
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
