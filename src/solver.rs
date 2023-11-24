use std::ops::Not;
use std::{error, fmt};

use crate::fixed_size_stack::FixedSizeStack;
use crate::slot_map::{SlotKey, SlotMap};

#[derive(Debug, PartialEq)]
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

    fn union(&mut self, clause: Clause) {
        let mut clause = clause;
        self.literals.append(&mut clause.literals);
        self.literals.sort();
        self.literals.dedup();
    }

    fn is_empty(&self) -> bool {
        self.literals.is_empty()
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

impl Not for Clause {
    type Output = Clause;

    fn not(self) -> <Self as Not>::Output {
        Clause {
            literals: self.literals.iter().map(|&l| !l).collect::<Vec<_>>(),
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

    // branching heuristic
    decay_factor: f32,
    conflict_learn_rate: f32,
    variable_branching_scores: Vec<f32>,

    // implication_vertices:
    watched_literals: SlotMap<[Literal; 2]>,
    unit_clauses: FixedSizeStack<ClauseIndex>,

    // learning
    visited: Vec<bool>,
    seen: Vec<bool>,
}

impl Solver {
    pub fn new(formula: Formula) -> Self {
        let mut formula = formula;

        // add a standalone unit clause to make backtracking simpler
        let v = formula.add_var();
        formula.add_clause(vec![v.literal()]);

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
            decay_factor: 0.95,
            conflict_learn_rate: 1.0,
            variable_branching_scores: vec![0.0; num_variables],
            antecedents,
            watched_literals,
            unit_clauses,
            visited: vec![false; num_variables],
            seen: vec![false; num_variables],
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
            if cfg!(debug_assertions) {
                if self.clause_length(self.clauses.get(&slot_key).unwrap()) > 1 {
                    self.print_clause(self.clauses.get(&slot_key).unwrap());
                    unreachable!("non unit clause in unit stack");
                }
                match self.eval_clause(self.clauses.get(&slot_key).unwrap()) {
                    // need to continue to avoid "false positive" unit clause which incorrectly triggers a DL backtrack
                    Value::True => continue,
                    Value::False => {
                        println!("Num unit clauses {}", self.unit_clauses.len());
                        self.print_clause(self.clauses.get(&slot_key).unwrap());
                        unreachable!("False unit clause not earlier caught");
                    }
                    Value::Unknown => (),
                }
            }

            for literal in self.clauses.get(&slot_key).unwrap().iter() {
                if literal.value(self.values[literal.handle]) == Value::Unknown {
                    self.antecedents[literal.handle] = Some(slot_key);
                    let dl = self.decision_levels.last().map_or(0, |&dl| dl);
                    return Some((
                        dl,
                        VariableAssignment::new(literal.handle, literal.polarity),
                    ));
                }
            }
        }

        let mut decision_variable_handle = None;
        let mut max_score = 0.0;
        for (handle, &score) in self.variable_branching_scores.iter().enumerate() {
            if self.values[handle] != Value::Unknown {
                continue;
            }
            if decision_variable_handle.is_none() || max_score < score {
                decision_variable_handle = Some(handle);
                max_score = score;
            }
        }

        decision_variable_handle.map(|decision_variable_handle| {
            (
                self.decision_levels.last().map_or(0, |&dl| dl + 1),
                VariableAssignment::new(decision_variable_handle, true),
            )
        })
    }

    fn clause_length(&self, clause: &Clause) -> usize {
        let mut count = 0;
        for literal in clause.iter() {
            match literal.value(self.values[literal.handle]) {
                Value::True => return 0,
                Value::False => (),
                Value::Unknown => count += 1,
            }
        }

        count
    }

    fn clause_length_and_value(&self, clause: &Clause) -> (usize, Value) {
        let mut count = 0;
        for literal in clause.iter() {
            match literal.value(self.values[literal.handle]) {
                Value::True => return (0, Value::True),
                Value::False => (),
                Value::Unknown => count += 1,
            }
        }

        (count, if count == 0 {Value::False} else {Value::Unknown}) 
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
            "_({},{},{},{}) ",
            self.variable_decision_levels[literal.handle]
                .map_or("None".to_owned(), |dl| format!("{}", dl)),
            match self.values[literal.handle] {
                Value::True => "T",
                Value::False => "F",
                Value::Unknown => "U",
            },
            if self.seen[literal.handle] { "s" } else { "." },
            if self.visited[literal.handle] {
                "v"
            } else {
                "."
            },
        );
    }

    fn print_clause(&self, clause: &Clause) {
        for literal in clause.iter() {
            self.print_literal(literal);
        }
        println!();
    }

    fn reassign_watched_literal(&mut self) -> Result<(), SlotKey> {
        if let Some(&va) = self.decisions.last() {
            let false_literal_clauses = match va.values[va.index] {
                Value::True => &self.negative_literal_clauses[va.handle],
                Value::False => &self.positive_literal_clauses[va.handle],
                Value::Unknown => unreachable!("Unknown value on decision stack"),
            };

            // iterate watching clauses and reassign the watched literal to an unset one
            for &slot_key in false_literal_clauses.iter() {
                let watched_literals = self.watched_literals.get(&slot_key).unwrap();
                let watched_literal_index = if va.handle == watched_literals[0].handle {
                    0
                } else if va.handle == watched_literals[1].handle {
                    1
                } else {
                    continue;
                };

                let clause = self.clauses.get(&slot_key).unwrap();

                match self.clause_length_and_value(clause) {
                    (0, Value::False) => {
                        return Err(slot_key);
                    }
                    (0, Value::True) => (),
                    (1, _) => {
                        self.unit_clauses.push(slot_key);
                    }
                    _ => {
                        for &l in clause.iter() {
                            if self.values[l.handle] == Value::Unknown
                                && l != watched_literals[0]
                                && l != watched_literals[1]
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

    fn check_satisfiability(&self, iteration: usize, num_clauses: usize) -> Solution {
        println!("Solver completed in {} iterations", iteration);
        println!("Clauses: {}", num_clauses);
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
        let (decision_level, variable_assignment) = 'backtrack: loop {
            let (decision_level, variable_assignment) = if let Some(var) = self.backtrack_once() {
                var
            } else {
                // all variables exhausted
                return Solution::UnSat;
            };

            if decision_level == backtrack_decision_level {
                break 'backtrack (decision_level, variable_assignment);
            } else {
                self.antecedents[variable_assignment.handle] = None;
            };
        };

        if decision_level == 0 {
            self.discover_unit_clauses();
            match self.unit_propagation() {
                Ok(_) => return Solution::Unknown,
                Err(_) => return Solution::UnSat,
            }
        }

        // reached a variable with a remaining assignment, try the other truth value
        self.values[variable_assignment.handle] =
            variable_assignment.values[variable_assignment.index];
        // push it back onto the top of the stack
        self.decisions.push(variable_assignment);

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

    fn conflict_analysis_last_uip(&mut self, clause_index: ClauseIndex) -> Clause {
        let mut clause: Vec<Literal> = vec![];

        let mut literal_queue = self.clauses.get(&clause_index).unwrap().literals.clone();

        let mut visited_to_clear: Vec<usize> = vec![];

        loop {
            if literal_queue.is_empty() {
                for l in visited_to_clear {
                    self.visited[l] = false;
                }
                return Clause::new(clause);
            }

            let literal = literal_queue.remove(0);
            visited_to_clear.push(literal.handle);
            self.visited[literal.handle] = true;
            match self.antecedents[literal.handle] {
                None => clause.push(literal),
                Some(antecedent) => {
                    let antecedent_clause =
                        &mut self.clauses.get(&antecedent).unwrap().literals.clone();
                    literal_queue.append(
                        &mut antecedent_clause
                            .iter()
                            .filter(|&&l| !self.visited[l.handle])
                            .copied()
                            .collect::<Vec<_>>(),
                    );
                }
            }
        }
    }

    fn conflict_analysis_first_uip(&mut self, clause_index: ClauseIndex) -> Clause {
        // iterate decision stack
        // replace the literal in the clause with the literals in antecedent
        // stop when there is only 1 literal at decision level in the clause

        let latest_decision_level = *self.decision_levels.last().unwrap();
        let mut clause = self
            .clauses
            .get(&clause_index)
            .unwrap()
            .literals
            .iter()
            .filter(|&l| self.variable_decision_levels[l.handle] != Some(0))
            .copied()
            .collect::<Vec<_>>();
        for literal in clause.iter() {
            if self.variable_decision_levels[literal.handle].is_none() {
                self.print_clause(&Clause::new(clause.clone()));
                unreachable!("unassigned variable in clause");
            }
            self.visited[literal.handle] = true;
        }

        for va in self.decisions.iter() {
            if clause
                .iter()
                .filter(|&l| self.variable_decision_levels[l.handle] == Some(latest_decision_level))
                .count()
                == 1
            {
                self.visited = vec![false; self.variables.len()];
                return Clause::new(clause);
            }

            if clause.iter().filter(|&l| l.handle == va.handle).count() == 0 {
                self.visited[va.handle] = true;
                continue;
            }
            match self.antecedents[va.handle] {
                None => {
                    if self.variable_decision_levels[va.handle] == Some(latest_decision_level) {
                        println!(
                            "latest_decision_level {} literal {}",
                            latest_decision_level, va.handle
                        );
                        self.print_clause(&Clause::new(clause.clone()));
                    }
                    unreachable!("too many decision level variables in clause")
                }
                Some(slot_key) => {
                    clause.retain(|&l| l.handle != va.handle);

                    let antecedent = self.clauses.get(&slot_key).unwrap();
                    for literal in antecedent.iter() {
                        if self.variable_decision_levels[literal.handle].is_none() {
                            self.print_clause(&Clause::new(clause.clone()));
                            unreachable!("unassigned variable in clause");
                        }
                        if !self.visited[literal.handle]
                            && self.variable_decision_levels[literal.handle] != Some(0)
                        {
                            clause.push(*literal);
                        }
                        self.visited[literal.handle] = true;
                    }
                }
            }
        }
        Clause::new(vec![]) // unsat
    }

    fn conflict_analysis(&mut self, clause_index: ClauseIndex) -> Clause {
        for score in self.variable_branching_scores.iter_mut() {
            *score *= self.decay_factor;
        }
        for literal in self.clauses.get(&clause_index).unwrap().iter() {
            self.variable_branching_scores[literal.handle] += self.conflict_learn_rate;
        }

        self.conflict_analysis_first_uip(clause_index)
    }

    fn learn_clause(&mut self, learned_clause: Clause) {
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

        if cfg!(debug_assertions) {
            if self.clause_length(&learned_clause) != 1 {
                println!("Learned clause: ");
                self.print_clause(&learned_clause);
                unreachable!("non unit learned clause");
            }
        }
        let slot_key = self.clauses.insert(learned_clause);
        for literal in self.clauses.get(&slot_key).unwrap().iter() {
            if literal.polarity {
                self.positive_literal_clauses[literal.handle].push(slot_key);
            } else {
                self.negative_literal_clauses[literal.handle].push(slot_key);
            }
            self.variable_clauses[literal.handle].push(slot_key);
        }

        self.unit_clauses.push(slot_key);
    }

    fn discover_unit_clauses(&mut self) {
        let unit_clause_slot_keys = self
            .clauses
            .iter()
            .items()
            .filter(|(_, c)| self.clause_length(c) == 1)
            .map(|(sk, _)| sk)
            .collect::<Vec<_>>();

        for slot_key in unit_clause_slot_keys {
            self.unit_clauses.push(slot_key);
        }
    }

    fn unit_propagation(&mut self) -> Result<(), SlotKey> {
        while let Some(slot_key) = self.unit_clauses.pop() {
            let clause = self.clauses.get(&slot_key).unwrap();
            match self.eval_clause(clause) {
                // need to continue to avoid "false positive" unit clause which incorrectly triggers a DL backtrack
                Value::True => continue,
                Value::False => {
                    println!("Num unit clauses {}", self.unit_clauses.len());
                    self.print_clause(clause);
                    unreachable!("False unit clause not earlier caught");
                }
                Value::Unknown => (),
            }

            match clause
                .iter()
                .find(|&l| self.values[l.handle] == Value::Unknown)
            {
                Some(literal) => {
                    self.antecedents[literal.handle] = Some(slot_key);
                    let dl = self.decision_levels.last().map_or(0, |&dl| dl);
                    let va = VariableAssignment::new(literal.handle, literal.polarity);

                    self.values[va.handle] = va.values[0];
                    self.variable_decision_levels[va.handle] = Some(dl);
                    self.decisions.push(va);
                    self.decision_levels.push(dl);
                }
                None => unreachable!("No unknown variables in unit clause"),
            }

            self.reassign_watched_literal()?;
        }
        Ok(())
    }

    pub fn solve(&mut self) -> Solution {
        println!(
            "Solving for {} variables with {} clauses",
            self.variables.len(),
            self.clauses.len()
        );

        self.discover_unit_clauses();

        match self.unit_propagation() {
            Ok(_) => (),
            Err(_) => return Solution::UnSat,
        }

        if cfg!(debug_assertions) {
            for clause in self.clauses.iter() {
                if self.clause_length(clause) == 1 {
                    match self.eval_clause(clause) {
                        Value::True => (),
                        Value::Unknown => (),
                        Value::False => {
                            self.print_clause(clause);
                            unreachable!("Unit clause not found during unit propagation");
                        }
                    }
                }
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
                    "{}: Vars: {} / {} Clauses: {} DL: {:#?}",
                    i,
                    self.variables.len() - self.decisions.len(),
                    self.variables.len(),
                    self.clauses.len(),
                    self.decision_levels.last()
                );
            }

            match self.next_unassigned() {
                Some((dl, va)) => {
                    self.values[va.handle] = va.values[0];
                    self.variable_decision_levels[va.handle] = Some(dl);
                    self.decisions.push(va);
                    self.decision_levels.push(dl);

                    match self.reassign_watched_literal() {
                        Ok(_) => (),
                        Err(slot_key) => {
                            let learned_clause = self.conflict_analysis(slot_key);
                            if learned_clause.is_empty() {
                                return Solution::UnSat;
                            }

                            let decision_level = if learned_clause.literals.len() == 1 {
                                0
                            } else {
                                let mut decision_levels = learned_clause
                                    .literals
                                    .iter()
                                    .filter_map(|&l| self.variable_decision_levels[l.handle])
                                    .collect::<Vec<_>>();
                                decision_levels.sort();
                                decision_levels.dedup();
                                decision_levels.reverse();
                                decision_levels
                                    .get(1)
                                    .map_or(*self.decision_levels.last().unwrap(), |&dl| dl)
                            };

                            self.unit_clauses.clear();

                            match self.backtrack(decision_level) {
                                Solution::Sat => unreachable!("Backtrack found a solution"),
                                Solution::UnSat => return Solution::UnSat,
                                Solution::Unknown => {
                                    // need to ensure that the learned clause is the top clause on the stack
                                    // to force the algorithm to make different decisions
                                    match self.reassign_watched_literal() {
                                        Ok(()) => {
                                            self.learn_clause(learned_clause);
                                        }
                                        Err(slot_key) => {
                                            print!("Back track conflict clause: ");
                                            let clause = self.clauses.get(&slot_key).unwrap();
                                            self.print_clause(clause);
                                            for literal in clause.iter() {
                                                for c in
                                                    self.variable_clauses[literal.handle].iter()
                                                {
                                                    self.print_clause(self.clauses.get(c).unwrap());
                                                }
                                            }
                                            println!("{:#?}", self.decisions.last().unwrap());
                                            unreachable!(
                                                "Backtracking lead to conflict {}",
                                                slot_key
                                            );
                                        }
                                    }
                                }
                            }
                        }
                    }
                }
                None => return self.check_satisfiability(i, self.clauses.len()),
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
        if let Some(mut dl) = dl_iter.next() {
            for dl_ in dl_iter {
                if dl < dl_ {
                    unreachable!("Decision levels out of order! Decision level {} is a more recent decision than {}", dl, dl_);
                }
                dl = dl_;
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
mod test_solutions {
    use super::*;
    use std::error::Error;

    #[test]
    fn test_unsat_formula() -> Result<(), Box<dyn Error>> {
        let mut formula = Formula::new();

        let v1 = formula.add_var();
        let v2 = formula.add_var();
        let v3 = formula.add_var();

        let c1 = vec![v1.literal(), v2.literal()];
        let c2 = vec![!v1.literal(), v2.literal()];
        let c3 = vec![v1.literal(), !v2.literal()];
        let c4 = vec![!v1.literal(), !v2.literal()];
        let c5 = vec![v3.literal()];

        let sk1 = formula.add_clause(c1);
        let sk2 = formula.add_clause(c2);
        let sk3 = formula.add_clause(c3);
        let sk4 = formula.add_clause(c4);
        // let sk5 = formula.add_clause(c5);

        let mut solver = Solver::new(formula);

        let solution = solver.solve();

        println!("v1: {:#?}", solver.value(&v1));
        println!("v2: {:#?}", solver.value(&v2));
        // println!("v3: {:#?}", solver.value(&v3));

        assert_eq!(solution, Solution::UnSat);

        Ok(())
    }
}

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
mod test_unit_propagation {
    use super::*;
    use std::error::Error;

    #[test]
    fn test_unit_propagation() -> Result<(), Box<dyn Error>> {
        let mut formula = Formula::new();

        let v1 = formula.add_var();
        let v2 = formula.add_var();
        let v3 = formula.add_var();

        let c1 = vec![v1.literal()];
        let c2 = vec![!v1.literal(), v2.literal()];
        let c3 = vec![!v3.literal()];

        let sk1 = formula.add_clause(c1);
        let sk2 = formula.add_clause(c2);
        let sk3 = formula.add_clause(c3);

        let mut solver = Solver::new(formula);
        solver.discover_unit_clauses();
        assert_eq!(solver.unit_propagation(), Ok(()));

        assert_eq!(solver.value(&v1), Value::True);
        assert_eq!(solver.value(&v2), Value::True);
        assert_eq!(solver.value(&v3), Value::False);

        assert_eq!(solver.next_unassigned(), None);

        Ok(())
    }

    #[test]
    fn test_unit_propagation_2() -> Result<(), Box<dyn Error>> {
        let mut formula = Formula::new();

        let v1 = formula.add_var();
        let v2 = formula.add_var();
        let v3 = formula.add_var();

        let c1 = vec![v1.literal()];
        let c2 = vec![!v2.literal(), v3.literal()];

        let sk1 = formula.add_clause(c1);
        let sk2 = formula.add_clause(c2);

        let mut solver = Solver::new(formula);
        solver.discover_unit_clauses();
        assert_eq!(solver.unit_propagation(), Ok(()));

        assert_eq!(solver.value(&v1), Value::True);
        assert_eq!(solver.value(&v2), Value::Unknown);
        assert_eq!(solver.value(&v3), Value::Unknown);

        assert_eq!(
            solver.next_unassigned(),
            Some((
                1,
                VariableAssignment {
                    handle: v2.handle,
                    index: 0,
                    values: [Value::False, Value::True],
                }
            ))
        );

        Ok(())
    }

    #[test]
    fn test_unit_propagation_3() -> Result<(), Box<dyn Error>> {
        let mut formula = Formula::new();

        let v1 = formula.add_var();
        let v2 = formula.add_var();
        let v3 = formula.add_var();

        let c1 = vec![v1.literal()];
        let c2 = vec![!v1.literal(), !v2.literal(), v3.literal()];

        let sk1 = formula.add_clause(c1);
        let sk2 = formula.add_clause(c2);

        let mut solver = Solver::new(formula);
        solver.discover_unit_clauses();

        assert_eq!(solver.watched_literals.get(&sk1).unwrap()[0], v1.literal());
        assert_eq!(solver.watched_literals.get(&sk2).unwrap()[0], !v1.literal());
        assert_eq!(solver.watched_literals.get(&sk2).unwrap()[1], !v2.literal());

        assert_eq!(solver.unit_propagation(), Ok(()));

        assert_eq!(solver.value(&v1), Value::True);
        assert_eq!(solver.value(&v2), Value::Unknown);
        assert_eq!(solver.value(&v3), Value::Unknown);

        assert_eq!(solver.watched_literals.get(&sk2).unwrap()[0], v3.literal());
        assert_eq!(solver.watched_literals.get(&sk2).unwrap()[1], !v2.literal());

        assert_eq!(
            solver.next_unassigned(),
            Some((
                1,
                VariableAssignment {
                    handle: v2.handle,
                    index: 0,
                    values: [Value::False, Value::True],
                }
            ))
        );

        assert_eq!(solver.reassign_watched_literal(), Ok(()));

        assert_eq!(solver.watched_literals.get(&sk2).unwrap()[0], v3.literal());
        assert_eq!(solver.watched_literals.get(&sk2).unwrap()[1], !v2.literal());

        Ok(())
    }

    #[test]
    fn test_unit_propagation_4() -> Result<(), Box<dyn Error>> {
        let mut formula = Formula::new();

        let v1 = formula.add_var();
        let v2 = formula.add_var();
        let v3 = formula.add_var();

        let c1 = vec![v1.literal(), v2.literal()];
        let c2 = vec![!v1.literal(), !v2.literal(), v3.literal()];
        let c3 = vec![!v1.literal(), v2.literal(), !v3.literal()];

        let sk1 = formula.add_clause(c1);
        let sk2 = formula.add_clause(c2);
        let sk3 = formula.add_clause(c3);

        let mut solver = Solver::new(formula);
        solver.discover_unit_clauses();
        assert_eq!(solver.unit_clauses.len(), 1);

        assert_eq!(solver.watched_literals.get(&sk1).unwrap()[0], v1.literal());
        assert_eq!(solver.watched_literals.get(&sk2).unwrap()[0], !v1.literal());
        assert_eq!(solver.watched_literals.get(&sk3).unwrap()[0], !v1.literal());

        assert_eq!(solver.unit_propagation(), Ok(()));

        assert_eq!(solver.value(&v1), Value::Unknown);
        assert_eq!(solver.value(&v2), Value::Unknown);
        assert_eq!(solver.value(&v3), Value::Unknown);

        let decision_level = 1;
        let va = VariableAssignment {
            handle: v1.handle,
            index: 0,
            values: [Value::True, Value::False],
        };

        assert_eq!(solver.next_unassigned(), Some((decision_level, va)));

        solver.values[v1.handle] = va.values[0];
        solver.variable_decision_levels[v1.handle] = Some(decision_level);
        solver.decisions.push(va);
        solver.decision_levels.push(decision_level);

        assert_eq!(solver.reassign_watched_literal(), Ok(()));

        assert_eq!(solver.value(&v1), Value::True);
        assert_eq!(solver.value(&v2), Value::Unknown);
        assert_eq!(solver.value(&v3), Value::Unknown);

        assert_eq!(solver.watched_literals.get(&sk1).unwrap()[0], v1.literal());
        assert_eq!(solver.watched_literals.get(&sk2).unwrap()[0], v3.literal());
        assert_eq!(solver.watched_literals.get(&sk3).unwrap()[0], v2.literal());

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

    #[test]
    fn test_conflict_analysis_() -> Result<(), Box<dyn Error>> {
        let mut formula = Formula::new();

        formula.add_var();
        let v1 = formula.add_var();
        let v2 = formula.add_var();
        let v3 = formula.add_var();
        let v4 = formula.add_var();
        let v5 = formula.add_var();
        let v6 = formula.add_var();
        let v7 = formula.add_var();
        let v8 = formula.add_var();
        let v9 = formula.add_var();

        let c1 = vec![!v2.literal(), !v3.literal(), !v4.literal()];
        let c2 = vec![!v3.literal(), !v5.literal(), !v6.literal()];
        let c3 = vec![v4.literal(), v6.literal(), v7.literal()];
        let c4 = vec![!v7.literal(), !v8.literal()];
        let c5 = vec![!v1.literal(), !v7.literal(), !v9.literal()];
        let c6 = vec![!v1.literal(), v8.literal(), v9.literal()];

        let sk1 = formula.add_clause(c1);
        let sk2 = formula.add_clause(c2);
        let sk3 = formula.add_clause(c3);
        let sk4 = formula.add_clause(c4);
        let sk5 = formula.add_clause(c5);
        let sk6 = formula.add_clause(c6);

        let mut solver = Solver::new(formula);

        let v = v1;
        let dl = 1;
        let va = VariableAssignment {
            handle: v.handle,
            index: 0,
            values: [Value::True, Value::False],
        };
        solver.values[va.handle] = va.values[0];
        solver.variable_decision_levels[va.handle] = Some(dl);
        solver.decision_levels.push(dl);
        solver.decisions.push(va);

        assert_eq!(solver.reassign_watched_literal(), Ok(()));
        assert!(solver.unit_clauses.empty());

        let v = v2;
        let dl = 2;
        let va = VariableAssignment {
            handle: v.handle,
            index: 0,
            values: [Value::True, Value::False],
        };
        solver.values[va.handle] = va.values[0];
        solver.variable_decision_levels[va.handle] = Some(dl);
        solver.decision_levels.push(dl);
        solver.decisions.push(va);

        assert_eq!(solver.reassign_watched_literal(), Ok(()));
        assert!(solver.unit_clauses.empty());

        let v = v3;
        let dl = 3;
        let va = VariableAssignment {
            handle: v.handle,
            index: 0,
            values: [Value::True, Value::False],
        };
        solver.values[va.handle] = va.values[0];
        solver.variable_decision_levels[va.handle] = Some(dl);
        solver.decision_levels.push(dl);
        solver.decisions.push(va);

        assert_eq!(solver.reassign_watched_literal(), Ok(()));
        assert_eq!(*solver.unit_clauses.last().unwrap(), sk1);

        match solver.next_unassigned() {
            Some((dl, va)) => {
                assert_eq!(dl, 3);
                assert_eq!(
                    va,
                    VariableAssignment {
                        handle: v4.handle,
                        index: 0,
                        values: [Value::False, Value::True]
                    }
                );
                solver.values[va.handle] = va.values[0];
                solver.variable_decision_levels[va.handle] = Some(dl);
                solver.decision_levels.push(dl);
                solver.decisions.push(va);
            }
            None => {
                assert!(false);
            }
        }

        // solver
        // .unit_clauses
        // .iter()
        // .for_each(|sk| solver.print_clause(solver.clauses.get(sk).unwrap()));

        assert_eq!(solver.reassign_watched_literal(), Ok(()));
        assert!(solver.unit_clauses.empty());

        let v = v5;
        let dl = 4;
        let va = VariableAssignment {
            handle: v.handle,
            index: 0,
            values: [Value::True, Value::False],
        };
        solver.values[va.handle] = va.values[0];
        solver.variable_decision_levels[va.handle] = Some(dl);
        solver.decision_levels.push(dl);
        solver.decisions.push(va);

        assert_eq!(solver.reassign_watched_literal(), Ok(()));
        assert_eq!(*solver.unit_clauses.last().unwrap(), sk2);

        match solver.next_unassigned() {
            Some((dl, va)) => {
                assert_eq!(dl, 4);
                assert_eq!(
                    va,
                    VariableAssignment {
                        handle: v6.handle,
                        index: 0,
                        values: [Value::False, Value::True]
                    }
                );
                solver.values[va.handle] = va.values[0];
                solver.variable_decision_levels[va.handle] = Some(dl);
                solver.decision_levels.push(dl);
                solver.decisions.push(va);
            }
            None => {
                assert!(false);
            }
        }

        assert_eq!(solver.reassign_watched_literal(), Ok(()));
        assert_eq!(*solver.unit_clauses.last().unwrap(), sk3);

        solver
            .unit_clauses
            .iter()
            .for_each(|sk| solver.print_clause(solver.clauses.get(sk).unwrap()));

        match solver.next_unassigned() {
            Some((dl, va)) => {
                assert_eq!(dl, 4);
                assert_eq!(
                    va,
                    VariableAssignment {
                        handle: v7.handle,
                        index: 0,
                        values: [Value::True, Value::False]
                    }
                );
                solver.values[va.handle] = va.values[0];
                solver.variable_decision_levels[va.handle] = Some(dl);
                solver.decision_levels.push(dl);
                solver.decisions.push(va);
            }
            None => {
                assert!(false);
            }
        }

        solver
            .unit_clauses
            .iter()
            .for_each(|sk| solver.print_clause(solver.clauses.get(sk).unwrap()));

        assert_eq!(solver.reassign_watched_literal(), Ok(()));

        solver
            .unit_clauses
            .iter()
            .for_each(|sk| solver.print_clause(solver.clauses.get(sk).unwrap()));

        // assert_eq!(*solver.unit_clauses.last().unwrap(), sk4);

        match solver.next_unassigned() {
            Some((dl, va)) => {
                assert_eq!(dl, 4);
                // assert_eq!(
                //     va,
                //     VariableAssignment {
                //         handle: v8.handle,
                //         index: 0,
                //         values: [Value::False, Value::True]
                //     }
                // );
                solver.values[va.handle] = va.values[0];
                solver.variable_decision_levels[va.handle] = Some(dl);
                solver.decision_levels.push(dl);
                solver.decisions.push(va);
            }
            None => {
                assert!(false);
            }
        }

        assert_eq!(solver.reassign_watched_literal(), Ok(()));
        assert_eq!(*solver.unit_clauses.last().unwrap(), sk6);

        solver
            .unit_clauses
            .iter()
            .for_each(|sk| solver.print_clause(solver.clauses.get(sk).unwrap()));

        match solver.next_unassigned() {
            Some((dl, va)) => {
                assert_eq!(dl, 4);
                // assert_eq!(
                //     va,
                //     VariableAssignment {
                //         handle: v9.handle,
                //         index: 0,
                //         values: [Value::True, Value::False]
                //     }
                // );
                solver.values[va.handle] = va.values[0];
                solver.variable_decision_levels[va.handle] = Some(dl);
                solver.decision_levels.push(dl);
                solver.decisions.push(va);
            }
            None => {
                assert!(false);
            }
        }

        solver
            .unit_clauses
            .iter()
            .for_each(|sk| solver.print_clause(solver.clauses.get(sk).unwrap()));

        match solver.reassign_watched_literal() {
            Ok(()) => assert!(false),
            Err(slot_key) => {
                // assert_eq!(slot_key, sk5);

                let learned_clause = solver.conflict_analysis_last_uip(slot_key);

                learned_clause
                    .iter()
                    .for_each(|l| print!("{:#?} ", solver.antecedents[l.handle]));

                assert_eq!(
                    learned_clause,
                    Clause::new(vec![
                        !v1.literal(),
                        !v2.literal(),
                        !v3.literal(),
                        !v5.literal()
                    ])
                );

                let learned_clause = solver.conflict_analysis_first_uip(slot_key);

                learned_clause
                    .iter()
                    .for_each(|l| print!("{:#?} ", solver.antecedents[l.handle]));

                assert_eq!(
                    learned_clause,
                    Clause::new(vec![!v1.literal(), !v7.literal()])
                );
            }
        }

        Ok(())
    }
}
