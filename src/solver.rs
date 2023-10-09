use std::ops::Not;

struct Stack<T> {
    top: usize,
    stack: Vec<Option<T>>,
}

impl<T> Stack<T>
where
    T: Clone,
{
    fn new() -> Self {
        Self {
            top: 0,
            stack: Vec::new(),
        }
    }

    fn reserve(&mut self, capacity: usize) {
        self.stack = vec![None; capacity];
    }

    fn clear(&mut self) {
        self.stack = vec![None; self.stack.len()];
        self.top = 0;
    }

    fn push(&mut self, item: T) {
        self.stack[self.top] = Some(item);
        self.top += 1;
    }

    fn pop(&mut self) -> Option<T> {
        if self.top == 0 {
            return None;
        }
        self.top -= 1;
        self.stack[self.top].take()
    }

    fn last(&self) -> Option<&T> {
        if self.top == 0 {
            return None;
        }
        if let Some(last) = &self.stack[self.top - 1] {
            Some(last)
        } else {
            None
        }
    }

    fn len(&self) -> usize {
        self.top
    }
}

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
    pub fn literal(&self) -> Literal {
        Literal {
            polarity: true,
            variable: *self,
        }
    }
}

#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash)]
pub struct Literal {
    polarity: bool,
    variable: Variable,
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
            variable: self.variable,
        }
    }
}

type Clause = Vec<Literal>;
type DecisionLevel = Option<usize>;

#[derive(Copy, Clone)]
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
    clauses: Vec<Clause>,

    // lookup
    // variable map to clause
    variable_clauses: Vec<Vec<usize>>,
    // variable map to clause where the literal is positive
    positive_literal_clauses: Vec<Vec<usize>>,
    // variable map to clause where the literal is negative
    negative_literal_clauses: Vec<Vec<usize>>,

    // search
    decisions: Stack<VariableAssignment>,
    decision_levels: Stack<DecisionLevel>,

    // state
    values: Vec<Value>,
    watched_literals: Vec<[Literal; 2]>,
    unit_clauses: Stack<usize>,
}

impl Solver {
    pub fn new() -> Self {
        Self {
            variables: vec![],
            variable_clauses: vec![],
            positive_literal_clauses: vec![],
            negative_literal_clauses: vec![],
            values: vec![],
            decisions: Stack::new(),
            decision_levels: Stack::new(),
            clauses: vec![],
            watched_literals: vec![],
            unit_clauses: Stack::new(),
        }
    }

    pub fn add_var(&mut self) -> Variable {
        let var = Variable {
            handle: self.variables.len(),
        };
        self.variables.push(var);
        var
    }

    pub fn add_clause(&mut self, clause: Clause) {
        self.clauses.push(clause);
    }

    pub fn value(&self, variable: &Variable) -> Value {
        self.values[variable.handle]
    }

    fn next_unassigned(&mut self) -> Option<(DecisionLevel, VariableAssignment)> {
        // unassigned variable search order:
        //   1. unit clause
        //   2. pure literal
        //   3. smallest clause

        while let Some(c) = self.unit_clauses.pop() {
            match self.eval_clause(&self.clauses[c]) {
                // need to continue to avoid "false positive" unit clause which incorrectly triggers a DL backtrack
                Value::True => continue,
                Value::False => unreachable!("False clause not earlier caught"),
                Value::Unknown => (),
            }

            for literal in &self.clauses[c] {
                if literal.value(self.values[literal.variable.handle]) == Value::Unknown {
                    let dl = self.decision_levels.last().map_or(None, |&dl| dl);
                    return Some((
                        dl,
                        VariableAssignment::new(literal.variable.handle, literal.polarity),
                    ));
                }
            }
        }

        let (mut handle, mut min_clause_length) = (None, None);
        for (c, clause) in self.clauses.iter().enumerate() {
            // unit clause propagation
            let clause_length = self.clause_length(clause);

            if clause_length == 0 {
                continue;
            }

            if clause_length == 1 {
                match self.eval_clause(&self.clauses[c]) {
                    // need to continue to avoid "false positive" unit clause which incorrectly triggers a DL backtrack
                    Value::True => continue,
                    Value::False => unreachable!("False clause not earlier caught"),
                    Value::Unknown => (),
                }

                for literal in &self.clauses[c] {
                    if literal.value(self.values[literal.variable.handle]) == Value::Unknown {
                        let dl = self.decision_levels.last().map_or(None, |&dl| dl);
                        return Some((
                            dl,
                            VariableAssignment::new(literal.variable.handle, literal.polarity),
                        ));
                    }
                }
            }

            // cache the smallest clause encountered
            match (handle, min_clause_length) {
                (None, None) => {
                    for literal in &self.clauses[c] {
                        if literal.value(self.values[literal.variable.handle]) == Value::Unknown {
                            (handle, min_clause_length) =
                                (Some(literal.variable.handle), Some(clause_length));
                            break;
                        }
                    }
                }
                (Some(_), Some(min_clause_length_)) => {
                    if clause_length < min_clause_length_ {
                        for literal in &self.clauses[c] {
                            if literal.value(self.values[literal.variable.handle]) == Value::Unknown
                            {
                                (handle, min_clause_length) =
                                    (Some(literal.variable.handle), Some(clause_length));
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
                        if self.eval_clause(&self.clauses[clause]) == Value::Unknown {
                            for literal in self.clauses[clause].iter() {
                                if literal.variable.handle == v {
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
                            return Some((
                                Some(self.decision_levels.len()),
                                VariableAssignment::new(v, polarity),
                            ));
                        }
                    }
                };
            }
        }

        // smallest clause
        handle.map(|handle| {
            (
                Some(self.decision_levels.len()),
                VariableAssignment::new(handle, false),
            )
        })
    }

    fn clause_length(&self, clause: &Clause) -> usize {
        clause
            .iter()
            .filter(|l| self.values[l.variable.handle] == Value::Unknown)
            .count()
    }

    fn eval_clause(&self, clause: &Clause) -> Value {
        let mut acc = Value::False;
        for literal in clause {
            acc = Value::or(acc, literal.value(self.values[literal.variable.handle]));
            if acc == Value::True {
                return Value::True;
            }
        }
        acc
    }

    fn print_clause(&self, clause: &Clause) {
        for literal in clause {
            println!(
                "Literal Value {} {:#?}",
                literal.variable.handle,
                literal.value(self.values[literal.variable.handle])
            );
        }
    }

    fn reassign_watched_literal(&mut self) -> Solution {
        if let Some(&va) = self.decisions.last() {
            let false_literal_clauses = match va.values[va.index] {
                Value::True => &self.negative_literal_clauses[va.handle],
                Value::False => &self.positive_literal_clauses[va.handle],
                Value::Unknown => unreachable!("Unknown value on decision stack"),
            };

            // iterate watching clauses and reassign the watched literal to an unset one
            for &c in false_literal_clauses.iter() {
                let watched_literal_index =
                    if va.handle == self.watched_literals[c][0].variable.handle {
                        0
                    } else if va.handle == self.watched_literals[c][1].variable.handle {
                        1
                    } else {
                        continue;
                    };

                match self.clause_length(&self.clauses[c]) {
                    0 => {
                        if self.eval_clause(&self.clauses[c]) == Value::False {
                            return Solution::UnSat;
                        }
                    }
                    1 => {
                        if self.eval_clause(&self.clauses[c]) == Value::Unknown {
                            self.unit_clauses.push(c);
                        }
                    }
                    _ => {
                        for &l in self.clauses[c].iter() {
                            if self.values[l.variable.handle] == Value::Unknown
                                && l != self.watched_literals[c][0]
                                && l != self.watched_literals[c][1]
                            {
                                // replace the watched literal
                                self.watched_literals[c][watched_literal_index] = l;
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
            .fold(Value::True, |acc, v| Value::and(acc, v))
        {
            Value::True => Solution::Sat,
            Value::False => Solution::UnSat,
            Value::Unknown => Solution::Unknown,
        }
    }

    fn backtrack_once(&mut self) -> Option<(DecisionLevel, VariableAssignment)> {
        let variable_assignment = if let Some(variable_assignment) = self.decisions.pop() {
            variable_assignment
        } else {
            // all variables exhausted
            return None;
        };

        self.values[variable_assignment.handle] = Value::Unknown;

        Some((
            self.decision_levels.pop().map_or(None, |dl| dl),
            variable_assignment,
        ))
    }

    fn init(&mut self) {
        self.variable_clauses = vec![vec![]; self.variables.len()];
        self.positive_literal_clauses = vec![vec![]; self.variables.len()];
        self.negative_literal_clauses = vec![vec![]; self.variables.len()];

        for (i, clause) in self.clauses.iter().enumerate() {
            for literal in clause {
                self.variable_clauses[literal.variable.handle].push(i);
                if literal.polarity {
                    self.positive_literal_clauses[literal.variable.handle].push(i);
                } else {
                    self.negative_literal_clauses[literal.variable.handle].push(i);
                }
            }
        }

        self.values = vec![Value::Unknown; self.variables.len()];
        self.watched_literals = self
            .clauses
            .iter()
            .map(|c| {
                if c.len() == 1 {
                    [c[0], c[0]] // unit clauses watch the only literal twice
                } else {
                    [c[0], c[1]]
                }
            })
            .collect();

        self.decisions.reserve(self.variables.len());
        self.decision_levels.reserve(self.variables.len());
        self.unit_clauses.reserve(self.clauses.len());
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
                    self.decision_levels.last().map_or(None, |&dl| dl)
                );
            }
            match self.reassign_watched_literal() {
                Solution::Sat => {
                    println!("Solved in Iterations: {}", i);
                    return Solution::Sat;
                }
                Solution::UnSat => {
                    self.unit_clauses.clear();

                    let prior_decision_level = self.decision_levels.last().map_or(None, |&dl| dl);

                    let (decision_level, variable_assignment) = 'backtrack: loop {
                        let (decision_level, variable_assignment) =
                            if let Some(var) = self.backtrack_once() {
                                var
                            } else {
                                // all variables exhausted
                                println!("All backtrack variables exhausted, decision_level");
                                return Solution::UnSat;
                            };

                        // go to the first decision with the same decision level
                        if self.decision_levels.last().map_or(None, |&dl| dl)
                            != prior_decision_level
                            || self.decision_levels.len() == 0
                        {
                            break 'backtrack (decision_level, variable_assignment);
                        }
                    };

                    let (decision_level, variable_assignment) = if variable_assignment.index == 0 {
                        (decision_level, variable_assignment)
                    } else {
                        'backtrack: loop {
                            let (decision_level, variable_assignment) =
                                if let Some(var) = self.backtrack_once() {
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
                }
                Solution::Unknown => {
                    if let Some((decision_level, var)) = self.next_unassigned() {
                        self.values[var.handle] = var.values[0];
                        self.decisions.push(var);
                        self.decision_levels.push(decision_level);
                    } else {
                        return self.check_satisfiability();
                    };
                }
            }
        }
    }
}

#[cfg(test)]
mod test_stack {
    use super::*;
    use std::error::Error;

    #[test]
    fn test_stack() -> Result<(), Box<dyn Error>> {
        let mut stack = Stack::new();
        stack.reserve(5);
        stack.push(0);
        stack.push(1);

        assert_eq!(stack.len(), 2);
        assert_eq!(stack.pop(), Some(1));
        assert_eq!(stack.len(), 1);
        assert_eq!(stack.last(), Some(&0));

        stack.push(2);
        stack.push(3);

        assert_eq!(stack.pop(), Some(3));
        assert_eq!(stack.last(), Some(&2));

        Ok(())
    }
}
