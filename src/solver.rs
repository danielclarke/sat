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
            negated: false,
            variable: *self,
        }
    }
}

#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash)]
pub struct Literal {
    negated: bool,
    variable: Variable,
}

impl Literal {
    fn value(&self, value: Value) -> Value {
        if self.negated {
            !value
        } else {
            value
        }
    }
}

impl Not for Literal {
    type Output = Literal;

    fn not(self) -> <Self as Not>::Output {
        Literal {
            negated: !self.negated,
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
    fn new(handle: usize, negated: bool) -> Self {
        let values = if negated {
            [Value::False, Value::True]
        } else {
            [Value::True, Value::False]
        };
        Self {
            handle,
            index: 0,
            values,
        }
    }
}

pub struct Solver {
    variables: Vec<Variable>,
    clauses: Vec<Clause>,
    variable_clauses: Vec<Vec<usize>>,
    decisions: Stack<VariableAssignment>,
    decision_levels: Stack<DecisionLevel>,
    values: Vec<Value>,
    clause_values: Vec<Value>,
    clause_truth_variables: Vec<Option<usize>>,
    clause_lengths: Vec<usize>, // number of unassigned literals in the clause
}

impl Solver {
    pub fn new() -> Self {
        Self {
            variables: vec![],
            variable_clauses: vec![],
            values: vec![],
            decisions: Stack::new(),
            decision_levels: Stack::new(),
            clauses: vec![],
            clause_values: vec![],
            clause_truth_variables: vec![],
            clause_lengths: vec![],
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

    fn next_unassigned(&self) -> Option<(DecisionLevel, VariableAssignment)> {
        // unassigned variable search order:
        //   1. unit clause
        //   2. pure literal
        //   3. smallest clause

        let (mut handle, mut min_clause_length) = (None, None);
        for (c, &clause_length) in self.clause_lengths.iter().enumerate() {
            // unit clause propagation
            if clause_length == 1 {
                for literal in &self.clauses[c] {
                    if literal.value(self.values[literal.variable.handle]) == Value::Unknown {
                        let dl = self.decision_levels.last().map_or(None, |&dl| dl);
                        return Some((
                            dl,
                            VariableAssignment::new(literal.variable.handle, literal.negated),
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
                    let mut negated = None;
                    for &clause in clauses.iter() {
                        if self.clause_values[clause] == Value::Unknown {
                            for literal in self.clauses[clause].iter() {
                                if literal.variable.handle == v {
                                    match negated {
                                        None => negated = Some(literal.negated),
                                        Some(negated) => {
                                            if negated == literal.negated {
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
                    match negated {
                        None => (),
                        Some(negated) => {
                            return Some((
                                Some(self.decision_levels.len()),
                                VariableAssignment::new(v, negated),
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
        let mut acc = 0;
        for literal in clause {
            match literal.value(self.values[literal.variable.handle]) {
                Value::True => return 0,
                Value::False => (),
                Value::Unknown => acc += 1,
            }
        }
        acc
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

    fn check_satisfiability(&mut self) -> Solution {
        if let Some(&v) = self.decisions.last() {
            for &c in self.variable_clauses[v.handle].iter() {
                if self.clause_values[c] == Value::Unknown {
                    match self.eval_clause(&self.clauses[c]) {
                        Value::False => {
                            return Solution::UnSat;
                        }
                        Value::Unknown => {
                            self.clause_lengths[c] = self.clause_length(&self.clauses[c]);
                        }
                        Value::True => {
                            self.clause_values[c] = Value::True;
                            self.clause_truth_variables[c] = Some(v.handle);
                            self.clause_lengths[c] = self.clause_length(&self.clauses[c]);
                        }
                    }
                }
            }
        }

        for value in self.clause_values.iter() {
            match value {
                Value::False => unreachable!(),
                Value::Unknown => return Solution::Unknown,
                Value::True => (),
            }
        }

        Solution::Sat
    }

    fn backtrack_once(&mut self) -> Option<(DecisionLevel, VariableAssignment)> {
        let variable_assignment = if let Some(variable_assignment) = self.decisions.pop() {
            variable_assignment
        } else {
            // all variables exhausted
            return None;
        };

        self.values[variable_assignment.handle] = Value::Unknown;

        for &c in self.variable_clauses[variable_assignment.handle].iter() {
            // undo clause length changes from trying this assignment
            self.clause_lengths[c] = self.clause_length(&self.clauses[c]);
            if self.clause_truth_variables[c] == Some(variable_assignment.handle) {
                // undo clause value changes from trying this assignment
                self.clause_values[c] = Value::Unknown;
                self.clause_truth_variables[c] = None;
            }
        }

        Some((
            self.decision_levels.pop().map_or(None, |dl| dl),
            variable_assignment,
        ))
    }

    pub fn solve(&mut self) -> Solution {
        println!(
            "Solving for {} variables with {} clauses",
            self.variables.len(),
            self.clauses.len()
        );

        self.variable_clauses = vec![vec![]; self.variables.len()];

        for (i, clause) in self.clauses.iter().enumerate() {
            for literal in clause {
                self.variable_clauses[literal.variable.handle].push(i);
            }
        }

        self.values = vec![Value::Unknown; self.variables.len()];
        self.clause_values = vec![Value::Unknown; self.clauses.len()];
        self.clause_truth_variables = vec![None; self.clauses.len()];
        self.clause_lengths = self.clauses.iter().map(|c| c.len()).collect();

        self.decisions.reserve(self.variables.len());
        self.decision_levels.reserve(self.variables.len());

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
                    "{}: Vars: {} / {} Clauses: {} / {} DL: {:#?}",
                    i,
                    self.variables.len() - self.decisions.len(),
                    self.variables.len(),
                    self.clauses.len()
                        - self
                            .clause_values
                            .iter()
                            .filter(|&&v| v == Value::True)
                            .count(),
                    self.clauses.len(),
                    self.decision_levels.last().map_or(None, |&dl| dl)
                );
            }
            match self.check_satisfiability() {
                Solution::Sat => {
                    println!("Solved in Iterations: {}", i);
                    return Solution::Sat;
                }
                Solution::UnSat => {
                    let prior_decision_level = self.decision_levels.last().map_or(None, |&dl| dl);

                    let (decision_level, variable_assignment) = 'backtrack: loop {
                        let (decision_level, variable_assignment) =
                            if let Some(var) = self.backtrack_once() {
                                var
                            } else {
                                // all variables exhausted
                                println!("All variables exhausted, decision_level");
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
                                    println!("All variables exhausted, other assignment");
                                    return Solution::UnSat;
                                };

                            if variable_assignment.index == 0 {
                                break 'backtrack (decision_level, variable_assignment);
                            }
                        }
                    };

                    // let (decision_level, variable_assignment) = 'backtrack: loop {
                    //     let (decision_level, variable_assignment) =
                    //         if let Some(var) = self.backtrack_once() {
                    //             var
                    //         } else {
                    //             // all variables exhausted
                    //             println!("All variables exhausted, other assignment");
                    //             return Solution::UnSat;
                    //         };

                    //     if variable_assignment.index == 0 {
                    //         break 'backtrack (decision_level, variable_assignment);
                    //     }
                    // };

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
                        unreachable!("No next unassigned variable, yet unknown clauses!");
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
