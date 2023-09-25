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

pub struct Solver {
    variables: Vec<Variable>,
    values: Vec<Value>,
    var_search_stack: Stack<usize>,
    clauses: Vec<Clause>,
}

impl Solver {
    pub fn new() -> Self {
        Self {
            variables: vec![],
            values: vec![],
            var_search_stack: Stack::new(),
            clauses: vec![],
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

    fn next_unassigned(&self) -> Option<usize> {
        for (i, v) in self.values.iter().enumerate() {
            if *v == Value::Unknown {
                return Some(i);
            }
        }
        None
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

    fn check_satisfiability(&mut self) -> Solution {
        let mut acc = Value::True;
        for (i, clause) in self.clauses.iter().enumerate() {
            match self.eval_clause(clause) {
                Value::False => {
                    return Solution::UnSat;
                }
                Value::Unknown => acc = Value::and(acc, Value::Unknown),
                Value::True => acc = Value::and(acc, Value::True),
            }
        }
        match acc {
            Value::False => return Solution::UnSat,
            Value::Unknown => return Solution::Unknown,
            Value::True => return Solution::Sat,
        }
    }

    pub fn solve(&mut self) -> Solution {
        println!(
            "Solving for {} variables with {} clauses",
            self.variables.len(),
            self.clauses.len()
        );

        self.values = vec![Value::Unknown; self.variables.len()];

        self.var_search_stack.reserve(self.variables.len());

        let unassigned = if let Some(var) = self.next_unassigned() {
            var
        } else {
            return Solution::Sat;
        };

        self.values[unassigned] = Value::True;
        self.var_search_stack.push(unassigned);

        let mut i = 0;
        loop {
            i += 1;
            if i % 10000 == 0 {
                println!(
                    "Vars set: {} / {}",
                    self.var_search_stack.len(),
                    self.variables.len()
                );
            }
            match self.check_satisfiability() {
                Solution::Sat => return Solution::Sat,
                Solution::UnSat => {
                    let mut value_index = if let Some(&value_index) = self.var_search_stack.last() {
                        value_index
                    } else {
                        // all variables exhausted
                        return Solution::UnSat;
                    };

                    let mut value = self.values[value_index];
                    match value {
                        Value::True => self.values[value_index] = Value::False,
                        Value::False => {
                            // backtrack until reaching a variable assigned true
                            while value == Value::False {
                                self.values[value_index] = Value::Unknown;
                                self.var_search_stack.pop();
                                value_index =
                                    if let Some(&value_index) = self.var_search_stack.last() {
                                        value_index
                                    } else {
                                        return Solution::UnSat;
                                    };

                                value = self.values[value_index];
                            }
                            // try the other truth value
                            self.values[value_index] = Value::False;
                        }
                        Value::Unknown => unreachable!(),
                    }
                }
                Solution::Unknown => {
                    if let Some(var) = self.next_unassigned() {
                        self.values[var] = Value::True;
                        self.var_search_stack.push(var);
                    } else {
                        return Solution::Sat;
                    };
                }
            }
        }
    }
}

#[cfg(test)]
mod tests {
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
