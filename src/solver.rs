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
            stack: vec![],
        }
    }

    fn reserve(&mut self, capacity: usize) {
        self.stack = vec![None; capacity];
    }

    fn clear(&mut self) {
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

type Generation = usize;

#[derive(Debug, Clone, Copy)]
pub struct SlotKey {
    index: usize,
    generation: Generation,
}

struct SlotMap<T> {
    data: Vec<T>,
    generations: Vec<Generation>,
    empty: Vec<bool>,
    empty_slot_stack: Vec<usize>,
}

impl<T> SlotMap<T>
where
    T: Clone,
{
    fn new() -> Self {
        Self {
            data: vec![],
            generations: vec![],
            empty: vec![],
            empty_slot_stack: vec![],
        }
    }

    fn get(&self, key: &SlotKey) -> Option<&T> {
        if self.generations[key.index] != key.generation {
            return None;
        }

        Some(&self.data[key.index])
    }

    fn get_mut(&mut self, key: &SlotKey) -> Option<&mut T> {
        if self.generations[key.index] != key.generation {
            return None;
        }

        Some(&mut self.data[key.index])
    }

    fn delete(&mut self, key: &SlotKey) {
        if self.generations[key.index] != key.generation {
            return;
        }

        self.generations[key.index] += 1;
        self.empty[key.index] = true;
        self.empty_slot_stack.push(key.index);
    }

    fn insert(&mut self, value: T) -> SlotKey {
        let index = self.empty_slot_stack.pop();

        match index {
            Some(index) => {
                self.data[index] = value;
                self.empty[index] = false;
                SlotKey {
                    index,
                    generation: self.generations[index],
                }
            }
            None => {
                self.data.push(value);
                self.generations.push(0);
                self.empty.push(false);

                SlotKey {
                    index: self.data.len() - 1,
                    generation: self.generations[self.data.len() - 1],
                }
            }
        }
    }

    fn len(&self) -> usize {
        self.empty.iter().filter(|&&empty| !empty).count()
    }

    fn iter(&self) -> SlotMapIterator<T> {
        SlotMapIterator {
            slot_map: self,
            index: 0,
        }
    }
}

struct SlotMapIterator<'a, T> {
    slot_map: &'a SlotMap<T>,
    index: usize,
}

impl<'a, T> SlotMapIterator<'a, T> {
    fn items(&'a mut self) -> SlotMapEnumerator<'a, T> {
        SlotMapEnumerator {
            slot_map_iterator: self,
        }
    }
}

impl<'a, T> Iterator for SlotMapIterator<'a, T> {
    type Item = &'a T;

    fn next(&mut self) -> Option<Self::Item> {
        if self.index < self.slot_map.data.len() {
            while self.slot_map.empty[self.index] {
                self.index += 1;
                if self.slot_map.data.len() <= self.index {
                    return None;
                }
            }
            let result = Some(&self.slot_map.data[self.index]);
            self.index += 1;
            result
        } else {
            None
        }
    }
}

struct SlotMapEnumerator<'a, T> {
    slot_map_iterator: &'a mut SlotMapIterator<'a, T>,
}

impl<'a, T> Iterator for SlotMapEnumerator<'a, T> {
    type Item = (SlotKey, &'a T);

    fn next(&mut self) -> Option<Self::Item> {
        let n = self.slot_map_iterator.next();

        match n {
            None => return None,
            Some(v) => {
                let generation =
                    self.slot_map_iterator.slot_map.generations[self.slot_map_iterator.index - 1];
                return Some((
                    SlotKey {
                        index: self.slot_map_iterator.index - 1,
                        generation,
                    },
                    v,
                ));
            }
        }
    }
}

#[derive(Clone)]
struct AdjacencySubList {
    data: Vec<usize>,
}

impl AdjacencySubList {
    fn new() -> Self {
        Self { data: vec![] }
    }
    fn get(&self, index: usize) -> Option<usize> {
        self.data.iter().find(|&&x| x == index).copied()
    }
    fn push(&mut self, value: usize) {
        self.data.push(value);
    }
    fn clear(&mut self) {
        self.data.clear();
    }
}

struct AdjacencyList {
    data: Vec<AdjacencySubList>,
}

impl AdjacencyList {
    fn new() -> Self {
        Self { data: vec![] }
    }

    fn reserve(&mut self, capacity: usize) {
        self.data = vec![AdjacencySubList::new(); capacity];
    }

    fn clear(&mut self, index: usize) {
        self.data[index].clear();
    }

    fn push(&mut self, index: usize, value: usize) {
        self.data[index].push(value)
    }

    fn get(&self, index: usize, sub_index: usize) -> Option<usize> {
        match self.data.get(index) {
            None => None,
            Some(asl) => asl.get(sub_index),
        }
    }
}

impl std::ops::Index<usize> for AdjacencyList {
    type Output = AdjacencySubList;

    fn index(&self, index: usize) -> &Self::Output {
        &self.data[index]
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
    clauses: SlotMap<Clause>,

    // lookup
    // variable map to clause
    variable_clauses: Vec<Vec<ClauseIndex>>,
    // variable map to clause where the literal is positive
    positive_literal_clauses: Vec<Vec<ClauseIndex>>,
    // variable map to clause where the literal is negative
    negative_literal_clauses: Vec<Vec<ClauseIndex>>,

    // search
    decisions: Stack<VariableAssignment>,
    decision_levels: Stack<DecisionLevel>,

    // state
    values: Vec<Value>,
    variable_decision_levels: Vec<DecisionLevel>,
    antecedants: Vec<Antecedant>,
    implication_vertices: AdjacencyList,

    // implication_vertices:
    watched_literals: SlotMap<[Literal; 2]>,
    unit_clauses: Stack<ClauseIndex>,
}

impl Solver {
    pub fn new() -> Self {
        Self {
            variables: vec![],
            clauses: SlotMap::new(),
            variable_clauses: vec![],
            positive_literal_clauses: vec![],
            negative_literal_clauses: vec![],
            decisions: Stack::new(),
            decision_levels: Stack::new(),
            values: vec![],
            variable_decision_levels: vec![],
            antecedants: vec![],
            implication_vertices: AdjacencyList::new(),
            watched_literals: SlotMap::new(),
            unit_clauses: Stack::new(),
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

        while let Some(c) = self.unit_clauses.pop() {
            match self.eval_clause(self.clauses.get(&c).unwrap()) {
                // need to continue to avoid "false positive" unit clause which incorrectly triggers a DL backtrack
                Value::True => continue,
                Value::False => unreachable!("False clause not earlier caught"),
                Value::Unknown => (),
            }

            for literal in self.clauses.get(&c).unwrap().iter() {
                if literal.value(self.values[literal.handle]) == Value::Unknown {
                    self.antecedants[literal.handle] = Some(c);
                    let dl = self.decision_levels.last().and_then(|&dl| dl);
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
                        self.antecedants[literal.handle] = Some(slot_key);
                        let dl = self.decision_levels.last().and_then(|&dl| dl);
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
            print!("{} ", literal.handle,)

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
            for &c in false_literal_clauses.iter() {
                let watched_literal_index =
                    if va.handle == self.watched_literals.get(&c).unwrap()[0].handle {
                        0
                    } else if va.handle == self.watched_literals.get(&c).unwrap()[1].handle {
                        1
                    } else {
                        continue;
                    };

                match self.clause_length(self.clauses.get(&c).unwrap()) {
                    0 => {
                        if self.eval_clause(self.clauses.get(&c).unwrap()) == Value::False {
                            self.learn_clause(c);
                            return Solution::UnSat;
                        }
                    }
                    1 => {
                        if self.eval_clause(self.clauses.get(&c).unwrap()) == Value::Unknown {
                            self.unit_clauses.push(c);
                        }
                    }
                    _ => {
                        for &l in self.clauses.get(&c).unwrap().iter() {
                            if self.values[l.handle] == Value::Unknown
                                && l != self.watched_literals.get(&c).unwrap()[0]
                                && l != self.watched_literals.get(&c).unwrap()[1]
                            {
                                // replace the watched literal
                                self.watched_literals.get_mut(&c).unwrap()[watched_literal_index] =
                                    l;
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

        self.antecedants[variable_assignment.handle] = None;

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

        Solution::Unknown
    }

    fn conflict_analysis(&self, clause_index: ClauseIndex) -> Clause {
        let mut clause = self.clauses.get(&clause_index).unwrap().clone();

        let mut literal_queue = clause.literals.clone();
        let mut visited_list = vec![];

        loop {
            if literal_queue.is_empty() {
                return clause;
            }

            let literal = literal_queue.remove(0);

            if self.variable_decision_levels[literal.handle]
                == *self.decision_levels.last().unwrap()
            {
                visited_list.push(literal.handle);
                match self.antecedants[literal.handle] {
                    None => (),
                    Some(antecedant) => {
                        let antecedant_clause =
                            &mut self.clauses.get(&antecedant).unwrap().literals.clone();
                        literal_queue.append(
                            &mut antecedant_clause
                                .iter()
                                .filter(|&&l| !visited_list.contains(&l.handle))
                                .map(|&l| l)
                                .collect::<Vec<_>>(),
                        );
                        match resolve(&clause, &self.clauses.get(&antecedant).unwrap()) {
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
    }

    fn learn_clause(&mut self, c: ClauseIndex) {
        let learned_clause = self.conflict_analysis(c);
        let watched_literals = if learned_clause.len() == 1 {
            [learned_clause[0], learned_clause[0]] // unit clauses watch the only literal twice
        } else {
            let mut watched_literals = [learned_clause[0], learned_clause[1]];
            let mut index = 0;
            for &literal in learned_clause.iter() {
                if self.variable_decision_levels[literal.handle]
                    == *self.decision_levels.last().unwrap()
                {
                    if index == 1 && literal == watched_literals[0] {
                        continue;
                    }
                    watched_literals[index] = literal;
                    index += 1;
                    if watched_literals.len() == 2 {
                        break;
                    }
                }
            }
            if watched_literals[0] == watched_literals[1] {
                for &literal in learned_clause.iter() {
                    if literal != watched_literals[0] {
                        watched_literals[1] = literal;
                        break;
                    }
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
        if self.clause_length(&self.clauses.get(&slot_key).unwrap()) == 1 {
            self.unit_clauses.push(slot_key);
        }
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

        self.decisions.reserve(self.variables.len());
        self.decision_levels.reserve(self.variables.len());
        self.antecedants = vec![None; self.variables.len()];
        self.implication_vertices.reserve(self.variables.len());
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

#[cfg(test)]
mod test_slot_map {
    use super::*;
    use std::error::Error;

    #[test]
    fn test_slot_map() -> Result<(), Box<dyn Error>> {
        let mut slot_map = SlotMap::new();

        let sk_0 = slot_map.insert(0);
        assert_eq!(slot_map.get(&sk_0), Some(&0));

        let sk_1 = slot_map.insert(1);
        assert_eq!(slot_map.get(&sk_0), Some(&0));
        assert_eq!(slot_map.get(&sk_1), Some(&1));

        slot_map.delete(&sk_0);
        assert_eq!(slot_map.get(&sk_0), None);
        assert_eq!(slot_map.get(&sk_1), Some(&1));

        assert_eq!(slot_map.iter().collect::<Vec<_>>(), [&1]);

        let sk_2 = slot_map.insert(2);
        assert_eq!(slot_map.get(&sk_0), None);
        assert_eq!(slot_map.get(&sk_1), Some(&1));
        assert_eq!(slot_map.get(&sk_2), Some(&2));

        assert_eq!(slot_map.iter().collect::<Vec<_>>(), [&2, &1]);

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

        solver.values[v31.handle] = Value::False;
        solver.variable_decision_levels[v31.handle] = Some(3);
        solver.decision_levels.push(Some(3));

        solver.values[v1.handle] = Value::False;
        solver.variable_decision_levels[v1.handle] = Some(5);
        solver.decision_levels.push(Some(5));

        solver.values[v2.handle] = Value::False;
        solver.antecedants[v2.handle] = Some(sk1);
        solver.variable_decision_levels[v2.handle] = Some(5);
        solver.decision_levels.push(Some(5));

        solver.values[v3.handle] = Value::False;
        solver.antecedants[v3.handle] = Some(sk2);
        solver.variable_decision_levels[v3.handle] = Some(5);
        solver.decision_levels.push(Some(5));

        solver.values[v4.handle] = Value::False;
        solver.antecedants[v4.handle] = Some(sk3);
        solver.variable_decision_levels[v4.handle] = Some(5);
        solver.decision_levels.push(Some(5));

        solver.values[v5.handle] = Value::False;
        solver.antecedants[v5.handle] = Some(sk4);
        solver.variable_decision_levels[v5.handle] = Some(5);
        solver.decision_levels.push(Some(5));

        solver.values[v6.handle] = Value::False;
        solver.antecedants[v6.handle] = Some(sk5);
        solver.variable_decision_levels[v6.handle] = Some(5);
        solver.decision_levels.push(Some(5));

        let learned_clause = solver.conflict_analysis(sk6);

        assert_eq!(
            learned_clause,
            Clause::new(vec![v1.literal(), v21.literal(), v31.literal()])
        );

        Ok(())
    }
}
