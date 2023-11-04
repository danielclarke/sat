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
