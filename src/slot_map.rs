use std::fmt;
type Generation = usize;

#[derive(Debug, Clone, Copy, PartialEq, PartialOrd, Eq, Ord)]
pub struct SlotKey {
    index: usize,
    generation: Generation,
}

impl fmt::Display for SlotKey {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{} ({})", self.index, self.generation)
    }
}

#[derive(Clone)]
pub struct SlotMap<T> {
    data: Vec<T>,
    generations: Vec<Generation>,
    empty: Vec<bool>,
    empty_slot_stack: Vec<usize>,
}

impl<T> SlotMap<T>
where
    T: Clone,
{
    pub fn new() -> Self {
        Self {
            data: vec![],
            generations: vec![],
            empty: vec![],
            empty_slot_stack: vec![],
        }
    }

    pub fn get(&self, key: &SlotKey) -> Option<&T> {
        if self.generations[key.index] != key.generation {
            return None;
        }

        Some(&self.data[key.index])
    }

    pub fn get_mut(&mut self, key: &SlotKey) -> Option<&mut T> {
        if self.generations[key.index] != key.generation {
            return None;
        }

        Some(&mut self.data[key.index])
    }

    pub fn delete(&mut self, key: &SlotKey) {
        if self.generations[key.index] != key.generation {
            return;
        }

        self.generations[key.index] += 1;
        self.empty[key.index] = true;
        self.empty_slot_stack.push(key.index);
    }

    pub fn insert(&mut self, value: T) -> SlotKey {
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

    pub fn len(&self) -> usize {
        self.empty.iter().filter(|&&empty| !empty).count()
    }

    pub fn iter(&self) -> SlotMapIterator<T> {
        SlotMapIterator {
            slot_map: self,
            index: 0,
        }
    }
}

impl<T> FromIterator<T> for SlotMap<T>
where
    T: Clone,
{
    fn from_iter<I: IntoIterator<Item = T>>(iter: I) -> Self {
        let mut c = SlotMap::<T>::new();

        for i in iter {
            c.insert(i);
        }

        c
    }
}

pub struct SlotMapIterator<'a, T> {
    slot_map: &'a SlotMap<T>,
    index: usize,
}

impl<'a, T> SlotMapIterator<'a, T> {
    pub fn items(&'a mut self) -> SlotMapEnumerator<'a, T> {
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

pub struct SlotMapEnumerator<'a, T> {
    slot_map_iterator: &'a mut SlotMapIterator<'a, T>,
}

impl<'a, T> Iterator for SlotMapEnumerator<'a, T> {
    type Item = (SlotKey, &'a T);

    fn next(&mut self) -> Option<Self::Item> {
        let n = self.slot_map_iterator.next();

        match n {
            None => None,
            Some(v) => {
                let generation =
                    self.slot_map_iterator.slot_map.generations[self.slot_map_iterator.index - 1];
                Some((
                    SlotKey {
                        index: self.slot_map_iterator.index - 1,
                        generation,
                    },
                    v,
                ))
            }
        }
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
