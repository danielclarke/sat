pub struct FixedSizeStack<T> {
    top: usize,
    data: Vec<Option<T>>,
}

impl<T> FixedSizeStack<T>
where
    T: Clone,
{
    pub fn new(capacity: usize) -> Self {
        Self {
            top: 0,
            data: vec![None; capacity],
        }
    }

    pub fn clear(&mut self) {
        self.top = 0;
    }

    pub fn push(&mut self, item: T) {
        self.data[self.top] = Some(item);
        self.top += 1;
    }

    pub fn pop(&mut self) -> Option<T> {
        if self.top == 0 {
            return None;
        }
        self.top -= 1;
        self.data[self.top].take()
    }

    pub fn last(&self) -> Option<&T> {
        if self.top == 0 {
            return None;
        }
        if let Some(last) = &self.data[self.top - 1] {
            Some(last)
        } else {
            None
        }
    }

    pub fn len(&self) -> usize {
        self.top
    }

    pub fn empty(&self) -> bool {
        self.top == 0
    }

    pub fn iter(&self) -> StackIterator<T> {
        StackIterator {
            stack: self,
            index: self.top,
        }
    }
}
pub struct StackIterator<'a, T> {
    stack: &'a FixedSizeStack<T>,
    index: usize,
}

impl<'a, T> Iterator for StackIterator<'a, T> {
    type Item = &'a T;

    fn next(&mut self) -> Option<Self::Item> {
        if self.index == 0 {
            None
        } else {
            let result = Some(self.stack.data[self.index - 1].as_ref().unwrap());
            self.index -= 1;
            result
        }
    }
}

#[cfg(test)]
mod test_fixed_size_stack {
    use super::*;
    use std::error::Error;

    #[test]
    fn test_fixed_size_stack() -> Result<(), Box<dyn Error>> {
        let mut stack = FixedSizeStack::new(5);
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

        stack.push(4);
        stack.push(5);

        assert_eq!(stack.iter().collect::<Vec<_>>(), vec![&5, &4, &2, &0]);

        Ok(())
    }
}
