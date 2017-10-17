#![cfg_attr(feature="clippy", feature(plugin))]

#![cfg_attr(feature="clippy", plugin(clippy))]

extern crate rand;

/// A node inside a `SearchTree`.
#[derive(Debug, Clone, PartialEq)]
pub struct Node<T: PartialEq> {
    pub value: T,
    parent: Option<usize>,
    left_child: Option<usize>,
    right_child: Option<usize>,
    height: usize,
}

/// A simple AVL tree.
#[derive(Debug, PartialEq, Default)]
pub struct SearchTree <T: PartialEq + PartialOrd> {
    nodes: Vec<Node<T>>,
    root: Option<usize>,
}

impl<'a, T> SearchTree<T>
    where T: PartialEq + PartialOrd + Clone {
    /// Creates an empty search tree.
    ///
    /// # Example
    /// ```
    /// use avl_tree::SearchTree;
    /// let tree: SearchTree<String> = SearchTree::new();
    /// assert!(tree.is_empty());
    /// ```
    pub fn new() -> SearchTree<T> {
        SearchTree {
            nodes: Vec::new(),
            root: None
        }
    }

    /// Test if this tree is empty.
    ///
    /// # Example
    /// ```
    /// use avl_tree::SearchTree;
    /// let mut tree: SearchTree<String> = SearchTree::new();
    /// assert!(tree.is_empty());
    /// tree.insert(String::from("foo"));
    /// assert!(!tree.is_empty());
    /// ```
    pub fn is_empty(&self) -> bool {
        self.root.is_none()
    }

    /// Test if this contains a given value.
    ///
    /// # Example
    /// ```
    /// use avl_tree::SearchTree;
    /// let mut tree: SearchTree<String> = SearchTree::new();
    /// tree.insert(String::from("hello"));
    /// tree.insert(String::from("world!"));
    /// assert!(tree.contains(&String::from("hello")));
    /// assert!(!tree.contains(&String::from("cruel")));
    /// ```
    pub fn contains(&self, value: &T) -> bool {
        match self.get_node(value) {
            None => false,
            Some(index) => self.nodes[index].value == *value
        }
    }

    /// Add the specified value to this tree.
    ///
    /// # Example
    /// ```
    /// use avl_tree::SearchTree;
    /// let mut tree: SearchTree<String> = SearchTree::new();
    /// tree.insert(String::from("hello"));
    /// tree.insert(String::from("world!"));
    /// assert!(tree.contains(&String::from("hello")));
    /// assert!(tree.contains(&String::from("world!")));
    /// ```
    pub fn insert(&mut self, value: T) {
        if let Some(node) = self.create_node(value) {
            self.nodes.push(node);
            // inserted the root
            if self.nodes.len() == 1 {
                self.root = Some(0);
            }
            let last_added = self.nodes.len() - 1;
            self.update_heights(last_added);
            let mut node = Some(last_added);
            while let Some(index) = node {
                if !self.is_balanced(index) {
                    self.rebalance(index);
                }
                node = self.nodes[index].parent;
            }
        }
    }

    /// Return an `Option` containing the index of the node that has the
    /// lowest value that is greater or equal to `value`.
    fn get_node(&self, value: &T) -> Option<usize> {
        let mut current_index = self.root;
        let mut previous_index = None;
        while let Some(index) = current_index {
            previous_index = current_index;
            if *value > self.nodes[index].value {
                current_index = self.nodes[index].right_child;
            } else if *value < self.nodes[index].value {
                current_index = self.nodes[index].left_child;
            } else {
                // the value already exists in the tree - return the index of
                // the corresponding node
                return current_index;
            }
        }
        // return the index of the node containing the smallest value
        // greater than `value`
        previous_index
    }

    /// Return a new node containing `value`, or None if `value` is already in
    /// the tree.
    fn create_node(&mut self, value: T) -> Option<Node<T>> {
        let parent = self.get_node(&value);
        if let Some(index) = parent {
            if self.nodes[index].value == value {
                return None; // no need to create the node
            } else {
                if self.nodes[index].value < value {
                    self.nodes[index].right_child = Some(self.nodes.len());
                } else {
                    self.nodes[index].left_child = Some(self.nodes.len());
                }
            }
        }
        Some(Node {
            value: value,
            parent: parent,
            left_child: None,
            right_child: None,
            height: 0
        })
    }

    fn update_heights(&mut self, start_index: usize) {
        if !self.nodes.is_empty() {
            let mut child_index = start_index;
            while let Some(ancestor_index) = self.nodes[child_index].parent {
                self.nodes[ancestor_index].height =
                    self.compute_height(self.nodes[ancestor_index].left_child,
                                        self.nodes[ancestor_index].right_child);
                child_index = ancestor_index;
            }
            // update the height of the root
            self.nodes[self.root.unwrap()].height =
                self.compute_height(self.nodes[self.root.unwrap()].left_child,
                                    self.nodes[self.root.unwrap()].right_child);
        }
    }

    /// Helper function that computes the height of a node based
    /// on the heights of its children.
    fn compute_height(&self, l_subtree: Option<usize>,
            r_subtree: Option<usize>) -> usize {
        let (mut left_height, mut right_height) = (0, 0);
        if let Some(index) = l_subtree {
            left_height = self.nodes[index].height + 1;
        }
        if let Some(index) = r_subtree {
            right_height = self.nodes[index].height + 1;
        }
        std::cmp::max(left_height, right_height)
    }

    fn balance_factor(&self, node: &Node<T>) -> i8 {
        let (mut left_height, mut right_height) = (-1, -1);
        if let Some(left_child) = node.left_child {
            left_height = self.nodes[left_child].height as isize;
        }
        if let Some(right_child) = node.right_child {
            right_height = self.nodes[right_child].height as isize;
        }
        (left_height - right_height) as i8
    }

    fn left_rotation(&mut self, index: usize) {
        if let Some(right_index) = self.nodes[index].right_child {
            // The right child of `index` becomes the parent of `index`.
            // Therefore, `index` must become the left child of `right_index`
            // (its value is lower than that of `right_index`). If `index`
            // becomes the left child of `right_index`, that means the 'old'
            // left child of `right_index` must become the new right child of
            // `index`.
            //
            //       A (index)          (right_index) B
            //     /  \            =>               /  \
            //    X    B (right_index)     (index) A    C
            //       /  \                        /  \
            //      Y    C                      X   Y
            self.nodes[index].right_child = self.nodes[right_index].left_child;
            // If the right child of `index` is None, that means the old right
            // child of index did not have a left subtree.
            if let Some(new_right_index) = self.nodes[index].right_child {
                self.nodes[new_right_index].parent = Some(index);
            }
            self.nodes[right_index].left_child = Some(index);
            let parent = self.nodes[index].parent;
            if let Some(parent_index) = parent {
                if self.nodes[parent_index].left_child == Some(index) {
                    self.nodes[parent_index].left_child = Some(right_index);
                } else {
                    self.nodes[parent_index].right_child = Some(right_index);
                }
            } else {
                // change the root
                self.root = Some(right_index);
            }
            self.nodes[index].height =
                self.compute_height(self.nodes[index].left_child,
                                    self.nodes[index].right_child);
            self.nodes[right_index].height =
                self.compute_height(self.nodes[right_index].left_child,
                                    self.nodes[right_index].right_child);
            self.nodes[right_index].parent = self.nodes[index].parent;
            self.nodes[index].parent = Some(right_index);
            self.update_heights(index);
        }
    }

    fn right_rotation(&mut self, index: usize) {
        if let Some(left_index) = self.nodes[index].left_child {
            // See the comments for `left_rotation` (this is a mirrored
            // implementation of `left_rotation`)
            //
            //         (index)  A                  B (left_index)
            //                /  \       =>      /  \
            // (left_index)  B    X             C     A (index)
            //             /  \                     /  \
            //            C   Y                    Y   X
            self.nodes[index].left_child = self.nodes[left_index].right_child;
            if let Some(new_left_index) = self.nodes[index].left_child {
                self.nodes[new_left_index].parent = Some(index);
            }
            self.nodes[left_index].right_child = Some(index);
            let parent = self.nodes[index].parent;
            if let Some(parent_index) = parent {
                if self.nodes[parent_index].left_child == Some(index) {
                    self.nodes[parent_index].left_child = Some(left_index);
                } else {
                    self.nodes[parent_index].right_child = Some(left_index);
                }
            } else {
                // change the root
                self.root = Some(left_index);
            }
            self.nodes[index].height =
                self.compute_height(self.nodes[index].left_child,
                                    self.nodes[index].right_child);
            self.nodes[left_index].height =
                self.compute_height(self.nodes[left_index].left_child,
                                    self.nodes[left_index].right_child);
            self.nodes[left_index].parent = self.nodes[index].parent;
            self.nodes[index].parent = Some(left_index);
            self.update_heights(index);
        }
    }

    fn right_left_rotation(&mut self, index: usize) {
        if let Some(right_index) = self.nodes[index].right_child {
            self.right_rotation(right_index);
            self.left_rotation(index);
        }
    }

    fn left_right_rotation(&mut self, index: usize) {
        if let Some(left_index) = self.nodes[index].left_child {
            self.left_rotation(left_index);
            self.right_rotation(index);
        }
    }

    fn rebalance(&mut self, index: usize) {
        let balance_factor = self.balance_factor(&self.nodes[index]);
        if balance_factor == -2 {
            // right-heavy tree
            let right_index = self.nodes[index].right_child.unwrap();
            if self.balance_factor(&self.nodes[right_index]) == -1 {
                self.left_rotation(index);
            } else {
                self.right_left_rotation(index);
            }
        } else if balance_factor == 2 {
            // left-heavy
            let left_index = self.nodes[index].left_child.unwrap();
            if self.balance_factor(&self.nodes[left_index]) == 1 {
                self.right_rotation(index);
            } else {
                self.left_right_rotation(index);
            }
        } else if balance_factor < -2 || balance_factor > 2 {
            // this should not happen - the tree is normally rebalanced
            // whenever the balance factor of one of its nodes becomes -2 or 2
            unreachable!("Invalid balance factor for {}: {}",
                         index, balance_factor);
        }
    }

    fn is_balanced(&self, index: usize) -> bool {
        self.balance_factor(&self.nodes[index]).abs() < 2
    }

    /// Return an iterator over the values in this tree.
    ///
    /// # Example
    /// ```
    /// use avl_tree::SearchTree;
    /// let mut tree: SearchTree<u64> = SearchTree::new();
    /// tree.insert(5);
    /// tree.insert(2);
    /// tree.insert(1);
    /// assert!(tree.iter().zip(vec![1, 2, 5]).all(|(x, y)| *x == y));
    /// ```
    pub fn iter(&'a self) -> SearchTreeIter<'a, T> {
        SearchTreeIter::new(&self.nodes, self.root)
    }
}

pub struct SearchTreeIter<'a, T: PartialEq + PartialOrd + Clone> where T: 'a {
    nodes: &'a Vec<Node<T>>,
    current_node: Option<usize>,
}

impl<'a, T> SearchTreeIter<'a, T>
    where T: PartialOrd + Clone {
    pub fn new(nodes: &'a Vec<Node<T>>, root: Option<usize>)
            -> SearchTreeIter<'a, T> {
        SearchTreeIter {
            nodes: nodes,
            current_node: SearchTreeIter::get_leftmost(&nodes, root)
        }
    }

    /// Return the index of the leftmost node of the subtree rooted at `root`.
    fn get_leftmost(nodes: &'a Vec<Node<T>>, root: Option<usize>)
            -> Option<usize> {
        if let Some(mut leftmost_node) = root {
            while let Some(node) = nodes[leftmost_node].left_child {
                leftmost_node = node;
            }
            return Some(leftmost_node);
        }
        None
    }
}

impl<'a, T> Iterator for SearchTreeIter<'a, T>
    where T: PartialEq + PartialOrd + Clone {
    type Item = &'a T;

    fn next(&mut self) -> Option<Self::Item> {
        match self.current_node {
            None => None,
            Some(node_index) => {
                let mut node = &self.nodes[node_index];
                let result = &node.value;
                if node.right_child.is_some() {
                    // find the lowest value in the right subtree of `node`, so
                    // `self.current_node` becomes the node containing the
                    // lowest value greater than the value inside `node`
                    self.current_node =
                        SearchTreeIter::get_leftmost(self.nodes,
                                                     node.right_child);
                } else {
                    // find the first ancestor which holds a value greater
                    // than the one stored by `self.current_node`
                    while node.parent.is_some() &&
                        self.nodes[node.parent.unwrap()].value < node.value {
                        self.current_node = node.parent;
                        node = &self.nodes[self.current_node.unwrap()];
                    }
                    self.current_node = node.parent
                }
                Some(result)
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use rand;

    #[test]
    fn empty_tree() {
        let tree: SearchTree<u64> = SearchTree::new();
        assert_eq!(tree.is_empty(), true);
        assert_eq!(tree.nodes, vec![]);
        assert_eq!(tree.root, None);
    }

    #[test]
    fn insert_node() {
        let mut tree: SearchTree<u64> = SearchTree::new();
        let mut v = vec![20, 11, 25, 12, 8];
        for &value in v.iter() {
            tree.insert(value);
            // the tree should always be balanced
            for node_index in 0..tree.nodes.len() {
                assert!(tree.is_balanced(node_index));
            }
        }
        assert_eq!(tree.is_empty(), false);
        assert_eq!(tree.root, Some(0)); // the root is 20
        for (index, &value) in v.iter().enumerate() {
            assert_eq!(tree.nodes[index].value, value);
            assert!(tree.contains(&value));
        }
        v.sort();
        assert!(tree.iter().zip(v.iter()).all(|(x, y)| *x == *y));
        tree.insert(7);
        assert_eq!(tree.nodes[4].height, 1);
    }

    #[test]
    fn insert_left_rot() {
        //   10              20
        //    \            /  \
        //    20     =>  10   30
        //     \
        //     30
        let mut tree: SearchTree<u8> = SearchTree::new();
        tree.insert(10);
        assert_eq!(tree.root, Some(0));
        assert_eq!(tree.nodes[0].left_child, None);
        assert_eq!(tree.nodes[0].right_child, None);
        assert_eq!(tree.nodes[0].parent, None);
        tree.insert(20);
        assert_eq!(tree.nodes[0].left_child, None);
        assert_eq!(tree.nodes[0].right_child, Some(1));
        assert_eq!(tree.nodes[0].parent, None);
        assert_eq!(tree.nodes[1].left_child, None);
        assert_eq!(tree.nodes[1].right_child, None);
        assert_eq!(tree.nodes[1].parent, Some(0));
        assert_eq!(tree.nodes[0].height, 1);
        assert_eq!(tree.nodes[1].height, 0);
        tree.insert(30);
        assert_eq!(tree.nodes[0].left_child, None);
        assert_eq!(tree.nodes[0].right_child, None);
        assert_eq!(tree.nodes[0].parent, Some(1));
        assert_eq!(tree.nodes[1].left_child, Some(0));
        assert_eq!(tree.nodes[1].right_child, Some(2));
        assert_eq!(tree.nodes[1].parent, None);
        assert_eq!(tree.nodes[2].left_child, None);
        assert_eq!(tree.nodes[2].right_child, None);
        assert_eq!(tree.nodes[2].parent, Some(1));
        assert_eq!(tree.root, Some(1));
        assert_eq!(tree.nodes[0].height, 0);
        assert_eq!(tree.nodes[1].height, 1);
        assert_eq!(tree.nodes[2].height, 0);
    }

    #[test]
    fn insert_right_rot() {
        //    30            20
        //    /            /  \
        //   20     =>   10   30
        //   /
        //  10
        let mut tree: SearchTree<u8> = SearchTree::new();
        tree.insert(30);
        assert_eq!(tree.root, Some(0));
        assert_eq!(tree.nodes[0].left_child, None);
        assert_eq!(tree.nodes[0].right_child, None);
        assert_eq!(tree.nodes[0].parent, None);
        tree.insert(20);
        assert_eq!(tree.nodes[0].height, 1);
        assert_eq!(tree.nodes[0].left_child, Some(1));
        assert_eq!(tree.nodes[0].right_child, None);
        assert_eq!(tree.nodes[0].parent, None);
        assert_eq!(tree.nodes[1].left_child, None);
        assert_eq!(tree.nodes[1].right_child, None);
        assert_eq!(tree.nodes[1].parent, Some(0));
        assert_eq!(tree.nodes[0].height, 1);
        assert_eq!(tree.nodes[1].height, 0);
        tree.insert(10);
        assert_eq!(tree.root, Some(1));
        assert_eq!(tree.nodes[0].left_child, None);
        assert_eq!(tree.nodes[0].right_child, None);
        assert_eq!(tree.nodes[0].parent, Some(1));
        assert_eq!(tree.nodes[1].left_child, Some(2));
        assert_eq!(tree.nodes[1].right_child, Some(0));
        assert_eq!(tree.nodes[1].parent, None);
        assert_eq!(tree.nodes[2].left_child, None);
        assert_eq!(tree.nodes[2].right_child, None);
        assert_eq!(tree.nodes[2].parent, Some(1));
        assert_eq!(tree.nodes[0].height, 0);
        assert_eq!(tree.nodes[1].height, 1);
        assert_eq!(tree.nodes[2].height, 0);
    }

    #[test]
    fn left_right_rot() {
        //    30            25
        //    /            /  \
        //   20     =>   20   30
        //    \
        //    25
        let mut tree: SearchTree<u8> = SearchTree::new();
        tree.insert(30);
        assert_eq!(tree.root, Some(0));
        assert_eq!(tree.nodes[0].left_child, None);
        assert_eq!(tree.nodes[0].right_child, None);
        assert_eq!(tree.nodes[0].parent, None);
        tree.insert(20);
        assert_eq!(tree.root, Some(0));
        assert_eq!(tree.nodes[0].height, 1);
        assert_eq!(tree.nodes[0].left_child, Some(1));
        assert_eq!(tree.nodes[0].right_child, None);
        assert_eq!(tree.nodes[0].parent, None);
        assert_eq!(tree.nodes[1].left_child, None);
        assert_eq!(tree.nodes[1].right_child, None);
        assert_eq!(tree.nodes[1].parent, Some(0));
        assert_eq!(tree.nodes[0].height, 1);
        assert_eq!(tree.nodes[1].height, 0);
        tree.insert(25);
        assert_eq!(tree.root, Some(2));
        assert_eq!(tree.nodes[0].left_child, None);
        assert_eq!(tree.nodes[0].right_child, None);
        assert_eq!(tree.nodes[0].parent, Some(2));
        assert_eq!(tree.nodes[1].left_child, None);
        assert_eq!(tree.nodes[1].right_child, None);
        assert_eq!(tree.nodes[1].parent, Some(2));
        assert_eq!(tree.nodes[2].left_child, Some(1));
        assert_eq!(tree.nodes[2].right_child, Some(0));
        assert_eq!(tree.nodes[2].parent, None);
        assert_eq!(tree.nodes[0].height, 0);
        assert_eq!(tree.nodes[1].height, 0);
        assert_eq!(tree.nodes[2].height, 1);
    }

    #[test]
    fn right_left_rot() {
        //   10             15
        //    \            /  \
        //    20     =>  10   20
        //    /
        //   15
        let mut tree: SearchTree<u8> = SearchTree::new();
        tree.insert(10);
        assert_eq!(tree.root, Some(0));
        assert_eq!(tree.nodes[0].left_child, None);
        assert_eq!(tree.nodes[0].right_child, None);
        assert_eq!(tree.nodes[0].parent, None);
        tree.insert(20);
        assert_eq!(tree.root, Some(0));
        assert_eq!(tree.nodes[0].height, 1);
        assert_eq!(tree.nodes[0].left_child, None);
        assert_eq!(tree.nodes[0].right_child, Some(1));
        assert_eq!(tree.nodes[0].parent, None);
        assert_eq!(tree.nodes[1].left_child, None);
        assert_eq!(tree.nodes[1].right_child, None);
        assert_eq!(tree.nodes[1].parent, Some(0));
        assert_eq!(tree.nodes[0].height, 1);
        assert_eq!(tree.nodes[1].height, 0);
        tree.insert(15);
        assert_eq!(tree.root, Some(2));
        assert_eq!(tree.nodes[0].left_child, None);
        assert_eq!(tree.nodes[0].right_child, None);
        assert_eq!(tree.nodes[0].parent, Some(2));
        assert_eq!(tree.nodes[1].left_child, None);
        assert_eq!(tree.nodes[1].right_child, None);
        assert_eq!(tree.nodes[1].parent, Some(2));
        assert_eq!(tree.nodes[2].left_child, Some(0));
        assert_eq!(tree.nodes[2].right_child, Some(1));
        assert_eq!(tree.nodes[2].parent, None);
        assert_eq!(tree.nodes[0].height, 0);
        assert_eq!(tree.nodes[1].height, 0);
        assert_eq!(tree.nodes[2].height, 1);
    }

    #[test]
    fn random_values() {
        const LENGTH: usize = 10000;
        let mut v: Vec<u64> = Vec::with_capacity(LENGTH);
        for _ in 0..(LENGTH + 1) {
            v.push(rand::random::<u64>());
        }
        let mut tree: SearchTree<u64> = SearchTree::new();
        for &value in v.iter() {
            tree.insert(value);
            // the tree should always be balanced
            for node_index in 0..tree.nodes.len() {
                assert!(tree.is_balanced(node_index));
            }
        }
        v.sort();
        assert!(tree.iter().zip(v.iter()).all(|(x, y)| *x == *y));
    }
}
