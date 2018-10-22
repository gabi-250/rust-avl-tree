# avl-tree-rust
An AVL tree implementation in Rust.

The current implementation stores the nodes in a `vec` inside the
`SearchTree` struct. The parent of a node and its children are referenced
using their index in the `vec`.

### Supported operations:
* insert
* lookup

## Example
Returning an iterator over the values in the tree:

 ```rust
extern crate avl_tree;

use avl_tree::SearchTree;

fn main() {
    let mut tree: SearchTree<u64> = SearchTree::new();
    tree.insert(5);
    tree.insert(2);
    tree.insert(1);
    assert!(tree.iter().zip(vec![1, 2, 5]).all(|(x, y)| *x == y));
}
```
