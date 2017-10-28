# avl-tree-rust
An AVL tree implementation in Rust.

The current implementation stores the nodes in a `vec` inside the
`SearchTree` struct. The parent and children of a node are referenced
using their index in the `vec`.

### Supported operations:
* insert
* lookup
