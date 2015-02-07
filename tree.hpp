#ifndef TREE_HPP
#define TREE_HPP

template <typename C>
C insert_left(C it, C to_insert) {
    using Tree = typename C::tree_type;
    using Cons = typename Tree::Cons;
    C copy = bifurcate_copy<C, Cons>(to_insert);
    set_left_successor(it, copy);
    return copy;
}

template <typename C>
C insert_right(C it, C to_insert) {
    using Tree = typename C::tree_type;
    using Cons = typename Tree::Cons;
    C copy = bifurcate_copy<C, Cons>(to_insert);
    set_right_successor(it, copy);
    return copy;
}

#endif
