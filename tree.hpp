#ifndef TREE_HPP
#define TREE_HPP

#define requires(...)

template<typename T>
requires(WeakBifurcateCoordinate(T))
struct weight_type;

#define WeightType(T) typename weight_type< T >::type

template<typename T>
    requires(Container(T))
struct coordinate_type;

#define CoordinateType(T) typename coordinate_type<T>::type

template<typename T>
    requires(Regular(T))
    struct value_type
{
        typedef T type;
};
#define ValueType(T) typename value_type< T >::type

template <class T>
class tree_node;

template <class T>
struct tree_coordinate {
    tree_node<T>* ptr;
    tree_coordinate() : ptr(0) {}
    tree_coordinate(tree_node<T>* ptr) : ptr(ptr) {}
};

template<typename T>
    requires(Regular(T))
bool operator==(tree_coordinate<T> c0, tree_coordinate<T> c1)
{
    return c0.ptr == c1.ptr;
}
template<typename T>
    requires(Regular(T))
bool operator!=(tree_coordinate<T> c0, tree_coordinate<T> c1)
{
    return !(c0.ptr == c1.ptr);
}

template <class T>
tree_coordinate<T> left_successor(tree_coordinate<T> x) {
    return x.ptr->left;
}

template <class T>
tree_coordinate<T> right_successor(tree_coordinate<T> x) {
    return x.ptr->right;
}

template <class T>
void set_left_successor(
        tree_coordinate<T> c,
        tree_coordinate<T> l) {
    c.ptr->left = l.ptr;
    if (!empty(l)) set_predecessor(l, c);
}

template <class T>
void set_right_successor(
        tree_coordinate<T> c,
        tree_coordinate<T> r) {
    c.ptr->right = r.ptr;
    if (!empty(r)) set_predecessor(r, c);
}

template<typename T>
    requires(Regular(T))
const T& source(tree_coordinate<T> c)
{
    return c.ptr->value;
}

template<typename T>
    requires(Regular(T))
T& sink(tree_coordinate<T> c)
{
    return c.ptr->value;
}

template <class T>
struct tree_node {
    T value;

    tree_node<T>* left;
    tree_node<T>* right;
    tree_node<T>* predecessor_link;

    tree_node() : left(0), right(0) {}
    tree_node(const T& x) : value(x), left(0), right(0) {}
    tree_node(const T& x, tree_node* l, tree_node* r)
        : value(x), left(l), right(r) {}
};

static int tree_node_count = 0; /* ***** TESTING ***** */

template<typename T>
    requires(Regular(T))
struct tree_node_construct
{
    typedef tree_coordinate<T> C;
    tree_node_construct() { }
    C operator()(T x, C l = C(0), C r = C(0))
    {
        ++tree_node_count;
        return C(new tree_node<T>(x, l.ptr, r.ptr));
    }
    C operator()(C c)           { return (*this)(source(c), left_successor(c),
                                                            right_successor(c)); }
    C operator()(C c, C l, C r) { return (*this)(source(c), l, r); }
};

template<typename T>
    requires(Regular(T))
struct tree_node_destroy
{
    tree_node_destroy() { }
    void operator()(tree_coordinate<T> i)
    {
        --tree_node_count;
        delete i.ptr;
    }
};

template<typename C, typename ND>
    requires(BifurcateCoordinate(C) && TreeNodeDeleter(ND))
void bifurcate_erase(C c, ND node_delete)
{
    if (empty(c)) return;
    C stack = C(0); // chained through left_successor
    while (true) {
        C left = left_successor(c);
        C right = right_successor(c);
        if (!empty(left)) {
            if (!empty(right)) {
                set_left_successor(c, stack);
                stack = c;
            } else
                node_delete(c);
            c = left;
        } else if (!empty(right)) {
            node_delete(c);
            c = right;
        } else {
            node_delete(c);
            if (!empty(stack)) {
                c = stack;
                stack = left_successor(stack);
                set_left_successor(c, C(0));
           } else return;
        }
    }
}

/*
   The next function is based on MAKECOPY in this paper:

   K. P. Lee.
   A linear algorithm for copying binary trees using bounded workspace.
   Commun. ACM 23, 3 (March 1980), 159-162. DOI=10.1145/358826.358835
   http://doi.acm.org/10.1145/358826.358835
*/

template<typename C, typename Cons>
    requires(EmptyLinkedBifurcateCoordinate(C) &&
        TreeNodeConstructor(Cons) && NodeType(C) == NodeType(Cons))
C bifurcate_copy(C c)
{
    Cons construct_node;
    if (empty(c)) return c;              // Us      / Lee
    C stack = construct_node(c, c, C()); // stack   / V'
    C c_new = stack;                     // c\_new  / COPY
    while (!empty(stack)) {              // empty() / null
        c = left_successor(stack);       // c       / V
        C l = left_successor(c);
        C r = right_successor(c);
        C top = stack;
        if (!empty(l)) {
            if (!empty(r)) {
                r = construct_node(r, r, right_successor(stack));
                stack = construct_node(l, l, r);
            }
            else  {
                r = C();
                stack = construct_node(l, l, right_successor(stack));
            }
            l = stack;
        } else if (!empty(r)) {
            stack = construct_node(r, r, right_successor(stack));
            r = stack;
        } else
            stack = right_successor(stack);
        set_right_successor(top, r);
        set_left_successor(top, l);
    }
    return c_new;
}

template <class T>
struct tree {
    typedef tree_coordinate<T> C;
    typedef tree_node_construct<T> Cons;
    C root;

    tree() : root(0) {}
    tree(T x) : root(Cons()(x)) { }
    tree(T x, const tree& left, const tree& right) : root(Cons()(x))
    {
        set_left_successor(root, bifurcate_copy<C, Cons>(left.root));
        set_right_successor(root, bifurcate_copy<C, Cons>(right.root));
    }
    tree(const tree& x) : root(bifurcate_copy<C, Cons>(x.root)) { }
    ~tree()
    {
        bifurcate_erase(root, tree_node_destroy<T>());
    }
    void operator=(tree x)
    {
        using std::swap;
        swap(root, x.root);
    }
};

enum visit { pre, in, post };

template<typename C>
    requires(BidirectionalBifurcateCoordinate(C))
int traverse_step(visit& v, C& c)
{
    // Precondition: $\func{has\_predecessor}(c) \vee v \neq post$
    switch (v) {
    case pre:
        if (has_left_successor(c))  {
                     c = left_successor(c);  return 1;
        }   v = in;                          return 0;
    case in:
        if (has_right_successor(c)) {
            v = pre; c = right_successor(c); return 1;
        }   v = post;                        return 0;
    case post:
        if (is_left_successor(c))
            v = in;
                     c = predecessor(c);     return -1;
    }
}

template<typename T>
    requires(Regular(T))
tree_coordinate<T> predecessor(tree_coordinate<T> c)
{
    return c.ptr->predecessor_link;
}

template<typename T>
    requires(Regular(T))
bool has_predecessor(tree_coordinate<T> c)
{
    return !empty(predecessor(c));
}

template<typename T>
    requires(Regular(T))
void set_predecessor(tree_coordinate<T> c, tree_coordinate<T> p)
{
    c.ptr->predecessor_link = p.ptr;
}

template<typename C, typename Proc>
    requires(BidirectionalBifurcateCoordinate(C) &&
        Procedure(Proc) && Arity(Proc) == 2 &&
        visit == InputType(Proc, 0) &&
        C == InputType(Proc, 1))
Proc traverse(C c, Proc proc)
{
    // Precondition: $\property{tree}(c)$
    if (empty(c)) return proc;
    C root = c;
    visit v = pre;
    proc(pre, c);
    do {
        traverse_step(v, c);
        proc(v, c);
    } while (c != root || v != post);
    return proc;
}

template<typename T>
    requires(BidirectionalBifurcateCoordinate(T))
bool is_left_successor(T j)
{
    // Precondition: $\func{has\_predecessor}(j)$
    T i = predecessor(j);
    return has_left_successor(i) && left_successor(i) == j;
}

template<typename T>
    requires(BidirectionalBifurcateCoordinate(T))
bool is_right_successor(T j)
{
    // Precondition: $\func{has\_predecessor}(j)$
    T i = predecessor(j);
    return has_right_successor(i) && right_successor(i) == j;
}


template<typename T>
requires(Regular(T))
struct coordinate_type< tree<T> >
{
    typedef tree_coordinate<T> type;
};

template<typename T>
requires(Regular(T))
struct value_type< tree<T> >
{
    typedef ValueType(CoordinateType(tree<T>)) type;
};

template<typename T>
requires(Regular(T))
struct weight_type< tree<T> >
{
    typedef WeightType(CoordinateType(tree<T>)) type;
};

template<typename T>
    requires(Regular(T))
tree_coordinate<T> begin(const tree<T>& x)
{
    return x.root;
}

template<typename T>
    requires(Regular(T))
bool empty(const tree<T>& x)
{
    return empty(x.root);
}

template<typename T>
    requires(Regular(T))
bool empty(tree_coordinate<T> c)
{
    return c.ptr == 0;
}

template<typename T>
    requires(Regular(T))
bool has_left_successor(tree_coordinate<T> c)
{
    return !empty(left_successor(c));
}

template<typename T>
    requires(Regular(T))
bool has_right_successor(tree_coordinate<T> c)
{
    return !empty(right_successor(c));
}
#endif
