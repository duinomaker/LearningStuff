#ifndef CPP_EXPLORED_B_TREE_H
#define CPP_EXPLORED_B_TREE_H

#include <cstddef>
#include <functional>
#include <memory>

template<typename ElemType>
class BTree {
    using Self = BTree<ElemType>;

public:
    ElemType element;
    BTree<ElemType> *l_child;
    BTree<ElemType> *r_child;

    BTree() : element(),
              l_child(nullptr),
              r_child(nullptr) {}

    explicit BTree(ElemType element)
            : element(std::move(element)),
              l_child(nullptr),
              r_child(nullptr) {}

    ~BTree() {
        delete this->l_child;
        delete this->r_child;
    }

    static Self *cons(Self *l_child,
                      Self *r_child) {
        auto root = new Self();
        root->l_child = l_child;
        root->r_child = r_child;
        return root;
    }

    static Self *cons(Self *l_child,
                      ElemType element,
                      Self *r_child) {
        auto root = new Self(std::move(element));
        root->l_child = l_child;
        root->r_child = r_child;
        return root;
    }

    void flip() {
        std::function<void(Self *)> traverse =
                [&](Self *parent) {
                    if (parent == nullptr) {
                        return;
                    }
                    std::swap(parent->l_child, parent->r_child);
                    traverse(parent->l_child);
                    traverse(parent->r_child);
                };
        traverse();
    }

    size_t node_count() const {
        size_t size = 1;
        std::function<void(Self const *)> traverse =
                [&](Self const *parent) {
                    if (parent == nullptr) {
                        return;
                    }
                    ++size;
                    traverse(parent->l_child);
                    traverse(parent->r_child);
                };
        traverse(this->l_child);
        traverse(this->r_child);
        return size;
    }

    size_t leaf_count() const {
        size_t size = 0;
        std::function<void(Self const *)> traverse =
                [&](Self const *parent) {
                    if (parent->is_leaf()) {
                        ++size;
                        return;
                    }
                    traverse(parent->l_child);
                    traverse(parent->r_child);
                };
        traverse(this->l_child);
        traverse(this->r_child);
        return size;
    }

    size_t height() const {
        size_t max_depth = 0;
        std::function<void(Self const *, size_t)> traverse =
                [&](Self const *parent, size_t depth) {
                    if (depth > max_depth) {
                        max_depth = depth;
                    }
                    if (parent == nullptr) {
                        return;
                    }
                    traverse(parent->l_child, depth + 1);
                    traverse(parent->r_child, depth + 1);
                };
        traverse(this->l_child, 1);
        traverse(this->r_child, 1);
        return max_depth;
    }

    bool is_leaf() const {
        return l_child == nullptr && r_child == nullptr;
    }
};

template<typename ElemType>
void preorder_traverse(BTree<ElemType> const *tree) {
    if (tree == nullptr) {
        return;
    }
    std::cout << tree->element << ' ';
    preorder_traverse(tree->l_child);
    preorder_traverse(tree->r_child);
}

template<typename ElemType>
void inorder_traverse(BTree<ElemType> const *tree) {
    if (tree == nullptr) {
        return;
    }
    inorder_traverse(tree->l_child);
    std::cout << tree->element << ' ';
    inorder_traverse(tree->r_child);
}

template<typename ElemType>
void postorder_traverse(BTree<ElemType> const *tree) {
    if (tree == nullptr) {
        return;
    }
    postorder_traverse(tree->l_child);
    postorder_traverse(tree->r_child);
    std::cout << tree->element << ' ';
}

//    template<typename ElemType>
//    struct BTreeNode {
//        bool empty
//    };
//
//    std::vector<BTreeNode < char>>
//
//    string_to_nodes(
//            char const *slice, size_t size) {
//        std::vector<BTreeNode < char>>
//        result;
//        result.reserve(size);
//        for (size_t i = 0; i != size; ++i) {
//            result.push_back(slice[i] == '#' ?
//                             BTreeNode<char>(true) :
//                             BTreeNode<char>(false, slice[i]));
//        }
//        return result;
//    }
//
//    void preorder_construct() {
//        std::string str;
//        std::cin >> str;
//        auto nodes = string_to_nodes(str.data(), str.size());
//        auto tree = preorder_construct(nodes.data(), nodes.size());
//        preorder_traverse(&tree);
//    }

#endif //CPP_EXPLORED_B_TREE_H
