#ifndef CPP_EXPLORED_HUFFMAN_TREE_H
#define CPP_EXPLORED_HUFFMAN_TREE_H

#include <functional>
#include <iostream>
#include <unordered_map>
#include <utility>
#include <vector>
#include "priority_queue.h"

template<typename ElemType>
class HfmBTree {
    using Self = HfmBTree<ElemType>;

public:
    int weight;
    ElemType element;
    Self *l_child;
    Self *r_child;

    explicit HfmBTree(int weight, ElemType element = {})
            : weight(weight),
              element(std::move(element)),
              l_child(nullptr),
              r_child(nullptr) {};

    ~HfmBTree() {
        delete this->l_child;
        delete this->r_child;
    }

    static Self *cons(Self *l_child,
                      Self *r_child) {
        auto root = new Self(l_child->weight + r_child->weight);
        root->l_child = l_child;
        root->r_child = r_child;
        return root;
    }

    bool is_leaf() const {
        return this->l_child == nullptr && this->r_child == nullptr;
    }

    bool operator<(Self const &rhs) {
        return this->weight < rhs.weight;
    }
};

template<typename ElemType>
HfmBTree<ElemType> minimal_huffman_tree(
        std::pair<ElemType, int> const *slice, size_t size) {
    using TreeType = HfmBTree<ElemType>;
    std::vector<TreeType *> vec;
    vec.reserve(size);
    for (size_t i = 0; i != size; ++i) {
        vec.push_back(new TreeType(slice[i].second, slice[i].first));
    }
    PriorityQueue<TreeType *> pq(vec.data(), vec.size());
    while (pq.size() >= 2) {
        auto t1 = pq.front();
        pq.pop();
        auto t2 = pq.front();
        pq.pop();
        pq.push(TreeType::cons(t1, t2));
    }
    return *pq.front();
}

template<typename ElemType>
std::vector<std::pair<ElemType, int>> statistical_analyze(
        ElemType const *slice, size_t size) {
    std::unordered_map<ElemType, int> ump;
    for (size_t i = 0; i != size; ++i) {
        auto it = ump.find(slice[i]);
        if (it != ump.end()) {
            ++it->second;
        } else {
            ump.insert(std::make_pair(slice[i], 1));
        }
    }
    return std::vector<std::pair<ElemType, int>>(ump.begin(), ump.end());
}

template<typename ElemType>
std::unordered_map<ElemType, std::vector<bool>>
generate_dictionary(HfmBTree<ElemType> const &tree) {
    std::unordered_map<ElemType, std::vector<bool>> ump;
    std::vector<bool> current;
    std::function<void(HfmBTree<ElemType> const *)> traverse =
            [&](HfmBTree<ElemType> const *tree) {
                if (tree == nullptr) {
                    return;
                }
                if (tree->is_leaf()) {
                    ump.insert(std::make_pair(tree->element, current));
                } else {
                    current.push_back(false);
                    traverse(tree->l_child);
                    current.pop_back();
                    current.push_back(true);
                    traverse(tree->r_child);
                    current.pop_back();
                }
            };
    traverse(&tree);
    return ump;
}

void display_binary(std::vector<bool> const &binary) {
    for (bool b: binary) {
        std::cout << (b ? '1' : '0');
    }
    std::cout << std::endl;
}

template<typename ElemType>
void display_dictionary(
        std::unordered_map<ElemType, std::vector<bool>> const &dictionary) {
    for (auto &it: dictionary) {
        std::cout << it.first << ' ';
        display_binary(it.second);
    }
}

namespace huffman {

    template<typename ElemType>
    std::vector<bool> encode(HfmBTree<ElemType> const &tree,
                             ElemType const *slice, size_t size) {
        auto dictionary = generate_dictionary(tree);
        std::vector<bool> result;
        for (size_t i = 0; i != size; ++i) {
            std::vector<bool> &entry = dictionary[slice[i]];
            result.insert(result.end(), entry.cbegin(), entry.cend());
        }
        return result;
    }

    template<typename ElemType>
    std::vector<ElemType> decode(HfmBTree<ElemType> const &tree,
                                 std::vector<bool> const &binary) {
        std::vector<ElemType> result;
        HfmBTree<ElemType> const *current = &tree;
        for (bool b: binary) {
            current = b ?
                      current->r_child :
                      current->l_child;
            if (current->is_leaf()) {
                result.push_back(current->element);
                current = &tree;
            }
        }
        return result;
    }

}

#endif //CPP_EXPLORED_HUFFMAN_TREE_H
