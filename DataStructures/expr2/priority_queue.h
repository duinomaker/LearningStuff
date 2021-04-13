#ifndef CPP_EXPLORED_PRIORITY_QUEUE_H
#define CPP_EXPLORED_PRIORITY_QUEUE_H

#include <cstddef>
#include <memory>
#include <vector>

template<typename ElemType>
class PriorityQueue {
    std::vector<ElemType> data;

    void adjust_down(size_t index) {
        size_t size = this->data.size();
        size_t min_child = index * 2 + 1;
        size_t r_child = index * 2 + 2;
        if (min_child >= size) {
            return;
        }
        if (r_child < size
            && this->data[r_child] < this->data[min_child]) {
            min_child = r_child;
        }
        if (this->data[min_child] < this->data[index]) {
            std::swap(this->data[min_child],
                      this->data[index]);
            adjust_down(min_child);
        }
    }

    void adjust_up(size_t index) {
        if (index == 0) {
            return;
        }
        size_t parent = (index - 1) / 2;
        if (this->data[index] < this->data[parent]) {
            std::swap(this->data[index],
                      this->data[parent]);
            adjust_up(parent);
        }
    }

    void initialize() {
        for (size_t i = this->data.size() / 2 - 1; i != -1; --i) {
            adjust_down(i);
        }
    }

public:
    PriorityQueue() : data() {}

    PriorityQueue(ElemType const *slice, size_t size)
            : data(slice, slice + size) {
        initialize();
    }

    size_t size() const {
        return this->data.size();
    }

    bool empty() const {
        return this->data.empty();
    }

    void push(ElemType element) {
        this->data.push_back(std::move(element));
        adjust_up(this->data.size() - 1);
    }

    void pop() {
        std::swap(this->data[0],
                  this->data[data.size() - 1]);
        data.pop_back();
        adjust_down(0);
    }

    ElemType &front() {
        return this->data.front();
    }
};

#endif //CPP_EXPLORED_PRIORITY_QUEUE_H
