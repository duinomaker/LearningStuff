#include <chrono>
#include <cstdint>
#include <cstring>
#include <functional>
#include <iostream>
#include <mutex>
#include <random>
#include <string>
#include <thread>
#include <unordered_map>
#include <vector>

void random_sequence(int *dst, int length) {
    static std::random_device rd;
    static std::mt19937 gen(rd());
    for (int i = 0; i != length; ++i) {
        dst[i] = static_cast<int>(gen());
    }
}

void heap_sort(int *seq, int length) {
    auto adjust_down = [seq](int cur, int length) {
        int r_child, m_child;
        while ((m_child = cur * 2 + 1) < length) {
            if ((r_child = m_child + 1) < length
                && seq[r_child] > seq[m_child]) {
                m_child = r_child;
            }
            if (seq[m_child] > seq[cur]) {
                std::swap(seq[m_child], seq[cur]);
                cur = m_child;
            } else {
                break;
            }
        }
    };
    if (length < 2) {
        return;
    }
    for (int i = length / 2 - 1; i != -1; --i) {
        adjust_down(i, length);
    }
    for (int i = length - 1; i != -1; --i) {
        std::swap(seq[0], seq[i]);
        adjust_down(0, i);
    }
}

void quick_sort(int *seq, int length) {
    std::function<void(int, int)> impl = [seq, &impl](int l, int r) {
        if (r - l < 2) {
            return;
        }
        int i = l, j = r;
        for (;;) {
            do {
                ++i;
            } while (i < j && seq[i] < seq[l]);
            do {
                --j;
            } while (i < j && seq[l] < seq[j]);
            if (i < j) {
                std::swap(seq[i], seq[j]);
            } else {
                break;
            }
        }
        std::swap(seq[l], seq[i - 1]);
        impl(l, i);
        impl(i, r);
    };
    impl(0, length);
}

void merge_sort(int *seq, int length) {
    auto temp = new int[length];
    std::function<void(int, int)> impl = [seq, temp, &impl](int l, int r) {
        if (r - l < 2) {
            return;
        }
        int m = l + (r - l) / 2;
        impl(l, m);
        impl(m, r);
        int i = l, j = m, p = l;
        while (i != m && j != r) {
            temp[p++] = seq[i] < seq[j] ? seq[i++] : seq[j++];
        }
        if (i != m) {
            memcpy(temp + p, seq + i, (m - i) * sizeof(int));
        } else if (j != r) {
            memcpy(temp + p, seq + j, (r - j) * sizeof(int));
        }
        memcpy(seq + l, temp + l, (r - l) * sizeof(int));
    };
    impl(0, length);
    delete[] temp;
}

void select_sort(int *seq, int length) {
    for (int i = 0; i != length - 1; ++i) {
        int min = i;
        for (int j = i + 1; j != length; ++j) {
            if (seq[j] < seq[min]) {
                min = j;
            }
            std::swap(seq[i], seq[min]);
        }
    }
}

void insert_sort(int *seq, int length) {
    for (int i = 0; i != length; ++i) {
        for (int j = i; j > 0 && seq[j] < seq[j - 1]; --j) {
            std::swap(seq[j - 1], seq[j]);
        }
    }
}

void bubble_sort(int *seq, int length) {
    for (int i = 0; i != length - 1; ++i) {
        for (int j = 0; j < length - 1 - i; ++j) {
            if (seq[j] > seq[j + 1]) {
                std::swap(seq[j], seq[j + 1]);
            }
        }
    }
}

std::mutex mtx;

void worker(const std::function<void(int *, int)> &sort,
            const std::string &name,
            int length) {
    static const int rounds = 1000;
    auto seq = new int[length];
    double duration = 0.0;
    for (int i = 0; i != rounds; ++i) {
        random_sequence(seq, length);
        auto start = std::chrono::high_resolution_clock::now();
        sort(seq, length);
        auto end = std::chrono::high_resolution_clock::now();
        duration += static_cast<std::chrono::duration<double>>(end - start)
                .count();
    }

    mtx.lock();
    printf("%s,%d,0x%016llx\n", name.c_str(), length,
           *reinterpret_cast<uint64_t *>(&duration));
    std::cout.flush();
    mtx.unlock();
    delete[] seq;
}

int main() {
    std::unordered_map<std::string, std::function<void(int *, int)>> ump = {
            {"heap",   heap_sort},
            {"merge",  merge_sort},
            {"quick",  quick_sort},
            {"select", select_sort},
            {"insert", insert_sort},
            {"bubble", bubble_sort}};
    std::string line;
    std::getline(std::cin, line);
    line.push_back(' ');

    std::vector<int> lengths;
    std::vector<std::string> names;

    size_t pos;
    while ((pos = line.find(' ')) != std::string::npos) {
        auto sub = line.substr(0, pos);
        if (isdigit(sub[0])) {
            lengths.push_back(
                    static_cast<int>(strtol(sub.c_str(), nullptr, 10)));
        } else {
            names.push_back(sub);
        }
        line.erase(0, pos + 1);
    }
    std::vector<std::thread> threads;
    for (auto &name: names) {
        for (auto &length: lengths) {
            threads.emplace_back(worker, ump[name], name, length);
        }
    }
    for (auto &thread: threads) {
        thread.join();
    }
}
