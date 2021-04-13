#include <algorithm>
#include <cstddef>
#include <cstdint>
#include <iostream>
#include <sstream>
#include <string>
#include <utility>
#include <vector>

inline bool divides(std::uint32_t a, std::uint32_t b) {
    return !(b % a);
}

std::vector<std::uint32_t>
input() {
    std::vector<std::uint32_t> ret;
    std::string line;
    std::getline(std::cin, line);
    std::istringstream iss(line);
    std::uint32_t num;
    while (iss >> num) {
        ret.push_back(num);
    }
    return ret;
}

////////////////////////////////////////////////////////////////

std::vector<std::pair<std::size_t, std::size_t>>
cover(const std::vector<std::uint32_t> &elements) {
    std::size_t size = elements.size();
    std::vector<std::pair<std::size_t, std::size_t>> cov;
    for (std::size_t i = 0; i != size; ++i) {
        for (std::size_t j = i + 1; j != size; ++j) {
            bool flag = divides(elements[i], elements[j]);
            for (std::size_t k = i + 1; flag && k != j; ++k) {
                if (divides(elements[i], elements[k]) &&
                    divides(elements[k], elements[j])) {
                    flag = false;
                }
            }
            if (flag) {
                cov.emplace_back(i, j);
            }
        }
    }
    return cov;
}

std::uint32_t lub(const std::vector<std::uint32_t> &elements, std::size_t i, std::size_t j) {
    std::size_t size = elements.size();
    if (j < i) {
        std::swap(i, j);
    }
    for (std::size_t k = j; k != size; ++k) {
        if (divides(elements[i], elements[k]) &&
            divides(elements[j], elements[k])) {
            return elements[k];
        }
    }
    return 0;
}

std::uint32_t glb(const std::vector<std::uint32_t> &elements, std::size_t i, std::size_t j) {
    if (j < i) {
        std::swap(i, j);
    }
    for (std::size_t k = i; k != -1; --k) {
        if (divides(elements[k], elements[i]) &&
            divides(elements[k], elements[j])) {
            return elements[k];
        }
    }
    return 0;
}

bool is_lattice(const std::vector<std::uint32_t> &elements) {
    std::size_t size = elements.size();
    std::uint32_t zero = elements.front(), one = elements.back();
    for (std::size_t i = 1; i != size - 1; ++i) {
        if (!divides(zero, elements[i]) ||
            !divides(elements[i], one)) {
            return false;
        }
    }
    return true;
}

bool is_complemented_lattice(const std::vector<std::uint32_t> &elements) {
    std::size_t size = elements.size();
    std::uint32_t zero = elements.front(), one = elements.back();
    for (std::size_t i = 0; i != size; ++i) {
        bool flag = true;
        for (std::size_t j = 0; flag && j != size; ++j)
            if (glb(elements, i, j) == zero &&
                lub(elements, i, j) == one)
                flag = false;
        if (flag)
            return false;
    }
    return true;
}

int main() {
    std::cout << "A = {\n    ";
    auto elements = input();
    std::cout << "}\n" << std::flush;

    std::sort(elements.begin(), elements.end());

    auto cov = cover(elements);
    std::cout << "COV A = {\n";
    for (const auto &p: cov) {
        std::cout << "    <" << elements[p.first] << ", " << elements[p.second] << ">\n";
    }
    std::cout << "}\n" << std::flush;

    bool lat = is_lattice(elements), cmpl_lat = is_complemented_lattice(elements);

    if (lat) {
        std::cout << "A is a lattice.\n";
        if (cmpl_lat) {
            std::cout << "A is also a complement lattice.\n";
        } else {
            std::cout << "A is not a complement lattice.\n";
        }
    } else {
        std::cout << "A is not a lattice.\n";
    }
    std::cout << std::flush;
}
