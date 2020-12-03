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

inline bool in(std::uint32_t num, const std::vector<std::uint32_t> &elements) {
    return *(std::lower_bound(elements.cbegin(), elements.cend(), num)) == num;
}

std::uint32_t gcd(std::uint32_t a, std::uint32_t b) {
    if (!a)
        return b;
    return gcd(b % a, a);
}

inline std::uint32_t lcm(std::uint32_t a, std::uint32_t b) {
    return a * b / gcd(a, b);
}

auto input() {
    std::vector<std::uint32_t> ret;
    std::string line;
    std::getline(std::cin, line);
    std::istringstream iss(line);
    std::uint32_t num;
    while (iss >> num)
        ret.push_back(num);
    return ret;
}

////////////////////////////////////////////////////////////////

auto cover(const std::vector<std::uint32_t> &elements) {
    std::size_t size = elements.size();
    std::vector<std::pair<std::size_t, std::size_t>> cov;
    for (std::size_t i = 0; i != size; ++i)
        for (std::size_t j = i + 1; j != size; ++j) {
            bool flag = divides(elements[i], elements[j]);
            for (std::size_t k = i + 1; flag && k != j; ++k)
                if (divides(elements[i], elements[k]) &&
                    divides(elements[k], elements[j]))
                    flag = false;
            if (flag)
                cov.emplace_back(i, j);
        }
    return cov;
}

bool is_lattice(const std::vector<std::uint32_t> &elements) {
    std::size_t size = elements.size();
    for (std::size_t i = 0; i != size; ++i)
        for (std::size_t j = i + 1; j != size; ++j)
            if (!in(gcd(elements[i], elements[j]), elements) ||
                !in(lcm(elements[i], elements[j]), elements))
                return false;
    return true;
}

bool is_complemented_lattice(const std::vector<std::uint32_t> &elements) {
    std::size_t size = elements.size();
    std::uint32_t zero = elements[0], one = elements[size - 1];
    for (std::size_t i = 0; i != size; ++i) {
        bool flag = true;
        for (std::size_t j = 0; flag && j != size; ++j)
            if (gcd(elements[i], elements[j]) == zero &&
                lcm(elements[i], elements[j]) == one)
                flag = false;
        if (flag)
            return false;
    }
    return true;
}

int main() {
    std::cout << "A = {\n    ";
    auto elements = input();
    std::cout << "}" << std::endl;

    std::sort(elements.begin(), elements.end());

    auto cov = cover(elements);
    std::cout << "COV A = {\n";
    for (auto &p: cov)
        std::cout << "    <" << elements[p.first] << ", " << elements[p.second] << ">\n";
    std::cout << '}' << std::endl;

    bool lat = is_lattice(elements), cmpl_lat = is_complemented_lattice(elements);

    if (lat) {
        std::cout << "A is a lattice.\n";
        if (cmpl_lat)
            std::cout << "A is also a complement lattice.\n";
        else
            std::cout << "A is not a complement lattice.\n";
    } else
        std::cout << "A is not a lattice.\n";

    std::cout << std::flush;
}
