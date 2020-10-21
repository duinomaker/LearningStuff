#include <exception>
#include <iostream>
#include <regex>
#include <string>
#include <unordered_map>
#include <utility>
#include <vector>
using namespace std;

class Relation {
    friend istream& operator>>(istream& in, Relation& rel);
    friend void from_adjacency_matrix(istream& in, Relation& rel);
    friend void from_domain_and_pairs(istream& in, Relation& rel);

public:
    Relation()
        : dimension(0)
    {
    }

    void set(size_t row, size_t col, bool val)
    {
        data.at(row * dimension + col) = val;
    }

    bool get(size_t row, size_t col) const
    {
        return data.at(row * dimension + col);
    }

    bool is_symmetrical() const
    {
        for (size_t i = 0; i < dimension; ++i) {
            for (size_t j = i + 1; j < dimension; ++j) {
                if (data.at(i * dimension + j) != data.at(j * dimension + i)) {
                    return false;
                }
            }
        }
        return true;
    }

    bool is_asymmetrical() const
    {
        for (size_t i = 0; i < dimension; ++i) {
            for (size_t j = i + 1; j < dimension; ++j) {
                if (data.at(i * dimension + j) && data.at(j * dimension + i)) {
                    return false;
                }
            }
        }
        return true;
    }

    bool is_reflexive() const
    {
        for (size_t i = 0; i < dimension; ++i) {
            if (!data.at(i * dimension + i)) {
                return false;
            }
        }
        return true;
    }

    bool is_irreflexive() const
    {
        for (size_t i = 0; i < dimension; ++i) {
            if (data.at(i * dimension + i)) {
                return false;
            }
        }
        return true;
    }

    bool is_transitive() const
    {
        for (size_t i = 0; i < dimension; ++i) {
            for (size_t j = 0; j < dimension; ++j) {
                if (!data.at(i * dimension + j)) {
                    for (size_t k = 0; k < dimension; ++k) {
                        if (data.at(i * dimension + k) && data.at(k * dimension + j)) {
                            return false;
                        }
                    }
                }
            }
        }
        return true;
    }

private:
    size_t dimension;
    vector<bool> data;
    unordered_map<string, size_t> domain_map;
};

void from_adjacency_matrix(istream& in, Relation& rel)
{
    runtime_error errfmt(string("incorrect format for an adjacency matrix"));
    string str;
    getline(in, str);
    rel.dimension = str.length();
    rel.data.resize(rel.dimension * rel.dimension);
    size_t i = 0;
    do {
        if (str.length() != rel.dimension) {
            throw errfmt;
        }
        for (size_t j = 0; j < rel.dimension; ++j) {
            switch (str.at(j)) {
            case '0':
                rel.set(i, j, false);
                break;
            case '1':
                rel.set(i, j, true);
                break;
            default:
                throw errfmt;
            }
        }
    } while (++i < rel.dimension && !(getline(in, str), in.eof()));
    if (i < rel.dimension) {
        throw errfmt;
    }
}

void from_domain_and_pairs(istream& in, Relation& rel)
{
    runtime_error errfmt(string("objects in pairs don't exist in the domain"));
    string str;
    getline(in, str);
    auto search_begin = str.cbegin();
    smatch matched;
    /* match and store the domain */
    rel.domain_map.clear();
    rel.dimension = 0;
    if (str.empty()) {
        rel.data.clear();
        return;
    }
    if (str.at(0) == '{') {
        ++search_begin;
        regex pat_domain("(.*?)([,\\}])");
        for (; regex_search(search_begin, str.cend(), matched, pat_domain);
             search_begin = matched.suffix().first) {
            if (rel.domain_map.find(matched[1]) == rel.domain_map.end()) {
                rel.domain_map.insert({ matched[1], rel.dimension++ });
            }
            if (matched[2] == "}") {
                break;
            }
        }
    }
    /* match and store pairs */
    rel.data.clear();
    rel.data.resize(rel.dimension * rel.dimension);
    regex pat_pair("<(.*?),(.*?)>");
    for (; regex_search(search_begin, str.cend(), matched, pat_pair);
         search_begin = matched.suffix().first) {
        if (rel.domain_map.find(matched[1]) == rel.domain_map.end()
            || rel.domain_map.find(matched[2]) == rel.domain_map.end()) {
            throw errfmt;
        }
        rel.set(rel.domain_map.at(matched[1]), rel.domain_map.at(matched[2]), true);
    }
}

istream& operator>>(istream& in, Relation& rel)
{
    runtime_error errfmt(string("incorrect format for a relationship"));
    char type = in.get();
    in.putback(type);
    try {
        if (type == '0' || type == '1') {
            from_adjacency_matrix(in, rel);
        } else {
            from_domain_and_pairs(in, rel);
        }
    } catch (exception& e) {
        cout << "[ERROR]\t" << e.what() << endl;
        throw errfmt;
    }
    return in;
}

void output_relation_properties(ostream& out, const Relation& rel)
{
    out << boolalpha << "\n";
    out << "   Reflexive:\t" << rel.is_reflexive() << "\n"
        << " Symmetrical:\t" << rel.is_symmetrical() << "\n"
        << " Irreflexive:\t" << rel.is_irreflexive() << "\n"
        << "Asymmetrical:\t" << rel.is_asymmetrical() << "\n"
        << "  Transitive:\t" << rel.is_transitive() << "\n"
        << endl;
    out << noboolalpha;
}

int main()
{
    Relation rel;
    cout << "To type in a relation, you may want to type in an adjacency matrix directly,\n"
            "like this one:  1001\n"
            "                0101\n"
            "                0010\n"
            "                1111 .\n\n"
            "But you may also prefer to represent a relation as a domain together with a set\n"
            "of ordered pairs, for example\n\n"
            "  {27,apple, ,^-^} <apple,27><^-^, >< ,^-^>\n\n"
            "for a relation on a 4-set with 3 ordered pairs (note that spaces, empties, any\n"
            "characters are allowed), or even\n\n"
            "  {, ,  ,   } <, ><  , ><,><   ,>\n\n"
            "if you would like, for another relation on a 4-set with 4 ordered pairs.\n\n"
            "Now you're able to represent your relation in this descriptive language, please\n"
            "type in your relation:\n"
         << endl;
    while (true) {
        try {
            cin >> rel;
        } catch (exception& e) {
            cout << "Please try again:\n"
                 << endl;
            continue;
        }
        output_relation_properties(cout, rel);
        cout << "You can type in another relation:\n"
             << endl;
    }
}
