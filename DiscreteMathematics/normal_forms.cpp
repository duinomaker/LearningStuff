#include <algorithm>
#include <deque>
#include <iostream>
#include <string>
using namespace std;

class Wff {
private:
    int vars; // number of variables in the WFF
    deque<char> symbols; // postfix expression form of the WFF
    string alphabet;

public:
    Wff(const string& wff)
        : vars(0)
    {
        int letters[26] {};
        deque<char> temp;
        /* refactor the WFF into a postfix expression */
        for (auto it = wff.cbegin(), it_ = wff.cend(); it != it_; ++it) {
            switch (*it) {
            case '(':
                temp.push_back(*it);
                break;
            case ')':
                while (temp.back() != '(') {
                    symbols.push_back(temp.back());
                    temp.pop_back();
                }
                temp.pop_back();
                break;
            case '~':
                temp.push_back(*it);
                break;
            case '^':
            case 'v':
                while (!temp.empty() && temp.back() == '~') {
                    symbols.push_back(temp.back());
                    temp.pop_back();
                }
                temp.push_back(*it);
                break;
            default:
                symbols.push_back(*it);
            }
        }
        while (!temp.empty()) {
            symbols.push_back(temp.back());
            temp.pop_back();
        }
        /* extract an alphabet from the WFF */
        for (auto it = symbols.cbegin(), it_ = symbols.cend(); it != it_; ++it)
            if ('A' <= *it && *it <= 'Z')
                ++letters[*it - 'A'];
        for (int i = 0; i != 26; ++i)
            if (letters[i])
                ++vars, alphabet.push_back('A' + i);
    }

    bool evaluate(int index) const
    {
        /* evaluate the WFF with truth values specified by the binary bits in `index` */
        deque<bool> temp;
        bool operand;
        for (auto it = symbols.cbegin(), it_ = symbols.cend(); it != it_; ++it) {
            switch (*it) {
            case '~':
                temp.back() = !temp.back();
                break;
            case '^':
                operand = temp.back();
                temp.pop_back();
                temp.back() = temp.back() && operand;
                break;
            case 'v':
                operand = temp.back();
                temp.pop_back();
                temp.back() = temp.back() || operand;
                break;
            default:
                temp.push_back((1 << (vars - 1 - letter2index(*it))) & index);
            }
        }
        return temp.back();
    }

    string generate_truth_table() const
    {
        string result;
        for (int i = (1 << vars) - 1; i != -1; --i)
            result.push_back(evaluate(i) ? 'T' : 'F');
        return result;
    }

    const string& get_alphabet() const
    {
        return alphabet;
    }

private:
    int letter2index(char c) const
    {
        /* given a letter, tells the index of it in the WFF's alphabet */
        const char* const ptr = alphabet.c_str();
        return lower_bound(ptr, ptr + vars, c) - ptr;
    }
};

void print_a_term(int vars, int index, const string& alphabet, bool is_major)
{
    /* print a minor/major term with letters taken from the alphabet */
    const char op = is_major ? 'v' : '^';
    cout << "(";
    for (int i = 1 << (vars - 1), j = 0; j != vars; i >>= 1, ++j) {
        if ((is_major && !(index & i)) || (!is_major && (index & i)))
            cout << "~";
        cout << alphabet[j];
        if (i != 1)
            cout << op;
    }
    cout << ")";
}

void read_a_truth_table(string& truth_values)
{
    /* read a truth table from keyboard */
    bool flag = true;
    while (flag) {
        flag = false;
        cout << "\nPlease input your truth table (e.g. `TFFFFTFT`): " << flush;
        cin >> truth_values;
        const int size = truth_values.length();
        int temp = size;
        while (temp && !(temp & 1))
            temp >>= 1;
        if (size < 2 || temp != 1) {
            cout << "[Error]\tLength of your truth table is not a positive integral power of 2" << endl;
            flag = true;
            continue;
        }
        for (int i = size - 1; i != -1; --i) {
            char c = truth_values.at(i);
            if (c != 'T' && c != 'F') {
                cout << "[Error]\tYour truth table contains invalid characters" << endl;
                flag = true;
                break;
            }
        }
    }
}

void truth_table2norm(const string& truth_values, const string& alphabet = "PQRSTUVWXYZABCDEFGHIJKLMNO")
{
    /* print out normal forms given a truth table and an alphabet */
    const int size = truth_values.length();
    int temp = size, vars = 0;
    while (temp >>= 1)
        ++vars;
    cout << "\nPrincipal disjunctive normal form:\n";
    for (int i = 0, i_ = size, n = 0; i != i_; ++i) {
        if (truth_values.at(i) == 'T') {
            if (n++)
                cout << "v";
            print_a_term(vars, i, alphabet, false);
        }
    }
    cout << "\n\nPrincipal conjunctive normal form:\n";
    for (int i = 0, i_ = size, n = 0; i != i_; ++i) {
        if (truth_values.at(i) == 'F') {
            if (n++)
                cout << "^";
            print_a_term(vars, i, alphabet, true);
        }
    }
    cout << "\n"
         << endl;
}

void main_truth_table2norm()
{
    string truth_values;
    read_a_truth_table(truth_values);
    truth_table2norm(truth_values);
}

void main_wff2norm()
{
    string wff_string;
    cout << "\n[Hint]\tUse `^` for conjunction, `v` for disjunction, and `~` for negation\n\n"
         << "Please input your WFF (e.g. `(A^~B)v(QvPv~A)`): " << flush;
    cin >> wff_string;
    Wff wff(wff_string);
    truth_table2norm(wff.generate_truth_table(), wff.get_alphabet());
}

int main()
{
    char choice;
    while (true) {
        cout << "===============================================================================\n\n"
             << "[1] Truth table to norm\n"
             << "[2] WFF to norm" << endl;
        cout << "\nPlease input your choice [1-2]: " << flush;
        cin >> choice;
        switch (choice) {
        case '1':
            main_truth_table2norm();
            break;
        case '2':
            main_wff2norm();
            break;
        default:
            cout << "[Error]\tInvalid command" << endl;
        }
    }
}
