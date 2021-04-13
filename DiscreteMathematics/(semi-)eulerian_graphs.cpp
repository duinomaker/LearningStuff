#include <cstddef>
#include <exception>
#include <functional>
#include <iostream>
#include <list>
#include <sstream>
#include <string>
#include <vector>

class Graph {
public:
    using edge_type = std::pair<std::size_t, std::size_t>;
    using edges_type = std::list<edge_type>;
    using adj_mat_type = std::vector<std::vector<bool>>;
    using path_type = std::list<std::size_t>;
    using paths_type = std::list<path_type>;

    explicit Graph(adj_mat_type mat_to_move) : mat(std::move(mat_to_move)), edges(0) {
        for (std::size_t u = 0; u != mat.size(); ++u) {
            for (std::size_t v = u + 1; v != mat.size(); ++v) {
                if (mat[u][v]) {
                    ++edges;
                }
            }
        }
    }

    static Graph from_edges(std::size_t vertices, const edges_type &edges) {
        adj_mat_type mat(vertices, std::vector<bool>(vertices, false));
        for (const auto &e: edges) {
            mat[e.first][e.second] = true;
            mat[e.second][e.first] = true;
        }
        return Graph(mat);
    }

    static void print_paths(const paths_type &paths) {
        for (const auto &path: paths) {
            std::size_t count = 0;
            for (std::size_t v: path) {
                std::cout << v + 1 << (++count != path.size() ? "-" : "");
            }
            std::cout << '\n';
        }
        std::cout << std::flush;
    };

    std::size_t count_degree(std::size_t v) const {
        static std::vector<std::size_t> memory(mat.size(), -1);
        if (memory[v] != -1) {
            return memory[v];
        }
        memory[v] = 0;
        for (size_t j = 0; j != mat.size(); ++j) {
            if (mat[v][j]) {
                ++memory[v];
            }
        }
        return memory[v];
    }

    bool is_connected() const {
        std::vector<bool> visited(mat.size(), false);
        std::function<void(std::size_t)> dfs =
                [this, &dfs, &visited](std::size_t u) {
                    visited[u] = true;
                    for (std::size_t v = 0; v != mat.size(); ++v) {
                        if (!visited[v] && mat[u][v]) {
                            dfs(v);
                        }
                    }
                };
        dfs(0);
        for (std::size_t v = 0; v != mat.size(); ++v) {
            if (!visited[v]) {
                return false;
            }
        }
        return true;
    }

    bool is_eulerian() const {
        if (!is_connected()) {
            return false;
        }
        for (size_t v = 0; v != mat.size(); ++v) {
            if (count_degree(v) % 2) {
                return false;
            }
        }
        return true;
    }

    bool is_semi_eulerian() const {
        if (!is_connected()) {
            return false;
        }
        std::size_t odd_count = 0;
        for (size_t v = 0; v != mat.size(); ++v) {
            if (count_degree(v) % 2) {
                if (++odd_count > 2) {
                    return false;
                }
            }
        }
        return true;
    }

    paths_type eulerian_paths() const {
        paths_type ret;
        adj_mat_type mat_dfs(mat);
        path_type path;
        std::function<void(std::size_t, std::size_t)> dfs =
                [this, &dfs, &ret, &mat_dfs, &path](std::size_t u, std::size_t depth) {
                    if (depth == edges) {
                        ret.push_back(path);
                        return;
                    }
                    for (std::size_t v = 0; v != mat.size(); ++v) {
                        if (mat_dfs[u][v]) {
                            mat_dfs[u][v] = false;
                            mat_dfs[v][u] = false;
                            path.push_back(v);
                            dfs(v, depth + 1);
                            mat_dfs[u][v] = true;
                            mat_dfs[v][u] = true;
                            path.pop_back();
                        }
                    }
                };
        std::size_t vertex_to_start_with = 0;
        for (size_t v = 0; v != mat.size(); ++v) {
            if (count_degree(v) % 2) {
                vertex_to_start_with = v;
                break;
            }
        }
        path.push_back(vertex_to_start_with);
        dfs(vertex_to_start_with, 0);
        return ret;
    }

private:
    adj_mat_type mat;
    std::size_t edges;
};

Graph input() {
    std::string line;
    std::size_t vertices;
    std::cout << "Number of vertices: " << std::flush;
    std::getline(std::cin, line);
    std::istringstream(line) >> vertices;
    std::size_t first, second;
    Graph::edges_type edges;
    std::cout << "The program accepts edges separated by lines, for example\n"
                 "1 2\n"
                 "2 3\n"
                 "3 4\n"
                 "4 1\n"
                 "(empty line)\n"
                 "represents a graph like (vertex indices start from 1)\n"
                 "4-1\n"
                 "| |\n"
                 "3-2.\n\n"
                 "Input your edges:\n" << std::flush;
    while (std::getline(std::cin, line), !line.empty()) {
        std::istringstream iss(line);
        iss >> first >> second;
        if (first < 1 || first > vertices || second < 1 || second > vertices) {
            std::cout << "invalid edge: index out-of-range\n" << std::flush;
            continue;
        }
        if (first == second) {
            std::cout << "edge ignored: self-loops aren't accepted within an undirected graph\n" << std::flush;
            continue;
        }
        edges.emplace_back(first - 1, second - 1);
    }
    return Graph::from_edges(vertices, edges);
}

int main() {
    Graph graph = input();
    if (graph.is_eulerian()) {
        std::cout << "The graph is an Eulerian graph.\n\nEulerian loops:\n" << std::flush;
        Graph::print_paths(graph.eulerian_paths());
    } else if (graph.is_semi_eulerian()) {
        std::cout << "The graph is a semi-Eulerian graph.\n\nEulerian paths:\n" << std::flush;
        Graph::print_paths(graph.eulerian_paths());
    } else {
        std::cout << "The graph is not a semi-Eulerian graph.\n" << std::flush;
    }
}
