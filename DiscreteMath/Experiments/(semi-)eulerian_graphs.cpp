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
    using adj_mat_type = std::vector<std::vector<bool>>;
    using path_type = std::list<std::size_t>;
    using paths_type = std::list<path_type>;

    explicit Graph(adj_mat_type mat, std::size_t edge_count) :
            mat(std::move(mat)), edges(edge_count) {}

    static Graph from_edges(std::size_t vertices, const std::vector<edge_type> &edges) {
        adj_mat_type mat(vertices, std::vector<bool>(vertices, false));
        std::size_t edge_count = 0;
        for (const Graph::edge_type &e: edges) {
            mat[e.first][e.second] = true;
            mat[e.second][e.first] = true;
        }
        for (std::size_t i = 0; i != vertices; ++i) {
            for (std::size_t j = i + 1; j != vertices; ++j) {
                if (mat[i][j]) {
                    ++edge_count;
                }
            }
        }
        return Graph(mat, edge_count);
    }

    std::size_t count_degree(std::size_t v) const {
        std::size_t degree = 0;
        for (size_t j = 0; j != mat.size(); ++j) {
            if (mat[v][j]) {
                ++degree;
            }
        }
        return degree;
    }

    inline std::size_t edge_count() const {
        return edges;
    }

    bool is_connected() const {
        std::vector<bool> visited(mat.size(), false);
        std::function<void(std::size_t)> dfs =
                [this, &dfs, &visited](std::size_t u) {
                    visited[u] = true;
                    for (std::size_t v = 0; v != edges; ++v) {
                        if (!visited[v] && mat[u][v]) {
                            dfs(v);
                        }
                    }
                };
        dfs(0);
        for (std::size_t i = 0; i != mat.size(); ++i) {
            if (!visited[i]) {
                return false;
            }
        }
        return true;
    }

    bool is_eulerian() const {
        if (!is_connected()) {
            return false;
        }
        for (size_t i = 0; i != mat.size(); ++i) {
            std::size_t degree = 0;
            for (size_t j = 0; j != mat.size(); ++j) {
                if (mat[i][j]) {
                    ++degree;
                }
            }
            if (degree % 2) {
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
            std::size_t degree = count_degree(v);
            if (degree % 2) {
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
    std::vector<Graph::edge_type> edges;
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
    std::function<void(const Graph::paths_type &)> print_paths =
            [&graph](const Graph::paths_type &paths) {
                for (const Graph::path_type &path: paths) {
                    std::size_t count = 0;
                    for (std::size_t v: path) {
                        std::cout << v + 1 << (count++ != graph.edge_count() ? "-" : "");
                    }
                    std::cout << '\n';
                }
                std::cout << std::flush;
            };
    if (graph.is_eulerian()) {
        std::cout << "The graph is an Eulerian graph.\n\nEulerian loops:\n" << std::flush;
        print_paths(graph.eulerian_paths());
    } else if (graph.is_semi_eulerian()) {
        std::cout << "The graph is a semi-Eulerian graph.\n\nEulerian paths:\n" << std::flush;
        print_paths(graph.eulerian_paths());
    } else {
        std::cout << "The graph is not a semi-Eulerian graph.\n" << std::flush;
    }
}
