use std::collections::{HashMap, HashSet, VecDeque};

enum Graph {
    AdjacencyList(HashMap<usize, HashSet<usize>>),
    AdjacencyMatrix(Vec<Vec<bool>>),
}

#[derive(Eq, Hash, Clone)]
struct Edge {
    beginning: usize,
    ending: usize,
}

impl PartialEq for Edge {
    fn eq(&self, other: &Self) -> bool {
        self.beginning == other.beginning
            && self.ending == other.ending
    }
}

impl Graph {
    fn list_new() -> Self {
        Self::AdjacencyList(Default::default())
    }

    fn matrix_new() -> Self {
        Self::AdjacencyMatrix(Default::default())
    }

    fn insert_edge(&mut self, edge: &Edge) {
        match self {
            Self::AdjacencyList(list) => {
                if let Some(set) = list.get_mut(&edge.beginning) {
                    set.insert(edge.ending);
                } else {
                    let mut new_set = HashSet::new();
                    new_set.insert(edge.ending);
                    list.insert(edge.beginning, new_set);
                }
            }
            Self::AdjacencyMatrix(mat) => {
                if mat.len() <= edge.beginning {
                    mat.resize(edge.beginning + 1, Default::default());
                }
                let row = &mut mat[edge.beginning];
                if row.len() <= edge.ending {
                    row.resize(edge.ending + 1, Default::default());
                }
                row[edge.ending] = true;
            }
        }
    }

    fn remove_edge(&mut self, edge: Edge) {
        match self {
            Self::AdjacencyList(list) => {
                if let Some(set) = list.get_mut(&edge.beginning) {
                    set.remove(&edge.ending);
                }
            }
            Self::AdjacencyMatrix(mat) => {
                if mat.len() > edge.beginning {
                    let row = &mut mat[edge.beginning];
                    if row.len() > edge.ending {
                        row[edge.ending] = false;
                    }
                }
            }
        }
    }

    fn vertices_from_vertex(&self, beginning: usize) -> Vec<usize> {
        let mut result = Vec::new();
        match self {
            Self::AdjacencyList(list) => {
                if let Some(set) = list.get(&beginning) {
                    result = set.iter().map(|x| *x).collect();
                }
            }
            Self::AdjacencyMatrix(mat) => {
                if beginning < mat.len() {
                    result = mat[beginning].iter().enumerate()
                        .filter(|x| *x.1).map(|x| x.0).collect();
                }
            }
        }
        result
    }

    fn vertices(&self) -> Vec<usize> {
        let mut set = HashSet::new();
        match self {
            Self::AdjacencyList(list) => {
                for (k, vs) in list.iter() {
                    set.insert(*k);
                    for v in vs.iter() {
                        set.insert(*v);
                    }
                }
            }
            Self::AdjacencyMatrix(mat) => {
                for (row_number, row) in mat.iter().enumerate() {
                    let mut all_zero = true;
                    for (item_number, item) in row.iter().enumerate() {
                        if *item {
                            set.insert(item_number);
                            all_zero = false;
                        }
                    }
                    if !all_zero {
                        set.insert(row_number);
                    }
                }
            }
        }
        set.iter().map(|x| *x).collect()
    }
}

#[derive(Default)]
struct Attributes<EA, VA> {
    edge_attrs: HashMap<Edge, EA>,
    vertex_attrs: HashMap<usize, VA>,
}

impl<EA, VA> Attributes<EA, VA> {
    fn edge_get(&self, edge: &Edge) -> Option<&EA> {
        self.edge_attrs.get(edge)
    }

    fn edge_set(&mut self, edge: &Edge, attr: EA) {
        self.edge_attrs.insert((*edge).clone(), attr);
    }

    fn vertex_get(&self, vertex: usize) -> Option<&VA> {
        self.vertex_attrs.get(&vertex)
    }

    fn vertex_set(&mut self, vertex: usize, attr: VA) {
        self.vertex_attrs.insert(vertex, attr);
    }
}

struct AttributedGraph<EA, VA> {
    graph: Graph,
    attrs: Attributes<EA, VA>,
}

impl AttributedGraph<i32, ()> {
    fn from_vec(edge_attrs: Vec<(usize, usize, i32)>) -> Self {
        let mut result = Self {
            graph: Graph::list_new(),
            attrs: Default::default(),
        };
        for edge_attr in edge_attrs.iter() {
            let edge = Edge { beginning: edge_attr.0, ending: edge_attr.1 };
            result.graph.insert_edge(&edge);
            result.attrs.edge_set(&edge, edge_attr.2);
        }
        result
    }
}

fn breadth_first_traverse(graph: &Graph) {
    print!("BFS-visit:");
    let vertices = graph.vertices();
    let mut visited: HashMap<_, _> =
        vertices.iter().map(|x| (*x, false)).collect();
    let mut pending = VecDeque::new();
    for v in vertices.iter() {
        if visited[v] {
            continue;
        }
        pending.push_back(*v);
        visited.insert(*v, true);
        while !pending.is_empty() {
            let front = *pending.front().unwrap();
            print!(" {}", front);
            pending.pop_front();
            for v in graph.vertices_from_vertex(front).iter() {
                if !visited[v] {
                    pending.push_back(*v);
                    visited.insert(*v, true);
                }
            }
        }
    }
    println!();
}

fn depth_first_traverse(graph: &Graph) {
    print!("DFS-visit:");
    let vertices = graph.vertices();
    let mut visited: HashMap<_, _> =
        vertices.iter().map(|x| (*x, false)).collect();
    fn recursion(u: usize, graph: &Graph, visited: &mut HashMap<usize, bool>) {
        print!(" {}", u);
        for v in graph.vertices_from_vertex(u).iter() {
            if !visited[v] {
                visited.insert(*v, true);
                recursion(*v, graph, visited);
            }
        }
    }
    for v in vertices.iter() {
        if !visited[v] {
            visited.insert(*v, true);
            recursion(*v, graph, &mut visited);
        }
    }
    println!();
}

fn shortest_path(attributed_graph: &AttributedGraph<i32, ()>,
                 beginning: usize, ending: usize) {
    let vertices = attributed_graph.graph.vertices();
    let mut pending: HashSet<_> = vertices.iter().map(|x| *x).collect();
    let mut dist: HashMap<_, _> =
        vertices.iter().map(|x| (*x, i32::MAX)).collect();
    let mut prev: HashMap<_, _> =
        vertices.iter().map(|x| (*x, usize::MAX)).collect();
    dist.insert(beginning, 0);
    while !pending.is_empty() {
        let u = *pending.iter().min_by_key(|x| dist[x]).unwrap();
        pending.remove(&u);
        for v in attributed_graph.graph.vertices_from_vertex(u).iter() {
            let edge = Edge { beginning: u, ending: *v };
            let delta = attributed_graph.attrs.edge_get(&edge).unwrap();
            let alt = dist[&u] + delta;
            if alt < dist[v] {
                dist.insert(*v, alt);
                prev.insert(*v, u);
            }
        }
    }
    fn trace_back(current: usize,
                  prev: &HashMap<usize, usize>,
                  result: &mut VecDeque<usize>) {
        if current != usize::MAX {
            result.push_front(current);
            trace_back(prev[&current], prev, result)
        }
    }
    let mut path = VecDeque::<usize>::new();
    trace_back(ending, &prev, &mut path);
    print!("Path:");
    for v in path {
        print!(" {}", v);
    }
    println!("\nMin-distance: {}", dist[&ending]);
}

fn main() {
    let distance_graph = AttributedGraph::from_vec(
        vec![(1, 2, 7), (1, 3, 9), (1, 6, 14),
             (2, 1, 7), (2, 3, 10), (2, 4, 15),
             (3, 1, 9), (3, 2, 10), (3, 4, 11),
             (3, 6, 2), (4, 2, 15), (4, 3, 11),
             (4, 5, 6), (5, 4, 6), (5, 6, 9),
             (6, 1, 14), (6, 3, 2), (6, 5, 9)]);
    breadth_first_traverse(&distance_graph.graph);
    println!();
    depth_first_traverse(&distance_graph.graph);
    println!();
    shortest_path(&distance_graph, 1, 5);
}
