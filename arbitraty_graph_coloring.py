import os
import math
import csv
import pandas as pd
import itertools 



class Cvf_Node_Effect_Graph:
    def __init__(self, graph_path, result_path):
        self.graph = self.read_graph(graph_path)
        self.graph_name = os.path.splitext(os.path.basename(graph_path))[0]
        self.result_path = result_path
        self.nodes = list(self.graph.keys())
        self.node_positions = {v : i for i, v in enumerate(self.nodes)}
        self.max_degree = self.get_max_degree()
        self.colors = list(range(self.max_degree+1))
        self.all_configurations = self.generate_configurations()
        self.program_transitions_rank = {}
        self.invariants = set()
        self.program_transitions_n_cvf = {}
        

        self.pt_rank_effect = {}
        self.cvfs_in_rank_effect = {}
        self.cvfs_out_rank_effect = {}


        self.pt_rank_effect_df = pd.DataFrame()
        self.cvfs_in_rank_effect_df = pd.DataFrame()
        self.cvfs_out_rank_effect_df = pd.DataFrame()

    
    def read_graph(self, graph_file):
        graph = {}
        with open(graph_file, "r") as f:
            for line in f:
                all_edges = line.split()
                node = all_edges[0]
                edges =  all_edges[1:]
                graph[node] = set(edges)
        return graph

    def get_max_degree(self):
        max_degree = 0
        for node, neighbor in self.graph.items():
            degree = len(neighbor)
            if degree > max_degree:
                max_degree = degree
        return max_degree
    
    def generate_configurations(self):
        # Generate all possible colorings using itertools.product
        all_colorings = list(itertools.product(self.colors, repeat=len(self.nodes)))

        # Convert the colorings into a list of dictionaries
        coloring_dicts = []
        for coloring in all_colorings:
            state = {self.nodes[i]: coloring[i] for i in range(len(self.nodes))}
            coloring_dicts.append(state)
        return coloring_dicts
    def is_valid_coloring(self, coloring):
        for node in self.graph:
            for neighbor in self.graph[node]:
                if coloring[node] == coloring[neighbor]:
                    return False
        return True
    
    def get_invariants(self):
        for coloring in self.all_configurations:
            if self.is_valid_coloring(coloring):
                inv = tuple(coloring.values())
                self.program_transitions_rank[inv] = {"L": 0, "C": 1, "A": 0, "Ar": 0, "M": 0}
                self.invariants.add(inv)

        return self.invariants
    

    def is_different_color(self,node_color, neighbor_color):
        for color in neighbor_color:
            if color == node_color:
                return False
        return True
    

    def get_minimal_color(self, neighbor_color):
        for i in range(self.max_degree + 1):
            if i not in neighbor_color:
                return i
     
    def is_program_transition(self,position, start_state, perturb_state):
        if start_state in self.invariants and perturb_state in self.invariants:
            return False
        node =  self.nodes[position]
        neighbor_pos = [self.node_positions[n] for n in self.graph[node]]
        neighbor_color = set(perturb_state[i] for i in neighbor_pos)
        minimal = self.get_minimal_color(neighbor_color)
        return perturb_state[position] == minimal

    def get_program_transitions(self, start_state):
        program_transitions = set()
        for position, val in enumerate(start_state):
            node = self.nodes[position]
            neighbor_pos = [self.node_positions[n] for n in self.graph[node]]
            neighbor_color = set(start_state[i] for i in neighbor_pos)
            if self.is_different_color(val, neighbor_color):
                continue

            all_colors = set(range(self.max_degree + 1))
            
            for color in all_colors:
                perturb_state = list(start_state)
                perturb_state[position] = color
                perturb_state = tuple(perturb_state)
                
                if perturb_state != start_state:
                    if self.is_program_transition(position, start_state, perturb_state):
                        program_transitions.add(perturb_state)
        return {"program_transitions": program_transitions}

    def get_cvfs(self, start_state):
        cvfs_in = dict()
        cvfs_out = dict()

        for position,_ in enumerate(start_state):
            all_colors = set(range(self.max_degree + 1))
            for color in all_colors:
                perturb_state = list(start_state)
                perturb_state[position] = color
                perturb_state = tuple(perturb_state)
                if perturb_state != start_state:
                    if start_state in self.invariants:
                        cvfs_in[perturb_state] = position
                    else:
                        cvfs_out[perturb_state] = position

        return {"cvfs_in": cvfs_in , "cvfs_out": cvfs_out }
        

    def compute_transitions_and_cvfs(self):
        
        for state in self.all_configurations:
            state_tuple = tuple(state.values())
            self.program_transitions_n_cvf[state_tuple] = {**self.get_program_transitions(state_tuple), **self.get_cvfs(state_tuple)}
        return self.program_transitions_n_cvf

    def rank_states(self):
        unranked_states = set(self.program_transitions_n_cvf.keys()) - set(self.program_transitions_rank.keys())
        while unranked_states:
            ranked_states = set(self.program_transitions_rank.keys())
            removed_unranked_state = set()
            for state in unranked_states:
                dests = self.program_transitions_n_cvf[state]['program_transitions']
                if dests - ranked_states:
                    pass
                else:
                    total_path_length = 0
                    path_count = 0
                    max_length = 0
                    for config in dests:
                        path_count += self.program_transitions_rank[config]["C"]
                        total_path_length += self.program_transitions_rank[config]["L"] + self.program_transitions_rank[config]["C"]
                        max_length = max(max_length, self.program_transitions_rank[config]["M"])
                    self.program_transitions_rank[state] = {
                        "L": total_path_length,
                        "C": path_count,
                        "A": total_path_length/path_count,
                        "Ar": math.ceil(total_path_length/path_count),
                        "M": max_length + 1
                    }
                    removed_unranked_state.add(state)
            unranked_states -= removed_unranked_state

    
    def calculate_rank_effect(self):
        # Program Transitions rank effect
        for state, pt_cvfs in self.program_transitions_n_cvf.items():
            for pt in pt_cvfs['program_transitions']:
                self.pt_rank_effect[(state, pt)] = {
                    "Ar": self.program_transitions_rank[pt]["Ar"] - self.program_transitions_rank[state]["Ar"],
                    "M": self.program_transitions_rank[pt]["M"] - self.program_transitions_rank[state]["M"]
                }

            # CVFS_In and Out rank Effect
            for cvf, node in pt_cvfs['cvfs_in'].items():
                self.cvfs_in_rank_effect[(state, cvf)] = {
                    "node": node,
                    "Ar": self.program_transitions_rank[cvf]["Ar"] - self.program_transitions_rank[state]["Ar"],
                    "M": self.program_transitions_rank[cvf]["M"] - self.program_transitions_rank[state]["M"]
                }
            
            # Moved the cvfs_out processing inside the loop
            for cvf, node in pt_cvfs['cvfs_out'].items():
                self.cvfs_out_rank_effect[(state, cvf)] = {
                    "node": node,
                    "Ar": self.program_transitions_rank[cvf]["Ar"] - self.program_transitions_rank[state]["Ar"],
                    "M": self.program_transitions_rank[cvf]["M"] - self.program_transitions_rank[state]["M"]
                }

    def rank_count(self):
        pt_rank_ = []
        for state in self.program_transitions_rank:
            pt_rank_.append({"state": state, **self.program_transitions_rank[state]})

        pt_rank_df = pd.DataFrame(pt_rank_)
        pt_avg_counts = pt_rank_df['Ar'].value_counts()
        pt_max_counts = pt_rank_df['M'].value_counts()

        fieldnames = ["Rank", "Count (Max)", "Count (Avg)"]
        with open(f"{self.result_path}/rank_{self.graph_name}.csv","w", newline="") as f:
            writer = csv.DictWriter(f, fieldnames=fieldnames)
            writer.writeheader()

            for rank in sorted(set(pt_avg_counts.index)|set(pt_max_counts.index)):
                writer.writerow({"Rank": rank, "Count (Max)": pt_max_counts.get(rank, 0), "Count (Avg)": pt_avg_counts.get(rank, 0)})


    def rank_effect_count(self):
        #Program Transition rank effect count
        pt_rank_effect_ = []
        for state in self.pt_rank_effect:
            pt_rank_effect_.append({"state": state, **self.pt_rank_effect[state]})
        self.pt_rank_effect_df = pd.DataFrame(pt_rank_effect_)
        
        pt_avg_counts = self.pt_rank_effect_df['Ar'].value_counts()
        pt_max_counts = self.pt_rank_effect_df['M'].value_counts()

        #Cvfs_in and out rank effect count
        cvfs_in_rank_effect_ = []
        for state in self.cvfs_in_rank_effect:
            cvfs_in_rank_effect_.append({"state": state, **self.cvfs_in_rank_effect[state]})
    
        self.cvfs_in_rank_effect_df = pd.DataFrame(cvfs_in_rank_effect_)

        cvfs_out_rank_effect_ = []
        for state in self.cvfs_out_rank_effect:
            cvfs_out_rank_effect_.append({"state": state, **self.cvfs_out_rank_effect[state]})

        self.cvfs_out_rank_effect_df = pd.DataFrame(cvfs_out_rank_effect_)

        cvf_in_avg_counts = self.cvfs_in_rank_effect_df['Ar'].value_counts()
        cvf_in_max_counts = self.cvfs_in_rank_effect_df['M'].value_counts()
        cvf_out_avg_counts = self.cvfs_out_rank_effect_df['Ar'].value_counts()
        cvf_out_max_counts = self.cvfs_out_rank_effect_df['M'].value_counts()

        #Writing in the result
        fieldnames = ["Rank Effect", "PT (Max)", "PT (Avg)", "CVF In (Max)", "CVF In (Avg)", "CVF Out (Max)", "CVF Out (Avg)"]
        with open(f"{self.result_path}/rank_effect_{self.graph_name}.csv","w", newline="") as f:
            writer = csv.DictWriter(f, fieldnames=fieldnames)
            writer.writeheader()

            for re in sorted(
                set(pt_avg_counts.index) |
                set(pt_max_counts.index) |
                set(cvf_in_avg_counts.index) |
                set(cvf_in_max_counts.index) |
                set(cvf_out_avg_counts.index) |
                set(cvf_out_max_counts.index)
            ):
                writer.writerow({
                    "Rank Effect": re,
                    "PT (Max)": pt_max_counts.get(re, 0),
                    "PT (Avg)": pt_avg_counts.get(re, 0),
                    "CVF In (Max)": cvf_in_max_counts.get(re, 0),
                    "CVF In (Avg)": cvf_in_avg_counts.get(re, 0),
                    "CVF Out (Max)": cvf_out_max_counts.get(re, 0),
                    "CVF Out (Avg)": cvf_out_avg_counts.get(re, 0),
                })
    def rank_effect_individual_nodes(self):
        cvf_in_avg_counts_by_node = self.cvfs_in_rank_effect_df.groupby(['node', 'Ar'])['Ar'].count()
        cvf_in_max_counts_by_node = self.cvfs_in_rank_effect_df.groupby(['node', 'M'])['M'].count()
        cvf_out_avg_counts_by_node = self.cvfs_out_rank_effect_df.groupby(['node', 'Ar'])['Ar'].count()
        cvf_out_max_counts_by_node = self.cvfs_out_rank_effect_df.groupby(['node', 'M'])['M'].count()

        max_Ar = max(self.cvfs_in_rank_effect_df['Ar'].max(), self.cvfs_out_rank_effect_df['Ar'].max())
        min_Ar = min(self.cvfs_in_rank_effect_df['Ar'].min(), self.cvfs_out_rank_effect_df['Ar'].min())

        max_M = max(self.cvfs_in_rank_effect_df['M'].max(), self.cvfs_out_rank_effect_df['M'].max())
        min_M = min(self.cvfs_in_rank_effect_df['M'].min(), self.cvfs_out_rank_effect_df['M'].min())

        max_Ar_M = max(max_Ar, max_M)
        min_Ar_M = min(min_Ar, min_M)

        # rank effect of individual node
        fieldnames = ["Node", "Rank Effect", "CVF In (Max)", "CVF In (Avg)", "CVF Out (Max)", "CVF Out (Avg)"]
        with open(f"{self.result_path}/rank_effect_by_node_{self.graph_name}.csv","w", newline="") as f:
            writer = csv.DictWriter(f, fieldnames=fieldnames)
            writer.writeheader()

            # for node_re in sorted(
            #     set(cvf_in_avg_counts_by_node.index) |
            #     set(cvf_in_max_counts_by_node.index) |
            #     set(cvf_out_avg_counts_by_node.index) |
            #     set(cvf_out_max_counts_by_node.index)
            # ):
            for node in self.nodes:
                for rank_effect in range(min_Ar_M, max_Ar_M+1):
                    node_re = (self.node_positions[node], rank_effect)
                    writer.writerow({
                        "Node": node,
                        "Rank Effect": rank_effect,
                        "CVF In (Max)": cvf_in_max_counts_by_node.get(node_re, 0),
                        "CVF In (Avg)": cvf_in_avg_counts_by_node.get(node_re, 0),
                        "CVF Out (Max)": cvf_out_max_counts_by_node.get(node_re, 0),
                        "CVF Out (Avg)": cvf_out_avg_counts_by_node.get(node_re, 0),
                    })



    def analyse(self):
        self.get_invariants()
        self.compute_transitions_and_cvfs()
        self.rank_states()
        self.calculate_rank_effect()
        self.rank_count()
        self.rank_effect_count()
        self.rank_effect_individual_nodes()
        print("Test Graph")







