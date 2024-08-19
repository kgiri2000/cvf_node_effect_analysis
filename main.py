import os
from arbitraty_graph_coloring import Cvf_Node_Effect_Graph
from dijkstra_graph_coloring import Cvf_Node_Effect_Dijkstra


if __name__ == "__main__":
    graph_path = "graphs/dijkstra_10_nodes.txt"
    result_path = "results"
    graph_name = os.path.splitext(os.path.basename(graph_path))[0]
    identifier = graph_name.split("_")[0]
    if identifier == "graph":
        cvf =  Cvf_Node_Effect_Graph(graph_path,result_path)
    else:
        cvf =  Cvf_Node_Effect_Dijkstra(graph_path,result_path)

    cvf.analyse()



