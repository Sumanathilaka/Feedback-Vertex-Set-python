#-*- mode: python; python-indent: 4;-*-

import argparse # For parsing input arguments
import igraph # Fast graph library
import sys # System-related stuff
from collections import deque, Counter
import copy 
from itertools import dropwhile 
from io import StringIO
from tempfile import TemporaryFile



# Read in command-line arguments.
#
# The only, mandatory argument is the name of a file that
# contains the graph data.  We will later read this file and
# convert it into a Graph object G.
#
#
def get_args():
    # Parse command-line arguments.
    parser = argparse.ArgumentParser(prog = "python -O" + sys.argv[0])
    parser.add_argument("file",
                        type = argparse.FileType())
    
    return(parser.parse_args())



def read_input(args):
    # Read the input, remove comments. 
    clean_input = StringIO() # String as file.

    with open(args.file.name, 'r') as f:
        with clean_input:
            for line in f:
                if not line.lstrip().startswith('#'):
                    clean_input.write(line.lstrip())
            # Remove extra newline from the end.
            clean_string = clean_input.getvalue().rstrip() 
            
    # Write the cleaned-up input string to a temporary file so
    # that igraph can read it back. This file is automatically
    # deleted at the end of the with block.
    with TemporaryFile(mode="w+t") as f: # Read/write text, truncated.
        f.write(clean_string)
        f.seek(0)
        G = igraph.Graph.Read_Ncol(f, names = True, weights = False, directed=False)
        
    for v in G.vs():
        v["label"] = v.index 
        v["component"] = v.index

    # Throw away isolated vertices, including those which we
    # introduced spuriously.
    # Deleting vertices from a graph while iterating over them
    # results in strange behaviour. So we collect them first and
    # delete them all at one go.
    isolates = (x for x in G.vs() if (G.degree(x) == 0))
    G.delete_vertices(isolates)

    return G 

               
# Apply the degree-1 rule exhaustively, starting from next_vertex
# which has degree 1. forbidden_set is the set of vertices which
# must not be deleted during this process. small_degree_labels is
# a set of labels of vertices which have degree at most 2 in the
# graph.
def degree_one_rule(next_vertex, forbidden_set,
                    small_degree_labels):
    H = next_vertex.graph
    next_label = next_vertex['label']
    parent_vertex = next_vertex.neighbors()[0]
    parent_label = parent_vertex['label']
    next_vertex.delete() # Don't try to delete the label.
    parent_vertex = H.vs.find(label = parent_label)
    parent_degree = parent_vertex.degree()
    while parent_degree == 1 and \
          parent_label not in forbidden_set :
        next_vertex = parent_vertex
        next_label = next_vertex['label']
        parent_vertex = next_vertex.neighbors()[0]
        parent_label = parent_vertex["label"]
        next_vertex.delete()
        small_degree_labels.remove(next_label)
        parent_vertex = H.vs.find(label = parent_label)
        parent_degree = parent_vertex.degree()

    # At this point, parent_degree is not 1 or parent is
    # forbidden. If this degree is small and parent_vertex does
    # not belong to the forbidden set, then we add it to the list
    # of small-degree vertices.
    if parent_label not in forbidden_set:
        if parent_degree == 0:  # Throw this vertex away.
            parent_vertex.delete()
            small_degree_labels.remove(parent_label)

            # Now the degree of the parent vertex is 2, so we add
            # the label of this vertex to the set of small degree
            # vertices.
        elif parent_degree == 2: 
            small_degree_labels.add(parent_label)


# Apply the degree-2 rule to next_vertex.
def degree_two_rule(next_vertex, forbidden_set,
                    small_degree_labels, partial_fvs):
    H = next_vertex.graph
    next_label = next_vertex['label']
    neighbours = next_vertex.neighbors()
    nbr1 = neighbours[0]
    nbr2 = neighbours[1]

        
    # If both the neighbours are the same, then pick this sole
    # neighbour into our solution, unless this sole neighbour is
    # forbidden to be picked, in which case we pick next_vertex
    # itself into the solution. Since we reach this point only if
    # next_vertex is not forbidden, there is no third case to
    # handle.
    #
    # next_vertex has degree 2 because it is a self-loop, iff both
    # its neighbours are identical to itself. We check for this
    # case and pick next_vertex into the solution. This is safe
    # since we reach this point only if next_vertex is not
    # forbidden: if a vertex has a self-loop, then we do not add
    # it to the no-set anywhere. 
    #
    # Since we do this processing, there should be no
    # self-loops left in the graph once we are
    # done. That is, the only self-loops that could appear are
    # those which are present in the input, and these are dealt
    # with during the first call to reduct(). 
    if nbr1['label'] == nbr2['label']:  
        if next_label == nbr1['label']: # Self loop
            partial_fvs.append(next_label)
            next_vertex.delete() # Don't try to delete the label.
        else: # Not a self-loop, but a multiple edge.
            sole_neighbour = nbr1
            sole_nbr_label = sole_neighbour['label']

            if sole_nbr_label not in forbidden_set:
                partial_fvs.append(sole_nbr_label)
            else:
                partial_fvs.append(next_label)

            next_vertex.delete() # Don't try to delete the label.

            if sole_nbr_label not in forbidden_set:
                sole_neighbour = H.vs.find(label = sole_nbr_label)
                neighbours = sole_neighbour.neighbors()
                neighbour_labels = list(v['label'] for v in neighbours)

                sole_neighbour.delete()
                # discard = remove if present
                small_degree_labels.discard(sole_nbr_label)
                for neighbour_label in neighbour_labels:
                    if neighbour_label not in forbidden_set:
                        neighbour = H.vs.find(label = neighbour_label)
                        neighbour_degree = neighbour.degree()
                        if neighbour_degree <= 2:
                            small_degree_labels.add(neighbour_label)

    else: # Our vertex has two distinct neighbours, so we
        # bypass our vertex. Except if *both* the neighbours are
        # in the forbidden set, in which case we don't do
        # anything. 
        nbr1_label = nbr1['label']
        nbr2_label = nbr2['label']
        if (nbr1_label not in forbidden_set) or (nbr2_label not in forbidden_set):
            next_vertex.delete() # Don't try to delete the label.
            nbr1 = H.vs.find(label = nbr1_label)
            nbr2 = H.vs.find(label = nbr2_label)

            # Check if there is an existing edge between the
            # two neighbours.
            edge_id = H.get_eid(nbr1, nbr2, error = False) 
            if edge_id == -1: # There is no edge, so add one.
                H.add_edge(nbr1, nbr2)
            else: # There is already an edge. If this is a
                # multiple edge, then check if our vertex
                # deletion has made either of the two
                # end-points to be of small degree, and update
                # the set accordingly. Else add an edge to
                # make it an edge of multiplicity 2.
                edge = H.es[edge_id]
                if edge.is_multiple():
                    for nbr in [nbr1, nbr2]:
                        neighbour_label = nbr['label']
                        if nbr.degree() <= 2 and \
                           neighbour_label not in \
                           forbidden_set :
                            small_degree_labels.add(neighbour_label)
                else:
                    H.add_edge(nbr1, nbr2)


# Takes a graph G in igraph format and optionally a set of vertex
# labels of G as argument. Returns a tuple (partial_fvs,
# current_graph) where current_graph is the
# graph obtained by exhaustively applying the degree-0, 1, 2 rules
# to G, and partial_fvs is the set of those vertices that are forced
# into every FVS of G by these rules.
#
# None of the vertices whose labels are present in the (optional)
# list forbidden_set will be deleted during the application of
# these rules. This list is empty by default.
#
# Whenever we need to refer to vertices we actually use their
# labels instead.
#
# This function first makes a deep copy of G so that the input
# instance is not modified.

# Calling it "reduct" to avoid conflicts with the built-in reduce()
def reduct(G, forbidden_set = []):

    # Since we will do frequent membership checking:
    forbidden_set = set(forbidden_set)

    H = G.copy() # Make a deep copy so that we don't change G.

    # We use deques below because we build these lists element by
    # element, which is not very efficient with the list data
    # structure in Python.
    partial_fvs = deque() # The partial fvs that we have computed
                          # so far.

    # We add to a set the labels of those vertices H whose degree
    # is at most 2, provided they are not in forbidden_set.  We
    # need to add the labels, and not the vertices themselves,
    # because the labels are the one invariant for each vertex
    # object. This is an artifact of the way igraph implements
    # vertices.
    labels = (v['label'] for v in H.vs if v.degree() <= 2)
    small_degree_labels = set(labels) - forbidden_set

    # From now on, the set small_degree_labels must contain
    # exactly those vertices of H whose degrees are at most 2 and
    # which are not in forbidden_set.

    # We now process, according to the degree-0,1,2 reduction
    # rules, the vertices whose labels are in
    # small_degree_labels. Whenever we make the degree of a vertex
    # to be at most 2, and we can't process this vertex
    # immediately, and the vertex is not in forbidden_set, we
    # add the label of this vertex to small_degree_labels.

    while small_degree_labels:
        next_label = small_degree_labels.pop()
        next_vertex = H.vs.find(label = next_label)
        next_degree = next_vertex.degree()
        if next_label not in forbidden_set:
            if next_degree == 0 :
                # Throw this vertex away.  We don't delete the label
                # of this vertex from the set of small-degree labels,
                # because we have popped this label already.
                next_vertex.delete() 
            elif next_degree == 1 : 
                degree_one_rule(next_vertex, forbidden_set,
                                small_degree_labels)

            
            else: # We found a vertex of degree 2.
                degree_two_rule(next_vertex, forbidden_set,
                                small_degree_labels, partial_fvs)
            
    # We have now exhaustively applied the reduction rules, and
    # can return the resulting partial FVS, the remaining
    # graph, and the set of deleted vertices.

    return(set(partial_fvs), H)

# The subsets of vertices (i.e. vertex labels) of the input graph
# that we have found so far to induce non-forest subgraphs of the
# input graph. This is for speeding up computation, seems to work. 
cyclic_subsets = set()

# Return True if graph G is a forest, and False otherwise. This
# does not modify G.
def is_forest(G):
    #return (not G.has_multiple()) and (not G.girth())
    # Doing some memoization seems to make this really faster. 
    global cyclic_subsets
    vertex_labels = frozenset(v['label'] for v in G.vs)
    if vertex_labels in cyclic_subsets:
        return False
    else:
        isforest = (not G.has_multiple()) and (not G.girth())
        if isforest:
            return True
        else:
            cyclic_subsets.add(vertex_labels)
            return False


# Finds and returns a lower bound for the size of an FVS of graph
# G. This lower bound is based on some simple arguments. We assume
# that the input graph has no vertices of degree up to 2.
def fvs_lower_bound(G):

    n = G.vcount()

    if n == 0: # Don't do anything fancy if the graph is already empty
        return 0
    else:
    
        max_degree = G.maxdegree()

        first_lower_bound = int((n + 2)/(max_degree + 1))
        
        degrees = sorted(G.degree(), reverse = True) # Sorted non-increasing

        min_degree = degrees[(n - 1)]
        d = min_degree - 2
    
        k = first_lower_bound
        degree_sum = sum(degrees[0:k])

        # A potential improvement on the lower bound
        new_lower_bound = (d*n - degree_sum + 2)/d

        if (new_lower_bound > k): # There is some actual improvement
            # in the lower bound.
            
            # Iterate as long as we have the inequality right
            while (k < new_lower_bound): # No FVS of size at most k
                k = k + 1 # Try the next k
                degree_sum = sum(degrees[0:k])
                #new_lower_bound = n - degree_sum + 2
                new_lower_bound = (d*n - degree_sum + 2)/d

        return k
    
# Crude lower bound on fvs size, obtained by greedily packing
# cycles in the graph.
def approx_packing_number(G):
   # Make a deep copy so that we don't mess up G.
    H = G.copy()
    packing_approx = 0

    while H.has_multiple(): # The girth function does not see multiedges.
        multi_edge = next(dropwhile(lambda e: not e.is_multiple(), H.es))
        H.delete_vertices(list(multi_edge.tuple))
        packing_approx += 1

    H_girth_vertices = H.girth(True)
    while H_girth_vertices: # While there are cycles left in H
        H.delete_vertices(H_girth_vertices)
        packing_approx += 1
        H_girth_vertices = H.girth(True)

    return packing_approx

# Pick a smallest cycle from G and return its vertex list. A
# multiple edge counts as a cycle. This function does not modify
# its argument.
def pick_smallest_cycle(G):
    if G.has_multiple(): # The girth function does not see multiedges.
        multi_edge = next(dropwhile(lambda e: not e.is_multiple(), G.es))
        vertex_set = list(multi_edge.tuple)
        vertex_label_set = [G.vs[multi_edge.tuple[0]]['label'], G.vs[multi_edge.tuple[1]]['label']]
        return vertex_label_set
        
    
    # No multiple edges, so find a simple smallest cycle.
    girth_vertices = G.girth(True)
    if girth_vertices: 
        girth_vertex_labels = list(G.vs[v]['label'] for v in girth_vertices)
        return girth_vertex_labels



# Return True if the subgraph of graph G, induced by its vertices
# corresponding to the given set of vertex labels, is a
# forest. Return False otherwise.
def subgraph_is_forest(G, vertex_labels) :
    vertex_dict = dict(zip(G.vs.get_attribute_values('label'), G.vs.indices))
    vertices = (G.vs[vertex_dict[l]] for l in vertex_labels)

    return is_forest(G.induced_subgraph(vertices))

# Branch on a shortest cycle.
def branch(G):

    # The maximum among component names.
    max_component = max(map(lambda v: v['component'], G.vs))

    # The best fvs we could find so far. This function does not
    # modify its argument.
    global_current_fvs = set(greedy_approx(G))
    global_current_upper_bound = len(global_current_fvs)
    
    # Compute a lower bound or two for FVS. Neither of these
    # functions modifies its argument.
    global_lower_bound1 = fvs_lower_bound(G) 
    global_lower_bound2 = approx_packing_number(G)
    
    
    global_current_lower_bound = global_lower_bound1
    if global_lower_bound2 > global_current_lower_bound:
        global_current_lower_bound = global_lower_bound2

    if global_current_lower_bound == global_current_upper_bound :
        return global_current_fvs # We got lucky on this one.

    graph = G
    yes_part = set() # Vertex labels
    no_part = set() # Vertex labels
    state_list = deque([(graph, yes_part, no_part)])     
    
    while state_list:
        (H, yes_part, no_part) = state_list.pop()
        # The best fvs we could find so far.
        local_current_fvs = greedy_approx(H)
        local_current_upper_bound = len(local_current_fvs)

        # Compute a lower bound for FVS. Cannot use the
        # degree-based method because there is no guarantee that
        # the minimum degree of H is at least 3, at this point.
        local_current_lower_bound = approx_packing_number(H)

        

        local_candidate_fvs = local_current_fvs | yes_part # Set union.
        local_candidate_upper_bound = len(local_candidate_fvs)
        if local_candidate_upper_bound == global_current_lower_bound:
            return local_candidate_fvs # We got lucky on this one.
        elif local_candidate_upper_bound < global_current_upper_bound:

            #global_current_upper_bound < optimal_check_value and optimality_ticker >= optimality_check_threshold:

            global_current_fvs = local_candidate_fvs
            global_current_upper_bound = len(local_candidate_fvs)

        # The greedy approximation did not get us a certifiably
        # best possible upper bound for H, so we have to process
        # it futher.
        yes_part_size = len(yes_part)

        # We process this state only if the yes-part is smaller
        # than the current best fvs.
        if yes_part_size < global_current_upper_bound: # and no_part_is_forest:

            # This is an attempt at optimization. If we have
            # already collected a sufficiently large partial fvs
            # (the yes-part), check to see if the best that we can
            # get from the remaining graph exceeds our remaining
            # budget. If this happens, then we don't need to
            # process this state and its children. This could
            # result in large savings if we are lucky.

            # We first apply the reduction  rules. 
            (partial_fvs, H) = reduct(H, forbidden_set = no_part)

            if yes_part_size >= (global_current_upper_bound/3): # TODO: Tweak this fraction
                # Check if we can rule out this branch
                # already. Seems to significantly improve performance.


                # The remaining instance.
                (rest_partial_fvs, rest_reduced_graph)  = copy.deepcopy((partial_fvs, H))

                # Compute a lower bound. This function does not
                # modify its argument.  We cannot use the
                # degree-based bound, because rest_reduced_graph
                # may have vertices (from no_part) of degree at
                # most 2.
                rest_lower_bound = approx_packing_number(rest_reduced_graph)

                rest_lower_bound += len(rest_partial_fvs)

                if (yes_part_size + rest_lower_bound) >= \
                   global_current_upper_bound:
                    continue


            # Now we check if the partial solution that we have
            # found so far, is already at least as big as our
            # current best upper bound. If it is, then we abort
            # this state.
            yes_part = yes_part | partial_fvs # Set union-update
            yes_part_size = len(yes_part)

            if yes_part_size > global_current_upper_bound :
                continue

            # If, after the reduction, we have no more vertices in
            # the non-no part of H, then the set we have picked so
            # far is an FVS for the input graph. This is because
            # H[no_part] is a forest.
            H_is_trivial = (H.vcount() - len(no_part) == 0)
            if H_is_trivial: # This means that we have found an FVS for the graph.
                if yes_part_size < global_current_upper_bound:
                    global_current_upper_bound = yes_part_size
                    
                    global_current_fvs = yes_part

                    if global_current_upper_bound == global_current_lower_bound:
                        return global_current_fvs

            # If H is nontrivial at this point, then its vertices
            # (other than some vertices in no_part, and some
            # neighbours of the no_part) have minimum degree at
            # least 3. We branch on the "non-no" vertices of a
            # shortest cycle of H.
            else: 
                # Get the label set of a smallest cycle in H.
                C = pick_smallest_cycle(H)
                girth = len(C)
               
                # The label of the vertex from the cycle that we
                # pick in our solution.
                v = None

                # The prefix of the cycle that we will push to the
                # no-part.
                new_nos = None
               
                # Loop over the vertex labels of the cycle. 
                for index in range(girth):
                    v = C[index] 
                    new_nos = C[:index]
                    # We don't want to pick a no-vertex into our
                    # solution.
                    if v not in no_part:
                        N_i = set(no_part)

                        N_i = N_i | set(new_nos)

                        # If H[N_i] is not a forest, then we stop
                        # processing this state and go to the
                        # next.
                        if not subgraph_is_forest(H, N_i): 
                            continue
                        
                        # A list of lists, where each list is the
                        # set of all labels of a component in
                        # H[N_i].
                        components = get_components(H, N_i)
                        
                        promoted_labels = set() # Labels of vertices that are
                        # promoted to the yes-part because they
                        # see two or more vertices in a component
                        # of H[N_i].
                        all_labels = set(v['label'] for v in H.vs)
                        candidate_labels = all_labels - N_i
                        for candidate_label in candidate_labels:
                            candidate_vertex = H.vs.find(label = candidate_label)
                            neighbour_labels = set(x['label'] for x in candidate_vertex.neighbors())
                            for component in components:
                                if len(component & neighbour_labels) >= 2:
                                   promoted_labels.add(candidate_label)
                                   break

                        Y_i = copy.deepcopy(yes_part)
                        Y_i |= (set([v]) | promoted_labels)

                        if len(Y_i) >= global_current_upper_bound :
                            continue

                        H_i = H.copy()
                        H_i.delete_vertices(v for v in H_i.vs.select(label_in = Y_i))
                        

                        state_list.append((H_i, Y_i, N_i))
                     
    return global_current_fvs


# To remember component label sets that we have already computed. 
component_label_sets = dict()

# Return a list of lists, where each list is the set of all labels
# of a component in G[X] where X is the set of vertices of G
# corresponding to label_set. Does not modify its arguments.
def get_components(G, label_set):
    global component_label_sets

    component_lists = component_label_sets.get(frozenset(label_set))
    if component_lists:
        return component_lists
    
    vertex_dict = dict(zip(G.vs.get_attribute_values('label'), G.vs.indices))
    vertices = (G.vs[vertex_dict[l]] for l in label_set)

    component_lists = list()
    subgraph = G.induced_subgraph(vertices)

    index_set = set(v.index for v in subgraph.vs)
    while index_set:
        temp_set = set()
        root = index_set.pop()
        for v in subgraph.bfsiter(root, igraph.ALL):
            temp_set.add(v['label'])
        others = set(subgraph.subcomponent(root)) - set([root])
        for index in others:
            index_set.remove(index)
        component_lists.append(temp_set)
        
    component_label_sets[frozenset(label_set)] = component_lists
        
    return component_lists




# The simple greedy approximation algorithm. Returns an
# approximate FVS. Does not modify graph G.
def greedy_approx(G):

    G = G.copy() 
    H = G.copy() # For a correctness check at the end.
    
    approx_fvs = deque()
    (partial_fvs, G) = reduct(G)
    approx_fvs.extend(partial_fvs)

    while G.vcount() : # The min-degree-3 reduction takes care of
                       # the base case and leaves an empty graph.

        # Pick the vertex of the largest degree to include in the approximate fvs.
        next_vertex = max_degree_vertex(G)
        approx_fvs.append(next_vertex['label'])
        G.delete_vertices([next_vertex])

        (partial_fvs, G) = reduct(G)
        approx_fvs.extend(partial_fvs)

    approx_fvs_vertices = H.vs.select(label_in = approx_fvs)

    H.delete_vertices(approx_fvs_vertices)
    
    return set(approx_fvs)

# Return a vertex of the maximum degree in graph G. This function
# does not modify G.
def max_degree_vertex(G): 
    max_degree = 0
    max_vertex = None
    for v in G.vs:
        v_degree = v.degree()
        if v_degree > max_degree:
            max_degree = v_degree
            max_vertex = v 
    return max_vertex 


# Parse command line arguments and invoke functions which do the
# actual work.
# 
if __name__ == '__main__':

    # Read in the command-line arguments.
    args = get_args()
    
    # Read the input file into an igraph graph object.
    G = read_input(args)
    
    #
    # This call does not modify G.
    (partial_fvs, reduced_graph) = reduct(G)

    # Lower bounds on the size of an fvs of the *reduced graph*,
    # computed in different ways. Neither of these modifies their
    # input graphs. 
    lower_bound1 = fvs_lower_bound(reduced_graph) 
    lower_bound2 = approx_packing_number(reduced_graph)
    
    current_lower_bound = lower_bound1
    if lower_bound2 > current_lower_bound:
        current_lower_bound = lower_bound2

    current_lower_bound += len(partial_fvs)

    # Branch on vertices of the reduced graph to find a
    # smallest FVS of the reduced graph. This modifies
    # reduced_graph. We need to do this only if there are vertices
    # left in the graph.
    remaining_fvs = []
    if reduced_graph.vcount():
        remaining_fvs = branch(reduced_graph)

    fvs = list(v for v in (list(partial_fvs) + list(remaining_fvs)))
    
    #assert len(fvs) == len(set(fvs)), "The FVS contains duplicates."

    #forest = G.copy() # This is the original graph 
    #forest.delete_vertices(fvs)
    #assert is_forest(forest), "The set we found is NOT an fvs."

    # Get the names of the fvs vertices from the input graph G,
    # and print them one on each line. 
    for v in G.vs.select(label_in = fvs):
        print(v['name'])
