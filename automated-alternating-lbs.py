#!/usr/bin/env python3

#Code for automating the synthesis of alternation-tradingi proofs
#following the ideas of http://www.cs.cmu.edu/~ryanw/automated-lbs.pdf
# (c) Ryan Williams 2010


import sys
import argparse
import pulp
from typing import Any, Dict, List, Tuple


def annotationGenerator(n: int):
    """
        n: an integer

        yields: a list of integers 

        A generator that yields valid proof annotations of length n. We require n to be odd because any valid 
        proof has odd length (first speedup adds two quantifiers, every subsequent step changes quantifier count
        by one).  

        1 denotes a SPEEDUP
        0 denotes a SLOWDOWN

        Procedure for generating strings of well-balanced parentheses taken from Knuth Vol. 4, Pre-Fascicle 4a, 
        p. 3, which was taken from I. Semba IPL 12 , 188-192, 1981. 
    """
    assert(n%2 == 1)
    curr = [0, 1]*(n-3)
    curr.insert(0,1)
    m = 2*n-1
    while 1: 
        output = curr[1:]
        output.insert(0, 1)
        output.append([0, 0])
        yield output
        curr[m] = 1
        if curr[m-1] == 1:
            curr[m-1] = 0
            m = m-1
        else:
            j = m-1
            k = 2*n-1
            while curr[j] == 0:
                curr[j] = 1
                curr[k] = 0
                j = j-1
                k = k-2
            if j == 0: 
                break
            curr[j] = 0
            m = 2*n-1



def printProof(c: float, proof: List[List[Tuple[int, float, float]]]) -> None: 
    """
        c: a floating point number, the exponent in the assumption NTIME[n] subset TSP[n^c]
        proof: a
    """
    pass


def initialize(lp_problem: LpProblem, n: int, m: int) -> LpProblem: 
    """
        lp_problem: A pulp.LpProblem instance
        n: an integer, representing the number of lines in the proof
        m: an integer, representing the maximum number of clauses in any line

        returns: A pulp.LpProblem instance

        Appends the initial constraints on the LP, and those for the first speedup step. 
    """
    #Constraints on the first and last lines, which are of the form TSP[n^a]. 
    lp += a[(0,0)] >= 1
    lp += b[(0,0)] = 1

    lp += a[(n-1, 0)] >= 1
    lp += b[(n-1, 0)] = 1

    for k in range(1,m):
        lp += a[(0,k)] = 0
        lp += b[(0,k)] = 0
        lp += a[(n-1,k)] = 0
        lp += b[(n-1,k)] = 0
    
    #Constraints for the first speedup
    lp += a[(1,0)] = a[(0,0)]-x[1] 
    lp += b[(1,0)] = 1
    lp += a[(1,1)] = 0
    lp += b[(1,1)] >= x[1]
    lp += b[(1,1)] >= 1 
    lp += a[(1,2)] = x[1]
    lp += b[(1,2)] = 1

    for k in range(3, m): 
        lp += a[(1,k)] = 0
        lp += b[(1,k)] = 0

def speedup(lp_problem: LpProblem, i: int) -> LpProblem:
    """
        lp_problem: A pulp.LpProblem instance
        i: an integer, representing the current proof line

        returns: A pulp.LpProblem instance

        Appends the constraints corresponding to this speedup step to the LP
    """

    lp += a[(i,0)] >= 1
    lp += a[(i,0)] >= a[(i-1,0)] - x[i]
    lp += b[(i,0)] >= b[(i-1,0)]
    lp += a[(i,1)] = 0
    lp += b[(i,1)] >= x[i]
    lp += b[(i,1)] >= b[(i-1,0)]
    lp += a[(i,2)] >= a[(i-1,1)] 
    lp += a[(i,2)] >= x[i]
    lp += b[(i,2)] >= b[(i-1,1)]
    
    for k in range(3,m):
        lp += a[(i,k)] = a[(i-1,k-1)]
        lp += b[(i,k)] = b[(i-1,k-1)] 


def slowdown(lp_problem: LpProblem, i: int, c: float) -> LpProblem:
    """
        lp_problem: A pulp.LpProblem instance
        i: an integer, representing the current proof line
        c: a float, representing the exponent in the assumption NTIME[n] \subset TSP[n^c, log n]

        returns: A pulp.LpProblem instance

        Appends the constraints corresponding to this slowdown step to the LP
    """

    lp += a[(i,0)] >= c*a[(i-1,0)]
    lp += a[(i,0)] >= c*a[(i-1,1)]
    lp += a[(i,0)] >= c*b[(i-1,0)]
    lp += a[(i,0)] >= c*b[(i-1,1)]
    lp += b[(i,0)] = b[(i-1,1)]

    for k in range(1,m-1):
        lp += a[(i,k)] = a[(i-1,k+1)]
        lp += b[(i,k)] = b[(i-1,k+1)]
        lp += a[(i,m)] = 0 
        lp += b[(i,m)] = 0

def buildLinearProgram(annotation: List[int], c: float) -> pulp.LpProblem:
    """
        annotation: A list of 0/1 bits encoding an annotation. 0 indicates a slowdown step, 1 indicates a speedup step
        c: the exponent against which we wish to prove lower bounds

        return: A pulp.LpProblem linear program to be run. 

        Given a bit list encoding an annotation, outputs a pair of numpy arrays. The first encodes all the inequality constraints 
        for a linear program, the second encodes the equality constraints. 


        We count quantifiers from the right to the left, so the outermost quantifier has the highest index. 

        The number of lines of the proof is equal to the number of inclusions (i.e. the length of the annotation) 
        PLUS ONE. Think of it as the number of lines if the proof were written as

        TSP[n^a] 
        \subset A_1
        \subset A_2 
        ...
        \subset A_{n-1}
        \subset TSP[n^{a'}]

        Then, the variables of the ith line are:

        (Q_k n^{a_{i,k})^{b_{k-1}} ... (Q_1 n^{a_{i,1})^{b_0} TSP[n^{a_{i,0}}]

        As such, each piece of each line is associated to a pair of numbers {a_ij, b_ij} which take on real values. Each line
        also has a variable x_i which corresponds to the "speedup parameter" if the rule applied in that line is a speedup rule. 
        Otherwise x_i is unused. 

    """
    n = len(annotation)+1
    m = 0
    j = 0 
    for i in range(n):
        if annotation[i] == 0:
            j  += 1
            m = max(m,j)
        j -= 1
    #We add one for the variables for the TSP[n^a] bit 
    m += 1

    a = pulp.LpVariable.dicts("a", [(i,j) for i in range(n) for j in range(m)], 0) 
    b = pulp.LpVariable.dicts("b", [(i,j) for i in range(n) for j in range(m)], 0) 
    x = pulp.LpVariable.dicts("x", [i for i in range(n), 0) 


    lp_problem = pulp.LpProblem("imnotsurewhathisdoes", pulp.LpMaximize)

    #Objective function (we don't need to optimize anything cause we're just checking for feasibility
    lp_problem += 0

    #Initial conditions and first speedup
    lp_problem += initialize(lp_problem)

    #Everything else, skipping the first speedup since it's in initialize
    for op in annotation[1:]:
        if op == 0:
            #slowdown
            lp_problem += slowdown(lp_problem)
        else:
            #speedup
            lp_problem += speedup(lp_problem)

    return lp_problem


def binarySearch(annotation: List[int], low: float, high: float, depth: int) -> Tuple[float, 'scipy.optimize.OptimizeResult']:
    """
        annotation: A list of 0/1 bits encoding an annotation. 0 indicates a slowdown step, 1 indicates a speedup step
        high: the maximum allowable value in binary search
        low: the minimum allowable value in binary search
        depth: the maximum search depth
        return: the largest value of c that yielded a feasible program and the corresponding result
    """
    if depth == 0:
        lp_result = buildLinearProgram(annotation, high).solve()
        if pulp.LpStatus[lp_result.status] is 1:
            return high, lp_result
        else:
            return low, buildLinearProgram(annotation, low).solve()

    mid = (high+low)/2
    if pulp.LpStatus[buildLinearProgram(annotation, mid).solve().status] is 1:
        return binarySearch(annotation, mid, high, depth-1)
    else:
        return binarySearch(annotation, low, mid, depth-1)


if __name__ == "__main__":
    """
        proof_length: how many lines the proof is allowed to be
        search_cap: how many doubling iterations we allow in the search
        search_depth: how deep we go when binary searching
        search_start: what the starting value of c should be


        Uses <<balancedStrings>> to generate balanced parentheses (proofs) of this length. Then, for each annotation, we can guess 
        a value for c in the assumption NTIME[n] \subset TSP[n^c]. Based on this value, builds the appropriate linear program 
        for this annotation and c with <<buildLinearProgram>> and runs it using <<scipy.optimize.linprog>>. We can use binary 
        search to guess appropriate values of c. Then, we output the best satisfying c we found and the corresponding proof!
    """

    parser = argparse.ArgumentParser()
    parser.add_argument("--proof_length", type = int, action = "store", help = "finds the best lower bounds using proofs of this length")
    parser.add_argument("--search_start", type = float, action = "store", help = "what value of c to start searching from")
    parser.add_argument("--search_cap", type = int, action = "store", help = "number of rounds of doubling we allow")
    parser.add_argument("--search_depth", type = int, action = "store", default = 6, help = "number of iterations of binary search we allow")

    args = parser.parse_args()

    proof_length = args.proof_length
    search_start = args.search_start
    search_cap = args.search_cap
    search_depth = args.search_depth


    best_c = search_start
    best_annotation = []
    
    for annotation in balancedStrings(proof_length):
        c = search_start

        #Check to make sure the search start is fine
        if pulp.LpStatus[buildLinearProgram(annotation, c).solve().status] is not 1:
            raise ValueError("Search start value was too high - no lower bounds could be found")
        
        for i in range(search_cap):
            c *= 2
            lp_result = buildLinearProgram(annotation, c).solve()
            if lp_result.status is not 1:
                #There's no feasible linear program at this value of c.
                #This means that we should search between c/2 and c
                annotation_best_c, lp_result = binarySearch(annotation, c/2, c, search_depth)
                assert(lp_result.status is 1)

                if annotation_best_c > best_c:
                    best_c = annotation_best_c
                    best_annotation = annotation
                    best_params = lp_result.variables()
            
        print("Maxed out the search cap on annotation: ", ''.join(best_annotation))

    #printProof(best_c, best_annotation, best_params)


