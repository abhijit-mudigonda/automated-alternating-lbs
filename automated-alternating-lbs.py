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

        A generator that yields valid proof annotations of length n. We require n to be odd because any valid 
        proof has odd length (first speedup adds two quantifiers, every subsequent step changes quantifier count
        by one).  

        Procedure for generating strings of well-balanced parentheses taken from Knuth Vol. 4, Pre-Fascicle 4a, 
        p. 3, which was taken from I. Semba IPL 12 , 188-192, 1981. 
    """
    assert(n%2 == 1)
    curr = ['0', '1']*(n-3)
    curr.insert(0,'1')
    m = 2*n-1
    while 1: 
        output = curr[1:]
        output.insert(0, '1')
        output.append(['0', '0'])
        yield output
        curr[m] = '1'
        if curr[m-1] == '1':
            curr[m-1] = '0'
            m = m-1
        else:
            j = m-1
            k = 2*n-1
            while curr[j] == '0':
                curr[j] = '1'
                curr[k] = '0'
                j = j-1
                k = k-2
            if j == 0: 
                break
            curr[j] = '0'
            m = 2*n-1



def printProof(c: float, proof: List[List[Tuple[int, float, float]]]) -> None: 
    """
        c: a floating point number, the exponent in the assumption NTIME[n] subset TSP[n^c]
        proof: a
    """
    pass


def initialize(n: int, m: int) -> Tuple[np.ndarray, np.ndarray]:


    ineq_mtx_rows = []
    ineq_constants = []
    eq_mtx_rows = []
    eq_constants = []


    #a_{0,0} >=1,       
    row = np.zeros(num_vars) 
    row[indexFromVariableTuple('a', 0, 0)] = 1
    ineq_mtx_rows.append(row)
    ineq_constants.append(1)

    #b_{0,0} = 1
    eq_constants.append(1)

    #a_{n-1, 0} >= 1    
    row = np.zeros(num_vars) 
    row[indexFromVariableTuple('a', n-1, 0)] = 1
    ineq_mtx_rows.append(row)
    ineq_constants.append(1)

    #b_{n-1} = 1
    eq_constants.append(1)


    #Constraints for the first speedup

    #    a_{1,0} = a_{0,0}-x_1 
    #<=> a_{1,0} - a_{0,0} + x_1 = 0
    row = np.zeros(num_vars) 
    row[indexFromVariableTuple('a', 1, 0)] = 1
    row[indexFromVariableTuple('a', 0, 0)] = -1
    row[indexFromVariableTuple('x', 1)] = 1
    eq_mtx_rows.append(row)
    eq_constants.append(0)



    #b_{1,0} = 1
    #a_{1,1} = 0
    #b_{1,1} >= x_1
    #b_{1,1} >= 1
    #a_{1,2} = x_1
    #b_{1,2} = 1

    

    
    
def speedup(m: int, first_line = False: bool) -> Tuple[np.ndarray, np.ndarray]:
    pass

def slowdown(m: int) -> Tuple[np.ndarray, np.ndarray]:
    pass

def indexFromVariableTuple(num_doubles: int, letter: str, line_idx: int, double_idx=0: int) -> int:
    """
        num_doubles: the maximum number of doubles of variables needed for any line of this proof
        letter: character in {a,b,x}
        line_idx: the line of the proof in which this variable is introduced. ZERO INDEXED
        double_idx: the quantifier to which this variable corresponds. ZERO INDEXED. 
        
        
        We count quantifiers from the right to the left, so the outermost quantifier has the highest index. 

        The number of lines of the proof is equal to the number of inclusions PLUS ONE. Think of it as the number of lines
        if the proof were written as

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

        Each line of the proof has a block of variables of size 2*num_doubles + 1. The first index in the ith block is assigned 
        to x_i, and the subsequent entries are a_{i,0}, b_{i,0}, a_{i,1}, b_{i,1}, ... , a_{i,num_doubles-1}, b_{i, num_doubles-1}
    """

    if letter == 'x':
        return line_idx*(2*num_doubles+1)
    elif letter == 'a':
        shift = 0
        return line_idx*(2*num_doubles+1)+2*double_idx+shift+1
    elif letter == 'b':
        shift = 1
        return line_idx*(2*num_doubles+1)+2*double_idx+shift+1
    else:
        raise ValueError("Letter was not one of {a, b, x}")
        return 0


def buildLinearProgram(annotation: List[int], c: float) -> Tuple[np.ndarray, np.ndarray, np.ndarray, np.ndarray]:
    """
        annotation: A list of 0/1 bits encoding an annotation. 0 indicates a slowdown step, 1 indicates a speedup step
        return: four numpy arrays. Two are inequalities, two are equalities. 

        Given a bit list encoding an annotation, outputs a pair of numpy arrays. The first encodes all the inequality constraints 
        for a linear program, the second encodes the equality constraints. 
    """
    n = len(annotation)
    m = 0
    j = 0 
    for i in range(n):
        if annotation[i] == '0':
            j  += 1
            m = max(m,j)
        j -= 1
    m *= 3



    [(i,j) for i in range(num_lines)
    #Initial case
    ineq_matrix = initialize(m)[0]
    eq_matrix = initialize(m)[1]

    for i in range(n):
        if i == 0:
            #first speedrun
            np.append([ineq_matrix, speedup(m, True)[0]], axis=0)
            np.append([eq_matrix, speedup(m, True)[1]], axis=0)
        elif annotation[i] == '0':
            #speedup
            np.append([ineq_matrix, speedup(m)[0]], axis=0)
            np.append([eq_matrix, speedup(m)[1]], axis=0)

        elif annotation[i] == '1':
            #slowdown
            np.append([ineq_matrix, slowdown(m)[0]], axis=0)
            np.append([eq_matrix, slowdown(m)[1]], axis=0)




def binarySearch(annotation: List[int], low: float, high: float, depth: int) -> Tuple[float, 'scipy.optimize.OptimizeResult']:
    """
        annotation: A list of 0/1 bits encoding an annotation. 0 indicates a slowdown step, 1 indicates a speedup step
        high: the maximum allowable value in binary search
        low: the minimum allowable value in binary search
        depth: the maximum search depth
        return: the largest value of c that yielded a feasible program and the corresponding result
    """
    if depth == 0:
        if scipy.optimize.linprog(buildLinearProgram(annotation, high)).success is True:
            return high, scipy.optimize.linprog(buildLinearProgram(annotation, high))
        return low, scipy.optimize.linprog(buildLinearProgram(annotation, low))

    mid = (high+low)/2
    if scipy.optimize.linprog(buildLinearProgram(annotation, mid)).success is True:
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
        if scipy.optimize.linprog(buildLinearProgram(annotation, c)).success is not True:
            raise ValueError("Search start value was too high - no lower bounds could be found")
        
        for i in range(search_cap):
            c *= 2
            lp_result = scipy.optimize.linprog(buildLinearProgram(annotation, c)) 
            if lp_result.success is False:
                #There's no feasible linear program at this value of c.
                #This means that we should search between c/2 and c
                annotation_best_c, lp_result = binarySearch(annotation, c/2, c, search_depth)
                assert(scipy.optimize.linprog(buildLinearProgram(annotation, annotation_best_c)) is True)

                if annotation_best_c > best_c:
                    best_c = annotation_best_c
                    best_annotation = annotation
                    best_proof = buildProof(annotation, lp_result.x)
            
        print("Maxed out the search cap on annotation: ", ''.join(annotation))

    printProof(best_c, best_annotation, best_proof)


