#!/usr/bin/env python3

"""
Code for automating the synthesis of alternation-trading proofs
following the ideas of http://www.cs.cmu.edu/~ryanw/automated-lbs.pdf
and based on the Maple code by Ryan Williams http://www.cs.cmu.edu/~ryanw/LB.txt
"""


import argparse
import pulp
from typing import Any, Dict, List, Tuple
from buildLinearProgram import buildLinearProgram

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
    if n == 3:
        #1 0 0 is the only one
        yield [1,0,0]

    elif n == 5:
        #1 1 0 0 0 is the only one
        yield [1,1,0,0,0]
        yield [1,0,1,0,0]

    else:
        curr = [1, 0]*(int((n-1)/2))
        curr.insert(0,0)
        m = (n-1)-1
        counter = 0
        while 1: 
            #Modifying the output so it's a valid annotation
            #Needs to start with a speedup and end with two slowdowns 
            #because the first speedup adds two quantifiers
            output = curr[1:]
            output.append(0)
            counter += 1
            yield output

            curr[m] = 0
            if curr[m-1] == 0:
                curr[m-1] = 1
                m = m-1
            else:
                j = m-1
                k = (n-1)-1
                while curr[j] == 1:
                    curr[j] = 0
                    curr[k] = 1
                    j = j-1
                    k = k-2
                if j == 0: 
                    break
                curr[j] = 1
                m = (n-1)-1


def binarySearch(annotation: List[int], low: float, high: float, depth: int, alpha: float) -> Tuple[float, str]:
    """
        annotation: A list of 0/1 bits encoding an annotation. 0 indicates a slowdown step, 1 indicates a speedup step
        high: the maximum allowable value in binary search
        low: the minimum allowable value in binary search
        depth: the maximum search depth
        return: the largest value of c that yielded a feasible program and the corresponding result
    """
    #If even the smallest exponent in the range is infeasible then fail out immediately
    #This guarantees that the output will be feasible. This function shouldn't be called on 
    #infeasible ranges (TODO maybe this is bad behavior)
    assert(buildLinearProgram(annotation, low, alpha).isFeasible() is True)
    if depth == 0:
        if buildLinearProgram(annotation, high, alpha).isFeasible() is True:
            return high, buildLinearProgram(annotation, high, alpha).getReadableProof()
        else:
            return low, buildLinearProgram(annotation, low, alpha).getReadableProof()

    mid = (high+low)/2
    if buildLinearProgram(annotation, mid, alpha).isFeasible() is True:
        return binarySearch(annotation, mid, high, depth-1, alpha)
    else:
        return binarySearch(annotation, low, mid, depth-1, alpha)


if __name__ == "__main__":
    """
        proof_length: how many lines the proof is allowed to be
       search_cap: how many doubling iterations we allow in the search
        search_depth: how deep we go when binary searching
        search_start: what the starting value of c should be


        Uses <<annotationGenerator>> to generate balanced parentheses (proofs) of this length. Then, for each annotation, we can guess 
        a value for c in the assumption NTIME[n] \subset TSP[n^c]. Based on this value, builds the appropriate linear program 
        for this annotation and c with <<buildLinearProgram>> and runs it using <<scipy.optimize.linprog>>. We can use binary 
        search to guess appropriate values of c. Then, we output the best satisfying c we found and the corresponding proof!
    """

    parser = argparse.ArgumentParser()
    parser.add_argument("--proof_length", required = True, type = int, action = "store", help = "finds the best lower bounds using proofs of this length. Must be even")
    parser.add_argument("--search_start", default = 1, type = float, action = "store", help = "what value of c to start searching from")
    parser.add_argument("--search_cap", default = 3, type = int, action = "store", help = "number of rounds of doubling we allow")
    parser.add_argument("--search_depth", default = 6, type = int, action = "store", help = "number of iterations of binary search we allow")
    parser.add_argument("--alpha", default = 1.0, type = float, action = "store", help = "value of alpha in generic slowdown rule")

    args = parser.parse_args()

    proof_length = args.proof_length
    search_start = args.search_start
    search_cap = args.search_cap
    search_depth = args.search_depth
    alpha = args.alpha

    assert(proof_length % 2 == 0)

    best_c = search_start-0.01
    best_annotations = []
    best_proofs = []
    
    for annotation in annotationGenerator(proof_length-1):
        #If even the smallest value under consideration fails to yield a feasible program 
        #for this annotation then we shouldn't bother with the binary searching
        if buildLinearProgram(annotation, search_start, alpha).isFeasible() is False:
            continue 
        c = search_start
        for i in range(search_cap):
            c *= 2
            if buildLinearProgram(annotation, c, alpha).isFeasible() is False:
                #There's no feasible linear program at this value of c.
                #This means that we should search between c/2 and c
                annotation_best_c, annotation_best_proof = binarySearch(annotation, c/2, c, search_depth, alpha)
                if annotation_best_c > best_c:
                    best_c = annotation_best_c
                    best_annotations = [annotation]
                    best_proofs = [annotation_best_proof]
                elif annotation_best_c == best_c:
                    best_annotations.append(annotation)
                    best_proofs.append(annotation_best_proof)
                break
    print("The best annotations were: ", best_annotations)
    print("The best value of c was: ", best_c) 
    print("The best proofs were: ")
    for idx, proof in enumerate(best_proofs):
        print(best_annotations[idx])
        print(proof)



