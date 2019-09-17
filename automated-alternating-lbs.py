#!/usr/bin/env python3

#Code for automating the synthesis of alternation-tradingi proofs
#following the ideas of http://www.cs.cmu.edu/~ryanw/automated-lbs.pdf
# (c) Ryan Williams 2010


import sys
import argparse
import pulp
from typing import Any, Dict, List, Tuple


class buildLinearProgram:
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

    def __init__(self, annotation: List[int], c: float) -> None:
        self.m = buildLinearProgram.maxNumClauses(annotation)
        self.n = len(annotation)+1
        self.a = pulp.LpVariable.dicts("a", [(i,j) for i in range(self.n) for j in range(self.m)]) 
        self.b = pulp.LpVariable.dicts("b", [(i,j) for i in range(self.n) for j in range(self.m)]) 
        self.c = c
        self.annotation = annotation
        self.x = pulp.LpVariable.dicts("x", [i for i in range(self.n)], 0) 
        self.lp_problem = pulp.LpProblem("imnotsurewhathisdoes", pulp.LpMinimize)

        print("Building for the annotation: ", annotation, "and exponent ", c, ". The value of n is: ", self.n, " and the value of m is: ", self.m)

    @staticmethod
    def maxNumClauses(annotation: List[int]) -> int:
        """
            annotation: a list of integers
            returns: the maximum number of clauses that ever occur in a proof 
                encoded by this annotation. 
        """
        m = 0
        j = 0
        for i in range(len(annotation)):
            #The clause is a SLOWDOWN   
            if annotation[i] == 0:
                j -= 1
            #The clause is a SPEEDUP
            else:
                j += 1
                m = max(m,j)
        #We add one for the variables for the TSP[n^a] bit 
        #and one for the extra quantifier added in the first speedup
        m += 2
        return m

    def addObjective(self) -> None:
        self.lp_problem += 0

    def addAnnotationConstraints(self) -> None:
        """
            Add all the linear program constraints for this annotation and this 
            value of c. 
        """

        #Initial conditions and first speedup
        self.addInitialConstraints()

        #Everything else, skipping the first speedup since it's in initialize
        for idx, op in enumerate(self.annotation[1:]):
            i = idx+2
            if op == 0:
                #slowdown
                self.addSlowdownConstraints(i)
            else:
                #speedup
                self.addSpeedupConstraints(i)

    def isFeasible(self) -> bool:
        """
            Returns 1 iff the linear program built from this annotation and this value of c
            is feasible. 
        """
            
        self.addObjective()
        self.addAnnotationConstraints()
        self.lp_problem.solve()
        if pulp.LpStatus[self.lp_problem.status] == "Optimal":
            return True
        elif pulp.LpStatus[self.lp_problem.status] == "Infeasible":
            return False
        raise ValueError

    def getProofParams(self):
        """
            Returns the variables corresponding to a feasible solution if one exists.
            TODO typehint
        """

        #if lp is unsolved
        if pulp.LpStatus[self.lp_problem.status] == "Not Solved": 
            self.addObjective()
            self.addAnnotationConstraints()
            self.lp_problem.solve()

        #if the solved program isn't feasible, fail
        assert(pulp.LpStatus[self.lp_problem.status] == "Optimal")
        return self.lp_problem.variables()
     
    def addInitialConstraints(self) -> None:
        """
            Appends the initial constraints on the LP, and those for the first speedup step. 
        """

        #Constraints on the first self.and last lines, which self.are of the form TSP[n^a]. 
        self.lp_problem += self.a[(0,0)] >= 1
        self.lp_problem += self.b[(0,0)] == 1

        self.lp_problem += self.a[(self.n-1, 0)] >= 1
        self.lp_problem += self.b[(self.n-1, 0)] == 1

        for k in range(1,self.m):
            self.lp_problem += self.a[(0,k)] == 0
            self.lp_problem += self.b[(0,k)] == 0
            self.lp_problem += self.a[(self.n-1,k)] == 0
            self.lp_problem += self.b[(self.n-1,k)] == 0
        
        #Constraint so that we actually get a lower bound
        self.lp_problem += self.a[(0,0)] >= self.a[(self.n-1,0)]

        #Constraints for the first speedup
        self.lp_problem += self.a[(1,0)] == self.a[(0,0)]-self.x[1] 
        self.lp_problem += self.b[(1,0)] == 1
        self.lp_problem += self.a[(1,1)] == 0
        self.lp_problem += self.b[(1,1)] >= self.x[1]
        self.lp_problem += self.b[(1,1)] >= 1 
        self.lp_problem += self.a[(1,2)] == self.x[1]
        self.lp_problem += self.b[(1,2)] == 1

        for k in range(3, self.m): 
            self.lp_problem += self.a[(1,k)] == 0
            self.lp_problem += self.b[(1,k)] == 0

    def addSpeedupConstraints(self, i: int) -> None:
        """
            lp_problem: A pulp.LpProblem instance
            i: an integer, representing the current proof line

            returns: A pulp.LpProblem instance

            Appends the constraints corresponding to this speedup step to the LP
        """

        self.lp_problem += self.a[(i,0)] >= 1
        self.lp_problem += self.a[(i,0)] >= self.a[(i-1,0)] - self.x[i]
        self.lp_problem += self.b[(i,0)] >= self.b[(i-1,0)]
        self.lp_problem += self.a[(i,1)] == 0
        self.lp_problem += self.b[(i,1)] >= self.x[i]
        self.lp_problem += self.b[(i,1)] >= self.b[(i-1,0)]
        self.lp_problem += self.a[(i,2)] >= self.a[(i-1,1)] 
        self.lp_problem += self.a[(i,2)] >= self.x[i]
        self.lp_problem += self.b[(i,2)] >= self.b[(i-1,1)]
        
        for k in range(3,self.m):
            self.lp_problem += self.a[(i,k)] == self.a[(i-1,k-1)]
            self.lp_problem += self.b[(i,k)] == self.b[(i-1,k-1)] 


    def addSlowdownConstraints(self, i: int) -> None:
        """
            lp_problem: A pulp.LpProblem instance
            i: an integer, representing the current proof line
            c: a float, representing the exponent in the assumption NTIME[n] \subset TSP[n^c, log n]

            returns: A pulp.LpProblem instance

            Appends the constraints corresponding to this slowdown step to the LP
        """
        self.lp_problem += self.a[(i,0)] >= self.c*self.a[(i-1,0)]
        self.lp_problem += self.a[(i,0)] >= self.c*self.a[(i-1,1)]
        self.lp_problem += self.a[(i,0)] >= self.c*self.b[(i-1,0)]
        self.lp_problem += self.a[(i,0)] >= self.c*self.b[(i-1,1)]
        self.lp_problem += self.b[(i,0)] == self.b[(i-1,1)]

        for k in range(1,self.m-1):
            self.lp_problem += self.a[(i,k)] == self.a[(i-1,k+1)]
            self.lp_problem += self.b[(i,k)] == self.b[(i-1,k+1)]
        self.lp_problem += self.a[(i,self.m-1)] == 0 
        self.lp_problem += self.b[(i,self.m-1)] == 0


def printProof(c: float, proof: List[List[Tuple[int, float, float]]]) -> None: 
    """
        c: a floating point number, the exponent in the assumption NTIME[n] subset TSP[n^c]
        proof: a
    """
    pass


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

    else:
        curr = [1, 0]*(int((n-3)/2))
        curr.insert(0,0)
        m = (n-3)-1
        counter = 0
        while 1: 
            #Modifying the output so it's a valid annotation
            #Needs to start with a speedup and end with two slowdowns 
            #because the first speedup adds two quantifiers
            output = curr[1:]
            output.insert(0, 1)
            output.append(0)
            output.append(0)
            counter += 1
            yield output

            curr[m] = 0
            if curr[m-1] == 0:
                curr[m-1] = 1
                m = m-1
            else:
                j = m-1
                k = (n-3)-1
                while curr[j] == 1:
                    curr[j] = 0
                    curr[k] = 1
                    j = j-1
                    k = k-2
                if j == 0: 
                    break
                curr[j] = 1
                m = (n-3)-1


def binarySearch(annotation: List[int], low: float, high: float, depth: int) -> Tuple[float, Any]:
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
    assert(buildLinearProgram(annotation, low).isFeasible() is True)
    if depth == 0:
        if buildLinearProgram(annotation, high).isFeasible() is True:
            return high, buildLinearProgram(annotation, high).getProofParams()
        else:
            return low, buildLinearProgram(annotation, low).getProofParams()

    mid = (high+low)/2
    if buildLinearProgram(annotation, mid).isFeasible() is True:
        return binarySearch(annotation, mid, high, depth-1)
    else:
        return binarySearch(annotation, low, mid, depth-1)


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
    parser.add_argument("--proof_length", required = True, type = int, action = "store", help = "finds the best lower bounds using proofs of this length")
    parser.add_argument("--search_start", default = 1, type = float, action = "store", help = "what value of c to start searching from")
    parser.add_argument("--search_cap", default = 3, type = int, action = "store", help = "number of rounds of doubling we allow")
    parser.add_argument("--search_depth", default = 4, type = int, action = "store", help = "number of iterations of binary search we allow")

    args = parser.parse_args()

    proof_length = args.proof_length
    search_start = args.search_start
    search_cap = args.search_cap
    search_depth = args.search_depth


    best_c = search_start
    best_annotation = []
    
    for annotation in annotationGenerator(proof_length):
        #If even the smallest value under consideration fails to yield a feasible program 
        #for this annotation then we shouldn't bother with the binary searching
        if buildLinearProgram(annotation, search_start).isFeasible() is False:
            print("this annotation failed from the start")
            continue 
        c = search_start
        for i in range(search_cap):
            c *= 2
            if buildLinearProgram(annotation, c).isFeasible() is False:
                #There's no feasible linear program at this value of c.
                #This means that we should search between c/2 and c
                annotation_best_c, annotation_best_params = binarySearch(annotation, c/2, c, search_depth)
                print("The best c for this annotation was: ", annotation_best_c)
                if annotation_best_c > best_c:
                    best_c = annotation_best_c
                    best_annotation = annotation
                    best_params = annotation_best_params

                break
    print("The best annotation was: ", best_annotation)
    print("The best value of c was: ", best_c) 

    #printProof(best_c, best_annotation, best_params)


