#!/usr/bin/env/python3

"""
Code for automating the synthesis of alternation-tradingi proofs
following the ideas of http://www.cs.cmu.edu/~ryanw/automated-lbs.pdf
(c) Ryan Williams 2010
"""

import pulp
from typing import Any, Dict, List, Tuple

class buildLinearProgram:
    """
        Class for building linear programs from annotations. An instance is created given an annotation and an exponent c, 
        and there are methods to add constraints and objective functions. In general, <buildLineearProgramisFeasible> is the
        best way to check if a particular annotation can be used to generate a proof with exponent c.
    """
    def __init__(self, annotation: List[int], c: float) -> None:
        """
            annotation: A list of 0/1 bits encoding an annotation. 0 indicates a slowdown step, 1 indicates a speedup step
            c: the exponent against which we wish to prove lower bounds

            We count quantifiers from the right to the left, so the outermost quantifier has the highest index. 
            Then, the variables of the ith line are:

            (Q_k n^{a_{i,k})^{b_{k-1}} ... (Q_1 n^{a_{i,1})^{b_0} TSP[n^{a_{i,0}}]

            As such, each piece of each line is associated to a pair of numbers {a_ij, b_ij} which take on real values. Each line
            also has a variable x_i which corresponds to the "speedup parameter" if the rule applied in that line is a speedup rule. 
            Otherwise x_i is unused. 
        """
        self.m = buildLinearProgram.maxNumClauses(annotation)
        self.n = len(annotation)+1
        self.a = pulp.LpVariable.dicts("a", [(i,j) for i in range(self.n) for j in range(self.m)]) 
        self.b = pulp.LpVariable.dicts("b", [(i,j) for i in range(self.n) for j in range(self.m)]) 
        self.c = c
        self.annotation = annotation
        self.x = pulp.LpVariable.dicts("x", [i for i in range(self.n)], 0) 
        self.lp_problem = pulp.LpProblem("imnotsurewhathisdoes", pulp.LpMinimize)

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
        """
            Must be run BEFORE any constraints are added!!
        """
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


