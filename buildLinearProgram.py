#!/usr/bin/env/python3

"""
Code for automating the synthesis of alternation-tradingi proofs
following the ideas of http://www.cs.cmu.edu/~ryanw/automated-lbs.pdf
and based on the Maple code by Ryan Williams http://www.cs.cmu.edu/~ryanw/LB.txt
"""

import pulp
from typing import Any, Dict, List, Tuple

class buildLinearProgram:
    """
        Class for building linear programs from annotations. An instance is created given an annotation and an exponent c, 
        and there are methods to add constraints and objective functions. In general, <buildLineearProgramisFeasible> is the
        best way to check if a particular annotation can be used to generate a proof with exponent c.
    """
    def __init__(self, annotation: List[int], c: float, alpha: float) -> None:
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
        self.alpha = alpha
        self.annotation = annotation
        self.rand_speedup = False
        if self.annotation[0] == 2:
            self.random = True
        self.x = pulp.LpVariable.dicts("x", [i for i in range(self.n)], 0) 
        self.lp_problem = pulp.LpProblem("iwonderwhatthisdoes", pulp.LpMinimize)


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
                j += annotation[i]
        m = max(m,j)
        #We add one for the variables for the TSP[n^a] bit 
        #and one for the extra quantifier added in the first speedup
        m += 2
        return m

    def addObjective(self) -> None:
        """
            Must be run BEFORE any constraints are added!!
        """
        self.lp_problem += pulp.lpSum([self.a[(i,j)] for i in range(self.n) for j in range(self.m)]) + pulp.lpSum([self.b[(i,j)] for i in range(self.n) for j in range(self.m)]) + pulp.lpSum([self.x[i] for i in range(self.n)])



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
        self.solveIfNotSolved()
        if pulp.LpStatus[self.lp_problem.status] == "Optimal":
            return True
        elif pulp.LpStatus[self.lp_problem.status] == "Infeasible":
            return False
        raise ValueError

    def solveIfNotSolved(self) -> None:
        """
            Solves the program if it isn't solved 
        """
        #if lp is unsolved
        if pulp.LpStatus[self.lp_problem.status] == "Not Solved": 
            self.addObjective()
            self.addAnnotationConstraints()
            self.lp_problem.solve()

    @staticmethod
    def getQuant(a: bool) -> str:
        if a is True:
            return 'E'
        else:
            return 'A'

    def getReadableProof(self) -> str:
        """
            Yields the proof in human readable format
        """
        self.solveIfNotSolved()
        #round the solution 
        self.lp_problem.roundSolution()
        output = ""

        #print line by line
        for i in range(self.n):
            line_out = ""
            #quant is True when you want to print an exists (E), false for forall (A)
            quant = True
            hit_zero = False
            for j in reversed(range(self.m)):
                if hit_zero is False:
                    if self.b[i,j].varValue != 0:
                        hit_zero = True
                        if j == 0:
                            line_out += "DTS[n^"+str(self.a[i,j].varValue)+"]"
                        else:
                            quant_out = "(" +  self.getQuant(quant) + "n^" + str(self.a[i,j].varValue) + ")^"
                            line_out += quant_out
                            quant = not quant
                else:
                    if j == 0:
                        quant_out = str(self.b[i,j].varValue) + " DTS[n^"+str(self.a[i,j].varValue)+"]"
                    else:
                        quant_out = str(self.b[i,j].varValue) + " (" +  self.getQuant(quant) + "n^" + str(self.a[i,j].varValue) + ")^"
                        quant = not quant
                    line_out += quant_out

            output += line_out + '\n'
        return output

    def addInitialConstraints(self) -> None:
        """
            Appends the initial constraints on the LP, and those for the first speedup step. 
        """


        #Constraints on the first self.and last lines, which self.are of the form TS[n^a]. 
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

        #Constraints for the first speedup. This depends on whether we're in 
        #the randomized or normal setting.

        self.lp_problem += self.a[(1,0)] == self.a[(0,0)]-self.x[1] 
        self.lp_problem += self.b[(1,0)] == 1
        self.lp_problem += self.a[(1,1)] == 0
        self.lp_problem += self.b[(1,1)] >= self.x[1]
        self.lp_problem += self.b[(1,1)] >= 1 

        self.lp_problem += self.a[(1,2)] == self.x[1]
        self.lp_problem += self.b[(1,2)] >= 1
        self.lp_problem += self.b[(1,2)] >= self.x[1]

        if self.rand_speedup is True:
            self.lp_problem += self.a[(1,3)] == 0
            self.lp_problem += self.b[(1,3)] == 1
        else:
            self.lp_problem += self.a[(1,3)] == 0
            self.lp_problem += self.b[(1,3)] == 0

        for k in range(4, self.m): 
            self.lp_problem += self.a[(1,k)] == 0
            self.lp_problem += self.b[(1,k)] == 0
           

    def addSpeedupConstraints(self, i: int) -> None:
        """
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


    def addRandomizedSpeedupConstraints(self) -> None:
        pass
    
    def addSlowdownConstraints(self, i: int) -> None:
        """
            Appends the constraints corresponding to this slowdown step to the LP
        """
        self.lp_problem += self.a[(i,0)] >= self.c*self.alpha*self.a[(i-1,0)]
        self.lp_problem += self.a[(i,0)] >= self.c*self.a[(i-1,1)]
        self.lp_problem += self.a[(i,0)] >= self.c*self.b[(i-1,0)]
        self.lp_problem += self.a[(i,0)] >= self.c*self.b[(i-1,1)]
        self.lp_problem += self.a[(i,0)] >= 1

        self.lp_problem += self.b[(i,0)] == self.b[(i-1,1)]

        for k in range(1,self.m-1):
            self.lp_problem += self.a[(i,k)] == self.a[(i-1,k+1)]
            self.lp_problem += self.b[(i,k)] == self.b[(i-1,k+1)]
        self.lp_problem += self.a[(i,self.m-1)] == 0 
        self.lp_problem += self.b[(i,self.m-1)] == 0



