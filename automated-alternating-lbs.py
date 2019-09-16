#!/usr/bin/env python3

#Code for automating the synthesis of alternation-tradingi proofs
#following the ideas of http://www.cs.cmu.edu/~ryanw/automated-lbs.pdf
# (c) Ryan Williams 2010

import argparse
import sys
import numpy as np
from scipy import optimize
from typing import Any, Dict, List, Tuple


def printProof(lp_output: 'scipy.optimize.OptimizeResult', k: int, outfile: str) -> None:
"""
    lp_output: a scipy.optimize.OptimizeResult object containing the result of scipy.optimize.linprog
    k: number of proof steps
    outfile: where output proof is written
    
    Given the output of an LP solver and the number of proof steps, prints a readable proof and writes it to the output file. 
"""

def translate(triples: List[Tuple[int, float, float]]) -> str:
"""
    triples: a list of tuples (quantifier, nondeterminism exponent, output exponent) each of which encode a quantifier
    return: a string representing the complexity class
"""

def proofProduce() -> : 


def tryAll(num_lines: int, c: float) -> None:
"""
    num_lines: the maximum proof length to try
    c: value in the assumption NTIME[n] \subsest TSP[n^c]

    Try all proofs of a given number of lines for a given exponent
"""

def listCheck(bit_list: List[int]) -> bool:
"""
    bit_list: A list of 0/1 bits encoding an annotation. 0 indicates a slowdown step, 1 indicates a speedup step
    return: true iff the list was a valid annotation

    An annotation is valid if it
    1) begins with a speedup and ends with a slowdown
    2) never has more slowdowns than speedups
    3) ends with an equal number of speedups and slowdowns 
    4) Never has more than 6 consecutive 0's
"""

def listToLinearProgram(bit_list: List[int], c: float) -> np.ndarray, np.ndarray
"""
    bit_list: A list of 0/1 bits encoding an annotation. 0 indicates a slowdown step, 1 indicates a speedup step
    return: a pair of numpy arrays

    Given a bit list encoding an annotation, outputs a pair of numpy arrays. The first encodes all the inequality constraints 
    for a linear program, the second encodes the equality constraints. 
"""

def binarySearch(bit_list: List[int], low: float, verbosity: bool) -> None:
"""
    Given an annotation and a minimum exponent, search for a good proof
"""

def heuristicSearch(bit_list: List[int], low: float, verbosity: bool) ->  None:
"""
    Given an annotation and minimum exponent, start a local search for better proofs. 
"""


    










