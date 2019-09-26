This code, based on [research](http://www.cs.cmu.edu/~ryanw/automated-lbs.pdf) and Maple [code](http://www.cs.cmu.edu/~ryanw/LB.txt) by Professor [Ryan Williams](https://people.csail.mit.edu/rrw/), generates alternation-trading proofs of time-space lower bounds for SAT. Loosely, the goal is to prove statements of form 


![NPDTS Equation](https://github.com/abhijit-mudigonda/automated-alternating-lbs/blob/master/images/npdts_eqn.gif)


where the goal is to make c as large as possible. 


These proofs consist of a sequence of applications of one of a small set of *rules*. By picking the rules in the right order and with the right parameters, we can get better lower bounds. In general, a proof annotation describes an ordering of rules, and we can brute force through the space of allowable annotation sequences. The problem of picking parameters can be reduced to a linear programming problem and solved using [PuLP](https://pypi.org/project/PuLP/). Most of the grunt work happens in `buildLinearProgram.py`, which builds a linear program from a given annotation and value of c. `findBestProof.py` starts at a particular value of c, iteratively doubling and then binary searching to find the largest value of c that still yields a proof. 


To use, run `findBestProof.py` with the arguments you want. 

![Arguments](https://github.com/abhijit-mudigonda/automated-alternating-lbs/blob/master/images/example_input.png)


The output looks something like this. Note that E and A denote existential and universal quantifiers, respectively. To understand the rest of the notation, check out the paper. 


![Output](https://github.com/abhijit-mudigonda/automated-alternating-lbs/blob/master/images/example_output.png)


