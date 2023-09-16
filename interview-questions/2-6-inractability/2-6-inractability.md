# Interview Questions: Intractability

## Graph 3-colorability 

**Question**. An undirected graph is 3-colorable if the vertices can be colored red, green, or blue in such a way that no edge connects two vertices with the same color. Prove that 3COLOR is NP-complete.

**Answer**.

## Decision problems 

**Question**. Traditionally, the complexity classes P and NP are defined in terms of decision problems (where the answer is either yes or no) instead of search problems (where the answer is the solution itself). Prove that the search problem version of SAT (find a binary solution to a given system of boolean equations?) polynomial-time reduces to the decision version of SAT (does there exists a binary solution to a given system of boolean equations?).

**Answer**.

## Optimization problems

**Question**. Given an undirected graph with positive edge weights, the traveling salesperson problem is to find a simple cycle that visits every vertex and has minimum total weight. The search problem version of the problem is, given a parameter L, find a tour of length at most L. Prove that the optimization version of the problem polynomial-time reduces to the search version of the problem.

> Remark: for many problems such as this one, the optimization version of the problem (which is not known to be in NP) is solvable in polynomial time if and only if the search version of the problem (which is easily seen to be in NP) is.

**Answer**.