## Tries

![[06.tries.png]]
Properties of the trie. A trie T storing a collection $S$ of $s$ strings of total length $n$ from an alphabet of size $d$ has the following properties:
- How many children can a node have?
  at most $d$
- How many leaves does T have? 
  $s$
- What is the height of T?
  length of the longest string ($n$)
- What is the number of nodes in T?
  $O(n)$

Search time: O(d) in each node => O(dm)
- O(m) if d constant
- d not constant: use dictionary
	- Perfect hashing O(1) expected
	- Balanced BST: O(log d)

![[06.compact_trie.png|751]]

![[06.compact_trie_props.png|615]]


String depth(u) = length of string obtained by concatenating labels on the path from the root to u.
# Tasks

## 1 \[w] Suffix Trees. Draw the suffix tree T for the string `mississippi$`. Write edge labels (substrings) and leaf labels (suffix number). Illustrate how a search for "issi"works.

![[06.1.suffix_tree.png|1081]]



## 2 \[w] Substring Counting. Let $S = s_0 s_1 \cdots s_{n−1}$ be a string of length n over an alphabet $\Sigma$. We are interested in a data structure for $S$ that supports the following query.
- count(P): return the number of occurrences of P in S. 
- Give a data structure that supports count(P) queries efficiently.

1. suffix tree
2. in every node add nr of leaves below it
3. 

## 3 Number of nodes in a compact trie. Let T be a tree where every internal node has at least 2 children. Let ℓ be the number of leaves in T and let i be the number of internal nodes. Use induction to prove that i ≤ ℓ−1. Give an example showing that this is a tight bound.


case 0: $n_{0} = 1$
then $i = 0$ and $\ell = 1$
$0 \leq 1-1$
$i \leq \ell-1$

case 1: $n_{1} = 3$
then $i=1$ and $\ell = 2$
$i \leq \ell -1$
$1 \leq 2-1$

case n: $n = n_1 + 1$


IH: Assume for any valid tree with $\ell = k + 1$ leaves, we have $i \leq (k + 1)-1$

case 1: $i =$

1. $\ell = 1$ ok
2. $\ell = \ell_{1}+\ell_{2}+\ell_{3}+ \dots \ell_{k}$
   $i = i_{1}+i_{2}+i_{3}+\dots+i_{k}+1$
   $\leq (\ell_{1}-1) + (\ell_{2}-1) + \dots + (\ell_{k}-1) + 1$
   $= \ell-k + 1 \leq \ell -1$
   $k \geq 2$

## 4 Repeats. Solve the following exercises. Assume you have an efficient black-box algorithm for computing the suffix tree of a string. 
### 4.1 A repeat in a string S is a substring R that occurs at least twice in S. Show how to efficiently compute the length of a longest substring of S that is a repeat. 

We construct a suffix tree, then we traverse internal edges in search for a string of maximum depth. 
The time is O(n) + O(n), since the number of nodes is O(n) in the suffix tree. -> O(n)
### 4.2 Given a string S of length n and an integer k, show how to efficiently find the smallest substring of S occurring exactly k times. Analyze the time and space consumption of your algorithm.

We construct a suffix tree, then we look at the top level edges

string depth should be computed until parent (then add 1) (?)

## 5 Longest Common Extensions. Let S be a string of length n over alphabet Σ. The longest common extension problem is to preprocess S into data structure to support queries of the following form: 
- LCE(i,j): Return the length of the longest common prefix of S\[i, n] and S\[ j, n].

## 6 Restricted Suffix. Search Let S be a string of length n over alphabet Σ. Give an efficient data structure for S that supports the following query: 
- rsearch(P, i, j): report the starting positions of occurrences of string P in S\[i, j].

lookup: suffix array

---
1.1
Directed graph G. n+1 vertices v1...vn
Edge vi to vj labelled alpha <=> t[j] is leftmost pos in $T[i..n]$ with char alpha



(assume FKS)
Store array indexed by char at each node to rep G.

1.2 sigma edges at node in array => O(n sigma) space
1.3 Traverse G from v0 with chars from P from left to-right.
- if all chars in P match => ret. true
- otherwise -> return false
1.4 O(1) time pr char => O(|P|) time

2.1
Store G as follows:
- LEt S_alpha be all pos in T with char alpha ~=vertices with incoming edge labeled alpha
- Store S_alpha for chars alpha in y-fast trie.
2.2
Each pos in T stored in exact 1 y-fast-trie. => O(n) space
2.3
Simulate graph traversal from 1.3. Each step at vi with char alpha is successor query with i+1 in S_alpha
2.4 O(loglog n) pr successor query => O(|P| loglog n) time.

