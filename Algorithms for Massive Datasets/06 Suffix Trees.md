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

dict of substrings (?)

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





---
1.1
Directed graph G. n+1 verttices v1...vn
Edge vi to vj labelled alpha <=> t[j] is leftmost pos in $T[i..n]$ with char alpha


(assume FKS)
Store array indexed by char at each node to rep G.