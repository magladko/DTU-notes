![[level_ancestor.png]]

rl-path: root-to-leaf path

|                             | Space                         | Time         |
| --------------------------- | ----------------------------- | ------------ |
| No datastructure            | $O(n)$                        | $O(n)$       |
| All rl-paths (direct paths) | $O(n^2)$                      | $O(1)$       |
| Jump pointers               | $O(n\log n)$                  | $O(\log k)$  |
| Long Path Decomposition     | $O(n)$                        | $O(n^{1/2})$ |
| Ladder decomposition        | $O(2n) = O(n)$                | $O(\log n)$  |
| Ladder decomp.+Jump ptr     | $O(n + n\log n) = O(n\log n)$ | $O(1)$       |
| Top-Bottom decomposition    | $O(n)$                        | $O(1)$       |
TopBottom-decomposition
- O(n/x) leaves in top tree
- bottom trees are of size O(x)
# Tasks

##  1. Direct shortcuts. Find a tree with n nodes such that the total size of all the arrays is $\Theta(n^2)$.

Just a linked list - note: 
$$
1+2+\dots+n = \frac{n(n+1)}{2} = O(n^2)
$$
## 2. \[w\] Find LCA Perform LA(v,11) on the tree in Figure 1(a) using.

| 2.1 Jump pointers    | 2.2 Long paths            | 2.3 Ladders            |
| -------------------- | ------------------------- | ---------------------- |
| ![[04.2.1_jump.png]] | ![[04.2.2_long_path.png]] | ![[04.2.3_ladder.png]] |

### 2.1 Jump pointers: show which jump pointers that are used. 
...
### 2.2 Long paths: Show which paths that are used. 
...
### 2.3 Ladders: Show which ladders that are used.
...

## 3. Long Path Decomposition Bounds. Prove tight bounds for the number of long paths in a root-to-leaf path. 

### 3.1 Find a tree with n nodes such that the maximum number of long paths on a root-to-leaf path is Ω( p n). 

![[04.3.1_sol.png|20%]]
### 3.2 \[∗\] Show that any tree with n nodes has $O( \sqrt{ n })$ long paths on a root-to-leaf path.

![[04.3.2_sol.png]]
## 4. Ladders. Let T be a tree of height h with n nodes. Solve the following exercises. 
### 4.1 Show that a node v of height $h(v)$ is on a ladder of length at least $2h(v)$ (or equals height of root).

Ladder is always twice as long as the longest-paths and the length longest-paths is always at least equal to the $h(v)$.
- long path has length $\geq h(v)$
- then ladder has length $\geq 2h(v)$
### 4.2 Show that any root-to-leaf path can be covered by at most $O(\log h) = O(\log n)$ ladders. 
When we switch ladder we are jumping to at least double the height
- switch ladder: jump => double height
### 4.3 Ladders are obtained by doubling the long paths. Suppose we instead extend long paths by a factor k > 2. What is the effect?

$T = O(\log_{k}h)$
Space: $O(k \cdot n)$
## 5. \[w\] Top-Bottom Decomposition
### 5.1 Show the jump nodes on the tree in Figure 1(a), using $\left\lceil  \frac{1}{4} \log n  \right\rceil = 3$. 

![[04.5.1_sol.png]]
### 5.2 Show the parentheses encoding of the tree in Figure 1(b) and the encoding for the query LA(u,4).

![[04.5.2.png]]
(()(()((((()))(()))))) (()()())
001001000001110011111100101011
n = 16
$\log\log 16 = 4$
u: 0111
4: 0100
LA(u,4) = 001001000001110011111100101011 0111 0100

## 6. Few Leafs. Suppose that your input tree has no more than $n/\log n$ leaves. Suggest a (slightly) simplified solution to the level ancestor problem with linear space and constant query time.

We make the leafs as jump nodes, since the number of jump nodes must be at most O(n/logn). Meaning we only have a top search.

## 7. Heavy Paths. Let T be a tree with n nodes. Define size(v) to be the number of descendant of v. Consider the following decomposition rule. 
- First find a root-to-leaf path as follows. Start at the root. At each node continue to a child of maximum size, until we reach a leaf. Remove the resulting path and recursively apply the rule to the remaining subtrees. 
The resulting paths are called the heavy paths and the edges not on a heavy path are light edges. Solve the following exercises. 

### 7.1 \[w\] Draw a not to small example of heavy paths in a tree. 

![[04.7.1.png|500]]
### 7.2 Give an upper bound on the number of heavy paths on any root-to-leaf path in T.

The upper bound is $O(\log n)$
When the path ends, we at least double the amount of descendants, that means we double the height (following the heavy path until root or change of paths).

## 8. Weighted Level Ancestor. Let T be tree with n nodes. Each edge is assigned a weight from {0, . . . , u − 1}, and the weight of a node v is the sum of the weight of the edges on the path from the root to v. Assume n < u. We want a data structure that supports the following operation on T. Given a leaf $\ell$ and an integer x define
- WLA($\ell$, x): return the deepest ancestor of $\ell$ of weight ≤ x. 
### 8.1 \[w\] Give a simple data structure that supports WLA queries in $O(n^2)$ space and $O(\log\log u)$ time. 


### 8.2 Give a data structure that supports WLA queries in $O(n)$ space and $O(\log n)$ time. 

### 8.3 Consider the predecessor problem on n elements from a universe of size u. Any solution that uses O(n) space requires at least Ω(loglog u) query time. Can we hope to solve the weighted level ancestor problem in O(n) space and O(1) time? 

### 8.4 \[∗\] Give a data structure that supports WLA queries O(n) space and O(loglog u) time. Hint: Use heavy path decomposition.

## 9. Level Ancestor on Shallow Binary Trees. Let T be a rooted, binary tree with n nodes of height O(log n). Give a simple and compact data structure that supports fast level ancestor queries (without using a level ancestor data structure). Hint: A path in T can be encoded in a single word of memory.