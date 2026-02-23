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
### 3.2 \[∗\] Show that any tree with n nodes has $O( p n)$ long paths on a root-to-leaf path.

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
