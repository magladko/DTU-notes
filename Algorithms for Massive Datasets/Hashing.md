

# Tasks
## 1. [w] Streaming Statistics. An IT-security friend of yours wants a high-speed algorithm to count the number of distinct incoming IP-addresses in his router to help detect denial-of-service attacks. Can you help him?

```
Let S = S_i , S_i be a stream of IP-adr
Init dictionary D with universal hash function
Init counter c
For each S_i: If lookup(S_i) do nothing
			  otherwise insert(S_i)
			  increment c
Return c
```

Time: O(1) **expected** - (expected is important due to randomization)
Space: O(n), where n = \#distinct IP addresses
## 2. [w] Dense Set Hashing. A set S ⊆ U = {0, . . . , u − 1} is called dense if |S| = Θ(u). Suggest a simple and efficient dictionary data structure for dense sets.

Initialize array of size u, link 1-1 index

Space: O(u) = O(n)
Ops time: O(1)
## 3. [w] Multi-Set Hashing. A multi-set is a set M, where each element may occur multiple times. Design an efficient data structure supporting the following operations:

- add(x): Add an(other) occurrence of x to M.
- remove(x): Remove an occurrence of x from M. If x does not occur in M do nothing.
- report(x): Return the number of occurrences of x.

dictionary structure + satellite data (counter)
when counter = 0 -> delete the element

## 4. Properties of Universal Hashing. Let h ∈ H be a hash function from a universal family mapping U = {0, . . . , u − 1} to M = {0, . . . , m − 1}. Solve the following exercises.

### 4.1 If h has no collision on U, how large must m be?

$m \geq u$
### 4.2 Suppose m ≥ u. Is the identity function f (x) = x a universal hash function?

![[universal_Hashing.png]]

Yes, because the collision probability in this case is equal to 0.
### 4.3 A family G of hash functions mapping U to M is family of pair-wise independent hash function if for any `g ∈ G`, `Pr(g(x) = α ∧ g( y) = β) = 1/m2 ∀x ∕= y ∈ U, ∀α,β ∈ M`. Show that any family of pairwise independent hash functions is a family of universal hash functions.

show collision prob. is $\leq \frac{1}{m}$
$$
\forall_{x \neq y}. Pr(g(x) = g(y)) = \sum_{\alpha \in M} Pr(g(x) = \alpha \land g(y) = \alpha) = m \frac{1}{m^2} = \frac{1}{m}
$$

Hence g is universal.
## 5. Linear Space Hashing. The chained hashing solution for the dynamic dictionary problem presented assumes that m = Θ(n). Solve the following exercises.

### 5.1 What is the space and time of chained hashing without this assumption? State your answer in terms of n and m.

![[ChainedHashing_space.png]]

Space = $O(m + n)$

![[ChainedHashin1.png]]
![[ChainedHashing2.png]]

time expected: $O\left( 1 + \frac{n}{m} \right)$

### 5.2 Suppose we do not know n in advance (as in the exercise streaming statistics where we do not know how many distinct IP addresses we will see). Give a solution that achieves O(n) space and fast amortized time without assuming m = Θ(n). Hint: Think dynamic arrays.

Dynamically reallocate the array and rehash values when running out of space.
## 6. Graph Adjacency. Let G be a graph with n vertices and m edges. We want to represent G efficiently and support the following operation.

- adjacent(v, w): Return true if nodes v are w are adjacent and false otherwise.

### 6.1 Analyse the space and query time in terms of n and m for the classic adjacency matrix and adjacency list representation.

Matrix:
Space: $O(V^2) = O(n^2)$
Time: $O(1)$

List:
Space: $O(V+E) = O(n+m)$
Time: $O(n)$
### 6.2 Design a data structure that improves both the adjacency matrix and adjacency list.

Use and array as in linked list + dictionary instead of linked list

## 7. Perfect Hashing Analysis. Consider the 2-level FKS perfect hashing scheme. A friend suggests the following two "optimizations" to the data structure. What happens to the performance of the data structure for each of these?

### 7.1 Modify level 1 of the data structure to map U to an array of size $n \sqrt{ n }$ instead of n to further decrease the probability of collisions.


$$
\begin{align}
E(C) & = {n \choose 2} \frac{1}{n \sqrt{ n }}  \\
 & = {n \choose 2} \frac{\sqrt{ n }}{n^2} \\
 & = \frac{n-1}{2} \cdot \frac{\sqrt{ n }}{n}  \\
 & = \frac{n-1}{2 \sqrt{ n }} < (\frac{n}{2 \sqrt{ n }} = \frac{\sqrt{ n }}{2})
\end{align}
$$

### 7.2 Suppose we replace the universal hash function with a simpler near-universal hash function on both levels. Near-universal hashing is the same as universal hashing except that ≤ 1/m guarantee on the probability is changed to ≤ 2/m. Show how to modify the FKS so that the scheme still works efficiently.

