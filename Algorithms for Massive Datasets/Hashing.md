

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

### 4.2 Suppose m ≥ u. Is the identity function f (x) = x a universal hash function?

### 4.3 A family G of hash functions mapping U to M is family of pair-wise independent hash function if for any `g ∈ G`, `Pr(g(x) = α ∧ g( y) = β) = 1/m2 ∀x ∕= y ∈ U, ∀α,β ∈ M`. Show that any family of pairwise independent hash functions is a family of universal hash functions.


## 5. Linear Space Hashing The chained hashing solution for the dynamic dictionary problem presented assumes that m = Θ(n). Solve the following exercises.

### 5.1 What is the space and time of chained hashing without this assumption? State your answer in terms of n and m.

![[ChainedHashing_space.png]]

#### Space = O(m + n)

![[ChainedHashin1.png]]
![[ChainedHashing2.png]]

#### O(n/m)

### 5.2 Suppose we do not know n in advance (as in the exercise streaming statistics where we do not know how many distinct IP addresses we will see). Give a solution that achieves O(n) space and fast amortized time without assuming m = Θ(n). Hint: Think dynamic arrays.

