![[Predecessor_intro.png]]


|                                        | Pred     | Succ     | Insert   | Delete   | Space |
| -------------------------------------- | -------- | -------- | -------- | -------- | ----- |
| Balanced Binary <br>Search Tree (BBST) | O(log n) | O(log n) | O(log n) | O(log n) | O(n)  |
| Linked List                            | O(n)     | O(n)     | O(n)*    | O(n)*    | O(n)  |
| Bit Vector (Array)                     | O(u)     | O(u)     | O(1)     | O(1)     | O(u)  |
| Sorted Array                           | O(log n) | O(log n) | O(n)     | O(n)     | O(n)  |
| Tabulation (Pred/Suc)\*\*\*            | O(1)     | O(1)     | O(u)     | O(u)     | O(u)  |
\* Needs to check for duplicates, else (e.g. for O(1)) other operations are unbounded
\*\* u - the largest number in the input set
\*\*\* At each idx of array, put pair of pred. and suc. for the number that is equal to the index

---
# Tasks
## 1. The Google Egg Interview Problem. You are given 2 identical eggs and a 100-floor building. You want compute the highest floor from which an egg (identical to yours) can be dropped without breaking. Solve the following exercises.

### 1.1 How few drops can you do it with? You are allowed to break the 2 eggs in the process.

 $< 2 \cdot \sqrt{ 100 }$ 
 < 20
### 1.2 Give a bound on the number of drops for a building with x floors.

$O(\sqrt{ x })$
### 1.3 \[∗\] Show how to achieve a good bound (maybe roughly the same as in 2?) even when you do not know the number of floors in advance.

1-step - not aggressive enough
n^2-step - too aggressive

## 2. Range Reporting. Give a data structure for a set S ⊆ U = {0, . . . , u−1} of n values that supports the following operation: 

 - report(x, y): return all values in S between x and y, that is, the set of values {z | z ∈ S, x ≤ z ≤ y}. 
 
 The goal is a data structure with fast output-sensitive query bounds, that is, the query time should be on the form O(f (n, u) + occ), where occ is the number of elements returned by the query and f (n, u) is as fast as possible.

predecessor-based data structure: $O(occ \cdot \log \log u)$

> Linked List: O(loglog n + occ)
> loglog n for predecessor
> occ for reporting

## 3 van Emde Boas Bounds. Show that $T(u) = T(\sqrt{ u } + O(1) = O(\log \log u)$. Hint: consider the binary representation of u.

$$
T(u) = T(\sqrt{ u }+O(1))
$$

$u \quad \sqrt{ u } \quad u^{1/4} \quad u^{1/8} \ldots 1$ - the claimL length = ~log log u

apply logarithm on all elements:
$\log u \quad \frac{1}{2}\log u \quad \frac{1}{4}\log u \dots 1$ - then we can see length ~= loglog u (is the same)

