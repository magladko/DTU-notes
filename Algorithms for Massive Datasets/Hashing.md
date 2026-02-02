# 1. [w] Streaming Statistics An IT-security friend of yours wants a high-speed algorithm to count the number of distinct incoming IP-addresses in his router to help detect denial-of-service attacks. Can you help him?

```
Let S = S_i , S_i be a stream of IP-adr
Init dictionary D with universal hash function
Init counter c
For each S_i: If lookup(S_i) do nothing
			  otherwise insert(S_i), increment
Return c
```
# 5. Linear Space Hashing The chained hashing solution for the dynamic dictionary problem presented assumes that m = Θ(n). Solve the following exercises.

## 5.1 What is the space and time of chained hashing without this assumption? State your answer in terms of n and m.

![[ChainedHashing_space.png]]

### Space = O(m + n)

![[ChainedHashin1.png]]
![[ChainedHashing2.png]]

### O(n/m)

## 5.2 Suppose we do not know n in advance (as in the exercise streaming statistics where we do not know how many distinct IP addresses we will see). Give a solution that achieves O(n) space and fast amortized time without assuming m = Θ(n). Hint: Think dynamic arrays.

