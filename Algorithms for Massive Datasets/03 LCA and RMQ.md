
| RMQ             | LCA                                           |
| --------------- | --------------------------------------------- |
| ![[03_rmq.png]] | ![[03_lca.png]]<br>![[03_lca_naive.png\|614]] |

# Tasks

## 1 \[w] RMQ. Consider the array $A = [3, 5, 1, 3, 8, 6, 9, 2, 42, 4, 7, 12]$. Construct the sparse table for $A$.

```
A = [3 5 1 3 8 6 9 2 42 4 7 12]
     0 1 2 3 4 5 6 7  8 9 1 11
                          0 
```

|     |  0  |  1  |  2  |  3  |
| --: | :-: | :-: | :-: | :-: |
|   0 |  3  |  3  |  1  |  1  |
|   1 |  5  |  1  |  1  |  1  |
|   2 |  1  |  1  |  1  |  1  |
|   3 |  3  |  3  |  3  |  2  |
|   4 |  8  |  6  |  2  |  2  |
|   5 |  6  |  6  |  2  |     |
|   6 |  9  |  2  |  2  |     |
|   7 |  2  |  2  |  2  |     |
|   8 | 42  |  4  |  4  |     |
|   9 |  4  |  4  |     |     |
|  10 |  7  |  7  |     |     |
|  11 | 12  |     |     |     |

## 2 Sparse table. Show that we can do the preprocessing of the sparse table in O(n log n) time.

Each entry compute as $st[i][j]=\min(st[i][j−1], st[i+2^{j−1}][j−1])$, which takes $O(1)$. There are at most $n \log n$ entries, which gives total calculation:
$O(n \log n)$

Correctness: $st[i][j−1], st[i+2^{j−1}][j−1]$ split the $st[i][j]$ range in half, so union of both form exactly the $st[i][j]$ range.


## 3 \[w] RMQ. Consider the array $A = [3, 4, 5, 4, 5, 4, 5, 4, 3, 2, 1, 0, 1, 0, 1, 2, 3, 4, 3, 4, 3, 2, 1, 2, 3, 2, 3, 4, 5, 6, 7, 6]$. 


### 3.1 Give the arrays A' and P used for the sparse table in the two level ±1RMQ data structure. Use block size 3. 

```
     0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 0, 1
A = [3, 4, 5, 4, 5, 4, 5, 4, 3, 2, 1, 0, 1, 0, 1, 2, 3, 4, 3, 4, 3, 2, 1, 2, 3, 2, 3, 4, 5, 6, 7, 6]
A'= [      3,       4,       3,       0,       0,       2,       3,       1,       2,       4,    6]
P = [      0,       3,       8,      11,      13,      15,      18,      22,      25,      27,   31]
```

### 3.2 How many different tabulation tables do we need to store (how many different describing sequences/normalized blocks are there)?

```
     0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 0, 1
A = [3, 4, 5, 4, 5, 4, 5, 4, 3, 2, 1, 0, 1, 0, 1, 2, 3, 4, 3, 4, 3, 2, 1, 2, 3, 2, 3, 4, 5, 6, 7, 6]
    [0, 1, 2; 0, 1, 0; 0,-1,-2; 0,-1,-2; 0,-1, 0; 0, 1, 2; 0, 1, 0; 0,-1, 0; 0,-1, 0; 0, 1, 2; 0,-1]
A'= [      3,       4,       3,       0,       0,       2,       3,       1,       2,       4,    6]
P = [      0,       3,       8,      11,      13,      15,      18,      22,      25,      27,   31]
```

```
0  1  2
0  1  0
0 -1 -2
0 -1  0
0 -1
```

4 tabulation tables

## 4. Size of blocks. In the ±1RMQ data structure we divided the array into blocks of length $\frac{1}{2} \log n$. What happens if we instead use a block size of 
- $\log n$
- $\frac{3}{4} \log n$

1. Sparse table: $O\left( \frac{n}{b} \log \frac{n}{b} \right)$
2. Lookup table: $O(2^b \cdot b^2)$

b = log n:
$O\left( \frac{n}{\log n} \log \frac{n}{\log n}\right)$
$O(2^{\log n} \cdot \log^2 n) = O(n \cdot \log^2 n)$

b = 3/4 log n:
$O\left( \frac{n}{\frac{3}{4}\log n} \log \frac{n}{\frac{3}{4}\log n}\right)$
$O\left( 2^{3/4\log n} \cdot \frac{9}{16} \log^2 n \right) = O(n^{3/4} \cdot \log^2 n)$

The lookup table grows in size -> the space complexity is no longer linear

