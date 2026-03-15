
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