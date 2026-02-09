![[Predecessor_intro.png]]


|                                        | Pred     | Succ     | Insert   | Delete   | Space |
| -------------------------------------- | -------- | -------- | -------- | -------- | ----- |
| Balanced Binary <br>Search Tree (BBST) | O(log n) | O(log n) | O(log n) | O(log n) | O(n)  |
| Linked List                            | O(n)     | O(n)     | O(n)*    | O(n)*    | O(n)  |
| Bit VectArray                          | O(u)     | O(u)     | O(1)     | O(1)     | O(u)  |
|                                        |          |          |          |          |       |
\* Needs to check for duplicates, else (e.g. for O(1)) other operations are unbounded
\*\* u - the largest number in the input set