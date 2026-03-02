![[05_rr_1d.png]]

# Tasks

## 1. \[w\] 2D Range Tree Example. Draw a 2D range tree for the set of points P = {(1, 3),(3, 8),(4, 1),(7, 5),(6, 6),(9, 6),(15, 4),(20, 17)}. Draw all stored arrays. Run a report(2, 2, 10, 10) query by hand and write all 1D queries on arrays

![[05.1_tree.png]]

### report(2,2,10,10)
![[05.1.2.png]]


1D queries:
1. {(3,8)} -> {(3,8)}
2. {(4,1), (6,6)} -> {(6,6)}
3. {(7,5), (9,6)} -> {(7,5), (9,6)}

Result: {(3,8), (6,6), (7,5), (9,6)}

## 2. Preprocessing for 2D Range Trees. Give a fast algorithm that constructs a 2D range tree from a set $P \subseteq \mathscr{R}^2$ of n points.

