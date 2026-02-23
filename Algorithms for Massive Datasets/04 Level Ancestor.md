![[level_ancestor.png]]

rl-path: root-to-leaf path

|                             | Space        | Time         |
| --------------------------- | ------------ | ------------ |
| No datastructure            | $O(n)$       | $O(n)$       |
| All rl-paths (direct paths) | $O(n^2)$     | $O(1)$       |
| Jump pointers               | $O(n\log n)$ | $O(\log k)$  |
| Long Path Decomposition     | $O(n)$       | $O(n^{1/2})$ |
