## Tries

![[06.tries.png]]
Properties of the trie. A trie T storing a collection $S$ of $s$ strings of total length $n$ from an alphabet of size $d$ has the following properties:
- How many children can a node have?
  at most $d$
- How many leaves does T have? 
  $s$
- What is the height of T?
  length of the longest string ($n$)
- What is the number of nodes in T?
  $O(n)$

Search time: O(d) in each node => O(dm)
- O(m) if d constant
- d not constant: use dictionary
	- Perfect hashing O(1) expected
	- Balanced BST: O(log d)

![[06.compact_trie.png|751]]

![[06.compact_trie_props.png|615]]
