
# Tasks

## 1 LSD and MSD Radix Sort. Radix sort that process digits in right-to-left order is called LSD radix sort. If we instead process digits in left-to-right order we call the algorithm MSD radix sort. Solve the following exercises. 

### 1.1 Show that LSD radix sort correctly sorts any input. 

induction by k (nr of digits)

base: k = 1
step: assume after pass k-1 the array is sorted on the last k-1 digits by IH
case 1:
 - a != b in digit k -> just sort by current digit
 - a = b in digit k -> needs to sort stabely to ensure k-1 digits are in the correct order
### 1.2 Explain why each step in LSD radix sort must use a stable sorting algorithm. 

In other case, the previously sorted order might be disrupted, since the context of the sorting looks at a single digit.
### 1.3 Show that that are input for which MSD radix sort does not correctly sort any input. 

Witness
```
12    12    21
21 -> 21 -> 12
```

### 1.4 \[∗] Explain how to modify MSD radix sort to sort correctly.

run the sorting on the subranges

## 2 \[w] Prefix Doubling Suffix sort cocoa using prefix doubling.

| order | $2^0$ |     | order |     | $2^1$ |     | order |     | $2^2$    |     | order |     | $2^3$            |
| ----- | ----- | --- | ----- | --- | ----- | --- | ----- | --- | -------- | --- | ----- | --- | ---------------- |
| 2     | c     |     | 2     | 23  | co    |     | 3     | 22  | coco     |     | 3     | 31  | cocoa\$\$\$      |
| 3     | o     |     | 4     | 32  | oc    |     | 5     | 43  | ocoa     |     | 5     | 50  | ocoa\$\$\$\$     |
| 2     | c     |     | 2     | 23  | co    |     | 2     | 21  | coa$     |     | 2     | 20  | coa\$\$\$\$\$    |
| 3     | o     |     | 3     | 31  | oa    |     | 4     | 30  | oa\$$    |     | 4     | 40  | oa\$\$\$\$\$\$   |
| 1     | a     |     | 1     | 10  | a$    |     | 1     | 10  | a\$\$$   |     | 1     | 10  | a\$\$\$\$\$\$\$  |
| 0     | $     |     | 0     | 00  | \$$   |     | 0     | 00  | \$\$\$\$ |     | 0     | 00  | \$\$\$\$\$\$\$\$ |

## 3 Odd-Even Sampling. Suppose we modify the sampling of suffixes in the DC3 algorithm such that the sampled and non-sampled suffixes are those starting at even and odd positions, respectively. Determine if the algorithm still works, i.e., show that it still works or explain where it fails.

