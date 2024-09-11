# 1.

![[q1-1.png]]

| x   | m(x) | $\mathfrak{m}[x\leftarrow 3](x)$ | $\mathfrak{m}[y\leftarrow 3](x)$ | $\mathfrak{m}[z\leftarrow 5](x)$ | $\mathfrak{m}[z\leftarrow 11](x)$ |
| --- | ---- | -------------------------------- | -------------------------------- | -------------------------------- | --------------------------------- |
| x   | 0    | 3                                | 3                                | 3                                | 3                                 |
| y   | 1    | 1                                | 3                                | 3                                | 3                                 |
| z   | 2    | 2                                | 2                                | 5                                | 11                                |

# 2.
![[q1-2.png]]

| x   | m(x) | $\mathfrak{m}[x\leftarrow 3](x)$ | $\mathfrak{m}[y\leftarrow 3](x)$ | $\mathfrak{m}[z\leftarrow 5](x)$ | $\mathfrak{m}[z\leftarrow 11](x)$ |
| --- | ---- | -------------------------------- | -------------------------------- | -------------------------------- | --------------------------------- |
| x   | 0    | 3                                | 3                                | 3                                | 3                                 |
| y   | 1    | 1                                | 3                                | 3                                | 3                                 |
| z   | 2    | 2                                | 2                                | 5                                | 11                                |

# 3.

| x   | m(x)  | $\mathfrak{m}[x\leftarrow y_1+z+1](x)$ | $\mathfrak{m}[y\leftarrow z_1+1](x)$ | $\mathfrak{m}[z\leftarrow y_1+z_1+2](x)$ | ... |
| --- | ----- | -------------------------------------- | ------------------------------------ | ---------------------------------------- | --- |
| x   |       | $y_1+z_1$                              | $y_1+z_1$                            | $y_1+z_1$                                |     |
| y   | $y_1$ | $y_1$                                  | $z_1+1$                              | $z_1+1$                                  |     |
| z   | $z_1$ | $z_1$                                  | $z_1$                                | $y_1+z_1+2$                              |     |

**(A)** $\mathfrak{m} \models (x == y)$, implying  $y_1+z_1 == z_1+1$, so for $y_1 = 1$

| x   | ... | $\mathfrak{m}[z\leftarrow y_1+z_1+1+y_1+z_1+2](x)$ | values    |
| --- | --- | -------------------------------------------------- | --------- |
| x   |     | $y_1+z_1$                                          | $z_1+1$   |
| y   |     | $z_1+1$                                            | $z_1+1$   |
| z   |     | $2*y_1 + 2*z_1 + 3$                                | $2*z_1+5$ |
**(B)** $\mathfrak{m} \not\models y_1+z_1 == z_1+1$, so for $y_1 \neq 1$

| x   | ... | $\mathfrak{m}[x\leftarrow z_1+1 + y_1+z_1](x)$ |
| --- | --- | ---------------------------------------------- |
| x   |     | $y_1 + 2*z_1 + 3$                              |
| y   |     | $z_1+1$                                        |
| z   |     | $y_1+z_1+2$                                    |

### a) 
pre: $y_1, z_1 > 0$
post: $x<z$
**(A)** $y_1 = 1$
then $x' = z_1+1$ and $z'=2*z_1+5$
=> x' < z'

**(B)** $y_1 \neq 1$
$x' = y_1+2*z_1+3$
$z'=y_1+z_1+2$
-> $x'-z' = z_1 + 1$ from precondition $z_1>0$, so x' > z'
**NOT VALID**

### b)
pre: {{ 0 < y ∧ 0 < z }} => $y_1, z_1 > 0$
post: {{ x < z ∨ y < x }} => x' < z' or y'<x'
**(A)** $y_1 = 1$
then 
- $x' = z_1+1$ 
- $y' = z_1+1$ 
- $z'=2*z_1+5$
$x' - z' = z_1 + 1 - 2*z_1 - 5$
$x' - z' = - z_1 - 4 < 0$ and z > 0
so x' < z'
**(B)** $y_1 \neq 1$
- $x'=y_1 + 2*z_1 + 3$
- $y'=z_1+1$
- $z'=y_1+z_1+2$
=> y' < x'
**(A) and (B) => VALID**

![[q1-3.png]]
## 1. 
```chip
{ 0 < y & 0 < z }
x := y + z;
y := z + 1;
z := x + 2;
if x = y -> 
    z := x + y + z
[] !(x = y) ->
    x := y + x
fi
{ x < z}
```
<span style="color:red;font-weight:bold">NOT VERIFIES</span>
## 2.
```chip
{ 0 < y & 0 < z }
x := y + z;
y := z + 1;
z := x + 2;
if x = y -> 
    z := x + y + z
[] !(x = y) ->
    x := y + x
fi
{ x < z | y < x }
```
<span style="color:green;font-weight:bold">VERIFIES</span>
## 3. 
```chip
{ true }
if (x < y) ->
  y := 42
[] !(x < y) ->
  y := x;
  if (0 < y) ->
    skip
  [] !(0 < y) ->
    y := 23
  fi
fi;
x := y
{ 0 < y }
```
<span style="color:green;font-weight:bold">VERIFIES</span>
## 4.
```chip
{ x = x0 & y = y0 }
z := x;
x := y;
y := z
{ x = y0 & y = x0 }
```
<span style="color:green;font-weight:bold">VERIFIES</span>

# 4.
![[q1-4.png]]

```
{{ y + x == 0 ∧ 0 <= x }}
if (x == 0) {
    {{ y + x == 0 && 0 <= x && x == 0 }} {{ (6) }}
    {{ x == 0 && 0 <= 0 }}               {{ (5) }}
    y := 0
    {{ x == 0 && y <= 0 }}
} else {
    {{ y+x == 0 && 0 <= x && !(x==0) }}  {{ (4) }}
    {{ x + y == 0 && y + 1 <= 0 }}       {{ (3) }}
    x := x + y;
    {{ x == 0 && y + 1 <= 0 }}           {{ (2) }}
    y := y + 1
    {{ x == 0 && y <= 0 }}               {{ (1) }}
}
{{ x == 0 && y <= 0 }}
```

[Chip](https://chip-pv.netlify.app/)
```chip
{ y + x = 0 & 0 <= x }
if
  (x = 0) -> 
    //     {{ (6) }}
    { y + x = 0 & 0 <= x & x = 0 }
    // { y + x = 0 & 0 <= 0 }
    { x = 0 & 0 <= 0 }
    y:=0
    { x = 0 & y <= 0 }
[] !(x=0) -> 
    { y+x = 0 & 0 <= x & !(x=0) }
    { x + y = 0 & y + 1 <= 0 }
    x := x + y;
    { x = 0 & y + 1 <= 0 }
    y := y + 1
    { x = 0 & y <= 0 }
fi
{ x = 0 & y <= 0 }
```

# 5. 
![[q1-5.png]]
- It is possible to construct a proof tree for a toy Floyd-Hoare triple that is not valid.
Let's try { true } skip { false }
