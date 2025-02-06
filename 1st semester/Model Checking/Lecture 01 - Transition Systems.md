[Slides](https://learn.inside.dtu.dk/d2l/le/lessons/215750/topics/866798)
$M \models \phi$

# Transition systems definition
Def.: **Transition system is a tuple**

![[transition systems, formally.png]]

![[Transition system (lamp).png]]

$$
\begin{aligned}
S = \set{S_0, S_1} \\\\
T = \set{(S_0 click, S_1), (S_1, click, S_0)} \\\\
A = \set{click} \\\\
%L = \set{S_0 \}
\end{aligned}
$$
# Forward and backwards reachability

$$
Post(s) = \set{s' \textbar \exists \alpha. s \stackrel{\alpha}{\rightarrow}s'}
$$
$$
Pre(s) = \set{s' \textbar \exists \alpha. s' \stackrel{\alpha}{\rightarrow}s}
$$
Modelling with transition systems
![[Modelling with transition sysmte.png]]

![[Pasted image 20240912163739.png]]

## Non-determinism

1. intentionally **under-specified** system
2.  may represent certain environmental uncertainty
![[Pasted image 20240912163958.png]]

## Deterministic transition system
![[Pasted image 20240912164055.png]]

## Terminal states
> $\lnot \exists s'.s\rightarrow s'$
> $\textit{Post}(s) = \emptyset$

![[Pasted image 20240912164259.png]]

## Transition systems with not terminals
![[Pasted image 20240912164436.png]]

## Executions
![[Pasted image 20240912164523.png]]

## Traces
![[Pasted image 20240912164559.png]]


| ![[Pasted image 20240912164810.png]] | =>  | ![[Pasted image 20240912164914.png]] |
| ------------------------------------ | --- | ------------------------------------ |
## Computation trees

(?)

| ![[Pasted image 20240912164810.png]] | =>  | ![[Pasted image 20240912165009.png]] |
| ------------------------------------ | --- | ------------------------------------ |

## Interactions and compositions

The transition system of the composition of two systems can be obtained in 2 ways:
1. Build both systems then compose
2. Build the composed TS directly

### Interleaving composition
![[Pasted image 20240912181826.png]]

### Synchronized composition of transition systems

![[Pasted image 20240912181857.png]]

