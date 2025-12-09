The Bounded Static Analysis on a program $P$ can defined as the set of traces of depth n: $\mathbf{BSA}_{P}^n$. We can get this set using a many-stepping function 𝚜𝚝𝚎𝚙. It takes a set of traces and steps them one step.

$$
\mathtt{step}_{P}(T) = \{ \tau's ~|~ s \in \Sigma, \tau' \in T, \delta_{P}(\tau'_{|\tau'|}, s) \}
$$
- $\delta$ is a transition relation defined by the single step semantics.
- $\tau's$ means appending $s$ to $\tau'$ 

- **Must analysis**: underestimate the set of traces
- **May analysis**: overestimate the set of traces

