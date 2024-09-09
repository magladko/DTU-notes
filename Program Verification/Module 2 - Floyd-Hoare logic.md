
> **Idea**: define judgements $\vdash \set{\set{F}}X\set{\set{G}}$ (read $\vdash$ as *provable*) such that
> $\vdash \set{\set{F}}C \set{\set{G}}$ implies $\models \set{\set{F}}C\set{\set{G}}$

Judgement $\vdash$ is bashed on *proof rules* without computing explicit executions

## Proof trees

$\frac{}{\text{conclusion}} \text{AXIOM}$  | $\frac{premises}{conclusion}\text{RULE}$

$$
\frac{\frac{}{\text{axiom}} \quad \frac{\frac{}{\text{other axiom}}}{\text{some premise}}}{\vdash \set{\set{F}} C \set{\set{G}}}
$$

Sketched proof tree with conclusions
$$
\vdash \set{\set{F}} C \set{\set{G}}
$$
### The skip rule

$$
\frac{}{\vdash \set{\set{F}} \textbf{ skip} \set{\set{F}}}\text{SKIP}
$$
**NOTE**: skip rule does not admit conclusions (sth like ~~x > 0 -> x >= 0~~)
![[fh-skip.png]]

### The consequence rule
**Entailment** $F \models G$: for all $\mathfrak{m}$, if $\mathfrak{m} \models F$ then also $\mathfrak{m} \models G$
$$
\frac{F \models F' \quad \vdash \set{\set{F}} C \set{\set{G'}} \quad G' \models G}{\vdash \set{\set{F}} C \set{\set{G}}}\text{CONSEQUENCE}
$$
![[fh-consequence.png]]
### The sequential composition rule
**Main idea**: decompose triples into smaller ones until we end up with obvious facts

$$
\frac{\vdash \set{\set{F}} C_1 \set{\set{H}} \quad \vdash \set{\set{H}} C_2 \set{\set{G}}}{\vdash \set{\set{F}}C_1; C_2 \set{\set{G}}}\text{SEQUENCE}
$$
![[fh-sequence.png]]

### The conditional rule

$$
\frac{\vdash \set{\set{F\land b}} C_1 \set{\set{G}} \quad \vdash \set{\set{F \land \lnot b}} C_2 \set{\set{G}}}{\vdash \set{\set{F}}\text{ if}(b) \set{C_1}\text{ else} \set{\set{G}}}\text{CONDITIONAL}
$$

![[fh-conditional.png]]