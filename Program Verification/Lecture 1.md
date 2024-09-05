[Introduction @DTU Learn](https://learn.inside.dtu.dk/d2l/le/lessons/215949/units/861144)

What is program verification

***Prove that a program always works as expected***
**Task**: *determine whether a given program satisfies its specification*

![[what is program verification.png]]

**seL4**  - fully verified system kernel
![[sel4-logo.png]]
### Informal Specifications
```java
// Informally specify what 
int [] sort ( int [] A) 
// is supposed to do
```
The method... 
- is memory safe 
- does not crash 
- runs in  $O(|A| * log|A|)$
- returns a sorted array 
- returns a permutation of A 
- does not modify A 
- maintains the original ordering of A where possible

**How can we verify that a program satisfies its specification?**

## Different approaches to **Program Verification**
### ...Testing
- **NOT** a Program Verification Technique
- Good on pointing out bugs and errors
- Impossible to actually verify (only can prove it does not work)
### ... Textbook correctness arguments
Even well-defined and proved argument can lead to unexpected behavior once implemented. Hence this is **cannot be treated as a formal verification**.

### ...Proving correctness on paper
- error prone
- good step forward, but not enough

### ...Model checking
- Automatic verification of intricate specifications...
- ... by exhaustive testing
- Targets finite-state system models 
- Suffers from state space explosion problem 
- Programs typically describe infinite-state models 
- Verified model  $\neq$ verified program
### ...Interactive theorem proving
#### Strengths:
- Can handle complex systems and properties 
- Well-established trusted code base 
#### Success stories:
- CompCert: formally verified C compiler (2008) 
- seL4: formally verified high-performance operating system microkernel (2009)
- EveryCrypt: formally verified crypto library (2020) 
#### Weaknesses: 
- Requires expert knowledge 
- Very labor-intensive (CompCert: > 6 person years)
- Possible detachment from production code or vendor lock-in

### Automated Deductive Verification
**Dafny, Viper, Vcc, Prusti**
#### Idea: "use verification like a type checker during compilation"
- Specifications take the form of **source code annotatons**
- Analogies: Python type hints, JUnit annotations, Rust attributes
#### Strengths
- Substantially **less effort** than **interactive theorem proving**
- Integrates into existing development process
- Think: very strong type checking / automated testing
- More annotations => more guarantees
#### Weaknesses:
- Less expressive than interactive verification
- May produce false positives (due to undecidability)
- Still requires effort and expertise

## The Three Main Course Topics 
1. Principles of deductive program verification 
	- How to design a verification technique 
	- How to justify that “verified” indeed means “correct” 
	- Reading, writing, and adapting formal verification techniques 
2. Engineering aspects of automated verification tools 
	- How to build or extend a verifier for your favourite language 
	- Group project 1: Develop your own verification tool 
3. Using a modern program verification tool
	- How do we approach a verification project?
	- Group project 2: program verification with Viper

![[course outline.png]]