
![[swp.png]]
## Exercise
1. Compute $\text{swp}[C](\emptyset)$ of the following command C:
```
{
	assert x == 7
} [] {
	assert x == 2
	assert x > 0
}
```
**Solution:**
```
{{ x == 7, x > 0, x == 2}}
{
	{{ x == 7 }}
	assert x == 7
	{{ }}
} [] {
	{{ x > 0, x == 2}}
	assert x == 2
	{{ x > 0 }}
	assert x > 0
	{{ }}
} {{ }}
```

2. Based on (1.) determine assertions that do not hold.
**None of the formulae is valid, so no assertion holds.**
3. For each assertion that do not hold determine a counterexample.
**Counterexamples: x == 7 fails for x == 2, x == 2 fails for x == 7**

# IVL0

![[summary-ivl0-slide.png]]

# Error localization
## swp
![[swp-slide.png]]
## Verification Condition for Error Localization in IVL0
![[ver-cond-err-loc-ivl0-slide.png]]
