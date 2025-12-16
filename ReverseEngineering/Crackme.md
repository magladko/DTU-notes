# Assignment 1

To unlock the text box - hold the following keyboard keys (described in StartAddress function called at initialization of DialogFunc):
- 46h - F
- 49h - I
- 54h - T

Password (variable of 403000 pointing at string at 402070):
First day of July 2019

- Which password is required for the next stage?
	- First day of July 2019
- How should the user enter this password to get to the next stage?
	- Hold keys F, I, T at the same time to unlock the text field
	- Type in the password
	- Click OK button
- How is the password stored in the application?
	- The password is stored in hardcoded plaintext as a global string literal.
- Which new obfuscation methods are used in this stage and how can we avoid them?
	- no obfuscation methods encountered
- Which new anti-debugging methods are used in this stage and how can we avoid them?
    - no anti-debugging methods encountered
- What was your approach to finding the password?
	1. Find interesting strings (e.g. "Invalid password :(")
	2. Go up the code to find the string comparison and locate the string that was used.
	3. To find the text box unlocking I followed branch opposite to the one leading to string comparison finding StartAddress function invoked in a new thread, which checked for keys pressed via `GetAsyncKeyState`.
