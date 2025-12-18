- Which password is required for the next stage?
- How should the user enter this password to get to the next stage?
- How is the password stored in the application?
    - If standard algorithms are used to hide it, name them!
- Which new obfuscation methods are used in this stage and how can we avoid them?
    - Why is this avoidance possible, i.e. how come it does not change the behavior of the program?
    - Don’t describe obfuscations which you had already explained in the previous stages of the application.
- Which new anti-debugging methods are used in this stage and how can we avoid them?
    - Don’t describe techniques which you had already explained in the previous stages of the application.
- What was your approach to finding the password?

# Password 1

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

from 0040100B (40B)
jump to 00401043 (443)

# Password 2

40 20F7

1. at 004012AD (and 0040138F) jmp "jumps to it's own argument" address, so we need to restart the machine code interpretation from this second jmp instruction byte. I also rewrote jmp to NOP so that the graphs show correct flow.
2. at 004012CF (and 004013AB) xor eax eax = 0, so jz is always run, hence we can restart analysis from the jump target.
3. at 00401321 (and 004013C4) either jz or jnz will always result in jumping to the target 401326 address, so it is safe to restart the analysis from this target byte.
4. There's a "nested function" at 0040136B. It modifies it's return address to 401373 (401369h + 0Ah = 401373). So the call can be modified to jump with 401373 as target and analysis can be restarted from that point.

Expected password length: 19h (0x401326), that is 25

Password:
8jSAuCXJXSzEmMUsmR1yTblkq
Discovered via RC4 Decription tool (both values found as function arguments):
- key: 1pFhAdxei3beq8
- Input (hex): 07C4A12AC2D19D6549B3AB7C93EF1EA04C4F36732D744772DF

- Which password is required for the next stage?
	8jSAuCXJXSzEmMUsmR1yTblkq
- How should the user enter this password to get to the next stage?
	Paste/Enter in the textbox.
- How is the password stored in the application?
	Password is encrypted using RC4 algorithm with the following parameters (both parameters are stored in the program memory):
	- key: 1pFhAdxei3beq8
	- cyphertext (in hex,): 07C4A12AC2D19D6549B3AB7C93EF1EA04C4F36732D744772DF
- Which new obfuscation methods are used in this stage and how can we avoid them?
	1. at 004012AD (and 0040138F) jmp "jumps to it's own argument" address, so we need to restart the machine code interpretation from this second jmp instruction byte. I also rewrote jmp to NOP so that the graphs show correct flow.
	2. at 004012CF (and 004013AB) xor eax eax = 0, so jz is always run, hence we can restart analysis from the jump target.
	3. at 00401321 (and 004013C4) either jz or jnz will always result in jumping to the target 401326 address, so it is safe to restart the analysis from this target byte.
	4. There's a "nested function" at 0040136B. It modifies it's return address to 401373 (401369h + 0Ah = 401373). So the call can be modified to jump with 401373 as target and analysis can be restarted from that point.

- Which new anti-debugging methods are used in this stage and how can we avoid them?
	none
- What was your approach to finding the password?
	- After extracting the exe with cff explorer, the same way as in 1st. When I identified the algorithm I used external tool to quickly calculate the password.
