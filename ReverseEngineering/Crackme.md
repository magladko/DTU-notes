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
	After extracting the exe with cff explorer, the same way as in 1st. When I identified the algorithm I used external tool to quickly calculate the password.

# Password 3

----
1. What I did next, but might not be necessary:
	1. Right click on the erroneous position then choose Cut thunk
	2. Adjust the Size to 1F4 (4 less than it used to be)
	3. 

NOTE
- `pushad` at 0070D3C0 (marked as entry point)
- `popad` at 0070D555
- `jmp` at 0070D563
- unpacked at 00413C98

424b0f

PASSWORD:
Faculty of cool things and stuff


- Which password is required for the next stage?
	Faculty of cool things and stuff
- How should the user enter this password to get to the next stage?
	Paste/type into the first edit box, then click the button.
- How is the password stored in the application?
	As Base64 string (RmFjdWx0eSBvZiBjb29sIHRoaW5ncyBhbmQgc3R1ZmY=)
- Which new obfuscation methods are used in this stage and how can we avoid them?
	Unpacking with `upx -d`:
	1. Ensure write access rights to the exe file `attrib -r .\Stage3.exe` (else it failed for me).
	2. Replace BPX0 to UPX0 (common anti-upx pattern to rename section names)
	3. Run `upx -d Stage3.exe` -- DONE

	Manual unpacking
	1. Open with x64dbg
	2. Run the program, the execution will stop at EntryPoint (`pushad` instruction)
	3. The complementary `popad` instruction is located at address 70D555 and the jmp instruction that leads to the unpacking location is at 70D563 (navigate there, that is Ctrl+G, enter the address then submit)
	4. Set a breakpoint on this address and click Run to continue running the program.
	5. When the breakpoint is achieved, press step into to jump to the unpacked program entry point.
	6. Click Plugins > Scylla
	7. Within Scylla click IAT Autosearch, accept advanced results
	8. Click Get Imports
	9. ISSUE: There is seemingly a phantom import record, this can be safely ignored. The file will not be functional, IDA will complain, but the analysis will be possible to perform.
	10. Then click Dump to save dump, and after that Fix Dump selecting the freshly created dump file to fix the IAT with the calculated values.

- Which new anti-debugging methods are used in this stage and how can we avoid them?
none
- What was your approach to finding the password?
	I followed the approach from the Password 2 exactly, however in the hindsight I probably should've tried putting the decoded Base64 string at the moment I have seen it...


# Password 4

Expected length: 19h (25)

For each byte of functions at 4102D0:
1. add previously calculated key byte
2. add current loop variant
3. take 2 lowest bytes of ECX (cl)
4. modify 

- Which password is required for the next stage?
	ETxXhmqg1RxdJz9ovWPkltW2V
- How should the user enter this password to get to the next stage?
	Write or paste in the second message box after submitting the prior one
- How is the password stored in the application?
    Password is encrypted with custom/mangled RC4 implementation. The key differences:
	    The string is processed in chunks of length 3 (or less in the last steps) consumed from both ends (instead of linearly byte-by-byte)
		S-Box is not a full permutation (some values are duplicate, some are missing)
- Which new obfuscation methods are used in this stage and how can we avoid them?
	Dynamically evaluated function calls, one needs to debug to see where the call leads
	The result string messages are built dynamically.
- Which new anti-debugging methods are used in this stage and how can we avoid them?
	The program is checking for debugging flags and terminates process if that is the case (loc_410407) via NtGlobalFlag check technique [Anti-Debug: Debug Flags](https://anti-debug.checkpoint.com/techniques/debug-flags.html#:~:text=2.2.-,NtGlobalFlag,-The%20NtGlobalFlag%20field). We could use a debugger plugin, but I just invalidated the check by modifying the binary to never jump (2xnop instead of jnz).
- What was your approach to finding the password?
1. I searched for the immediate value of 0x3EB (1003) to locate where the new edit box resource is touched. It shows in 2 locations, first just after the first password is guessed to unlock the box, second when the contents should be processed. 
2. Then I debugged the application to monitor how is the input value processed (after I modified anti-debugging check, which I identified by following call stack after setting breakpoints via: bp ExitProcess, bp TerminateProcess, bp NtTerminateProcess). The input modification occurred at address 4102BA.
3. This lead me to the encoding function on which I have put a breakpoint, that helped me to uncover a 'test string' value being passed at the beginning of the program helping me to reverse engineer the encryption algorithm.
4. I monitored the function calls to take note on the order in which the string chunks are processed.
5. I translated the algorithm to python to find the correct password. 
