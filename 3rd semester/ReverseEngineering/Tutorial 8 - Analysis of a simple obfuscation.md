1. exeinfo: Check for comipler information (MS VC++ -> IDA might be best)
2. cff explorer - check and disable Address Space Layout randomization (File - Nt Headers - Optional Header - Dll Characteristics: DLL can move (unchecked))
3. Resource Hacker - Dialog information (form window), gives us API functions expectations
4. cff explorer - import directory: look for characteristic libraries (eg. USER32.dll needed for window-based app)
5. IDA: Strings, right click - Setup... - possible to check different string types (possibly all)
6. IDA: cross reference: `X`
7. Try cross referencing strings of interest (CORRECT/WRONG etc.) or API function calls that might be invoked close to the point of interest.

Most of the cases: IDA finds only `start` function - goal: find main()
Scan through function calls there, follow what's promising in size. Main should be expected somewhere down the line (initialization the longest, call main, cleanup)

Main is expected to have arguments (argc \[nr of args\] + argv \[ptr\] - value/types we expect are important to recognize)

Else debug and observe which call is significant.

IDA `M`: provide useful enumerables part of system libraries (eg. WM_DESTROY, WM_... for windowed apps events)

IDA `H`: convert HEX/DEC

IDA `R` in the hex view: change repr to string
