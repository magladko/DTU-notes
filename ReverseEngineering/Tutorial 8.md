1. exeinfo: Check for comipler information (MS VC++ -> IDA might be best)
2. cff explorer - check and disable Address Space Layout randomization (File - Nt Headers - Optional Header - Dll Characteristics: DLL can move (unchecked))
3. Resource Hacker - Dialog information (form window), gives us API functions expectations
4. cff explorer - import directory: look for characteristic libraries (eg. USER32.dll needed for window-based app)
5. IDA: Strings, right click - Setup... - possible to check different string types (possibly all)
6. IDA: cross reference: `X`
7. Try cross referencing strings of interest (CORRECT/WRONG etc.)
8. 