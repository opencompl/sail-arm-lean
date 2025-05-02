# ARM ISA Semantics for Lean (arm-v9.4-a)

These semantics are generated from the official ARM SPEC available at
https://github.com/rems-project/sail-arm.

⚠️ While this repository covers the full ARM, our Lean backend for sail
is still work-in-progress. As a result, our semantics are still full of warnings
and errors. Similarly, our output is not yet polished for readability.
# RISC-V Lean Statistics

Lines: 2637382  
Definitions: 65584  
Inductive definitions: 884  
Abbreviations: 3447  

# Warnings and Errors

Errors found: 173321  
Warnings found: 873  

## Error Classes

- 87085x tabs are not allowed; please configure your editor to expand them
- 84423x unexpected command
- 1405x elaboration function for 'num' has not been implemented
- 383x (↥) must have a function type, not
- 21x failed to synthesize
- 1x omega could not prove the goal:
- 1x elaboration function for 'do' has not been implemented
- 1x could not synthesize default value for field 'step_pos' of 'IntRange' using tactics
- 1x Lean exited with code 134
error: /home/runner/work/sail-arm-lean/sail-arm-lean/sail-arm/arm-v9.4-a/lean/armv9/Armv9/SysregsAutogen.lean:113471:70: elaboration function for 'num' has not been implemented
error: /home/runner/work/sail-arm-lean/sail-arm-lean/sail-arm/arm-v9.4-a/lean/armv9/Armv9/SysregsAutogen.lean:113474:0: tabs are not allowed; please configure your editor to expand them
error: /home/runner/work/sail-arm-lean/sail-arm-lean/sail-arm/arm-v9.4-a/lean/armv9/Armv9/SysregsAutogen.lean:113473:6: unexpected command
error: /home/runner/work/sail-arm-lean/sail-arm-lean/sail-arm/arm-v9.4-a/lean/armv9/Armv9/SysregsAutogen.lean:113475:0: tabs are not allowed; please configure your editor to expand them
error: /home/runner/work/sail-arm-lean/sail-arm-lean/sail-arm/arm-v9.4-a/lean/armv9/Armv9/SysregsAutogen.lean:113474:2: unexpected command
error: /home/runner/work/sail-arm-lean/sail-arm-lean/sail-arm/arm-v9.4-a/lean/armv9/Armv9/SysregsAutogen.lean:113476:0: tabs are not allowed; please configure your editor to expand them
error: /home/runner/work/sail-arm-lean/sail-arm-lean/sail-arm/arm-v9.4-a/lean/armv9/Armv9/SysregsAutogen.lean:113475:26: unexpected command
error: /home/runner/work/sail-arm-lean/sail-arm-lean/sail-arm/arm-v9.4-a/lean/armv9/Armv9/SysregsAutogen.lean:113477:0: tabs are not allowed; please configure your editor to expand them
error: /home/runner/work/sail-arm-lean/sail-arm-lean/sail-arm/arm-v9.4-a/lean/armv9/Armv9/SysregsAutogen.lean:113476:3: unexpected command
error: /home/runner/work/sail-arm-lean/sail-arm-lean/sail-arm/arm-v9.4-a/lean/armv9/Armv9/SysregsAutogen.lean:113478:0: tabs are not allowed; please configure your editor to expand them
error: /home/runner/work/sail-arm-lean/sail-arm-lean/sail-arm/arm-v9.4-a/lean/armv9/Armv9/SysregsAutogen.lean:113477:6: unexpected command
error: /home/runner/work/sail-arm-lean/sail-arm-lean/sail-arm/arm-v9.4-a/lean/armv9/Armv9/SysregsAutogen.lean:113479:0: tabs are not allowed; please configure your editor to expand them
error: /home/runner/work/sail-arm-lean/sail-arm-lean/sail-arm/arm-v9.4-a/lean/armv9/Armv9/SysregsAutogen.lean:113478:95: unexpected command
error: /home/runner/work/sail-arm-lean/sail-arm-lean/sail-arm/arm-v9.4-a/lean/armv9/Armv9/SysregsAutogen.lean:113480:0: tabs are not allowed; please configure your editor to expand them
error: /home/runner/work/sail-arm-lean/sail-arm-lean/sail-arm/arm-v9.4-a/lean/armv9/Armv9/SysregsAutogen.lean:113479:84: unexpected command
error: /home/runner/work/sail-arm-lean/sail-arm-lean/sail-arm/arm-v9.4-a/lean/armv9/Armv9/SysregsAutogen.lean:113481:0: tabs are not allowed; please configure your editor to expand them
error: /home/runner/work/sail-arm-lean/sail-arm-lean/sail-arm/arm-v9.4-a/lean/armv9/Armv9/SysregsAutogen.lean:113480:43: unexpected command
error: /home/runner/work/sail-arm-lean/sail-arm-lean/sail-arm/arm-v9.4-a/lean/armv9/Armv9/SysregsAutogen.lean:113482:0: tabs are not allowed; please configure your editor to expand them
error: /home/runner/work/sail-arm-lean/sail-arm-lean/sail-arm/arm-v9.4-a/lean/armv9/Armv9/SysregsAutogen.lean:113481:7: unexpected command
error: /home/runner/work/sail-arm-lean/sail-arm-lean/sail-arm/arm-v9.4-a/lean/armv9/Armv9/SysregsAutogen.lean:113483:0: tabs are not allowed; please configure your editor to expand them
error: /home/runner/work/sail-arm-lean/sail-arm-lean/sail-arm/arm-v9.4-a/lean/armv9/Armv9/SysregsAutogen.lean:113482:3: unexpected command
error: /home/runner/work/sail-arm-lean/sail-arm-lean/sail-arm/arm-v9.4-a/lean/armv9/Armv9/SysregsAutogen.lean:113484:0: tabs are not allowed; please configure your editor to expand them
error: /home/runner/work/sail-arm-lean/sail-arm-lean/sail-arm/arm-v9.4-a/lean/armv9/Armv9/SysregsAutogen.lean:113483:63: unexpected command
error: /home/runner/work/sail-arm-lean/sail-arm-lean/sail-arm/arm-v9.4-a/lean/armv9/Armv9/SysregsAutogen.lean:113485:0: tabs are not allowed; please configure your editor to expand them
error: /home/runner/work/sail-arm-lean/sail-arm-lean/sail-arm/arm-v9.4-a/lean/armv9/Armv9/SysregsAutogen.lean:113484:4: unexpected command
error: /home/runner/work/sail-arm-lean/sail-arm-lean/sail-arm/arm-v9.4-a/lean/armv9/Armv9/SysregsAutogen.lean:113486:0: tabs are not allowed; please configure your editor to expand them
error: /home/runner/work/sail-arm-lean/sail-arm-lean/sail-arm/arm-v9.4-a/lean/armv9/Armv9/SysregsAutogen.lean:113485:7: unexpected command
error: /home/runner/work/sail-arm-lean/sail-arm-lean/sail-arm/arm-v9.4-a/lean/armv9/Armv9/SysregsAutogen.lean:113487:0: tabs are not allowed; please configure your editor to expand them
error: /home/runner/work/sail-arm-lean/sail-arm-lean/sail-arm/arm-v9.4-a/lean/armv9/Armv9/SysregsAutogen.lean:113486:67: unexpected command
error: /home/runner/work/sail-arm-lean/sail-arm-lean/sail-arm/arm-v9.4-a/lean/armv9/Armv9/SysregsAutogen.lean:113488:0: tabs are not allowed; please configure your editor to expand them
error: /home/runner/work/sail-arm-lean/sail-arm-lean/sail-arm/arm-v9.4-a/lean/armv9/Armv9/SysregsAutogen.lean:113487:44: unexpected command
error: /home/runner/work/sail-arm-lean/sail-arm-lean/sail-arm/arm-v9.4-a/lean/armv9/Armv9/SysregsAutogen.lean:113489:0: tabs are not allowed; please configure your editor to expand them
error: /home/runner/work/sail-arm-lean/sail-arm-lean/sail-arm/arm-v9.4-a/lean/armv9/Armv9/SysregsAutogen.lean:113488:78: unexpected command
error: /home/runner/work/sail-arm-lean/sail-arm-lean/sail-arm/arm-v9.4-a/lean/armv9/Armv9/SysregsAutogen.lean:113490:0: tabs are not allowed; please configure your editor to expand them
error: /home/runner/work/sail-arm-lean/sail-arm-lean/sail-arm/arm-v9.4-a/lean/armv9/Armv9/SysregsAutogen.lean:113489:4: unexpected command
error: /home/runner/work/sail-arm-lean/sail-arm-lean/sail-arm/arm-v9.4-a/lean/armv9/Armv9/SysregsAutogen.lean:113491:0: tabs are not allowed; please configure your editor to expand them
error: /home/runner/work/sail-arm-lean/sail-arm-lean/sail-arm/arm-v9.4-a/lean/armv9/Armv9/SysregsAutogen.lean:113490:69: elaboration function for 'num' has not been implemented
error: /home/runner/work/sail-arm-lean/sail-arm-lean/sail-arm/arm-v9.4-a/lean/armv9/Armv9/SysregsAutogen.lean:113492:0: tabs are not allowed; please configure your editor to expand them
error: /home/runner/work/sail-arm-lean/sail-arm-lean/sail-arm/arm-v9.4-a/lean/armv9/Armv9/SysregsAutogen.lean:113491:51: unexpected command
error: /home/runner/work/sail-arm-lean/sail-arm-lean/sail-arm/arm-v9.4-a/lean/armv9/Armv9/SysregsAutogen.lean:113493:0: tabs are not allowed; please configure your editor to expand them
error: /home/runner/work/sail-arm-lean/sail-arm-lean/sail-arm/arm-v9.4-a/lean/armv9/Armv9/SysregsAutogen.lean:113492:3: unexpected command
error: /home/runner/work/sail-arm-lean/sail-arm-lean/sail-arm/arm-v9.4-a/lean/armv9/Armv9/SysregsAutogen.lean:113494:0: tabs are not allowed; please configure your editor to expand them
info: stdout:
{"severity":"error","pos":{"line":113493,"column":6},"kind":"[anonymous]","keepFullRange":false,"isSilent":false,"fileName":"/home/runner/work/sail-arm-lean/sail-arm-lean/sail-arm/arm-v9.4-a/lean/armv9/Armv9/SysregsAutogen.lean"

info: stderr:
Stack overflow detected. Aborting.
error: Lean exited with code 134
Some required builds logged failures:
- Armv9.SysregsAutogen
