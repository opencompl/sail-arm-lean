# ARM ISA Semantics for Lean (arm-v9.4-a)

These semantics are generated from the official ARM SPEC available at
https://github.com/rems-project/sail-arm.

⚠️ While this repository covers the full ARM, our Lean backend for sail
is still work-in-progress. As a result, our semantics are still full of warnings
and errors. Similarly, our output is not yet polished for readability.
# RISC-V Lean Statistics

Lines: 2793195  
Definitions: 65579  
Inductive definitions: 884  
Abbreviations: 3446  

# Warnings and Errors

Errors found: 30  
Warnings found: 0  

## Error Classes

- 7x type mismatch
- 7x application type mismatch
- 4x don't know how to synthesize placeholder
- 2x unknown identifier 'AArch64_S2Walk'
- 2x unexpected identifier; expected 'do'
- 1x unknown identifier 'GPTWalk'
- 1x unknown identifier 'AArch64_AutoGen_ArchitectureReset'
- 1x maximum recursion depth has been reached
- 1x invalid field notation, type is not of the form (C ...) where C is a constant
- 1x failed to synthesize
- 1x failed to prove termination, possible solutions:
- 1x don't know how to synthesize placeholder for argument 'α'
- 1x Lean exited with code 1
has type
  BitVec 64 × DescriptorType × FaultRecord × ℤ × ℤ × AddressDescriptor × TTWState : Type
but is expected to have type
  SailME ?m.48776773 PUnit.{1} : Type
error: /home/runner/work/sail-arm-lean/sail-arm-lean/sail-arm/arm-v9.4-a/lean/armv9/Armv9/V8Base.lean:100521:12: application type mismatch
  @ite ?m.48883203 fun x => ?m.48883196
argument
  fun x => ?m.48883196
has type
  (x : ?m.48883192) → ?m.48883197 x : Sort (imax ?u.48883191 ?u.48883194)
but is expected to have type
  Prop : Type
error: /home/runner/work/sail-arm-lean/sail-arm-lean/sail-arm/arm-v9.4-a/lean/armv9/Armv9/V8Base.lean:100523:12: type mismatch
  loop_vars
has type
  BitVec 64 ×
    DescriptorType × FaultRecord × ℤ × ℤ × Bool × FaultRecord × AddressDescriptor × AddressDescriptor × TTWState : Type
but is expected to have type
  SailME ?m.48877329 PUnit.{1} : Type
error: /home/runner/work/sail-arm-lean/sail-arm-lean/sail-arm/arm-v9.4-a/lean/armv9/Armv9/V8Base.lean:101921:8: application type mismatch
  @ite ?m.49099075 fun x => ?m.49099068
argument
  fun x => ?m.49099068
has type
  (x : ?m.49099064) → ?m.49099069 x : Sort (imax ?u.49099063 ?u.49099066)
but is expected to have type
  Prop : Type
error: /home/runner/work/sail-arm-lean/sail-arm-lean/sail-arm/arm-v9.4-a/lean/armv9/Armv9/V8Base.lean:101923:8: type mismatch
  loop_vars
has type
  BitVec 3 ×
    BitVec 1 ×
      BitVec 1 ×
        BitVec 32 ×
          BitVec 4 ×
            FaultRecord ×
              BitVec 1 ×
                BitVec 1 ×
                  BitVec 1 ×
                    BitVec 1 ×
                      Bool × FaultRecord × AddressDescriptor × BitVec 3 × AddressDescriptor × TTWState × BitVec 1 : Type
but is expected to have type
  SailME ?m.49090809 PUnit.{1} : Type
error: /home/runner/work/sail-arm-lean/sail-arm-lean/sail-arm/arm-v9.4-a/lean/armv9/Armv9/V8Base.lean:101922:15: invalid field notation, type is not of the form (C ...) where C is a constant
  walkstate
has type
  ?m.49114876
error: Lean exited with code 1
Some required builds logged failures:
- Armv9.V8Base
