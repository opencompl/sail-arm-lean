# ARM ISA Semantics for Lean (arm-v9.4-a)

These semantics are generated from the official ARM SPEC available at
https://github.com/rems-project/sail-arm.

⚠️ While this repository covers the full ARM, our Lean backend for sail
is still work-in-progress. As a result, our semantics are still full of warnings
and errors. Similarly, our output is not yet polished for readability.
# RISC-V Lean Statistics

Lines: 2793177  
Definitions: 65575  
Inductive definitions: 884  
Abbreviations: 3441  

# Warnings and Errors

Errors found: 92  
Warnings found: 0  

## Error Classes

- 38x application type mismatch
- 30x type mismatch
- 4x don't know how to synthesize placeholder
- 2x unknown identifier 'AArch64_S2Walk'
- 2x unexpected identifier; expected 'do'
- 2x invalid `do` notation, expected type is not a monad application
- 1x unknown identifier 'sail_translation_start'
- 1x unknown identifier 'sail_translation_end'
- 1x unknown identifier 'sail_tlbi'
- 1x unknown identifier 'sail_take_exception'
- 1x unknown identifier 'sail_cache_op'
- 1x unknown identifier 'GPTWalk'
- 1x unknown identifier 'AArch64_AutoGen_ArchitectureReset'
- 1x unexpected token 'at'; expected '_' or identifier
- 1x maximum recursion depth has been reached
- 1x invalid field notation, type is not of the form (C ...) where C is a constant
- 1x failed to synthesize
- 1x failed to prove termination, possible solutions:
- 1x don't know how to synthesize placeholder for argument 'α'
- 1x Lean exited with code 1
has type
  BitVec 64 × DescriptorType × FaultRecord × ℤ × ℤ × AddressDescriptor × TTWState : Type
but is expected to have type
  SailME ?m.48712098 PUnit.{1} : Type
error: /home/runner/work/sail-arm-lean/sail-arm-lean/sail-arm/arm-v9.4-a/lean/armv9/Armv9/V8Base.lean:100516:12: application type mismatch
  @ite ?m.48818528 fun x => ?m.48818521
argument
  fun x => ?m.48818521
has type
  (x : ?m.48818517) → ?m.48818522 x : Sort (imax ?u.48818516 ?u.48818519)
but is expected to have type
  Prop : Type
error: /home/runner/work/sail-arm-lean/sail-arm-lean/sail-arm/arm-v9.4-a/lean/armv9/Armv9/V8Base.lean:100518:12: type mismatch
  loop_vars
has type
  BitVec 64 ×
    DescriptorType × FaultRecord × ℤ × ℤ × Bool × FaultRecord × AddressDescriptor × AddressDescriptor × TTWState : Type
but is expected to have type
  SailME ?m.48812654 PUnit.{1} : Type
error: /home/runner/work/sail-arm-lean/sail-arm-lean/sail-arm/arm-v9.4-a/lean/armv9/Armv9/V8Base.lean:101916:8: application type mismatch
  @ite ?m.49034400 fun x => ?m.49034393
argument
  fun x => ?m.49034393
has type
  (x : ?m.49034389) → ?m.49034394 x : Sort (imax ?u.49034388 ?u.49034391)
but is expected to have type
  Prop : Type
error: /home/runner/work/sail-arm-lean/sail-arm-lean/sail-arm/arm-v9.4-a/lean/armv9/Armv9/V8Base.lean:101918:8: type mismatch
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
  SailME ?m.49026134 PUnit.{1} : Type
error: /home/runner/work/sail-arm-lean/sail-arm-lean/sail-arm/arm-v9.4-a/lean/armv9/Armv9/V8Base.lean:101917:15: invalid field notation, type is not of the form (C ...) where C is a constant
  walkstate
has type
  ?m.49050201
error: Lean exited with code 1
Some required builds logged failures:
- Armv9.V8Base
