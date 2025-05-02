import Armv9.Prelude

set_option maxHeartbeats 1_000_000_000
set_option maxRecDepth 1_000_000
set_option linter.unusedVariables false
set_option match.ignoreUnusedAlts true

open Sail

noncomputable section

namespace Armv9.Functions

open signal
open option
open exception
open arm_acc_type
open __InstrEnc
open WFxType
open VFPNegMul
open VCGTtype
open VCGEType
open VBitOps
open VBitOp
open VARange
open Unpredictable
open TranslationStage
open TimeStamp
open TMFailure
open TLBIOp
open TLBIMemAttr
open TLBILevel
open TGx
open SystemHintOp
open Signal
open ShiftType
open Shareability
open SecurityState
open SVECmp
open SRType
open SMEExceptionType
open SDFType
open RestrictType
open Register
open Regime
open ReduceOp
open PrivilegeLevel
open PrefetchHint
open PSTATEField
open PGSe
open PASpace
open PARTIDspaceType
open OpType
open MoveWideOp
open MemType
open MemTagType
open MemOp
open MemAtomicOp
open MOPSStage
open MBReqTypes
open MBReqDomain
open LogicalOp
open InterruptID
open InstrSet
open ImmediateOp
open GPCF
open GCSInstruction
open Feature
open Fault
open FPUnaryOp
open FPType
open FPRounding
open FPMaxMinOp
open FPExc
open FPConvOp
open ExtendType
open ExceptionalOccurrenceTargetState
open Exception
open ErrorState
open DeviceType
open DescriptorType
open DSBAlias
open CrossTriggerIn
open CountOp
open Constraint
open CompareOp
open CacheType
open CachePASpace
open CacheOpScope
open CacheOp
open BranchType
open Barrier
open ArchVersion
open AccessType
open ATAccess

def EndOfInstruction (_ : Unit) : SailM Unit := do
  sailThrow ((Error_ExceptionTaken ()))

def EncodingSpecificOperations (_ : Unit) : Unit :=
  ()

/-- Type quantifiers: k_N : Nat, k_N ≥ 0 -/
def IsZeroBit (x : (BitVec k_N)) : (BitVec 1) :=
  bif (IsZero x)
  then (0b1 : (BitVec 1))
  else (0b0 : (BitVec 1))

/-- Type quantifiers: k_N : Int, shift : Int -/
def LSL_C (x : (BitVec k_N)) (shift : Int) : ((BitVec k_N) × (BitVec 1)) :=
  let carry_out :=
    bif (Bool.and (shift >b 0) (shift ≤b (Sail.BitVec.length x)))
    then (BitVec.access x ((Sail.BitVec.length x) -i shift))
    else 0#1
  ((x <<< shift), (BitVec.join1 [carry_out]))

/-- Type quantifiers: k_N : Int, shift : Int -/
def LSR_C (x : (BitVec k_N)) (shift : Int) : ((BitVec k_N) × (BitVec 1)) :=
  let carry_out :=
    bif (Bool.and (shift >b 0) (shift ≤b (Sail.BitVec.length x)))
    then (BitVec.access x (shift -i 1))
    else 0#1
  ((x >>> shift), (BitVec.join1 [carry_out]))

/-- Type quantifiers: k_N : Nat, shift : Nat, k_N ≥ 0 ∧ shift ≥ 0 -/
def ASR_C (x : (BitVec k_N)) (shift : Nat) : ((BitVec k_N) × (BitVec 1)) :=
  let carry_out :=
    bif (Bool.or (BEq.beq shift 0) (BEq.beq (Sail.BitVec.length x) 0))
    then 0#1
    else
      (bif (shift ≥b (Sail.BitVec.length x))
      then (BitVec.access x ((Sail.BitVec.length x) -i 1))
      else (BitVec.access x (shift -i 1)))
  ((BitVec.rotateRight x shift), (BitVec.join1 [carry_out]))

/-- Type quantifiers: k_N : Nat, shift : Int, k_N > 0 -/
def ROR_C (x : (BitVec k_N)) (shift : Int) : SailM ((BitVec k_N) × (BitVec 1)) := do
  assert (shift >b 0) "src/builtins.sail:100.20-100.21"
  let m := (Nat.div shift (Sail.BitVec.length x))
  let result : (BitVec k_N) := ((x >>> m) ||| (x <<< ((Sail.BitVec.length x) -i m)))
  let carry_out : (BitVec 1) :=
    (BitVec.join1 [(BitVec.access result ((Sail.BitVec.length x) -i 1))])
  (pure (result, carry_out))

/-- Type quantifiers: k_N : Nat, shift : Nat, k_N > 0 ∧ shift ≥ 0 -/
def ROR (x : (BitVec k_N)) (shift : Nat) : (BitVec k_N) :=
  bif (BEq.beq shift 0)
  then x
  else
    (let m := (Nat.div shift (Sail.BitVec.length x))
    ((x >>> m) ||| (x <<< ((Sail.BitVec.length x) -i m))))

/-- Type quantifiers: k_M : Nat, N : Nat, k_is_unsigned : Bool, k_M ≥ 0 ∧ N ≥ 0 -/
def Extend (x : (BitVec k_M)) (N : Nat) (is_unsigned : Bool) : SailM (BitVec N) := do
  bif is_unsigned
  then
    (do
      assert (Bool.and ((Sail.BitVec.length x) ≥b 0) (N ≥b (Sail.BitVec.length x))) "src/builtins.sail:121.47-121.48"
      (pure (Sail.BitVec.zeroExtend x N)))
  else
    (do
      assert (Bool.and ((Sail.BitVec.length x) >b 0) (N ≥b (Sail.BitVec.length x))) "src/builtins.sail:124.46-124.47"
      (pure (sign_extend x N)))

/-- Type quantifiers: k_N : Nat, k_is_unsigned : Bool, k_N ≥ 0 -/
def asl_Int (x : (BitVec k_N)) (is_unsigned : Bool) : SailM Int := do
  let result ← do
    bif is_unsigned
    then (pure (BitVec.toNat x))
    else
      (do
        assert ((Sail.BitVec.length x) >b 0) "src/builtins.sail:134.33-134.34"
        (pure (BitVec.toInt x)))
  (pure result)

/-- Type quantifiers: k_N : Nat, k_N ≥ 0 -/
def LowestSetBit (x : (BitVec k_N)) : Int := ExceptM.run do
  let loop_i_lower := 0
  let loop_i_upper := ((Sail.BitVec.length x) -i 1)
  let mut loop_vars := ()
  for i in [loop_i_lower:loop_i_upper:1]i do
    let () := loop_vars
    loop_vars ← do
      bif (BEq.beq (BitVec.join1 [(BitVec.access x i)]) (0b1 : (BitVec 1)))
      then throw (i : Int)
      else (pure ())
  (pure loop_vars)
  (pure (Sail.BitVec.length x))

/-- Type quantifiers: k_N : Nat, k_N ≥ 0 -/
def HighestSetBit (x : (BitVec k_N)) : Int := ExceptM.run do
  let loop_i_lower := 0
  let loop_i_upper := ((Sail.BitVec.length x) -i 1)
  let mut loop_vars := ()
  for i in [loop_i_upper:loop_i_lower:-1]i do
    let () := loop_vars
    loop_vars ← do
      bif (BEq.beq (BitVec.join1 [(BitVec.access x i)]) (0b1 : (BitVec 1)))
      then throw (i : Int)
      else (pure ())
  (pure loop_vars)
  (pure (Neg.neg 1))

/-- Type quantifiers: k_N : Nat, k_N ≥ 0 -/
def BitCount (x : (BitVec k_N)) : Int := Id.run do
  let result : Int := 0
  let result ← (( do
    let loop_i_lower := 0
    let loop_i_upper := ((Sail.BitVec.length x) -i 1)
    let mut loop_vars := result
    for i in [loop_i_lower:loop_i_upper:1]i do
      let result := loop_vars
      loop_vars :=
        bif (BEq.beq (BitVec.join1 [(BitVec.access x i)]) (0b1 : (BitVec 1)))
        then (result +i 1)
        else result
    (pure loop_vars) ) : Id Int )
  let result := result
  (pure result)

/-- Type quantifiers: k_N : Nat, k_N ≥ 0 -/
def CountLeadingZeroBits (x : (BitVec k_N)) : Int :=
  ((Sail.BitVec.length x) -i ((HighestSetBit x) +i 1))

/-- Type quantifiers: k_N : Nat, 1 ≤ (k_N - 1) -/
def CountLeadingSignBits (x : (BitVec k_N)) : Int :=
  (CountLeadingZeroBits
    ((Sail.BitVec.extractLsb x ((Sail.BitVec.length x) -i 1) 1) ^^^ (Sail.BitVec.extractLsb x
        ((Sail.BitVec.length x) -i 2) 0)))

/-- Type quantifiers: k_N : Nat, e : Int, size : Nat, k_N ≥ 0 ∧
  size ≥ 0 ∧
  (e * size) ≤ (e * size + size - 1) ∨ not((e ≥ 0 ∧ ((e + 1) * size) ≤ k_N)) -/
def Elem_read (vector_name : (BitVec k_N)) (e : Int) (size : Nat) : SailM (BitVec size) := do
  assert (Bool.and (e ≥b 0) (((e +i 1) *i size) ≤b (Sail.BitVec.length vector_name))) "src/builtins.sail:195.40-195.41"
  (pure (Sail.BitVec.extractLsb vector_name (((e *i size) +i size) -i 1) (e *i size)))

/-- Type quantifiers: k_N : Nat, e : Int, size : Nat, k_N ≥ 0 ∧
  size ≥ 0 ∧ (e * size) ≤ ((e + 1) * size - 1) ∨ not((e ≥ 0 ∧ ((e + 1) * size) ≤ k_N)) -/
def Elem_set (vector_name__arg : (BitVec k_N)) (e : Int) (size : Nat) (value_name : (BitVec size)) : SailM (BitVec k_N) := do
  let vector_name : (BitVec k_N) := vector_name__arg
  assert (Bool.and (e ≥b 0) (((e +i 1) *i size) ≤b (Sail.BitVec.length vector_name__arg))) "src/builtins.sail:205.40-205.41"
  (pure (Sail.BitVec.updateSubrange vector_name (((e +i 1) *i size) -i 1) (e *i size) value_name))

