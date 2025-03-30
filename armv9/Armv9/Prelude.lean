import Armv9.ReadWrite

set_option maxHeartbeats 1_000_000_000
set_option maxRecDepth 10_000
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

/-- Type quantifiers: k_ex7102533# : Bool, k_ex7102532# : Bool -/
def implies (p : Bool) (q : Bool) : Bool :=
  (Bool.or (Bool.not p) q)

/-- Type quantifiers: k_ex7102535# : Bool, k_ex7102534# : Bool -/
def iff (p : Bool) (q : Bool) : Bool :=
  (Bool.and (implies p q) (implies q p))

/-- Type quantifiers: n : Int, i : Int, j : Int -/
def in_range (n : Int) (i : Int) (j : Int) : Bool :=
  bif (i <b j)
  then (Bool.and (i ≤b n) (n ≤b j))
  else (Bool.and (j ≤b n) (n ≤b i))

def min_real (n : real) (m : real) : real :=
  bif (lteq_real n m)
  then n
  else m

def max_real (n : real) (m : real) : real :=
  bif (lteq_real n m)
  then m
  else n

/-- Type quantifiers: n : Int -/
def UInt1 (n : Int) (x : (BitVec n)) : Int :=
  (BitVec.toNat x)

/-- Type quantifiers: n : Nat, n > 0 -/
def SInt1 (n : Nat) (x : (BitVec n)) : Int :=
  (BitVec.toInt x)

/-- Type quantifiers: n : Nat, k_m : Nat, n ≥ 0 ∧ k_m > 0 ∧ (n % k_m) = 0 -/
def Replicate__1 {n : _} (x : (BitVec k_m)) : (BitVec n) :=
  (BitVec.replicateBits x (Int.ediv n (Sail.BitVec.length x)))

/-- Type quantifiers: n : Nat, n ≥ 0 -/
def Ones {n : _} : (BitVec n) :=
  (sail_ones n)

/-- Type quantifiers: n : Nat, n ≥ 0 -/
def Zeros {n : _} : (BitVec n) :=
  (BitVec.zero n)

/-- Type quantifiers: k_n : Nat, k_n ≥ 0 -/
def IsZero (x : (BitVec k_n)) : Bool :=
  (BEq.beq x (BitVec.zero (Sail.BitVec.length x)))

/-- Type quantifiers: k_n : Nat, k_n ≥ 0 -/
def IsOnes (x : (BitVec k_n)) : Bool :=
  (BEq.beq x (sail_ones (Sail.BitVec.length x)))

def Bit (b : (BitVec 1)) : (BitVec 1) :=
  (BitVec.access b 0)

def Bits (b : (BitVec 1)) : (BitVec 1) :=
  bif (BEq.beq b 1#1)
  then (0b1 : (BitVec 1))
  else (0b0 : (BitVec 1))

/-- Type quantifiers: k_n : Nat, m : Nat, k_n > 0 ∧ m ≥ k_n -/
def SignExtend1 {m : _} (x : (BitVec k_n)) : (BitVec m) :=
  (sign_extend x m)

/-- Type quantifiers: k_n : Nat, m : Nat, k_n ≥ 0 ∧ m ≥ k_n -/
def ZeroExtend1 {m : _} (x : (BitVec k_n)) : (BitVec m) :=
  (zero_extend x m)

/-- Type quantifiers: l : Int, i : Int, n : Nat, n ≥ 0 -/
def Slice_int (i : Int) (l : Int) (n : Nat) : (BitVec n) :=
  (get_slice_int n i l)

/-- Type quantifiers: y : Int, x : Int -/
def Align_int (x : Int) (y : Int) : Int :=
  ((fdiv_int x y) *i y)

/-- Type quantifiers: y : Int, k_n : Nat, k_n ≥ 0 -/
def Align_bits (x : (BitVec k_n)) (y : Int) : (BitVec k_n) :=
  (Slice_int (Align_int (BitVec.toNat x) y) 0 (Sail.BitVec.length x))

def RoundTowardsZero (r : real) : Int :=
  bif (lt_real r (to_real 0))
  then (round_up r)
  else (round_down r)

def undefined_signal (_ : Unit) : SailM signal := do
  (internal_pick [LOW, HIGH])

/-- Type quantifiers: arg_ : Nat, 0 ≤ arg_ ∧ arg_ ≤ 1 -/
def signal_of_num (arg_ : Nat) : signal :=
  match arg_ with
  | 0 => LOW
  | _ => HIGH

def num_of_signal (arg_ : signal) : Int :=
  match arg_ with
  | LOW => 0
  | HIGH => 1

def IsUNDEFINED (ex : exception) : Bool :=
  match ex with
  | .Error_Undefined () => true
  | _ => false

def IsUNPREDICTABLE (ex : exception) : Bool :=
  match ex with
  | .Error_Unpredictable () => true
  | _ => false

def IsSEE (ex : exception) : Bool :=
  match ex with
  | .Error_See _ => true
  | _ => false

def IsExceptionTaken (ex : exception) : Bool :=
  match ex with
  | .Error_ExceptionTaken () => true
  | _ => false

def IsSError (ex : exception) : Bool :=
  match ex with
  | .Error_SError _ => true
  | _ => false

/-- Type quantifiers: k_ex7102567# : Bool -/
def ThrowSError (iesb_req : Bool) : SailM Unit := do
  sailThrow ((Error_SError iesb_req))

def ReservedEncoding (_ : Unit) : SailM Unit := do
  sailThrow ((Error_ReservedEncoding ()))

/-- Type quantifiers: k_ex7102570# : Bool -/
def BoolStr (b : Bool) : String :=
  match b with
  | true => "true"
  | false => "false"

/-- Type quantifiers: n : Int -/
def append_int (str : String) (n : Int) : String :=
  (append_str str (dec_str n))

/-- Type quantifiers: k_ex7102573# : Bool -/
def append_bool (str : String) (b : Bool) : String :=
  (append_str str
    (bif b
    then "true"
    else "false"))

/-- Type quantifiers: i : Int -/
def print_integer (i : Int) : Unit :=
  (print_int "" i)

def print_newline (_ : Unit) : Unit :=
  (print_endline "")

/-- Type quantifiers: n : Nat, n ≥ 0 -/
def __UNKNOWN_bits (n : Nat) : SailM (BitVec n) := do
  (undefined_bitvector n)

def __UNKNOWN_integer (_ : Unit) : SailM Int := do
  (undefined_int ())

def __UNKNOWN_boolean (_ : Unit) : SailM Bool := do
  (undefined_bool ())

def __UNKNOWN_real (_ : Unit) : SailM real := do
  (undefined_real ())

def __UNKNOWN_string (_ : Unit) : SailM String := do
  (undefined_string ())

def __UNKNOWN_bit (_ : Unit) : SailM (BitVec 1) := do
  (undefined_bitvector 1)

def __UNKNOWN_signal (_ : Unit) : SailM signal := do
  (undefined_signal ())

/-- Type quantifiers: vl : Nat, vl ≥ 0 -/
def PL_of_VL (vl : Nat) : Nat :=
  (ediv_nat vl 8)

def __GetVerbosity (_ : Unit) : (BitVec 64) :=
  (0x0000000000000000 : (BitVec 64))

def check_cycle_count (_ : Unit) : Unit :=
  ()

def get_cycle_count (_ : Unit) : Int :=
  0

