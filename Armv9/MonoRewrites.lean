import Armv9.Option

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

/-- Type quantifiers: k_n : Int, m : Nat, m ≥ 0 -/
def extzv {m : _} (v : (BitVec k_n)) : (BitVec m) :=
  bif (m <b (Sail.BitVec.length v))
  then (Sail.BitVec.truncate v m)
  else (Sail.BitVec.zeroExtend v m)

/-- Type quantifiers: k_n : Int, m : Nat, m ≥ 0 -/
def extsv {m : _} (v : (BitVec k_n)) : (BitVec m) :=
  bif (m <b (Sail.BitVec.length v))
  then (Sail.BitVec.truncate v m)
  else (Sail.BitVec.signExtend v m)

/-- Type quantifiers: j : Int, i : Int, k_n : Nat, k_n ≥ 0 -/
def is_zero_subrange (xs : (BitVec k_n)) (i : Int) (j : Int) : Bool :=
  (BEq.beq (xs &&& (slice_mask (n := (Sail.BitVec.length xs)) j ((i -i j) +i 1)))
    (extzv (m := (Sail.BitVec.length xs)) (0b0 : (BitVec 1))))

/-- Type quantifiers: l : Int, i : Int, k_n : Nat, k_n ≥ 0 -/
def is_zeros_slice (xs : (BitVec k_n)) (i : Int) (l : Int) : Bool :=
  (BEq.beq (xs &&& (slice_mask (n := (Sail.BitVec.length xs)) i l))
    (extzv (m := (Sail.BitVec.length xs)) (0b0 : (BitVec 1))))

/-- Type quantifiers: j : Int, i : Int, k_n : Nat, k_n ≥ 0 -/
def is_ones_subrange (xs : (BitVec k_n)) (i : Int) (j : Int) : Bool :=
  let m : (BitVec k_n) := (slice_mask (n := (Sail.BitVec.length xs)) j ((i -i j) +i 1))
  (BEq.beq (xs &&& m) m)

/-- Type quantifiers: j : Int, i : Int, k_n : Nat, k_n ≥ 0 -/
def is_ones_slice (xs : (BitVec k_n)) (i : Int) (j : Int) : Bool :=
  let m : (BitVec k_n) := (slice_mask (n := (Sail.BitVec.length xs)) i j)
  (BEq.beq (xs &&& m) m)

/-- Type quantifiers: l' : Int, i' : Int, l : Int, i : Int, k_n : Nat, k_m : Nat, r : Nat, k_n ≥ 0
  ∧ k_m ≥ 0 ∧ r ≥ 0 -/
def slice_slice_concat {r : _} (xs : (BitVec k_n)) (i : Int) (l : Int) (ys : (BitVec k_m)) (i' : Int) (l' : Int) : (BitVec r) :=
  let xs := ((xs &&& (slice_mask (n := (Sail.BitVec.length xs)) i l)) >>> i)
  let ys := ((ys &&& (slice_mask (n := (Sail.BitVec.length ys)) i' l')) >>> i')
  (((extzv (m := r) xs) <<< l') ||| (extzv (m := r) ys))

/-- Type quantifiers: i : Int, k_n : Nat, l : Int, l' : Int, k_n ≥ 0 ∧ (l + l') ≥ 0 -/
def slice_zeros_concat (xs : (BitVec k_n)) (i : Int) (l : Int) (l' : Int) : (BitVec (l + l')) :=
  let xs := ((xs &&& (slice_mask (n := (Sail.BitVec.length xs)) i l)) >>> i)
  ((extzv (m := (l +i l')) xs) <<< l')

/-- Type quantifiers: k_n : Nat, hi : Int, lo : Int, l' : Int, k_n ≥ 0 ∧
  (hi - lo + 1 + l') ≥ 0 -/
def subrange_zeros_concat (xs : (BitVec k_n)) (hi : Int) (lo : Int) (l' : Int) : (BitVec (hi - lo + 1 + l')) :=
  (slice_zeros_concat xs lo ((hi -i lo) +i 1) l')

/-- Type quantifiers: j' : Int, i' : Int, j : Int, i : Int, k_n : Nat, k_n ≥ 0 -/
def subrange_subrange_eq (xs : (BitVec k_n)) (i : Int) (j : Int) (ys : (BitVec k_n)) (i' : Int) (j' : Int) : Bool :=
  let xs := ((xs &&& (slice_mask (n := (Sail.BitVec.length ys)) j ((i -i j) +i 1))) >>> j)
  let ys := ((ys &&& (slice_mask (n := (Sail.BitVec.length ys)) j' ((i' -i j') +i 1))) >>> j')
  (BEq.beq xs ys)

/-- Type quantifiers: k_n : Nat, i : Int, j : Int, k_m : Nat, i' : Int, j' : Int, s : Nat, s ≥ 0
  ∧ k_n ≥ 0 ∧ k_m ≥ 0 -/
def subrange_subrange_concat {s : _} (xs : (BitVec k_n)) (i : Int) (j : Int) (ys : (BitVec k_m)) (i' : Int) (j' : Int) : (BitVec s) :=
  let xs := ((xs &&& (slice_mask (n := (Sail.BitVec.length xs)) j ((i -i j) +i 1))) >>> j)
  let ys := ((ys &&& (slice_mask (n := (Sail.BitVec.length ys)) j' ((i' -i j') +i 1))) >>> j')
  (((extzv (m := s) xs) <<< ((i' -i j') +i 1)) ||| (extzv (m := s) ys))

/-- Type quantifiers: shift : Int, j : Int, i : Int, k_n : Nat, m : Nat, k_n ≥ 0 ∧ m ≥ 0 -/
def place_subrange {m : _} (xs : (BitVec k_n)) (i : Int) (j : Int) (shift : Int) : (BitVec m) :=
  let xs := ((xs &&& (slice_mask (n := (Sail.BitVec.length xs)) j ((i -i j) +i 1))) >>> j)
  ((extzv (m := m) xs) <<< shift)

/-- Type quantifiers: shift : Int, l : Int, i : Int, k_n : Nat, m : Nat, k_n ≥ 0 ∧ m ≥ 0 -/
def place_slice {m : _} (xs : (BitVec k_n)) (i : Int) (l : Int) (shift : Int) : (BitVec m) :=
  let xs := ((xs &&& (slice_mask (n := (Sail.BitVec.length xs)) i l)) >>> i)
  ((extzv (m := m) xs) <<< shift)

/-- Type quantifiers: l : Int, i : Int, n : Nat, n ≥ 0 -/
def set_slice_zeros {n : _} (xs : (BitVec n)) (i : Int) (l : Int) : (BitVec n) :=
  let ys : (BitVec n) := (slice_mask (n := n) i l)
  (xs &&& (Complement.complement ys))

/-- Type quantifiers: lo : Int, hi : Int, n : Nat, n ≥ 0 -/
def set_subrange_zeros {n : _} (xs : (BitVec n)) (hi : Int) (lo : Int) : (BitVec n) :=
  (set_slice_zeros (n := n) xs lo ((hi -i lo) +i 1))

/-- Type quantifiers: l : Int, i : Int, k_n : Nat, m : Nat, k_n ≥ 0 ∧ m ≥ 0 -/
def zext_slice {m : _} (xs : (BitVec k_n)) (i : Int) (l : Int) : (BitVec m) :=
  let xs := ((xs &&& (slice_mask (n := (Sail.BitVec.length xs)) i l)) >>> i)
  (extzv (m := m) xs)

/-- Type quantifiers: j : Int, i : Int, k_n : Nat, m : Nat, k_n ≥ 0 ∧ m ≥ 0 -/
def zext_subrange {m : _} (xs : (BitVec k_n)) (i : Int) (j : Int) : (BitVec m) :=
  (zext_slice (m := m) xs j ((i -i j) +i 1))

/-- Type quantifiers: l : Int, i : Int, k_n : Nat, m : Nat, k_n ≥ 0 ∧ m ≥ 0 -/
def sext_slice {m : _} (xs : (BitVec k_n)) (i : Int) (l : Int) : (BitVec m) :=
  let xs :=
    (BitVec.rotateRight
      ((xs &&& (slice_mask (n := (Sail.BitVec.length xs)) i l)) <<< (((Sail.BitVec.length xs) -i i) -i l))
      ((Sail.BitVec.length xs) -i l))
  (extsv (m := m) xs)

/-- Type quantifiers: j : Int, i : Int, k_n : Nat, m : Nat, k_n ≥ 0 ∧ m ≥ 0 -/
def sext_subrange {m : _} (xs : (BitVec k_n)) (i : Int) (j : Int) : (BitVec m) :=
  (sext_slice (m := m) xs j ((i -i j) +i 1))

/-- Type quantifiers: shift : Int, l : Int, i : Int, k_n : Nat, m : Nat, k_n ≥ 0 ∧ m ≥ 0 -/
def place_slice_signed {m : _} (xs : (BitVec k_n)) (i : Int) (l : Int) (shift : Int) : (BitVec m) :=
  ((sext_slice (m := m) xs i l) <<< shift)

/-- Type quantifiers: shift : Int, j : Int, i : Int, k_n : Nat, m : Nat, k_n ≥ 0 ∧ m ≥ 0 -/
def place_subrange_signed {m : _} (xs : (BitVec k_n)) (i : Int) (j : Int) (shift : Int) : (BitVec m) :=
  (place_slice_signed (m := m) xs j ((i -i j) +i 1) shift)

/-- Type quantifiers: i : Int, k_n : Nat, l : Nat, k_n ≥ 0 ∧ l ≥ 0 -/
def unsigned_slice (xs : (BitVec k_n)) (i : Int) (l : Nat) : Int :=
  let xs := ((xs &&& (slice_mask (n := (Sail.BitVec.length xs)) i l)) >>> i)
  (Nat.mod (_builtin_unsigned xs) (pow2 l))

/-- Type quantifiers: k_n : Nat, i : Int, j : Int, k_n ≥ 0 ∧ (i - j) ≥ 0 -/
def unsigned_subrange (xs : (BitVec k_n)) (i : Int) (j : Int) : Int :=
  let xs := ((xs &&& (slice_mask (n := (Sail.BitVec.length xs)) j ((i -i j) +i 1))) >>> i)
  (Nat.mod (_builtin_unsigned xs) (pow2 ((i -i j) +i 1)))

/-- Type quantifiers: m : Int, n : Nat, n ≥ 0 -/
def zext_ones {n : _} (m : Int) : (BitVec n) :=
  let v : (BitVec n) := (extsv (m := n) (0b1 : (BitVec 1)))
  (v >>> (n -i m))

/-- Type quantifiers: n : Nat, s1 : Nat, e1 : Nat, k_n2 : Nat, s2 : Nat, e2 : Nat, 0 ≤ e1 ∧
  e1 ≤ s1 ∧ s1 < n ∧ 0 ≤ e2 ∧ e2 ≤ s2 ∧ s2 < k_n2 ∧ (s1 - e1) = (s2 - e2) -/
def vector_update_subrange_from_subrange {n : _} (v1 : (BitVec n)) (s1 : Nat) (e1 : Nat) (v2 : (BitVec k_n2)) (s2 : Nat) (e2 : Nat) : (BitVec n) :=
  let xs := ((v2 &&& (slice_mask (n := (Sail.BitVec.length v2)) e2 ((s2 -i e2) +i 1))) >>> e2)
  let xs := ((extzv (m := n) xs) <<< e1)
  let ys :=
    (v1 &&& (Complement.complement (slice_mask (n := (Sail.BitVec.length xs)) e1 ((s1 -i e1) +i 1))))
  (xs ||| ys)

/-- Type quantifiers: i : Int, n1 : Nat, s1 : Nat, e1 : Nat, s2 : Nat, e2 : Nat, 0 ≤ e1 ∧
  e1 ≤ s1 ∧ s1 < n1 ∧ 0 ≤ e2 ∧ e2 ≤ s2 ∧ (s1 - e1) = (s2 - e2) -/
def vector_update_subrange_from_integer_subrange {n1 : _} (v1 : (BitVec n1)) (s1 : Nat) (e1 : Nat) (i : Int) (s2 : Nat) (e2 : Nat) : (BitVec n1) :=
  let v2 : (BitVec n1) := (get_slice_int n1 i e2)
  (vector_update_subrange_from_subrange (n := n1) v1 s1 e1 v2 (s2 -i e2) 0)

