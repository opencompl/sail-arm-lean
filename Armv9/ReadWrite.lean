import Armv9.Common

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

def undefined_Access_variety (_ : Unit) : SailM Access_variety := do
  (internal_pick [AV_plain, AV_exclusive, AV_atomic_rmw])

/-- Type quantifiers: arg_ : Nat, 0 ≤ arg_ ∧ arg_ ≤ 2 -/
def Access_variety_of_num (arg_ : Nat) : Access_variety :=
  match arg_ with
  | 0 => AV_plain
  | 1 => AV_exclusive
  | _ => AV_atomic_rmw

def num_of_Access_variety (arg_ : Access_variety) : Int :=
  match arg_ with
  | AV_plain => 0
  | AV_exclusive => 1
  | AV_atomic_rmw => 2

def undefined_Access_strength (_ : Unit) : SailM Access_strength := do
  (internal_pick [AS_normal, AS_rel_or_acq, AS_acq_rcpc])

/-- Type quantifiers: arg_ : Nat, 0 ≤ arg_ ∧ arg_ ≤ 2 -/
def Access_strength_of_num (arg_ : Nat) : Access_strength :=
  match arg_ with
  | 0 => AS_normal
  | 1 => AS_rel_or_acq
  | _ => AS_acq_rcpc

def num_of_Access_strength (arg_ : Access_strength) : Int :=
  match arg_ with
  | AS_normal => 0
  | AS_rel_or_acq => 1
  | AS_acq_rcpc => 2

def undefined_Explicit_access_kind (_ : Unit) : SailM Explicit_access_kind := do
  (pure { variety := (← (undefined_Access_variety ()))
          strength := (← (undefined_Access_strength ())) })

/-- Type quantifiers: k_n : Nat, k_vasize : Nat, k_pa : Type, k_translation_summary : Type, k_arch_ak
  : Type, k_n > 0 ∧ k_vasize > 0 -/
def mem_read_request_is_exclusive (request : (Mem_read_request k_n k_vasize k_pa k_translation_summary k_arch_ak)) : Bool :=
  match request.access_kind with
  | .AK_explicit eak =>
    (match eak.variety with
    | AV_exclusive => true
    | _ => false)
  | _ => false

/-- Type quantifiers: k_n : Nat, k_vasize : Nat, k_pa : Type, k_translation_summary : Type, k_arch_ak
  : Type, k_n > 0 ∧ k_vasize > 0 -/
def mem_read_request_is_ifetch (request : (Mem_read_request k_n k_vasize k_pa k_translation_summary k_arch_ak)) : Bool :=
  match request.access_kind with
  | .AK_ifetch () => true
  | _ => false

def __monomorphize_reads : Bool := false

def __monomorphize_writes : Bool := false

/-- Type quantifiers: k_n : Nat, k_vasize : Nat, k_pa : Type, k_translation_summary : Type, k_arch_ak
  : Type, k_n > 0 ∧ k_vasize > 0 -/
def mem_write_request_is_exclusive (request : (Mem_write_request k_n k_vasize k_pa k_translation_summary k_arch_ak)) : Bool :=
  match request.access_kind with
  | .AK_explicit eak =>
    (match eak.variety with
    | AV_exclusive => true
    | _ => false)
  | _ => false

/-- Type quantifiers: x_0 : Nat, x_0 ∈ {32, 64} -/
def sail_address_announce (x_0 : Nat) (x_1 : (BitVec x_0)) : Unit :=
  ()

