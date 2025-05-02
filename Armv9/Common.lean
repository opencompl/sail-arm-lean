import Armv9.Result

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

/-- Type quantifiers: k_n : Nat, k_n > 0 -/
def sail_instr_announce (x_0 : (BitVec k_n)) : Unit :=
  ()

/-- Type quantifiers: x_0 : Nat, x_0 ∈ {32, 64} -/
def sail_branch_announce (x_0 : Nat) (x_1 : (BitVec x_0)) : Unit :=
  ()

def sail_reset_registers (_ : Unit) : Unit :=
  ()

def sail_synchronize_registers (_ : Unit) : Unit :=
  ()

/-- Type quantifiers: k_a : Type -/
def sail_mark_register (x_0 : (RegisterRef k_a)) (x_1 : String) : Unit :=
  ()

/-- Type quantifiers: k_a : Type, k_b : Type -/
def sail_mark_register_pair (x_0 : (RegisterRef k_a)) (x_1 : (RegisterRef k_b)) (x_2 : String) : Unit :=
  ()

/-- Type quantifiers: k_a : Type -/
def sail_ignore_write_to (reg : (RegisterRef k_a)) : Unit :=
  (sail_mark_register reg "ignore_write")

/-- Type quantifiers: k_a : Type -/
def sail_pick_dependency (reg : (RegisterRef k_a)) : Unit :=
  (sail_mark_register reg "pick")

/-- Type quantifiers: k_n : Nat, k_n ≥ 0 -/
def __monomorphize (bv : (BitVec k_n)) : (BitVec k_n) :=
  bv

