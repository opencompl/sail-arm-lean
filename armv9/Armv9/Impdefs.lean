import Armv9.Devices

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

def HaveFP16Ext (_ : Unit) : Bool :=
  true

def ExclusiveMonitorsStatus (_ : Unit) : (BitVec 1) :=
  (0b0 : (BitVec 1))

/-- Type quantifiers: Rt : Int, k_acq_rel : Bool, k_sign_extend : Bool, k_sixty_four : Bool, size :
  Int -/
def AArch64_SetLSInstructionSyndrome (size : Int) (sign_extend : Bool) (Rt : Int) (sixty_four : Bool) (acq_rel : Bool) : Unit :=
  ()

def DataMemoryBarrier (domain : MBReqDomain) (types : MBReqTypes) : SailM Unit := do
  (sail_barrier
    (Barrier_DMB
      { domain := domain
        types := types
        nXS := false }))

/-- Type quantifiers: k_nXS : Bool -/
def DataSynchronizationBarrier (domain : MBReqDomain) (types : MBReqTypes) (nXS : Bool) : SailM Unit := do
  (sail_barrier
    (Barrier_DSB
      { domain := domain
        types := types
        nXS := nXS }))

def InstructionSynchronizationBarrier (_ : Unit) : SailM Unit := do
  (sail_barrier (Barrier_ISB ()))

def SpeculationBarrier (_ : Unit) : SailM Unit := do
  (sail_barrier (Barrier_SB ()))

