import Armv9.V8Base

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

/-- Type quantifiers: Rt : Int, k_acq_rel : Bool, k_sign_extend : Bool, size : Int -/
def AArch32_SetLSInstructionSyndrome (size : Int) (sign_extend : Bool) (Rt : Int) (acq_rel : Bool) : Unit :=
  ()

/-- Type quantifiers: crm : Int, crn : Int, op0 : Int, op1 : Int, op2 : Int -/
def AArch64_CheckNVCondsIfCurrentEL (op0 : Int) (op1 : Int) (crn : Int) (crm : Int) (op2 : Int) : SailM Bool := do
  let is_reg_current_el : Bool :=
    (Bool.and
      (Bool.and (Bool.and (Bool.and (BEq.beq op0 3) (BEq.beq op1 0)) (BEq.beq crn 4))
        (BEq.beq crm 2)) (BEq.beq op2 2))
  let have_nv_trap_conds ← (( do
    (pure (Bool.and
        (Bool.and (Bool.and (← (HaveNVExt ())) (BEq.beq (← readReg PSTATE).EL EL1))
          (← (EL2Enabled ())))
        (BEq.beq (BitVec.slice (← readReg HCR_EL2) 42 1) (0b1 : (BitVec 1))))) ) : SailM Bool )
  (pure (Bool.and is_reg_current_el have_nv_trap_conds))

def BPIALL (_ : Unit) : Unit :=
  ()

def BPIALLIS (_ : Unit) : Unit :=
  ()

def BPIMVA (val_name : (BitVec 32)) : Unit :=
  ()

def CP15DMB (_ : Unit) : Unit :=
  ()

def CP15DSB (_ : Unit) : Unit :=
  ()

def CP15ISB (_ : Unit) : Unit :=
  ()

def CPYPostSizeChoice (toaddress : (BitVec 64)) (fromaddress : (BitVec 64)) (cpysize : (BitVec 64)) : SailM (BitVec 64) := do
  (__UNKNOWN_bits 64)

def CPYPreSizeChoice (toaddress : (BitVec 64)) (fromaddress : (BitVec 64)) (cpysize : (BitVec 64)) : SailM (BitVec 64) := do
  (__UNKNOWN_bits 64)

def CPYSizeChoice (toaddress : (BitVec 64)) (fromaddress : (BitVec 64)) (cpysize : (BitVec 64)) : SailM Int := do
  (__UNKNOWN_integer ())

def ChooseRandomNonExcludedTag (exclude_in : (BitVec 16)) : SailM (BitVec 4) := do
  (__UNKNOWN_bits 4)

def CommitTransactionalWrites (_ : Unit) : Unit :=
  ()

def ConstrainUnpredictableProcedure (which : Unpredictable) : Unit :=
  ()

def ConsumptionOfSpeculativeDataBarrier (_ : Unit) : Unit :=
  ()

def DC_CIGDPAPA (val_name : (BitVec 64)) : Unit :=
  ()

def DC_CIPAPA (val_name : (BitVec 64)) : Unit :=
  ()

def GPTTLBCache (pgs : PGSe) (gpt_entry : GPTEntry) : Unit :=
  ()

def GPTTLBLookup (pa : (BitVec 56)) (pgs : PGSe) : SailM GPTTLBLine := do
  (__UNKNOWN_GPTTLBLine ())

def Hint_CLRBHB (_ : Unit) : Unit :=
  ()

def Hint_DGH (_ : Unit) : Unit :=
  ()

def Hint_PreloadData (address : (BitVec 32)) : Unit :=
  ()

def Hint_PreloadDataForWrite (address : (BitVec 32)) : Unit :=
  ()

def Hint_PreloadInstr (address : (BitVec 32)) : Unit :=
  ()

/-- Type quantifiers: count : Int, length : Int, reuse : Int, stride : Int -/
def Hint_RangePrefetch (address : (BitVec 64)) (length : Int) (stride : Int) (count : Int) (reuse : Int) (operation : (BitVec 6)) : Unit :=
  ()

def Hint_Yield (_ : Unit) : Unit :=
  ()

def MemCpyDirectionChoice (fromaddress : (BitVec 64)) (toaddress : (BitVec 64)) (cpysize : (BitVec 64)) : SailM Bool := do
  (__UNKNOWN_boolean ())

def MemCpyParametersIllformedE (toaddress : (BitVec 64)) (fromaddress : (BitVec 64)) (cpysize : (BitVec 64)) : SailM Bool := do
  (__UNKNOWN_boolean ())

def MemCpyParametersIllformedM (toaddress : (BitVec 64)) (fromaddress : (BitVec 64)) (cpysize : (BitVec 64)) : SailM Bool := do
  (__UNKNOWN_boolean ())

def MemCpyZeroSizeCheck (_ : Unit) : SailM Bool := do
  (__UNKNOWN_boolean ())

/-- Type quantifiers: k_IsSETGE : Bool -/
def MemSetParametersIllformedE (toaddress : (BitVec 64)) (setsize : (BitVec 64)) (IsSETGE : Bool) : SailM Bool := do
  (__UNKNOWN_boolean ())

/-- Type quantifiers: k_IsSETGM : Bool -/
def MemSetParametersIllformedM (toaddress : (BitVec 64)) (setsize : (BitVec 64)) (IsSETGM : Bool) : SailM Bool := do
  (__UNKNOWN_boolean ())

def MemSetZeroSizeCheck (_ : Unit) : SailM Bool := do
  (__UNKNOWN_boolean ())

def ProfilingSynchronizationBarrier (_ : Unit) : Unit :=
  ()

/-- Type quantifiers: k_IsSETGE : Bool -/
def SETPostSizeChoice (toaddress : (BitVec 64)) (setsize : (BitVec 64)) (IsSETGE : Bool) : SailM (BitVec 64) := do
  (__UNKNOWN_bits 64)

/-- Type quantifiers: k_IsSETGP : Bool -/
def SETPreSizeChoice (toaddress : (BitVec 64)) (setsize : (BitVec 64)) (IsSETGP : Bool) : SailM (BitVec 64) := do
  (__UNKNOWN_bits 64)

/-- Type quantifiers: AlignSize : Int -/
def SETSizeChoice (toaddress : (BitVec 64)) (setsize : (BitVec 64)) (AlignSize : Int) : SailM Int := do
  (__UNKNOWN_integer ())

def SendEvent (_ : Unit) : Unit :=
  ()

def SetIss2 (rs : (BitVec 5)) : Unit :=
  ()

def SetLoadStoreType (instr : (BitVec 2)) : Unit :=
  ()

def SpeculativeStoreBypassBarrierToPA (_ : Unit) : Unit :=
  ()

def SpeculativeStoreBypassBarrierToVA (_ : Unit) : Unit :=
  ()

def StartTrackingTransactionalReadsWrites (_ : Unit) : Unit :=
  ()

