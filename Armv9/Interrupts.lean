import Armv9.Stubs

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

def AArch64_PendingUnmaskedVirtualInterrupts (mask_in : (BitVec 3)) : SailM (Bool × Bool × Bool) := do
  let allintmask ← (( do (undefined_bitvector 1) ) : SailM (BitVec 1) )
  let mask : (BitVec 3) := mask_in
  let pending ← (( do (undefined_bitvector 3) ) : SailM (BitVec 3) )
  let (mask, pending) ← (( do
    bif (Bool.and
         (Bool.and
           (Bool.or (BEq.beq (← readReg PSTATE).EL EL0) (BEq.beq (← readReg PSTATE).EL EL1))
           (← (EL2Enabled ())))
         (BEq.beq (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2)) (0b0 : (BitVec 1))))
    then
      (do
        let pending ←
          (pure (((_get_HCR_EL2_Type_VSE (← readReg HCR_EL2)) ++ ((_get_HCR_EL2_Type_VI
                    (← readReg HCR_EL2)) ++ (_get_HCR_EL2_Type_VF (← readReg HCR_EL2)))) &&& ((_get_HCR_EL2_Type_AMO
                  (← readReg HCR_EL2)) ++ ((_get_HCR_EL2_Type_IMO (← readReg HCR_EL2)) ++ (_get_HCR_EL2_Type_FMO
                    (← readReg HCR_EL2))))))
        let mask ← (( do
          bif (Bool.and (← (HaveFeatNMI ()))
               (BEq.beq (_get_SCTLRType_NMI (← (SCTLR_read__1 ()))) (0b1 : (BitVec 1))))
          then
            (do
              let allintmask ← (( do
                (pure ((← readReg PSTATE).ALLINT ||| ((← readReg PSTATE).SP &&& (_get_SCTLRType_SPINTMASK
                        (← (SCTLR_read__1 ())))))) ) : SailM (BitVec 1) )
              let mask ← (( do
                bif (Bool.and (← (IsHCRXEL2Enabled ()))
                     (Bool.or (BEq.beq (← readReg PSTATE).EL EL0)
                       (BEq.beq allintmask (0b0 : (BitVec 1)))))
                then
                  (do
                    let mask ← (( do
                      bif (BEq.beq (_get_HCRX_EL2_Type_VFNMI (← readReg HCRX_EL2))
                           (0b1 : (BitVec 1)))
                      then (pure (BitVec.update mask 0 (Bit (0b0 : (BitVec 1)))))
                      else (pure mask) ) : SailM (BitVec 3) )
                    bif (BEq.beq (_get_HCRX_EL2_Type_VINMI (← readReg HCRX_EL2))
                         (0b1 : (BitVec 1)))
                    then (pure (BitVec.update mask 1 (Bit (0b0 : (BitVec 1)))))
                    else (pure mask))
                else (pure mask) ) : SailM (BitVec 3) )
              bif (Bool.and (BEq.beq (← readReg PSTATE).EL EL1)
                   (BEq.beq allintmask (0b1 : (BitVec 1))))
              then
                (do
                  let mask ← (( do
                    bif (BEq.beq (_get_HCR_EL2_Type_FMO (← readReg HCR_EL2)) (0b1 : (BitVec 1)))
                    then (pure (BitVec.update mask 0 (Bit (0b1 : (BitVec 1)))))
                    else (pure mask) ) : SailM (BitVec 3) )
                  bif (BEq.beq (_get_HCR_EL2_Type_IMO (← readReg HCR_EL2)) (0b1 : (BitVec 1)))
                  then (pure (BitVec.update mask 1 (Bit (0b1 : (BitVec 1)))))
                  else (pure mask))
              else (pure mask))
          else (pure mask) ) : SailM (BitVec 3) )
        (pure (mask, pending)))
    else
      (let pending : (BitVec 3) := (0b000 : (BitVec 3))
      (pure (mask, pending))) ) : SailM ((BitVec 3) × (BitVec 3)) )
  let unmasked_pending : (BitVec 3) := (pending &&& (Complement.complement mask))
  (pure ((BEq.beq (BitVec.join1 [(BitVec.access unmasked_pending 2)]) (0b1 : (BitVec 1))), (BEq.beq
      (BitVec.join1 [(BitVec.access unmasked_pending 1)]) (0b1 : (BitVec 1))), (BEq.beq
      (BitVec.join1 [(BitVec.access unmasked_pending 0)]) (0b1 : (BitVec 1)))))

def AArch32_PendingUnmaskedVirtualInterrupts (_ : Unit) : SailM (Bool × Bool × Bool) := do
  bif (Bool.or (Bool.and (HaveEL EL2) (Bool.not (← (ELUsingAArch32 EL2))))
       (Bool.and (HaveEL EL3) (Bool.not (← (ELUsingAArch32 EL3)))))
  then
    (AArch64_PendingUnmaskedVirtualInterrupts
      ((← readReg PSTATE).A ++ ((← readReg PSTATE).I ++ (← readReg PSTATE).F)))
  else
    (do
      let mask ← (( do
        (pure ((← readReg PSTATE).A ++ ((← readReg PSTATE).I ++ (← readReg PSTATE).F))) ) :
        SailM (BitVec 3) )
      let pending ← (( do (undefined_bitvector 3) ) : SailM (BitVec 3) )
      let pending ← (( do
        bif (Bool.and
             (Bool.and
               (Bool.or (BEq.beq (← readReg PSTATE).EL EL0) (BEq.beq (← readReg PSTATE).EL EL1))
               (← (EL2Enabled ())))
             (BEq.beq (_get_HCR_Type_TGE (← (HCR_read ()))) (0b0 : (BitVec 1))))
        then
          (do
            (pure (((_get_HCR_Type_VA (← (HCR_read ()))) ++ ((_get_HCR_Type_VI (← (HCR_read ()))) ++ (_get_HCR_Type_VF
                      (← (HCR_read ()))))) &&& ((_get_HCR_Type_AMO (← (HCR_read ()))) ++ ((_get_HCR_Type_IMO
                      (← (HCR_read ()))) ++ (_get_HCR_Type_FMO (← (HCR_read ()))))))))
        else (pure (0b000 : (BitVec 3))) ) : SailM (BitVec 3) )
      let unmasked_pending : (BitVec 3) := (pending &&& (Complement.complement mask))
      (pure ((BEq.beq (BitVec.join1 [(BitVec.access unmasked_pending 2)]) (0b1 : (BitVec 1))), (BEq.beq
          (BitVec.join1 [(BitVec.access unmasked_pending 1)]) (0b1 : (BitVec 1))), (BEq.beq
          (BitVec.join1 [(BitVec.access unmasked_pending 0)]) (0b1 : (BitVec 1))))))

def TakePendingInterrupts (interrupt_req : InterruptReq) : SailM Bool := do
  let interrupt_pend ← (( do (undefined_bool ()) ) : SailM Bool )
  let interrupt_taken ← (( do (undefined_bool ()) ) : SailM Bool )
  let vAA ← (( do (undefined_bool ()) ) : SailM Bool )
  let vIRQ ← (( do (undefined_bool ()) ) : SailM Bool )
  let vSE ← (( do (undefined_bool ()) ) : SailM Bool )
  let vFIQ ← (( do (undefined_bool ()) ) : SailM Bool )
  let AA ← (( do (undefined_bool ()) ) : SailM Bool )
  let IRQ ← (( do (undefined_bool ()) ) : SailM Bool )
  let FIQ ← (( do (undefined_bool ()) ) : SailM Bool )
  let SE ← (( do (undefined_bool ()) ) : SailM Bool )
  bif (← (UsingAArch32 ()))
  then
    (do
      let (tup__0, tup__1, tup__2) ← do (AArch32_PendingUnmaskedVirtualInterrupts ())
      let vAA : Bool := tup__0
      let vIRQ : Bool := tup__1
      let vFIQ : Bool := tup__2
      (pure ())
      let (tup__0, tup__1, tup__2) ← do (AArch32_PendingUnmaskedPhysicalInterrupts ())
      let AA : Bool := tup__0
      let IRQ : Bool := tup__1
      let FIQ : Bool := tup__2
      (pure ())
      let AA : Bool :=
        bif (Bool.not interrupt_req.take_SE)
        then false
        else AA
      let vAA : Bool :=
        bif (Bool.not interrupt_req.take_vSE)
        then false
        else vAA
      let IRQ : Bool :=
        bif (Bool.not interrupt_req.take_IRQ)
        then false
        else IRQ
      let vIRQ : Bool :=
        bif (Bool.not interrupt_req.take_vIRQ)
        then false
        else vIRQ
      let FIQ : Bool :=
        bif (Bool.not interrupt_req.take_FIQ)
        then false
        else FIQ
      let vFIQ : Bool :=
        bif (Bool.not interrupt_req.take_vFIQ)
        then false
        else vFIQ
      let interrupt_taken : Bool :=
        bif (Bool.or (Bool.or (Bool.or (Bool.or (Bool.or AA FIQ) IRQ) vAA) vFIQ) vIRQ)
        then true
        else false
      bif vFIQ
      then (AArch32_TakeVirtualFIQException ())
      else
        (do
          bif vIRQ
          then (AArch32_TakeVirtualIRQException ())
          else
            (do
              bif vAA
              then (AArch32_TakeVirtualSErrorException ())
              else
                (do
                  bif FIQ
                  then (AArch32_TakePhysicalFIQException ())
                  else
                    (do
                      bif IRQ
                      then (AArch32_TakePhysicalIRQException ())
                      else
                        (do
                          bif AA
                          then (AArch32_TakePhysicalSErrorException interrupt_req.iesb_req)
                          else (pure ()))))))
      (pure interrupt_taken))
  else
    (do
      let (tup__0, tup__1, tup__2) ← do
        (AArch64_PendingUnmaskedVirtualInterrupts
          ((← readReg PSTATE).A ++ ((← readReg PSTATE).I ++ (← readReg PSTATE).F)))
      let vSE : Bool := tup__0
      let vIRQ : Bool := tup__1
      let vFIQ : Bool := tup__2
      (pure ())
      let (tup__0, tup__1, tup__2) ← do
        (AArch64_PendingUnmaskedPhysicalInterrupts
          ((← readReg PSTATE).A ++ ((← readReg PSTATE).I ++ (← readReg PSTATE).F)))
      let SE : Bool := tup__0
      let IRQ : Bool := tup__1
      let FIQ : Bool := tup__2
      (pure ())
      let SE : Bool :=
        bif (Bool.not interrupt_req.take_SE)
        then false
        else SE
      let vSE : Bool :=
        bif (Bool.not interrupt_req.take_vSE)
        then false
        else vSE
      let IRQ : Bool :=
        bif (Bool.not interrupt_req.take_IRQ)
        then false
        else IRQ
      let vIRQ : Bool :=
        bif (Bool.not interrupt_req.take_vIRQ)
        then false
        else vIRQ
      let FIQ : Bool :=
        bif (Bool.not interrupt_req.take_FIQ)
        then false
        else FIQ
      let vFIQ : Bool :=
        bif (Bool.not interrupt_req.take_vFIQ)
        then false
        else vFIQ
      let (FIQ, IRQ, SE, interrupt_taken, vFIQ, vIRQ, vSE) ← (( do
        bif (Bool.or (Bool.or (Bool.or (Bool.or (Bool.or SE FIQ) IRQ) vSE) vFIQ) vIRQ)
        then
          (do
            let (FIQ, IRQ, SE, vFIQ, vIRQ, vSE) ← (( do
              bif (Bool.and (← (HaveTME ())) ((← readReg TSTATE).depth >b 0))
              then
                (do
                  let (tup__0, tup__1, tup__2) ← do
                    (AArch64_PendingUnmaskedVirtualInterrupts
                      ((← readReg TSTATE).A ++ ((← readReg TSTATE).I ++ (← readReg TSTATE).F)))
                  let vSE : Bool := tup__0
                  let vIRQ : Bool := tup__1
                  let vFIQ : Bool := tup__2
                  (pure ())
                  let (tup__0, tup__1, tup__2) ← do
                    (AArch64_PendingUnmaskedPhysicalInterrupts
                      ((← readReg TSTATE).A ++ ((← readReg TSTATE).I ++ (← readReg TSTATE).F)))
                  let SE : Bool := tup__0
                  let IRQ : Bool := tup__1
                  let FIQ : Bool := tup__2
                  (pure ())
                  let SE : Bool :=
                    bif (Bool.not interrupt_req.take_SE)
                    then false
                    else SE
                  let vSE : Bool :=
                    bif (Bool.not interrupt_req.take_vSE)
                    then false
                    else vSE
                  let IRQ : Bool :=
                    bif (Bool.not interrupt_req.take_IRQ)
                    then false
                    else IRQ
                  let vIRQ : Bool :=
                    bif (Bool.not interrupt_req.take_vIRQ)
                    then false
                    else vIRQ
                  let FIQ : Bool :=
                    bif (Bool.not interrupt_req.take_FIQ)
                    then false
                    else FIQ
                  let vFIQ : Bool :=
                    bif (Bool.not interrupt_req.take_vFIQ)
                    then false
                    else vFIQ
                  let interrupt_pend : Bool :=
                    (Bool.or (Bool.or (Bool.or (Bool.or (Bool.or SE FIQ) IRQ) vSE) vFIQ) vIRQ)
                  (FailTransaction__1 TMFailure_IMP interrupt_pend (Bool.not interrupt_pend)
                    (Zeros (n := 15)))
                  (pure (FIQ, IRQ, SE, vFIQ, vIRQ, vSE)))
              else (pure (FIQ, IRQ, SE, vFIQ, vIRQ, vSE)) ) : SailM
              (Bool × Bool × Bool × Bool × Bool × Bool) )
            let interrupt_taken : Bool := true
            (pure (FIQ, IRQ, SE, interrupt_taken, vFIQ, vIRQ, vSE)))
        else
          (let interrupt_taken : Bool := false
          (pure (FIQ, IRQ, SE, interrupt_taken, vFIQ, vIRQ, vSE))) ) : SailM
        (Bool × Bool × Bool × Bool × Bool × Bool × Bool) )
      bif vFIQ
      then (AArch64_TakeVirtualFIQException ())
      else
        (do
          bif vIRQ
          then (AArch64_TakeVirtualIRQException ())
          else
            (do
              bif vSE
              then (AArch64_TakeVirtualSErrorException ())
              else
                (do
                  bif FIQ
                  then (AArch64_TakePhysicalFIQException ())
                  else
                    (do
                      bif IRQ
                      then (AArch64_TakePhysicalIRQException ())
                      else
                        (do
                          bif SE
                          then (AArch64_TakePhysicalSErrorException interrupt_req.iesb_req)
                          else (pure ()))))))
      (pure interrupt_taken))

def TakeUnmaskedSErrorInterrupts (_ : Unit) : SailM Unit := do
  let interrupt_req ← (( do (undefined_InterruptReq ()) ) : SailM InterruptReq )
  let interrupt_req : InterruptReq := { interrupt_req with take_SE := false }
  let interrupt_req : InterruptReq := { interrupt_req with take_vSE := false }
  let interrupt_req : InterruptReq := { interrupt_req with take_FIQ := false }
  let interrupt_req : InterruptReq := { interrupt_req with take_vFIQ := false }
  let interrupt_req : InterruptReq := { interrupt_req with take_IRQ := false }
  let interrupt_req : InterruptReq := { interrupt_req with take_vIRQ := false }
  let interrupt_req : InterruptReq := { interrupt_req with iesb_req := false }
  let interrupt_req : InterruptReq := { interrupt_req with take_SE := true }
  let interrupt_req : InterruptReq := { interrupt_req with take_vSE := true }
  let interrupt_taken ← (( do (TakePendingInterrupts interrupt_req) ) : SailM Bool )
  (pure ())

