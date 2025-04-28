import Armv9.SysregsAutogen

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

def getISR (_ : Unit) : SailM (BitVec 32) := do
  let fiq_nmi ← (( do (undefined_bool ()) ) : SailM Bool )
  let fiq_pending ← (( do (undefined_bool ()) ) : SailM Bool )
  let irq_nmi ← (( do (undefined_bool ()) ) : SailM Bool )
  let irq_pending ← (( do (undefined_bool ()) ) : SailM Bool )
  let value_name : (BitVec 32) := (Zeros (n := 32))
  let value_name : (BitVec 32) :=
    (BitVec.update value_name 8
      (Bit
        (bif (IsPhysicalSErrorPending ())
        then (0b1 : (BitVec 1))
        else (0b0 : (BitVec 1)))))
  let (tup__0, tup__1) ← do (IRQPending ())
  let irq_pending : Bool := tup__0
  let irq_nmi : Bool := tup__1
  (pure ())
  let _ : Unit :=
    let (tup__0, tup__1) := ((FIQPending ()) : (Bool × Bool))
    let fiq_pending : Bool := tup__0
    let fiq_nmi : Bool := tup__1
    ()
  let value_name ← (( do
    bif (Bool.and (← (HaveFeatNMI ())) (Bool.not (← (UsingAArch32 ()))))
    then
      (let value_name : (BitVec 32) :=
        (BitVec.update value_name 10
          (Bit
            (bif (Bool.and irq_pending irq_nmi)
            then (0b1 : (BitVec 1))
            else (0b0 : (BitVec 1)))))
      (pure (BitVec.update value_name 9
          (Bit
            (bif (Bool.and fiq_pending fiq_nmi)
            then (0b1 : (BitVec 1))
            else (0b0 : (BitVec 1)))))))
    else (pure value_name) ) : SailM (BitVec 32) )
  let value_name : (BitVec 32) :=
    (BitVec.update value_name 7
      (Bit
        (bif irq_pending
        then (0b1 : (BitVec 1))
        else (0b0 : (BitVec 1)))))
  let value_name : (BitVec 32) :=
    (BitVec.update value_name 6
      (Bit
        (bif fiq_pending
        then (0b1 : (BitVec 1))
        else (0b0 : (BitVec 1)))))
  bif (Bool.and (Bool.and (BEq.beq (← readReg PSTATE).EL EL1) (← (EL2Enabled ())))
       (BEq.beq (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2)) (0b0 : (BitVec 1))))
  then
    (do
      let value_name ← (( do
        bif (Bool.and (Bool.and (← (HaveFeatNMI ())) (Bool.not (← (UsingAArch32 ()))))
             (← (IsHCRXEL2Enabled ())))
        then
          (do
            let value_name ← (( do
              bif (BEq.beq
                   ((_get_HCR_EL2_Type_IMO (← readReg HCR_EL2)) &&& (_get_HCR_EL2_Type_VI
                       (← readReg HCR_EL2))) (0b1 : (BitVec 1)))
              then
                (do
                  (pure (BitVec.update value_name 10
                      (Bit (_get_HCRX_EL2_Type_VINMI (← readReg HCRX_EL2))))))
              else (pure value_name) ) : SailM (BitVec 32) )
            bif (BEq.beq
                 ((_get_HCR_EL2_Type_FMO (← readReg HCR_EL2)) &&& (_get_HCR_EL2_Type_VF
                     (← readReg HCR_EL2))) (0b1 : (BitVec 1)))
            then
              (do
                (pure (BitVec.update value_name 9
                    (Bit (_get_HCRX_EL2_Type_VFNMI (← readReg HCRX_EL2))))))
            else (pure value_name))
        else (pure value_name) ) : SailM (BitVec 32) )
      let value_name ← (( do
        bif (BEq.beq (_get_HCR_EL2_Type_AMO (← readReg HCR_EL2)) (0b1 : (BitVec 1)))
        then
          (do
            (pure (BitVec.update value_name 8
                (Bit
                  ((BitVec.join1 [(BitVec.access value_name 8)]) ||| (_get_HCR_EL2_Type_VSE
                      (← readReg HCR_EL2)))))))
        else (pure value_name) ) : SailM (BitVec 32) )
      let value_name ← (( do
        bif (BEq.beq (_get_HCR_EL2_Type_IMO (← readReg HCR_EL2)) (0b1 : (BitVec 1)))
        then
          (do
            (pure (BitVec.update value_name 7 (Bit (_get_HCR_EL2_Type_VI (← readReg HCR_EL2))))))
        else (pure value_name) ) : SailM (BitVec 32) )
      bif (BEq.beq (_get_HCR_EL2_Type_FMO (← readReg HCR_EL2)) (0b1 : (BitVec 1)))
      then
        (do
          (pure (BitVec.update value_name 6 (Bit (_get_HCR_EL2_Type_VF (← readReg HCR_EL2))))))
      else (pure value_name))
  else (pure value_name)

/-- Type quantifiers: k_isRNDRRS : Bool -/
def genRandomNum (isRNDRRS : Bool) : SailM (BitVec 64) := do
  let split_vec := (0x0 : (BitVec 4))
  writeReg PSTATE { (← readReg PSTATE) with N := (Sail.BitVec.extractLsb split_vec 3 3) }
  writeReg PSTATE { (← readReg PSTATE) with Z := (Sail.BitVec.extractLsb split_vec 2 2) }
  writeReg PSTATE { (← readReg PSTATE) with C := (Sail.BitVec.extractLsb split_vec 1 1) }
  writeReg PSTATE { (← readReg PSTATE) with V := (Sail.BitVec.extractLsb split_vec 0 0) }
  let x ← (( do (pure (integer_subrange (← readReg __cycle_count) 127 0)) ) : SailM (BitVec 128)
    )
  let y ← (( do (pure (integer_subrange ((← readReg __cycle_count) +i 1) 127 0)) ) : SailM
    (BitVec 128) )
  let w ← (( do (pure (integer_subrange ((← readReg __cycle_count) +i 2) 127 0)) ) : SailM
    (BitVec 128) )
  (pure (Sail.BitVec.extractLsb (← (SHA256hash x y w true)) 63 0))

/-- Type quantifiers: k_data_cache : Bool, level : Int -/
def getCacheID (level : Int) (data_cache : Bool) : SailM (BitVec 64) := do
  let range_min := (level *i 3)
  let cache_type ← (( do (pure (BitVec.slice (← readReg CLIDR_EL1) range_min 3)) ) : SailM
    (BitVec 3) )
  let ccsidr_val ← (( do (undefined_bitvector 64) ) : SailM (BitVec 64) )
  let b__0 := cache_type
  bif (BEq.beq b__0 (0b000 : (BitVec 3)))
  then
    (do
      let ccsidr_val ← (__UNKNOWN_bits 64)
      (pure ()))
  else
    (do
      bif (BEq.beq b__0 (0b001 : (BitVec 3)))
      then
        (do
          let ccsidr_val ←
            bif data_cache
            then (__UNKNOWN_bits 64)
            else
              (do
                assert (Bool.and (0 ≤b level) (level <b 7)) "src/sysregs.sail:222.59-222.60"
                (pure (GetElem?.getElem! (← readReg __ICACHE_CCSIDR_RESET) level)))
          (pure ()))
      else
        (do
          bif (BEq.beq b__0 (0b010 : (BitVec 3)))
          then
            (do
              let ccsidr_val ←
                bif (Bool.not data_cache)
                then (__UNKNOWN_bits 64)
                else
                  (do
                    assert (Bool.and (0 ≤b level) (level <b 7)) "src/sysregs.sail:228.59-228.60"
                    (pure (GetElem?.getElem! (← readReg __DCACHE_CCSIDR_RESET) level)))
              (pure ()))
          else
            (do
              bif (BEq.beq b__0 (0b011 : (BitVec 3)))
              then
                (do
                  let ccsidr_val ←
                    bif data_cache
                    then
                      (do
                        assert (Bool.and (0 ≤b level) (level <b 7)) "src/sysregs.sail:234.59-234.60"
                        (pure (GetElem?.getElem! (← readReg __DCACHE_CCSIDR_RESET) level)))
                    else
                      (do
                        assert (Bool.and (0 ≤b level) (level <b 7)) "src/sysregs.sail:237.59-237.60"
                        (pure (GetElem?.getElem! (← readReg __ICACHE_CCSIDR_RESET) level)))
                  (pure ()))
              else
                (do
                  bif (BEq.beq b__0 (0b100 : (BitVec 3)))
                  then
                    (do
                      assert (Bool.and (0 ≤b level) (level <b 7)) "src/sysregs.sail:242.55-242.56"
                      let ccsidr_val ←
                        (pure (GetElem?.getElem! (← readReg __DCACHE_CCSIDR_RESET) level))
                      (pure ()))
                  else (pure ())))))
  (pure ccsidr_val)

def CacheConfigRead (cache_sel : (BitVec 4)) : SailM (BitVec 64) := do
  let data_cache : Bool :=
    bif (BEq.beq (BitVec.join1 [(BitVec.access cache_sel 0)]) (0b0 : (BitVec 1)))
    then true
    else false
  let level := (BitVec.toNat (Sail.BitVec.extractLsb cache_sel 3 1))
  assert (level <b 7) "src/sysregs.sail:253.20-253.21"
  (getCacheID level data_cache)

/-- Type quantifiers: crm : Int, crn : Int, op0 : Int, op1 : Int, op2 : Int, t : Int -/
def AArch64_SysRegRead (op0 : Int) (op1 : Int) (crn : Int) (crm : Int) (op2 : Int) (t : Int) : SailM Unit := SailME.run do
  let index ← (( do (undefined_int ()) ) : SailME _ Int )
  let n ← (( do (undefined_int ()) ) : SailME _ Int )
  bif (Bool.and (Bool.and (BEq.beq op0 3) (BEq.beq op1 3)) (BEq.beq crn 13))
  then
    (do
      let n :=
        (BitVec.toNat ((BitVec.join1 [(integer_access crm 0)]) ++ (integer_subrange op2 2 0)))
      bif (Bool.or (BEq.beq (integer_subrange crm 3 1) (0b010 : (BitVec 3)))
           (BEq.beq (integer_subrange crm 3 1) (0b011 : (BitVec 3))))
      then
        (do
          bif (n ≥b (BitVec.toNat (_get_AMCGCR_EL0_Type_CG0NC (← readReg AMCGCR_EL0))))
          then sailThrow ((Error_Undefined ()))
          else (pure ()))
      else
        (do
          bif (Bool.or (BEq.beq (integer_subrange crm 3 1) (0b110 : (BitVec 3)))
               (BEq.beq (integer_subrange crm 3 1) (0b111 : (BitVec 3))))
          then
            (do
              bif (n ≥b (BitVec.toNat (_get_AMCGCR_EL0_Type_CG1NC (← readReg AMCGCR_EL0))))
              then sailThrow ((Error_Undefined ()))
              else (pure ()))
          else (pure ())))
  else (pure ())
  bif (Bool.and
       (Bool.and (Bool.and (Bool.and (BEq.beq op0 3) (BEq.beq op1 3)) (BEq.beq crn 14))
         (Bool.or (BEq.beq (integer_subrange crm 3 2) (0b10 : (BitVec 2)))
           (BEq.beq (integer_subrange crm 3 2) (0b11 : (BitVec 2)))))
       (bne ((integer_subrange crm 1 0) ++ (integer_subrange op2 2 0)) (0b11111 : (BitVec 5))))
  then
    (do
      bif (Bool.or
           ((BitVec.toNat ((integer_subrange crm 1 0) ++ (integer_subrange op2 2 0))) >b ((← (GetNumEventCounters
                   ())) -i 1))
           (Bool.and
             (Bool.and (← (EL2Enabled ()))
               (Bool.or (BEq.beq (← readReg PSTATE).EL EL1)
                 (Bool.and (BEq.beq (← readReg PSTATE).EL EL0)
                   (Bool.or
                     (Bool.and (BEq.beq (integer_subrange crm 3 2) (0b10 : (BitVec 2)))
                       (bne
                         ((_get_PMUSERENR_EL0_Type_ER (← readReg PMUSERENR_EL0)) ++ (_get_PMUSERENR_EL0_Type_EN
                             (← readReg PMUSERENR_EL0))) (0b00 : (BitVec 2))))
                     (Bool.and (BEq.beq (integer_subrange crm 3 2) (0b11 : (BitVec 2)))
                       (BEq.beq (_get_PMUSERENR_EL0_Type_EN (← readReg PMUSERENR_EL0))
                         (0b1 : (BitVec 1))))))))
             (← do
               (pure ((BitVec.toNat ((integer_subrange crm 1 0) ++ (integer_subrange op2 2 0))) >b ((← (AArch64_GetNumEventCountersAccessible
                         ())) -i 1))))))
      then
        (do
          bif ((BitVec.toNat ((integer_subrange crm 1 0) ++ (integer_subrange op2 2 0))) >b ((← (GetNumEventCounters
                     ())) -i 1))
          then sailThrow ((Error_Undefined ()))
          else (AArch64_SystemAccessTrap EL2 (BitVec.toNat (0x18 : (BitVec 8)))))
      else (pure ()))
  else (pure ())
  bif (Bool.and
       (Bool.and
         (Bool.and (Bool.and (Bool.and (BEq.beq op0 3) (BEq.beq op1 3)) (BEq.beq crn 9))
           (BEq.beq crm 13)) (Bool.or (BEq.beq op2 1) (BEq.beq op2 2)))
       (bne (_get_PMSELR_EL0_Type_SEL (← readReg PMSELR_EL0)) (0b11111 : (BitVec 5))))
  then
    (do
      bif (Bool.or
           ((BitVec.toNat (_get_PMSELR_EL0_Type_SEL (← readReg PMSELR_EL0))) >b ((← (GetNumEventCounters
                   ())) -i 1))
           (Bool.and
             (Bool.and (← (EL2Enabled ()))
               (Bool.or (BEq.beq (← readReg PSTATE).EL EL1)
                 (Bool.and (BEq.beq (← readReg PSTATE).EL EL0)
                   (Bool.or
                     (Bool.and (BEq.beq op2 2)
                       (bne
                         ((_get_PMUSERENR_EL0_Type_ER (← readReg PMUSERENR_EL0)) ++ (_get_PMUSERENR_EL0_Type_EN
                             (← readReg PMUSERENR_EL0))) (0b00 : (BitVec 2))))
                     (Bool.and (BEq.beq op2 1)
                       (BEq.beq (_get_PMUSERENR_EL0_Type_EN (← readReg PMUSERENR_EL0))
                         (0b1 : (BitVec 1))))))))
             (← do
               (pure ((BitVec.toNat (_get_PMSELR_EL0_Type_SEL (← readReg PMSELR_EL0))) >b ((← (AArch64_GetNumEventCountersAccessible
                         ())) -i 1))))))
      then
        (do
          bif ((BitVec.toNat (_get_PMSELR_EL0_Type_SEL (← readReg PMSELR_EL0))) >b ((← (GetNumEventCounters
                     ())) -i 1))
          then sailThrow ((Error_Undefined ()))
          else (AArch64_SystemAccessTrap EL2 (BitVec.toNat (0x18 : (BitVec 8)))))
      else (pure ()))
  else (pure ())
  let temp ← (( do (X_read t 64) ) : SailME _ (BitVec 64) )
  (AArch64_AutoGen_SysRegRead (← readReg PSTATE).EL (integer_subrange op0 1 0)
    (integer_subrange op1 2 0) (integer_subrange crn 3 0) (integer_subrange op2 2 0)
    (integer_subrange crm 3 0) t)
  bif (Bool.and
       (Bool.and (Bool.and (Bool.and (BEq.beq op0 3) (BEq.beq crn 10)) (BEq.beq crm 5))
         (BEq.beq op2 0)) (Bool.or (BEq.beq op1 0) (BEq.beq op1 5)))
  then
    (do
      bif (Bool.and (← (HaveRME ()))
           (BEq.beq (_get_MPAMIDR_EL1_Type_HAS_ALTSP (← readReg MPAMIDR_EL1)) (0b1 : (BitVec 1))))
      then
        (X_set t 64
          (Sail.BitVec.updateSubrange (← (X_read t 64)) 54 54
            (← do
              bif (Bool.not (← (UsePrimarySpaceEL10 ())))
              then (pure (0b1 : (BitVec 1)))
              else (pure (0b0 : (BitVec 1))))))
      else (pure ()))
  else (pure ())
  bif (Bool.and
       (Bool.and (Bool.and (Bool.and (BEq.beq op0 3) (BEq.beq crn 10)) (BEq.beq crm 5))
         (BEq.beq op2 0)) (BEq.beq op1 4))
  then
    (do
      bif (Bool.and (← (HaveRME ()))
           (BEq.beq (_get_MPAMIDR_EL1_Type_HAS_ALTSP (← readReg MPAMIDR_EL1)) (0b1 : (BitVec 1))))
      then
        (X_set t 64
          (Sail.BitVec.updateSubrange (← (X_read t 64)) 54 54
            (← do
              bif (Bool.not (← (UsePrimarySpaceEL2 ())))
              then (pure (0b1 : (BitVec 1)))
              else (pure (0b0 : (BitVec 1))))))
      else (pure ()))
  else (pure ())
  bif (Bool.and
       (Bool.and (Bool.and (Bool.and (BEq.beq op0 3) (BEq.beq crn 9)) (BEq.beq op1 0))
         (BEq.beq op2 7)) (BEq.beq crm 10))
  then
    (X_set t 64 (Sail.BitVec.updateSubrange (← (X_read t 64)) 4 4 (← (SPE_PMBIDR_P_Read ()))))
  else (pure ())
  bif (Bool.and (Bool.and (BEq.beq op0 3) (BEq.beq crn 9))
       (Bool.or
         (Bool.or
           (Bool.and (Bool.and (BEq.beq op1 3) (BEq.beq op2 3))
             (Bool.or (BEq.beq crm 12) (BEq.beq crm 14)))
           (Bool.and (Bool.and (BEq.beq op1 3) (Bool.or (BEq.beq op2 1) (BEq.beq op2 2)))
             (BEq.beq crm 12)))
         (Bool.and (Bool.and (BEq.beq op1 0) (Bool.or (BEq.beq op2 1) (BEq.beq op2 2)))
           (BEq.beq crm 14))))
  then
    (do
      let mask ← (( do (PMUCounterMask ()) ) : SailME _ (BitVec 64) )
      (X_set t 64 ((← (X_read t 64)) &&& mask)))
  else (pure ())
  bif (Bool.and
       (Bool.and (Bool.and (Bool.and (BEq.beq op0 3) (BEq.beq op1 3)) (BEq.beq crn 9))
         (BEq.beq crm 13)) (Bool.or (BEq.beq op2 1) (BEq.beq op2 2)))
  then
    (do
      bif (BEq.beq op2 1)
      then
        (do
          bif (Bool.and
               (Bool.and
                 (Bool.and (← (EL2Enabled ()))
                   (Bool.or (BEq.beq (← readReg PSTATE).EL EL0)
                     (BEq.beq (← readReg PSTATE).EL EL1)))
                 (bne (_get_PMSELR_EL0_Type_SEL (← readReg PMSELR_EL0)) (0b11111 : (BitVec 5))))
               (← do
                 (pure ((BitVec.toNat (_get_PMSELR_EL0_Type_SEL (← readReg PMSELR_EL0))) >b ((← (AArch64_GetNumEventCountersAccessible
                           ())) -i 1)))))
          then
            (do
              bif ((BitVec.toNat (_get_PMSELR_EL0_Type_SEL (← readReg PMSELR_EL0))) >b ((← (GetNumEventCounters
                         ())) -i 1))
              then
                (do
                  (X_set t 64 temp)
                  sailThrow ((Error_Undefined ())))
              else
                (do
                  (X_set t 64 temp)
                  (AArch64_SystemAccessTrap EL2 (BitVec.toNat (0x18 : (BitVec 8))))))
          else
            (do
              bif (BEq.beq (_get_PMSELR_EL0_Type_SEL (← readReg PMSELR_EL0))
                   (0b11111 : (BitVec 5)))
              then (X_set t 64 (← readReg PMCCFILTR_EL0))
              else
                (do
                  let pmselr_el0 ← do
                    (pure (BitVec.toNat (_get_PMSELR_EL0_Type_SEL (← readReg PMSELR_EL0))))
                  assert (pmselr_el0 <b 31) "src/sysregs.sail:335.38-335.39"
                  (X_set t 64 (GetElem?.getElem! (← readReg PMEVTYPER_EL0) pmselr_el0)))))
      else (pure ())
      bif (BEq.beq op2 2)
      then
        (do
          bif (Bool.or
               (Bool.and
                 ((BitVec.toNat (_get_PMSELR_EL0_Type_SEL (← readReg PMSELR_EL0))) >b ((← (GetNumEventCounters
                         ())) -i 1))
                 (bne (_get_PMSELR_EL0_Type_SEL (← readReg PMSELR_EL0)) (0b11111 : (BitVec 5))))
               (Bool.and
                 (Bool.and (← (EL2Enabled ()))
                   (Bool.or (BEq.beq (← readReg PSTATE).EL EL0)
                     (BEq.beq (← readReg PSTATE).EL EL1)))
                 (← do
                   (pure ((BitVec.toNat (_get_PMSELR_EL0_Type_SEL (← readReg PMSELR_EL0))) >b ((← (AArch64_GetNumEventCountersAccessible
                             ())) -i 1))))))
          then
            (do
              bif ((BitVec.toNat (_get_PMSELR_EL0_Type_SEL (← readReg PMSELR_EL0))) >b ((← (GetNumEventCounters
                         ())) -i 1))
              then
                (do
                  (X_set t 64 temp)
                  sailThrow ((Error_Undefined ())))
              else
                (do
                  (X_set t 64 temp)
                  (AArch64_SystemAccessTrap EL2 (BitVec.toNat (0x18 : (BitVec 8))))))
          else
            (do
              let pmselr_el0 ← do
                (pure (BitVec.toNat (_get_PMSELR_EL0_Type_SEL (← readReg PMSELR_EL0))))
              assert (pmselr_el0 <b 31) "src/sysregs.sail:350.38-350.39"
              (X_set t 64 (GetElem?.getElem! (← readReg PMEVCNTR_EL0) pmselr_el0))))
      else (pure ()))
  else (pure ())
  bif (Bool.and
       (Bool.and (Bool.and (Bool.and (BEq.beq op0 3) (BEq.beq crn 9)) (BEq.beq op1 3))
         (BEq.beq op2 0)) (BEq.beq crm 12))
  then
    (X_set t 64
      (Sail.BitVec.updateSubrange (← (X_read t 64)) 15 11
        (integer_subrange (← (AArch64_GetNumEventCountersAccessible ())) 4 0)))
  else (pure ())
  bif (Bool.and (Bool.and (Bool.and (BEq.beq op0 3) (BEq.beq crn 14)) (BEq.beq op1 3))
       (Bool.or (BEq.beq (integer_subrange crm 3 2) (0b10 : (BitVec 2)))
         (Bool.and (BEq.beq (integer_subrange crm 3 2) (0b11 : (BitVec 2)))
           (bne ((integer_subrange crm 1 0) ++ (integer_subrange op2 2 0)) (0b11111 : (BitVec 5))))))
  then
    (do
      bif (Bool.or
           (Bool.and
             ((BitVec.toNat ((integer_subrange crm 1 0) ++ (integer_subrange op2 2 0))) >b ((← (GetNumEventCounters
                     ())) -i 1))
             (bne ((integer_subrange crm 1 0) ++ (integer_subrange op2 2 0)) (0b11111 : (BitVec 5))))
           (Bool.and
             (Bool.and (← (EL2Enabled ()))
               (Bool.or (BEq.beq (← readReg PSTATE).EL EL0) (BEq.beq (← readReg PSTATE).EL EL1)))
             (← do
               (pure ((BitVec.toNat ((integer_subrange crm 1 0) ++ (integer_subrange op2 2 0))) >b ((← (AArch64_GetNumEventCountersAccessible
                         ())) -i 1))))))
      then
        (do
          bif ((BitVec.toNat ((integer_subrange crm 1 0) ++ (integer_subrange op2 2 0))) >b ((← (GetNumEventCounters
                     ())) -i 1))
          then sailThrow ((Error_Undefined ()))
          else
            (do
              (X_set t 64 temp)
              (AArch64_SystemAccessTrap EL2 (BitVec.toNat (0x18 : (BitVec 8))))))
      else (pure ()))
  else (pure ())
  bif (Bool.and (Bool.and (Bool.and (BEq.beq op0 2) (BEq.beq op1 0)) (BEq.beq crn 7))
       (BEq.beq op2 6))
  then
    (do
      bif (BEq.beq crm 8)
      then
        throw (← do
            (X_set t 64 (Sail.BitVec.updateSubrange (← (X_read t 64)) 7 0 (0xFF : (BitVec 8)))))
      else
        (do
          bif (BEq.beq crm 9)
          then
            throw (← do
                (X_set t 64
                  (Sail.BitVec.updateSubrange (← (X_read t 64)) 7 0
                    (Sail.BitVec.extractLsb (← readReg DBGCLAIMCLR_EL1) 7 0))))
          else (pure ())))
  else (pure ())
  bif (Bool.and (Bool.and (Bool.and (BEq.beq op0 2) (BEq.beq op1 1)) (BEq.beq crn 7))
       (BEq.beq op2 6))
  then
    (do
      bif (BEq.beq crm 8)
      then
        throw (← do
            (X_set t 64
              (Sail.BitVec.updateSubrange (← (X_read t 64)) 31 0 (← readReg __trcclaim_tags))))
      else
        (do
          bif (BEq.beq crm 9)
          then
            throw (← do
                (X_set t 64
                  (Sail.BitVec.updateSubrange (← (X_read t 64)) 31 0 (← readReg __trcclaim_tags))))
          else (pure ())))
  else (pure ())
  bif (Bool.and
       (Bool.and
         (Bool.and (Bool.and (BEq.beq op0 3) (BEq.beq op1 0))
           ((BEq.beq crn (BitVec.toNat (0xA : (BitVec 4)))) : Bool)) (BEq.beq op2 0))
       (BEq.beq crm 5))
  then
    (do
      bif (BEq.beq (← (CurrentSecurityState ())) SS_Secure)
      then
        (X_set t 64
          (Sail.BitVec.updateSubrange (← (X_read t 64)) 60 60
            (_get_MPAM3_EL3_Type_FORCE_NS (← (MPAM3_EL3_read ())))))
      else (pure ()))
  else
    (do
      bif (Bool.and
           (Bool.and
             (Bool.and
               (Bool.and (BEq.beq op0 3) ((BEq.beq crn (BitVec.toNat (0xC : (BitVec 4)))) : Bool))
               (BEq.beq op1 0)) (BEq.beq op2 0)) (BEq.beq crm 1))
      then
        (do
          (X_set t 64 (Sail.BitVec.zeroExtend (← (getISR ())) 64)))
      else
        (do
          bif (Bool.and
               (Bool.and (Bool.and (Bool.and (BEq.beq op0 3) (BEq.beq crn 0)) (BEq.beq op1 1))
                 (Bool.or (BEq.beq op2 0) (BEq.beq op2 2))) (BEq.beq crm 0))
          then
            (do
              bif (BEq.beq op2 0)
              then
                (do
                  (X_set t 64
                    (← (CacheConfigRead (Sail.BitVec.extractLsb (← readReg CSSELR_EL1) 3 0)))))
              else
                (do
                  (X_set t 64
                    (Sail.BitVec.zeroExtend
                      (Sail.BitVec.extractLsb
                        (← (CacheConfigRead (Sail.BitVec.extractLsb (← readReg CSSELR_EL1) 3 0)))
                        63 32) 64))))
          else
            (do
              bif (Bool.and
                   (Bool.and (Bool.and (Bool.and (BEq.beq op0 3) (BEq.beq crn 0)) (BEq.beq op1 3))
                     (BEq.beq op2 7)) (BEq.beq crm 0))
              then
                (do
                  bif (BEq.beq (← readReg PSTATE).EL EL0)
                  then
                    (do
                      bif (← (IsInHost ()))
                      then
                        (X_set t 64
                          (Sail.BitVec.updateSubrange (← (X_read t 64)) 4 4
                            (← do
                              bif (BEq.beq (_get_SCTLR_EL2_Type_DZE (← readReg SCTLR_EL2))
                                   (0b0 : (BitVec 1)))
                              then (pure (0b1 : (BitVec 1)))
                              else (pure (0b0 : (BitVec 1))))))
                      else
                        (X_set t 64
                          (Sail.BitVec.updateSubrange (← (X_read t 64)) 4 4
                            (← do
                              bif (Bool.or
                                   (BEq.beq (_get_SCTLR_EL1_Type_DZE (← readReg SCTLR_EL1))
                                     (0b0 : (BitVec 1)))
                                   (Bool.and (← (EL2Enabled ()))
                                     (BEq.beq (_get_HCR_EL2_Type_TDZ (← readReg HCR_EL2))
                                       (0b1 : (BitVec 1)))))
                              then (pure (0b1 : (BitVec 1)))
                              else (pure (0b0 : (BitVec 1)))))))
                  else
                    (do
                      bif (BEq.beq (← readReg PSTATE).EL EL1)
                      then
                        (X_set t 64
                          (Sail.BitVec.updateSubrange (← (X_read t 64)) 4 4
                            (← do
                              bif (Bool.and (← (EL2Enabled ()))
                                   (BEq.beq (_get_HCR_EL2_Type_TDZ (← readReg HCR_EL2))
                                     (0b1 : (BitVec 1))))
                              then (pure (0b1 : (BitVec 1)))
                              else (pure (0b0 : (BitVec 1))))))
                      else (pure ())))
              else
                (do
                  bif (← (AArch64_CheckNVCondsIfCurrentEL op0 op1 crn crm op2))
                  then
                    (X_set t 64
                      (Sail.BitVec.updateSubrange (← (X_read t 64)) 3 2 (0b10 : (BitVec 2))))
                  else (pure ())
                  bif (Bool.and
                       (Bool.and
                         (Bool.and (Bool.and (BEq.beq op0 3) (BEq.beq crn 2)) (BEq.beq crm 4))
                         (BEq.beq op1 3)) (Bool.or (BEq.beq op2 0) (BEq.beq op2 1)))
                  then
                    (X_set t 64
                      (← do
                        bif (BEq.beq op2 0)
                        then (genRandomNum false)
                        else (genRandomNum true)))
                  else (pure ())
                  bif (Bool.and
                       (Bool.and (Bool.and (BEq.beq op0 2) (BEq.beq op1 1)) (BEq.beq crn 8))
                       (Bool.or (BEq.beq op2 0)
                         (Bool.or (BEq.beq op2 1)
                           (Bool.or (BEq.beq op2 2)
                             (Bool.or (BEq.beq op2 4) (Bool.or (BEq.beq op2 5) (BEq.beq op2 6)))))))
                  then
                    (do
                      let recordIdx ← do
                        (pure (BitVec.toNat
                            (((_get_BRBFCR_EL1_Type_BANK (← readReg BRBFCR_EL1)) ++ (BitVec.join1 [(integer_access
                                    op2 2)])) ++ (integer_subrange crm 3 0))))
                      bif (recordIdx <b (← (GetBRBENumRecords ())))
                      then
                        (do
                          bif (Bool.or (BEq.beq op2 0) (BEq.beq op2 4))
                          then
                            (do
                              assert (Bool.and (0 ≤b recordIdx) (recordIdx <b 64)) "src/sysregs.sail:443.70-443.71"
                              (X_set t 64 (GetElem?.getElem! (← readReg Records_INF) recordIdx)))
                          else (pure ())
                          bif (Bool.or (BEq.beq op2 1) (BEq.beq op2 5))
                          then
                            (do
                              assert (Bool.and (0 ≤b recordIdx) (recordIdx <b 64)) "src/sysregs.sail:447.70-447.71"
                              (X_set t 64 (GetElem?.getElem! (← readReg Records_SRC) recordIdx)))
                          else (pure ())
                          bif (Bool.or (BEq.beq op2 2) (BEq.beq op2 6))
                          then
                            (do
                              assert (Bool.and (0 ≤b recordIdx) (recordIdx <b 64)) "src/sysregs.sail:451.70-451.71"
                              (X_set t 64 (GetElem?.getElem! (← readReg Records_TGT) recordIdx)))
                          else (pure ()))
                      else (X_set t 64 (Zeros (n := 64))))
                  else (pure ())
                  bif (Bool.and
                       (Bool.and
                         (Bool.and (Bool.and (BEq.beq op0 3) (BEq.beq crn 5)) (BEq.beq op1 0))
                         (BEq.beq op2 0)) (BEq.beq crm 4))
                  then
                    (do
                      bif (Bool.or
                           (BEq.beq
                             (BitVec.toNat (_get_ERRIDR_EL1_Type_NUM (← readReg ERRIDR_EL1)))
                             (BitVec.toNat (0x0 : (BitVec 4))))
                           (← do
                             (pure ((BitVec.toNat
                                   (_get_ERRSELR_EL1_Type_SEL (← readReg ERRSELR_EL1))) ≥b (BitVec.toNat
                                   (_get_ERRIDR_EL1_Type_NUM (← readReg ERRIDR_EL1)))))))
                      then (X_set t 64 (Zeros (n := 64)))
                      else
                        (do
                          let index ← do
                            (pure (BitVec.toNat
                                (_get_ERRSELR_EL1_Type_SEL (← readReg ERRSELR_EL1))))
                          assert (Bool.and (0 ≤b index) (index <b 4)) "src/sysregs.sail:464.57-464.58"
                          (X_set t 64 (GetElem?.getElem! (← readReg ERRnFR) index))))
                  else (pure ())
                  bif (Bool.and
                       (Bool.and
                         (Bool.and (Bool.and (BEq.beq op0 2) (BEq.beq crn 7)) (BEq.beq op1 0))
                         (BEq.beq op2 6)) (BEq.beq crm 14))
                  then
                    (do
                      bif (HaveEL EL3)
                      then
                        (do
                          bif (← (ExternalInvasiveDebugEnabled ()))
                          then
                            (X_set t 64
                              (Sail.BitVec.updateSubrange (← (X_read t 64)) 1 0
                                (0b11 : (BitVec 2))))
                          else
                            (X_set t 64
                              (Sail.BitVec.updateSubrange (← (X_read t 64)) 1 0
                                (0b10 : (BitVec 2))))
                          (X_set t 64
                            (Sail.BitVec.updateSubrange (← (X_read t 64)) 3 2 (0b11 : (BitVec 2))))
                          bif (← (ExternalSecureInvasiveDebugEnabled ()))
                          then
                            (X_set t 64
                              (Sail.BitVec.updateSubrange (← (X_read t 64)) 5 4
                                (0b11 : (BitVec 2))))
                          else
                            (X_set t 64
                              (Sail.BitVec.updateSubrange (← (X_read t 64)) 5 4
                                (0b10 : (BitVec 2))))
                          (X_set t 64
                            (Sail.BitVec.updateSubrange (← (X_read t 64)) 7 6
                              (Sail.BitVec.extractLsb (← (X_read t 64)) 5 4))))
                      else (pure ()))
                  else
                    (do
                      bif (Bool.and
                           (Bool.and
                             (Bool.and (Bool.and (BEq.beq op0 2) (BEq.beq crn 0)) (BEq.beq op1 3))
                             (BEq.beq op2 0)) (BEq.beq crm 5))
                      then
                        (do
                          (DBGDSCRint_write
                            (_update_DBGDSCRint_Type_RXfull (← (DBGDSCRint_read ()))
                              (0b0 : (BitVec 1))))
                          writeReg MDCCSR_EL0 (Sail.BitVec.updateSubrange (← readReg MDCCSR_EL0)
                            30 30 (0b0 : (BitVec 1)))
                          (DBGDSCRext_write
                            (_update_DBGDSCRext_Type_RXfull (← (DBGDSCRext_read ()))
                              (0b0 : (BitVec 1))))
                          (EDSCR_write
                            (_update_EDSCR_Type_RXfull (← (EDSCR_read ())) (0b0 : (BitVec 1)))))
                      else (pure ())
                      bif (Bool.and
                           (Bool.and
                             (Bool.and (Bool.and (BEq.beq op0 2) (BEq.beq crn 0)) (BEq.beq op1 3))
                             (BEq.beq op2 0)) (BEq.beq crm 4))
                      then
                        (do
                          (DBGDSCRint_write
                            (_update_DBGDSCRint_Type_RXfull (← (DBGDSCRint_read ()))
                              (0b0 : (BitVec 1))))
                          writeReg MDCCSR_EL0 (Sail.BitVec.updateSubrange (← readReg MDCCSR_EL0)
                            30 30 (0b0 : (BitVec 1)))
                          (DBGDSCRext_write
                            (_update_DBGDSCRext_Type_RXfull (← (DBGDSCRext_read ()))
                              (0b0 : (BitVec 1))))
                          (EDSCR_write
                            (_update_EDSCR_Type_RXfull (← (EDSCR_read ())) (0b0 : (BitVec 1))))
                          (X_set t 64
                            (set_slice 32 (← (X_read t 64)) 32
                              (BitVec.slice (← readReg DBGDTRTX_EL0) 0 32)))
                          (X_set t 64
                            (set_slice 32 (← (X_read t 64)) 0
                              (BitVec.slice (← readReg DBGDTRRX_EL0) 0 32))))
                      else (pure ())
                      bif (Bool.and
                           (Bool.and
                             (Bool.and (Bool.and (BEq.beq op0 3) (BEq.beq crn 12)) (BEq.beq op1 4))
                             (BEq.beq op2 7)) (BEq.beq crm 11))
                      then
                        (do
                          bif (Bool.or (BEq.beq (← readReg PSTATE).EL EL2)
                               (BEq.beq (← readReg PSTATE).EL EL3))
                          then
                            (X_set t 64
                              (Sail.BitVec.updateSubrange (← (X_read t 64)) 26 24
                                (0b000 : (BitVec 3))))
                          else (pure ()))
                      else (pure ())
                      bif (Bool.and
                           (Bool.and
                             (Bool.and (Bool.and (BEq.beq op0 3) (BEq.beq crn 4)) (BEq.beq op1 0))
                             (BEq.beq op2 0)) (BEq.beq crm 6))
                      then
                        (X_set t 64
                          (Sail.BitVec.updateSubrange (← (X_read t 64)) 2 0 (0b000 : (BitVec 3))))
                      else (pure ())
                      bif (Bool.and
                           (Bool.and
                             (Bool.and (Bool.and (BEq.beq op0 3) (BEq.beq crn 1)) (BEq.beq op1 4))
                             (BEq.beq op2 0)) (BEq.beq crm 1))
                      then
                        (do
                          bif (Bool.and (Bool.not (← (ELUsingAArch32 EL1)))
                               (bne (← readReg PSTATE).EL EL1))
                          then
                            (X_set t 64
                              (Sail.BitVec.updateSubrange (← (X_read t 64)) 31 31
                                (0b1 : (BitVec 1))))
                          else (pure ()))
                      else (pure ())
                      bif (Bool.and
                           (Bool.and
                             (Bool.and (Bool.and (BEq.beq op0 3) (BEq.beq crn 12)) (BEq.beq op1 6))
                             (BEq.beq op2 2)) (BEq.beq crm 0))
                      then
                        (do
                          bif (BEq.beq (_get_ID_AA64PFR0_EL1_Type_EL3 (← readReg ID_AA64PFR0_EL1))
                               (0x1 : (BitVec 4)))
                          then
                            (X_set t 64
                              (Sail.BitVec.updateSubrange (← (X_read t 64)) 0 0 (0b1 : (BitVec 1))))
                          else (pure ()))
                      else (pure ()))))))

def SetResetVector (value_name : (BitVec 64)) : SailM Unit := do
  bif (Bool.not (← (HaveAArch64 ())))
  then
    (do
      bif (HaveEL EL3)
      then
        writeReg MVBAR (Mk_MVBAR_Type
          ((Sail.BitVec.extractLsb value_name 31 1) ++ (0b1 : (BitVec 1))))
      else writeReg RVBAR ((Sail.BitVec.extractLsb value_name 31 1) ++ (0b1 : (BitVec 1))))
  else
    (do
      bif (BEq.beq (HighestEL ()) EL3)
      then writeReg RVBAR_EL3 (Mk_RVBAR_EL3_Type value_name)
      else
        (do
          bif (BEq.beq (HighestEL ()) EL2)
          then writeReg RVBAR_EL2 (Mk_RVBAR_EL2_Type value_name)
          else writeReg RVBAR_EL1 (Mk_RVBAR_EL1_Type value_name)))

/-- Type quantifiers: k_cold : Bool -/
def TakeReset (cold : Bool) : SailM Unit := do
  assert (Bool.or (BEq.beq (HighestEL ()) EL1)
    (Bool.or (BEq.beq (HighestEL ()) EL2) (BEq.beq (HighestEL ()) EL3))) "src/reset.sail:1400.71-1400.72"
  writeReg FEAT_DoubleLock_IMPLEMENTED false
  writeReg FEAT_EPAC_IMPLEMENTED false
  (InitVariantImplemented ())
  (InitFeatureImpl ())
  bif cold
  then
    (do
      writeReg ID_AA64PFR0_EL1 (Sail.BitVec.updateSubrange (← readReg ID_AA64PFR0_EL1) 15 12
        CFG_ID_AA64PFR0_EL1_EL3)
      writeReg ID_AA64PFR0_EL1 (Sail.BitVec.updateSubrange (← readReg ID_AA64PFR0_EL1) 11 8
        CFG_ID_AA64PFR0_EL1_EL2)
      writeReg ID_AA64PFR0_EL1 (Sail.BitVec.updateSubrange (← readReg ID_AA64PFR0_EL1) 7 4
        CFG_ID_AA64PFR0_EL1_EL1)
      writeReg ID_AA64PFR0_EL1 (Sail.BitVec.updateSubrange (← readReg ID_AA64PFR0_EL1) 3 0
        CFG_ID_AA64PFR0_EL1_EL0)
      writeReg OSLSR_EL1 (Sail.BitVec.updateSubrange (← readReg OSLSR_EL1) 1 1 (0b1 : (BitVec 1)))
      writeReg RMR_EL3 (Sail.BitVec.updateSubrange (← readReg RMR_EL3) 0 0
        (← readReg CFG_RMR_AA64)))
  else (pure ())
  bif (BEq.beq (_get_RMR_EL3_Type_AA64 (← readReg RMR_EL3)) (0b1 : (BitVec 1)))
  then
    (do
      writeReg __highest_el_aarch32 false
      (SetResetVector (← readReg CFG_RVBAR))
      (AArch64_TakeReset cold))
  else
    (do
      let questionMark := (HighestEL ())
      bif (BEq.beq questionMark EL3)
      then
        assert (BEq.beq (_get_ID_AA64PFR0_EL1_Type_EL3 (← readReg ID_AA64PFR0_EL1))
          (0x2 : (BitVec 4))) "src/reset.sail:1420.51-1420.52"
      else
        (do
          bif (BEq.beq questionMark EL2)
          then
            assert (BEq.beq (_get_ID_AA64PFR0_EL1_Type_EL2 (← readReg ID_AA64PFR0_EL1))
              (0x2 : (BitVec 4))) "src/reset.sail:1423.51-1423.52"
          else
            (do
              bif (BEq.beq questionMark EL1)
              then
                assert (BEq.beq (_get_ID_AA64PFR0_EL1_Type_EL1 (← readReg ID_AA64PFR0_EL1))
                  (0x2 : (BitVec 4))) "src/reset.sail:1426.51-1426.52"
              else (pure ())))
      writeReg __highest_el_aarch32 true
      writeReg FeatureImpl (vectorUpdate (← readReg FeatureImpl) (num_of_Feature FEAT_AA64EL0)
        false)
      writeReg FeatureImpl (vectorUpdate (← readReg FeatureImpl) (num_of_Feature FEAT_AA64EL1)
        false)
      writeReg FeatureImpl (vectorUpdate (← readReg FeatureImpl) (num_of_Feature FEAT_AA64EL2)
        false)
      writeReg FeatureImpl (vectorUpdate (← readReg FeatureImpl) (num_of_Feature FEAT_AA64EL3)
        false)
      bif (← readReg __ignore_rvbar_in_aarch32)
      then (SetResetVector (Sail.BitVec.zeroExtend (0x0 : (BitVec 4)) 64))
      else (SetResetVector (← readReg CFG_RVBAR))
      bif (HaveEL EL3)
      then writeReg SCR (Sail.BitVec.updateSubrange (← readReg SCR) 0 0 (0b0 : (BitVec 1)))
      else (pure ())
      (AArch32_TakeReset cold))
  bif (bne (← readReg ZCR_EL3_LEN_VALUE) (Neg.neg 1))
  then
    writeReg ZCR_EL3 (Sail.BitVec.updateSubrange (← readReg ZCR_EL3) 3 0
      (integer_subrange (← readReg ZCR_EL3_LEN_VALUE) 3 0))
  else (pure ())
  bif (bne (← readReg CPTR_EL3_EZ_VALUE) (Neg.neg 1))
  then
    writeReg CPTR_EL3 (Sail.BitVec.updateSubrange (← readReg CPTR_EL3) 8 8
      (BitVec.join1 [(integer_access (← readReg CPTR_EL3_EZ_VALUE) 0)]))
  else (pure ())
  bif (bne (← readReg CPTR_EL3_ESM_VALUE) (Neg.neg 1))
  then
    writeReg CPTR_EL3 (Sail.BitVec.updateSubrange (← readReg CPTR_EL3) 12 12
      (BitVec.join1 [(integer_access (← readReg CPTR_EL3_ESM_VALUE) 0)]))
  else (pure ())
  bif (bne (← readReg SMCR_EL3_LEN_VALUE) (Neg.neg 1))
  then
    writeReg SMCR_EL3 (Sail.BitVec.updateSubrange (← readReg SMCR_EL3) 3 0
      (integer_subrange (← readReg SMCR_EL3_LEN_VALUE) 3 0))
  else (pure ())

/-- Type quantifiers: crm : Int, crn : Int, op0 : Int, op1 : Int, op2 : Int, t : Int -/
def AArch64_SysRegWrite (op0 : Int) (op1 : Int) (crn : Int) (crm : Int) (op2 : Int) (t : Int) : SailM Unit := SailME.run do
  let n ← (( do (undefined_int ()) ) : SailME _ Int )
  let tempxt ← (( do (X_read t 64) ) : SailME _ (BitVec 64) )
  let tempxt : (BitVec 64) :=
    bif (Bool.and (Bool.and (Bool.and (BEq.beq op0 2) (BEq.beq crn 0)) (BEq.beq op1 0))
         (BEq.beq op2 5))
    then
      (let tempxt : (BitVec 64) :=
        (BitVec.update tempxt 8 (Bit (BitVec.join1 [(BitVec.access tempxt 7)])))
      (BitVec.update tempxt 6 (Bit (BitVec.join1 [(BitVec.access tempxt 5)]))))
    else tempxt
  let tempxt ← (( do
    bif (Bool.and
         (Bool.and (Bool.and (Bool.and (BEq.beq op0 3) (BEq.beq crn 12)) (BEq.beq op1 0))
           (BEq.beq op2 4)) (BEq.beq crm 12))
    then
      (do
        let tempxt ←
          (pure (BitVec.update tempxt 19
              (Bit (_get_ICV_CTLR_EL1_Type_ExtRange (← readReg ICV_CTLR_EL1)))))
        let tempxt ←
          (pure (Sail.BitVec.updateSubrange tempxt 13 11
              (_get_ICV_CTLR_EL1_Type_IDbits (← readReg ICV_CTLR_EL1))))
        let tempxt ←
          (pure (Sail.BitVec.updateSubrange tempxt 10 8
              (_get_ICV_CTLR_EL1_Type_PRIbits (← readReg ICV_CTLR_EL1))))
        let tempxt ←
          (pure (BitVec.update tempxt 15
              (Bit (_get_ICV_CTLR_EL1_Type_A3V (← readReg ICV_CTLR_EL1)))))
        (pure (BitVec.update tempxt 14
            (Bit (_get_ICV_CTLR_EL1_Type_SEIS (← readReg ICV_CTLR_EL1))))))
    else (pure tempxt) ) : SailME _ (BitVec 64) )
  let tempxt ← (( do
    bif (Bool.and
         (Bool.and (Bool.and (Bool.and (BEq.beq op0 3) (BEq.beq crn 12)) (BEq.beq op1 6))
           (BEq.beq op2 4)) (BEq.beq crm 12))
    then
      (do
        let tempxt ←
          (pure (BitVec.update tempxt 19
              (Bit (_get_ICC_CTLR_EL3_Type_ExtRange (← readReg ICC_CTLR_EL3)))))
        let tempxt ←
          (pure (Sail.BitVec.updateSubrange tempxt 13 11
              (_get_ICC_CTLR_EL3_Type_IDbits (← readReg ICC_CTLR_EL3))))
        let tempxt ←
          (pure (Sail.BitVec.updateSubrange tempxt 10 8
              (_get_ICC_CTLR_EL3_Type_PRIbits (← readReg ICC_CTLR_EL3))))
        let tempxt ←
          (pure (BitVec.update tempxt 17
              (Bit (_get_ICC_CTLR_EL3_Type_nDS (← readReg ICC_CTLR_EL3)))))
        let tempxt ←
          (pure (BitVec.update tempxt 15
              (Bit (_get_ICC_CTLR_EL3_Type_A3V (← readReg ICC_CTLR_EL3)))))
        (pure (BitVec.update tempxt 14
            (Bit (_get_ICC_CTLR_EL3_Type_SEIS (← readReg ICC_CTLR_EL3))))))
    else (pure tempxt) ) : SailME _ (BitVec 64) )
  let tempxt ← (( do
    bif (Bool.and
         (Bool.and (Bool.and (Bool.and (BEq.beq op0 3) (BEq.beq crn 12)) (BEq.beq op1 4))
           (BEq.beq op2 7)) (BEq.beq crm 11))
    then
      (do
        bif (Bool.or (BEq.beq (← readReg PSTATE).EL EL2) (BEq.beq (← readReg PSTATE).EL EL3))
        then
          (do
            let tempxt ← (( do
              bif ((BitVec.toNat (Sail.BitVec.extractLsb tempxt 23 21)) <b (6 -i (BitVec.toNat
                       (_get_ICH_VTR_EL2_Type_PREbits (← readReg ICH_VTR_EL2)))))
              then
                (do
                  (pure (Sail.BitVec.updateSubrange tempxt 23 21
                      (integer_subrange
                        (6 -i (BitVec.toNat
                            (_get_ICH_VTR_EL2_Type_PREbits (← readReg ICH_VTR_EL2)))) 2 0))))
              else (pure tempxt) ) : SailME _ (BitVec 64) )
            let tempxt ← (( do
              bif (BEq.beq (← (CurrentSecurityState ())) SS_Secure)
              then
                (do
                  bif ((BitVec.toNat (Sail.BitVec.extractLsb tempxt 20 18)) <b (6 -i (BitVec.toNat
                           (_get_ICH_VTR_EL2_Type_PREbits (← readReg ICH_VTR_EL2)))))
                  then
                    (do
                      (pure (Sail.BitVec.updateSubrange tempxt 20 18
                          (integer_subrange
                            (6 -i (BitVec.toNat
                                (_get_ICH_VTR_EL2_Type_PREbits (← readReg ICH_VTR_EL2)))) 2 0))))
                  else (pure tempxt))
              else
                (do
                  bif ((BitVec.toNat (Sail.BitVec.extractLsb tempxt 20 18)) <b (7 -i (BitVec.toNat
                           (_get_ICH_VTR_EL2_Type_PREbits (← readReg ICH_VTR_EL2)))))
                  then
                    (do
                      (pure (Sail.BitVec.updateSubrange tempxt 20 18
                          (integer_subrange
                            (7 -i (BitVec.toNat
                                (_get_ICH_VTR_EL2_Type_PREbits (← readReg ICH_VTR_EL2)))) 2 0))))
                  else (pure tempxt)) ) : SailME _ (BitVec 64) )
            bif (BEq.beq (_get_ICC_SRE_EL1_Type_SRE (← readReg ICC_SRE_EL1_NS)) (0b1 : (BitVec 1)))
            then (pure (Sail.BitVec.updateSubrange tempxt 3 2 (0b10 : (BitVec 2))))
            else (pure tempxt))
        else (pure tempxt))
    else (pure tempxt) ) : SailME _ (BitVec 64) )
  let tempxt ← (( do
    bif (Bool.and
         (Bool.and (Bool.and (Bool.and (BEq.beq op0 3) (BEq.beq crn 12)) (BEq.beq op1 0))
           (BEq.beq op2 3)) (BEq.beq crm 8))
    then
      (do
        bif ((BitVec.toNat (Sail.BitVec.extractLsb tempxt 2 0)) <b (6 -i (BitVec.toNat
                 (_get_ICH_VTR_EL2_Type_PREbits (← readReg ICH_VTR_EL2)))))
        then
          (do
            (pure (Sail.BitVec.updateSubrange tempxt 2 0
                (integer_subrange
                  (6 -i (BitVec.toNat (_get_ICH_VTR_EL2_Type_PREbits (← readReg ICH_VTR_EL2)))) 2
                  0))))
        else (pure tempxt))
    else (pure tempxt) ) : SailME _ (BitVec 64) )
  let tempxt ← (( do
    bif (Bool.and
         (Bool.and (Bool.and (Bool.and (BEq.beq op0 3) (BEq.beq crn 12)) (BEq.beq op1 0))
           (BEq.beq op2 3)) (BEq.beq crm 12))
    then
      (do
        bif (BEq.beq (_get_ICV_CTLR_EL1_Type_CBPR (← readReg ICV_CTLR_EL1)) (0b0 : (BitVec 1)))
        then
          (do
            bif (BEq.beq (← (CurrentSecurityState ())) SS_Secure)
            then
              (do
                bif ((BitVec.toNat (Sail.BitVec.extractLsb tempxt 2 0)) <b (6 -i (BitVec.toNat
                         (_get_ICH_VTR_EL2_Type_PREbits (← readReg ICH_VTR_EL2)))))
                then
                  (do
                    (pure (Sail.BitVec.updateSubrange tempxt 2 0
                        (integer_subrange
                          (6 -i (BitVec.toNat
                              (_get_ICH_VTR_EL2_Type_PREbits (← readReg ICH_VTR_EL2)))) 2 0))))
                else (pure tempxt))
            else
              (do
                bif ((BitVec.toNat (Sail.BitVec.extractLsb tempxt 2 0)) <b (7 -i (BitVec.toNat
                         (_get_ICH_VTR_EL2_Type_PREbits (← readReg ICH_VTR_EL2)))))
                then
                  (do
                    (pure (Sail.BitVec.updateSubrange tempxt 2 0
                        (integer_subrange
                          (7 -i (BitVec.toNat
                              (_get_ICH_VTR_EL2_Type_PREbits (← readReg ICH_VTR_EL2)))) 2 0))))
                else (pure tempxt)))
        else
          (do
            (pure (Sail.BitVec.updateSubrange tempxt 2 0
                (_get_ICV_BPR1_EL1_Type_BinaryPoint (← readReg ICV_BPR1_EL1))))))
    else (pure tempxt) ) : SailME _ (BitVec 64) )
  bif (Bool.and (Bool.and (BEq.beq op0 3) (BEq.beq op1 3)) (BEq.beq crn 13))
  then
    (do
      let n :=
        (BitVec.toNat ((BitVec.join1 [(integer_access crm 0)]) ++ (integer_subrange op2 2 0)))
      bif (Bool.or (BEq.beq (integer_subrange crm 3 1) (0b010 : (BitVec 3)))
           (BEq.beq (integer_subrange crm 3 1) (0b011 : (BitVec 3))))
      then
        (do
          bif (n ≥b (BitVec.toNat (_get_AMCGCR_EL0_Type_CG0NC (← readReg AMCGCR_EL0))))
          then sailThrow ((Error_Undefined ()))
          else (pure ()))
      else
        (do
          bif (Bool.or (BEq.beq (integer_subrange crm 3 1) (0b110 : (BitVec 3)))
               (BEq.beq (integer_subrange crm 3 1) (0b111 : (BitVec 3))))
          then
            (do
              bif (n ≥b (BitVec.toNat (_get_AMCGCR_EL0_Type_CG1NC (← readReg AMCGCR_EL0))))
              then sailThrow ((Error_Undefined ()))
              else (pure ()))
          else (pure ())))
  else (pure ())
  let mask ← (( do (PMUCounterMask ()) ) : SailME _ (BitVec 64) )
  let tempxt ← (( do
    bif (Bool.and
         (Bool.and (Bool.and (Bool.and (BEq.beq op0 3) (BEq.beq crn 9)) (BEq.beq op1 3))
           (BEq.beq op2 3)) (Bool.or (BEq.beq crm 12) (BEq.beq crm 14)))
    then
      (do
        let tempxt ← (( do
          bif (BEq.beq crm 12)
          then
            (do
              (pure ((← readReg PMOVSSET_EL0) &&& (Complement.complement (tempxt &&& mask)))))
          else (pure tempxt) ) : SailME _ (BitVec 64) )
        bif (BEq.beq crm 14)
        then
          (do
            (pure ((← readReg PMOVSSET_EL0) ||| (tempxt &&& mask))))
        else (pure tempxt))
    else (pure tempxt) ) : SailME _ (BitVec 64) )
  let tempxt ← (( do
    bif (Bool.and
         (Bool.and (Bool.and (Bool.and (BEq.beq op0 3) (BEq.beq crn 9)) (BEq.beq op1 3))
           (Bool.or (BEq.beq op2 1) (BEq.beq op2 2))) (BEq.beq crm 12))
    then
      (do
        let tempxt ← (( do
          bif (BEq.beq op2 2)
          then
            (do
              (pure ((← readReg PMCNTENSET_EL0) &&& (Complement.complement (tempxt &&& mask)))))
          else (pure tempxt) ) : SailME _ (BitVec 64) )
        bif (BEq.beq op2 1)
        then
          (do
            (pure ((← readReg PMCNTENSET_EL0) ||| (tempxt &&& mask))))
        else (pure tempxt))
    else (pure tempxt) ) : SailME _ (BitVec 64) )
  let tempxt ← (( do
    bif (Bool.and
         (Bool.and (Bool.and (Bool.and (BEq.beq op0 3) (BEq.beq crn 9)) (BEq.beq op1 0))
           (Bool.or (BEq.beq op2 1) (BEq.beq op2 2))) (BEq.beq crm 14))
    then
      (do
        let tempxt ← (( do
          bif (BEq.beq op2 2)
          then
            (do
              (pure ((← readReg PMINTENSET_EL1) &&& (Complement.complement (tempxt &&& mask)))))
          else (pure tempxt) ) : SailME _ (BitVec 64) )
        bif (BEq.beq op2 1)
        then
          (do
            (pure ((← readReg PMINTENSET_EL1) ||| (tempxt &&& mask))))
        else (pure tempxt))
    else (pure tempxt) ) : SailME _ (BitVec 64) )
  bif (Bool.and
       (Bool.and (Bool.and (Bool.and (BEq.beq op0 3) (BEq.beq crn 9)) (BEq.beq op1 3))
         (BEq.beq op2 0)) (BEq.beq crm 12))
  then
    (do
      bif (Bool.and (BEq.beq (BitVec.join1 [(BitVec.access tempxt 3)]) (0b1 : (BitVec 1)))
           (BEq.beq (_get_PMCR_EL0_Type_D (← readReg PMCR_EL0)) (0b0 : (BitVec 1))))
      then writeReg __clock_divider 63
      else (pure ()))
  else (pure ())
  bif (Bool.and (Bool.and (Bool.and (BEq.beq op0 3) (BEq.beq crn 14)) (BEq.beq op1 3))
       (Bool.or (BEq.beq (integer_subrange crm 3 2) (0b10 : (BitVec 2)))
         (Bool.and (BEq.beq (integer_subrange crm 3 2) (0b11 : (BitVec 2)))
           (bne ((integer_subrange crm 1 0) ++ (integer_subrange op2 2 0)) (0b11111 : (BitVec 5))))))
  then
    (do
      bif (Bool.or
           (Bool.and
             ((BitVec.toNat ((integer_subrange crm 1 0) ++ (integer_subrange op2 2 0))) >b ((← (GetNumEventCounters
                     ())) -i 1))
             (bne ((integer_subrange crm 1 0) ++ (integer_subrange op2 2 0)) (0b11111 : (BitVec 5))))
           (Bool.and
             (Bool.and
               (Bool.and (← (EL2Enabled ()))
                 (Bool.or (BEq.beq (← readReg PSTATE).EL EL0)
                   (BEq.beq (← readReg PSTATE).EL EL1)))
               (BEq.beq (_get_PMUSERENR_EL0_Type_EN (← readReg PMUSERENR_EL0)) (0b1 : (BitVec 1))))
             (← do
               (pure ((BitVec.toNat ((integer_subrange crm 1 0) ++ (integer_subrange op2 2 0))) >b ((← (AArch64_GetNumEventCountersAccessible
                         ())) -i 1))))))
      then
        (do
          bif ((BitVec.toNat ((integer_subrange crm 1 0) ++ (integer_subrange op2 2 0))) >b ((← (GetNumEventCounters
                     ())) -i 1))
          then sailThrow ((Error_Undefined ()))
          else (AArch64_SystemAccessTrap EL2 (BitVec.toNat (0x18 : (BitVec 8)))))
      else (pure ()))
  else (pure ())
  bif (Bool.and
       (Bool.and (Bool.and (Bool.and (BEq.beq op0 3) (BEq.beq op1 3)) (BEq.beq crn 9))
         (BEq.beq crm 13))
       (Bool.or (BEq.beq op2 2)
         (Bool.and (BEq.beq op2 1)
           (bne (_get_PMSELR_EL0_Type_SEL (← readReg PMSELR_EL0)) (0b11111 : (BitVec 5))))))
  then
    (do
      bif (Bool.or
           (Bool.and
             ((BitVec.toNat (_get_PMSELR_EL0_Type_SEL (← readReg PMSELR_EL0))) >b ((← (GetNumEventCounters
                     ())) -i 1))
             (bne (_get_PMSELR_EL0_Type_SEL (← readReg PMSELR_EL0)) (0b11111 : (BitVec 5))))
           (Bool.and
             (Bool.and
               (Bool.and (← (EL2Enabled ()))
                 (Bool.or (BEq.beq (← readReg PSTATE).EL EL0)
                   (BEq.beq (← readReg PSTATE).EL EL1)))
               (BEq.beq (_get_PMUSERENR_EL0_Type_EN (← readReg PMUSERENR_EL0)) (0b1 : (BitVec 1))))
             (← do
               (pure ((BitVec.toNat (_get_PMSELR_EL0_Type_SEL (← readReg PMSELR_EL0))) >b ((← (AArch64_GetNumEventCountersAccessible
                         ())) -i 1))))))
      then
        (do
          bif ((BitVec.toNat (_get_PMSELR_EL0_Type_SEL (← readReg PMSELR_EL0))) >b ((← (GetNumEventCounters
                     ())) -i 1))
          then sailThrow ((Error_Undefined ()))
          else (AArch64_SystemAccessTrap EL2 (BitVec.toNat (0x18 : (BitVec 8)))))
      else (pure ()))
  else (pure ())
  let tempxt ← (( do
    bif (Bool.and (Bool.and (Bool.and (BEq.beq op0 2) (BEq.beq op1 0)) (BEq.beq crn 7))
         (BEq.beq op2 6))
    then
      (do
        let tempxt ← (( do
          bif (BEq.beq crm 8)
          then
            (do
              (pure (Sail.BitVec.updateSubrange tempxt 7 0
                  ((Sail.BitVec.extractLsb (← readReg DBGCLAIMCLR_EL1) 7 0) ||| (Sail.BitVec.extractLsb
                      tempxt 7 0)))))
          else (pure tempxt) ) : SailME _ (BitVec 64) )
        bif (BEq.beq crm 9)
        then
          (do
            (pure (Sail.BitVec.updateSubrange tempxt 7 0
                ((Sail.BitVec.extractLsb (← readReg DBGCLAIMCLR_EL1) 7 0) &&& (Complement.complement
                    (Sail.BitVec.extractLsb tempxt 7 0))))))
        else (pure tempxt))
    else (pure tempxt) ) : SailME _ (BitVec 64) )
  let tempxt2 ← (( do (undefined_bitvector 64) ) : SailME _ (BitVec 64) )
  let restore_xt ← (( do (undefined_bool ()) ) : SailME _ Bool )
  let (restore_xt, tempxt2) ← (( do
    bif (bne tempxt (← (X_read t 64)))
    then
      (do
        let tempxt2 ← (X_read t 64)
        (X_set t 64 tempxt)
        let restore_xt : Bool := true
        (pure (restore_xt, tempxt2)))
    else
      (let restore_xt : Bool := false
      (pure (restore_xt, tempxt2))) ) : SailME _ (Bool × (BitVec 64)) )
  (AArch64_AutoGen_SysRegWrite (← readReg PSTATE).EL (integer_subrange op0 1 0)
    (integer_subrange op1 2 0) (integer_subrange crn 3 0) (integer_subrange op2 2 0)
    (integer_subrange crm 3 0) t)
  bif restore_xt
  then (X_set t 64 tempxt2)
  else (pure ())
  bif (Bool.and
       (Bool.and (Bool.and (Bool.and (BEq.beq op0 2) (BEq.beq op1 0)) (BEq.beq crn 7))
         (BEq.beq op2 6)) (BEq.beq crm 8))
  then
    writeReg DBGCLAIMCLR_EL1 (Sail.BitVec.updateSubrange (← readReg DBGCLAIMCLR_EL1) 7 0
      (Sail.BitVec.extractLsb tempxt 7 0))
  else (pure ())
  bif (Bool.and
       (Bool.and (Bool.and (Bool.and (BEq.beq crm 0) (BEq.beq crn 1)) (BEq.beq op0 2))
         (BEq.beq op1 0)) (BEq.beq op2 4))
  then
    (do
      bif (Bool.and (BEq.beq (_get_OSLSR_EL1_Type_OSLK (← readReg OSLSR_EL1)) (0b1 : (BitVec 1)))
           (BEq.beq (_get_OSLAR_EL1_Type_OSLK (← readReg OSLAR_EL1)) (0b0 : (BitVec 1))))
      then (CheckOSUnlockCatch ())
      else (pure ())
      writeReg OSLSR_EL1 (Sail.BitVec.updateSubrange (← readReg OSLSR_EL1) 1 1
        (_get_OSLAR_EL1_Type_OSLK (← readReg OSLAR_EL1)))
      writeReg EDPRSR (Sail.BitVec.updateSubrange (← readReg EDPRSR) 5 5
        (_get_OSLSR_EL1_Type_OSLK (← readReg OSLSR_EL1)))
      (DBGOSLSR_write
        (_update_DBGOSLSR_Type_OSLK (← (DBGOSLSR_read ()))
          (_get_OSLSR_EL1_Type_OSLK (← readReg OSLSR_EL1)))))
  else (pure ())
  bif (Bool.and (Bool.and (Bool.and (BEq.beq op0 2) (BEq.beq op1 1)) (BEq.beq crn 7))
       (BEq.beq op2 6))
  then
    (do
      bif (BEq.beq crm 8)
      then
        throw (← do
            writeReg __trcclaim_tags ((← readReg __trcclaim_tags) ||| (Sail.BitVec.extractLsb
                tempxt 31 0)))
      else
        (do
          bif (BEq.beq crm 9)
          then
            throw (← do
                writeReg __trcclaim_tags ((← readReg __trcclaim_tags) &&& (Complement.complement
                    (Sail.BitVec.extractLsb tempxt 31 0))))
          else (pure ())))
  else (pure ())
  bif (Bool.and
       (Bool.and
         (Bool.and
           (Bool.and
             (Bool.and (BEq.beq op0 3) ((BEq.beq crn (BitVec.toNat (0xC : (BitVec 4)))) : Bool))
             (Bool.or (Bool.or (BEq.beq op1 6) (BEq.beq op1 4)) (BEq.beq op1 0))) (BEq.beq op2 2))
         (BEq.beq crm 0)) (BEq.beq (BitVec.join1 [(BitVec.access tempxt 1)]) (0b1 : (BitVec 1))))
  then (TakeReset false)
  else (pure ())
  bif (Bool.and
       (Bool.and (Bool.and (Bool.and (BEq.beq op0 3) (BEq.beq crn 9)) (BEq.beq op1 3))
         (BEq.beq op2 3)) (Bool.or (BEq.beq crm 12) (BEq.beq crm 14)))
  then
    (do
      bif (BEq.beq crm 12)
      then writeReg PMOVSSET_EL0 (Mk_PMOVSSET_EL0_Type tempxt)
      else (pure ())
      bif (BEq.beq crm 14)
      then writeReg PMOVSCLR_EL0 (Mk_PMOVSCLR_EL0_Type tempxt)
      else (pure ()))
  else (pure ())
  bif (Bool.and
       (Bool.and (Bool.and (Bool.and (BEq.beq op0 3) (BEq.beq crn 9)) (BEq.beq op1 3))
         (Bool.or (BEq.beq op2 1) (BEq.beq op2 2))) (BEq.beq crm 12))
  then
    (do
      bif (BEq.beq op2 2)
      then writeReg PMCNTENSET_EL0 (Mk_PMCNTENSET_EL0_Type tempxt)
      else (pure ())
      bif (BEq.beq op2 1)
      then writeReg PMCNTENCLR_EL0 (Mk_PMCNTENCLR_EL0_Type tempxt)
      else (pure ()))
  else (pure ())
  bif (Bool.and
       (Bool.and (Bool.and (Bool.and (BEq.beq op0 3) (BEq.beq crn 9)) (BEq.beq op1 0))
         (Bool.or (BEq.beq op2 1) (BEq.beq op2 2))) (BEq.beq crm 14))
  then
    (do
      bif (BEq.beq op2 2)
      then writeReg PMINTENSET_EL1 (Mk_PMINTENSET_EL1_Type tempxt)
      else (pure ())
      bif (BEq.beq op2 1)
      then writeReg PMINTENCLR_EL1 (Mk_PMINTENCLR_EL1_Type tempxt)
      else (pure ()))
  else (pure ())
  bif (Bool.and
       (Bool.and (Bool.and (Bool.and (BEq.beq op0 3) (BEq.beq crn 9)) (BEq.beq op1 3))
         (BEq.beq op2 0)) (BEq.beq crm 12))
  then
    (do
      bif (BEq.beq (BitVec.join1 [(BitVec.access tempxt 2)]) (0b1 : (BitVec 1)))
      then writeReg PMCCNTR_EL0 (Mk_PMCCNTR_EL0_Type (Zeros (n := 64)))
      else (pure ())
      bif (BEq.beq (BitVec.join1 [(BitVec.access tempxt 1)]) (0b1 : (BitVec 1)))
      then (AArch64_ClearEventCounters ())
      else (pure ()))
  else (pure ())
  bif (Bool.and
       (Bool.and (Bool.and (Bool.and (BEq.beq op0 3) (BEq.beq op1 3)) (BEq.beq crn 9))
         (BEq.beq crm 13)) (Bool.or (BEq.beq op2 1) (BEq.beq op2 2)))
  then
    (do
      bif (BEq.beq op2 1)
      then
        (do
          bif (BEq.beq (_get_PMSELR_EL0_Type_SEL (← readReg PMSELR_EL0)) (0b11111 : (BitVec 5)))
          then writeReg PMCCFILTR_EL0 (__get_PMCCFILTR_EL0 (Mk_PMCCFILTR_EL0_Type tempxt))
          else
            (do
              let pmselr_el0 ← do
                (pure (BitVec.toNat (_get_PMSELR_EL0_Type_SEL (← readReg PMSELR_EL0))))
              assert (pmselr_el0 <b 31) "src/sysregs.sail:748.38-748.39"
              writeReg PMEVTYPER_EL0 (vectorUpdate (← readReg PMEVTYPER_EL0) pmselr_el0
                (__get_PMEVTYPER_EL0 (Mk_PMEVTYPER_EL0_Type tempxt)))))
      else (pure ())
      bif (BEq.beq op2 2)
      then
        (do
          let pmselr_el0 ← do
            (pure (BitVec.toNat (_get_PMSELR_EL0_Type_SEL (← readReg PMSELR_EL0))))
          assert (pmselr_el0 <b 31) "src/sysregs.sail:754.34-754.35"
          writeReg PMEVCNTR_EL0 (vectorUpdate (← readReg PMEVCNTR_EL0) pmselr_el0 tempxt))
      else (pure ()))
  else (pure ())
  bif (Bool.and (Bool.and (Bool.and (BEq.beq op0 3) (BEq.beq op1 3)) (BEq.beq crn 14))
       (BEq.beq (integer_subrange crm 3 2) (0b11 : (BitVec 2))))
  then
    (do
      let index := (BitVec.toNat ((integer_subrange crm 1 0) ++ (integer_subrange op2 2 0)))
      bif (BEq.beq index 31)
      then writeReg PMCCFILTR_EL0 (__get_PMCCFILTR_EL0 (Mk_PMCCFILTR_EL0_Type tempxt))
      else
        writeReg PMEVTYPER_EL0 (vectorUpdate (← readReg PMEVTYPER_EL0) index
          (__get_PMEVTYPER_EL0 (Mk_PMEVTYPER_EL0_Type tempxt))))
  else (pure ())
  bif (Bool.and
       (Bool.and (Bool.and (Bool.and (BEq.beq op0 3) (BEq.beq crn 9)) (BEq.beq op1 3))
         (BEq.beq op2 4)) (BEq.beq crm 12))
  then (AArch64_PMUSwIncrement (Sail.BitVec.extractLsb tempxt 31 0))
  else (pure ())
  bif (Bool.and
       (Bool.and (Bool.and (Bool.and (BEq.beq op0 2) (BEq.beq crn 0)) (BEq.beq op1 3))
         (BEq.beq op2 0)) (BEq.beq crm 5))
  then
    (do
      (DBGDSCRint_write
        (_update_DBGDSCRint_Type_TXfull (← (DBGDSCRint_read ())) (0b1 : (BitVec 1))))
      writeReg MDCCSR_EL0 (Sail.BitVec.updateSubrange (← readReg MDCCSR_EL0) 29 29
        (0b1 : (BitVec 1)))
      (DBGDSCRext_write
        (_update_DBGDSCRext_Type_TXfull (← (DBGDSCRext_read ())) (0b1 : (BitVec 1))))
      (EDSCR_write (_update_EDSCR_Type_TXfull (← (EDSCR_read ())) (0b1 : (BitVec 1)))))
  else (pure ())
  bif (Bool.and
       (Bool.and (Bool.and (Bool.and (BEq.beq op0 2) (BEq.beq crn 0)) (BEq.beq op1 3))
         (BEq.beq op2 0)) (BEq.beq crm 4))
  then
    (do
      (DBGDSCRint_write
        (_update_DBGDSCRint_Type_TXfull (← (DBGDSCRint_read ())) (0b1 : (BitVec 1))))
      writeReg MDCCSR_EL0 (Sail.BitVec.updateSubrange (← readReg MDCCSR_EL0) 29 29
        (0b1 : (BitVec 1)))
      (DBGDSCRext_write
        (_update_DBGDSCRext_Type_TXfull (← (DBGDSCRext_read ())) (0b1 : (BitVec 1))))
      (EDSCR_write (_update_EDSCR_Type_TXfull (← (EDSCR_read ())) (0b1 : (BitVec 1))))
      writeReg DBGDTRTX_EL0 (Sail.BitVec.updateSubrange (← readReg DBGDTRTX_EL0) 31 0
        (BitVec.slice (← (DBGDTR_EL0_read__1 ())) 0 32))
      writeReg DBGDTRRX_EL0 (Sail.BitVec.updateSubrange (← readReg DBGDTRRX_EL0) 31 0
        (BitVec.slice (← (DBGDTR_EL0_read__1 ())) 32 32)))
  else (pure ())
  bif (Bool.and
       (Bool.and (Bool.and (Bool.and (BEq.beq op0 3) (BEq.beq crn 12)) (BEq.beq op1 4))
         (BEq.beq op2 7)) (BEq.beq crm 11))
  then
    (do
      writeReg ICV_PMR_EL1 (Sail.BitVec.updateSubrange (← readReg ICV_PMR_EL1) 7 0
        (_get_ICH_VMCR_EL2_Type_VPMR (← readReg ICH_VMCR_EL2)))
      writeReg ICV_BPR0_EL1 (Sail.BitVec.updateSubrange (← readReg ICV_BPR0_EL1) 2 0
        (_get_ICH_VMCR_EL2_Type_VBPR0 (← readReg ICH_VMCR_EL2)))
      writeReg ICV_BPR1_EL1 (Sail.BitVec.updateSubrange (← readReg ICV_BPR1_EL1) 2 0
        (_get_ICH_VMCR_EL2_Type_VBPR1 (← readReg ICH_VMCR_EL2)))
      writeReg ICV_IGRPEN0_EL1 (Sail.BitVec.updateSubrange (← readReg ICV_IGRPEN0_EL1) 0 0
        (_get_ICH_VMCR_EL2_Type_VENG0 (← readReg ICH_VMCR_EL2)))
      writeReg ICV_IGRPEN1_EL1 (Sail.BitVec.updateSubrange (← readReg ICV_IGRPEN1_EL1) 0 0
        (_get_ICH_VMCR_EL2_Type_VENG1 (← readReg ICH_VMCR_EL2)))
      writeReg ICV_CTLR_EL1 (Sail.BitVec.updateSubrange (← readReg ICV_CTLR_EL1) 1 1
        (_get_ICH_VMCR_EL2_Type_VEOIM (← readReg ICH_VMCR_EL2)))
      writeReg ICV_CTLR_EL1 (Sail.BitVec.updateSubrange (← readReg ICV_CTLR_EL1) 0 0
        (_get_ICH_VMCR_EL2_Type_VCBPR (← readReg ICH_VMCR_EL2))))
  else (pure ())
  bif (Bool.and
       (Bool.and (Bool.and (Bool.and (BEq.beq op0 3) (BEq.beq crn 4)) (BEq.beq op1 0))
         (BEq.beq op2 0)) (BEq.beq crm 6))
  then
    writeReg ICH_VMCR_EL2 (Sail.BitVec.updateSubrange (← readReg ICH_VMCR_EL2) 31 24
      (_get_ICV_PMR_EL1_Type_Priority (← readReg ICV_PMR_EL1)))
  else (pure ())
  bif (Bool.and
       (Bool.and (Bool.and (Bool.and (BEq.beq op0 3) (BEq.beq crn 12)) (BEq.beq op1 0))
         (BEq.beq op2 3)) (BEq.beq crm 8))
  then
    writeReg ICH_VMCR_EL2 (Sail.BitVec.updateSubrange (← readReg ICH_VMCR_EL2) 23 21
      (_get_ICV_BPR0_EL1_Type_BinaryPoint (← readReg ICV_BPR0_EL1)))
  else (pure ())
  bif (Bool.and
       (Bool.and (Bool.and (Bool.and (BEq.beq op0 3) (BEq.beq crn 12)) (BEq.beq op1 0))
         (BEq.beq op2 3)) (BEq.beq crm 12))
  then
    writeReg ICH_VMCR_EL2 (Sail.BitVec.updateSubrange (← readReg ICH_VMCR_EL2) 20 18
      (_get_ICV_BPR1_EL1_Type_BinaryPoint (← readReg ICV_BPR1_EL1)))
  else (pure ())
  bif (Bool.and
       (Bool.and (Bool.and (Bool.and (BEq.beq op0 3) (BEq.beq crn 12)) (BEq.beq op1 0))
         (BEq.beq op2 4)) (BEq.beq crm 12))
  then
    (do
      writeReg ICH_VMCR_EL2 (Sail.BitVec.updateSubrange (← readReg ICH_VMCR_EL2) 9 9
        (_get_ICV_CTLR_EL1_Type_EOImode (← readReg ICV_CTLR_EL1)))
      writeReg ICH_VMCR_EL2 (Sail.BitVec.updateSubrange (← readReg ICH_VMCR_EL2) 4 4
        (_get_ICV_CTLR_EL1_Type_CBPR (← readReg ICV_CTLR_EL1))))
  else (pure ())
  bif (Bool.and
       (Bool.and (Bool.and (Bool.and (BEq.beq op0 3) (BEq.beq crn 12)) (BEq.beq op1 0))
         (BEq.beq op2 6)) (BEq.beq crm 12))
  then
    writeReg ICH_VMCR_EL2 (Sail.BitVec.updateSubrange (← readReg ICH_VMCR_EL2) 0 0
      (_get_ICV_IGRPEN0_EL1_Type_Enable (← readReg ICV_IGRPEN0_EL1)))
  else (pure ())
  bif (Bool.and
       (Bool.and (Bool.and (Bool.and (BEq.beq op0 3) (BEq.beq crn 12)) (BEq.beq op1 0))
         (BEq.beq op2 7)) (BEq.beq crm 12))
  then
    writeReg ICH_VMCR_EL2 (Sail.BitVec.updateSubrange (← readReg ICH_VMCR_EL2) 1 1
      (_get_ICV_IGRPEN1_EL1_Type_Enable (← readReg ICV_IGRPEN1_EL1)))
  else (pure ())

/-- Type quantifiers: crm : Int, crn : Int, op0 : Int, op1 : Int, op2 : Int, t : Int -/
def AArch64_SysInstr (op0 : Int) (op1 : Int) (crn : Int) (crm : Int) (op2 : Int) (t : Int) : SailM Unit := do
  (AArch64_AutoGen_SysOpsWrite (← readReg PSTATE).EL (integer_subrange op0 1 0)
    (integer_subrange op1 2 0) (integer_subrange crn 3 0) (integer_subrange op2 2 0)
    (integer_subrange crm 3 0) t)

/-- Type quantifiers: crm : Int, crn : Int, op0 : Int, op1 : Int, op2 : Int, t : Int -/
def AArch64_SysInstrWithResult (op0 : Int) (op1 : Int) (crn : Int) (crm : Int) (op2 : Int) (t : Int) : SailM Unit := do
  (AArch64_AutoGen_SysInstrWithResult (← readReg PSTATE).EL (integer_subrange op0 1 0)
    (integer_subrange op1 2 0) (integer_subrange crn 3 0) (integer_subrange op2 2 0)
    (integer_subrange crm 3 0) t)

/-- Type quantifiers: crm : Int, crn : Int, op0 : Int, op1 : Int, op2 : Int, t : Int, t2 : Int -/
def AArch64_SysRegRead128 (op0 : Int) (op1 : Int) (crn : Int) (crm : Int) (op2 : Int) (t : Int) (t2 : Int) : SailM Unit := do
  (AArch64_AutoGen_SysRegRead128 (← readReg PSTATE).EL (integer_subrange op0 1 0)
    (integer_subrange op1 2 0) (integer_subrange crn 3 0) (integer_subrange op2 2 0)
    (integer_subrange crm 3 0) t t2)

/-- Type quantifiers: crm : Int, crn : Int, op0 : Int, op1 : Int, op2 : Int, t : Int, t2 : Int -/
def AArch64_SysRegWrite128 (op0 : Int) (op1 : Int) (crn : Int) (crm : Int) (op2 : Int) (t : Int) (t2 : Int) : SailM Unit := do
  (AArch64_AutoGen_SysRegWrite128 (← readReg PSTATE).EL (integer_subrange op0 1 0)
    (integer_subrange op1 2 0) (integer_subrange crn 3 0) (integer_subrange op2 2 0)
    (integer_subrange crm 3 0) t t2)

/-- Type quantifiers: crm : Int, crn : Int, op0 : Int, op1 : Int, op2 : Int, t : Int, t2 : Int -/
def AArch64_SysInstr128 (op0 : Int) (op1 : Int) (crn : Int) (crm : Int) (op2 : Int) (t : Int) (t2 : Int) : SailM Unit := do
  (AArch64_AutoGen_SysOpsWrite128 (← readReg PSTATE).EL (integer_subrange op0 1 0)
    (integer_subrange op1 2 0) (integer_subrange crn 3 0) (integer_subrange op2 2 0)
    (integer_subrange crm 3 0) t t2)

/-- Type quantifiers: cp_num : Int -/
def AArch32_SysRegRead (cp_num : Int) (instr : (BitVec 32)) (address : (BitVec 32)) : SailM Unit := do
  let CRd : (BitVec 4) := (Sail.BitVec.extractLsb instr 15 12)
  bif (Bool.and (BEq.beq CRd (0x5 : (BitVec 4)))
       ((BEq.beq cp_num (BitVec.toNat (0xE : (BitVec 4)))) : Bool))
  then (AArch32_STC (integer_subrange cp_num 3 0) CRd address)
  else (pure ())

/-- Type quantifiers: cp_num : Int, t : Int -/
def AArch32_SysRegRead__1 (cp_num : Int) (instr : (BitVec 32)) (t : Int) : SailM Unit := do
  let el ← (( do (undefined_bitvector 2) ) : SailM (BitVec 2) )
  let index ← (( do (undefined_int ()) ) : SailM Int )
  let n ← (( do (undefined_int ()) ) : SailM Int )
  let (_, __tup_1) ← do (ELFromM32 (← readReg PSTATE).M)
  let el : (BitVec 2) := __tup_1
  (pure ())
  let opc1 : (BitVec 3) := (BitVec.slice instr 21 3)
  let CRn : (BitVec 4) := (BitVec.slice instr 16 4)
  let CRm : (BitVec 4) := (BitVec.slice instr 0 4)
  let opc2 : (BitVec 3) := (BitVec.slice instr 5 3)
  let opc2 : (BitVec 3) :=
    bif (Bool.and
         (Bool.and
           (Bool.and (Bool.and (BEq.beq cp_num 15) (BEq.beq opc1 (0b000 : (BitVec 3))))
             (Bool.or (BEq.beq opc2 (0b100 : (BitVec 3))) (BEq.beq opc2 (0b111 : (BitVec 3)))))
           (BEq.beq CRn (0x0 : (BitVec 4)))) (BEq.beq CRm (0x0 : (BitVec 4))))
    then (0b000 : (BitVec 3))
    else opc2
  bif (Bool.and (Bool.and (BEq.beq cp_num 15) (BEq.beq opc1 (0b000 : (BitVec 3))))
       (BEq.beq CRn (0xD : (BitVec 4))))
  then
    (do
      let n := (BitVec.toNat ((BitVec.join1 [(BitVec.access CRm 0)]) ++ opc2))
      bif (BEq.beq (Sail.BitVec.extractLsb CRm 3 1) (0b011 : (BitVec 3)))
      then
        (do
          bif (n ≥b (BitVec.toNat (_get_AMCGCR_Type_CG0NC (← (AMCGCR_read ())))))
          then sailThrow ((Error_Undefined ()))
          else (pure ()))
      else (pure ())
      bif (BEq.beq (Sail.BitVec.extractLsb CRm 3 1) (0b111 : (BitVec 3)))
      then
        (do
          bif (n ≥b (BitVec.toNat (_get_AMCGCR_Type_CG1NC (← (AMCGCR_read ())))))
          then sailThrow ((Error_Undefined ()))
          else (pure ()))
      else (pure ()))
  else (pure ())
  bif (Bool.and
       (Bool.and
         (Bool.and (Bool.and (BEq.beq cp_num 15) (BEq.beq opc1 (0b000 : (BitVec 3))))
           (BEq.beq CRn (0xE : (BitVec 4))))
         (Bool.or (BEq.beq (Sail.BitVec.extractLsb CRm 3 2) (0b10 : (BitVec 2)))
           (BEq.beq (Sail.BitVec.extractLsb CRm 3 2) (0b11 : (BitVec 2)))))
       (bne ((Sail.BitVec.extractLsb CRm 1 0) ++ (Sail.BitVec.extractLsb opc2 2 0))
         (0b11111 : (BitVec 5))))
  then
    (do
      bif (Bool.or
           ((BitVec.toNat ((Sail.BitVec.extractLsb CRm 1 0) ++ (Sail.BitVec.extractLsb opc2 2 0))) >b ((← (GetNumEventCounters
                   ())) -i 1))
           (Bool.and
             (Bool.and (← (EL2Enabled ()))
               (Bool.or (BEq.beq (← readReg PSTATE).EL EL1)
                 (Bool.and (BEq.beq (← readReg PSTATE).EL EL0)
                   (Bool.or
                     (Bool.and (BEq.beq (Sail.BitVec.extractLsb CRm 3 2) (0b10 : (BitVec 2)))
                       (bne
                         ((_get_PMUSERENR_EL0_Type_ER (← readReg PMUSERENR_EL0)) ++ (_get_PMUSERENR_EL0_Type_EN
                             (← readReg PMUSERENR_EL0))) (0b00 : (BitVec 2))))
                     (Bool.and (BEq.beq (Sail.BitVec.extractLsb CRm 3 2) (0b11 : (BitVec 2)))
                       (BEq.beq (_get_PMUSERENR_EL0_Type_EN (← readReg PMUSERENR_EL0))
                         (0b1 : (BitVec 1))))))))
             (← do
               (pure ((BitVec.toNat
                     ((Sail.BitVec.extractLsb CRm 1 0) ++ (Sail.BitVec.extractLsb opc2 2 0))) >b ((← (AArch32_GetNumEventCountersAccessible
                         ())) -i 1))))))
      then
        (do
          bif ((BitVec.toNat ((Sail.BitVec.extractLsb CRm 1 0) ++ (Sail.BitVec.extractLsb opc2 2 0))) >b ((← (GetNumEventCounters
                     ())) -i 1))
          then sailThrow ((Error_Undefined ()))
          else
            (do
              bif (← (ELUsingAArch32 EL2))
              then (AArch32_TakeHypTrapException (BitVec.toNat (0x03 : (BitVec 8))))
              else (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat (0x03 : (BitVec 8))))))
      else (pure ()))
  else (pure ())
  bif (Bool.and
       (Bool.and
         (Bool.and
           (Bool.and (Bool.and (BEq.beq cp_num 15) (BEq.beq opc1 (0b000 : (BitVec 3))))
             (BEq.beq CRn (0x9 : (BitVec 4)))) (BEq.beq CRm (0xD : (BitVec 4))))
         (Bool.or (BEq.beq opc2 (0b001 : (BitVec 3))) (BEq.beq opc2 (0b010 : (BitVec 3)))))
       (bne (_get_PMSELR_EL0_Type_SEL (← readReg PMSELR_EL0)) (0b11111 : (BitVec 5))))
  then
    (do
      bif (Bool.or
           ((BitVec.toNat (_get_PMSELR_EL0_Type_SEL (← readReg PMSELR_EL0))) >b ((← (GetNumEventCounters
                   ())) -i 1))
           (Bool.and
             (Bool.and (← (EL2Enabled ()))
               (Bool.or (BEq.beq (← readReg PSTATE).EL EL1)
                 (Bool.and (BEq.beq (← readReg PSTATE).EL EL0)
                   (Bool.or
                     (Bool.and (BEq.beq opc2 (0b010 : (BitVec 3)))
                       (bne
                         ((_get_PMUSERENR_EL0_Type_ER (← readReg PMUSERENR_EL0)) ++ (_get_PMUSERENR_EL0_Type_EN
                             (← readReg PMUSERENR_EL0))) (0b00 : (BitVec 2))))
                     (Bool.and (BEq.beq opc2 (0b001 : (BitVec 3)))
                       (BEq.beq (_get_PMUSERENR_EL0_Type_EN (← readReg PMUSERENR_EL0))
                         (0b1 : (BitVec 1))))))))
             (← do
               (pure ((BitVec.toNat (_get_PMSELR_Type_SEL (← (PMSELR_read ())))) >b ((← (AArch32_GetNumEventCountersAccessible
                         ())) -i 1))))))
      then
        (do
          bif ((BitVec.toNat (_get_PMSELR_Type_SEL (← (PMSELR_read ())))) >b ((← (GetNumEventCounters
                     ())) -i 1))
          then sailThrow ((Error_Undefined ()))
          else
            (do
              bif (← (ELUsingAArch32 EL2))
              then (AArch32_TakeHypTrapException (BitVec.toNat (0x03 : (BitVec 8))))
              else (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat (0x03 : (BitVec 8))))))
      else (pure ()))
  else (pure ())
  let temp ← (( do (R_read t) ) : SailM (BitVec 32) )
  (AArch32_AutoGen_SysRegRead32 el (integer_subrange cp_num 3 0) opc1 CRn opc2 CRm t)
  bif (Bool.and
       (Bool.and
         (Bool.and (Bool.and (BEq.beq cp_num 15) (BEq.beq opc1 (0b000 : (BitVec 3))))
           (BEq.beq CRn (0x9 : (BitVec 4))))
         (Bool.or (BEq.beq CRm (0xC : (BitVec 4))) (BEq.beq CRm (0xE : (BitVec 4)))))
       (Bool.or (BEq.beq opc2 (0b001 : (BitVec 3)))
         (Bool.or (BEq.beq opc2 (0b010 : (BitVec 3))) (BEq.beq opc2 (0b011 : (BitVec 3))))))
  then
    (do
      let mask ← (( do (pure (Sail.BitVec.extractLsb (← (PMUCounterMask ())) 31 0)) ) : SailM
        (BitVec 32) )
      (R_set t ((← (R_read t)) &&& mask)))
  else (pure ())
  bif (Bool.and
       (Bool.and
         (Bool.and (Bool.and (BEq.beq cp_num 15) (BEq.beq opc1 (0b000 : (BitVec 3))))
           (BEq.beq CRn (0x9 : (BitVec 4)))) (BEq.beq CRm (0xD : (BitVec 4))))
       (Bool.or (BEq.beq opc2 (0b001 : (BitVec 3))) (BEq.beq opc2 (0b010 : (BitVec 3)))))
  then
    (do
      bif (BEq.beq opc2 (0b001 : (BitVec 3)))
      then
        (do
          let pmselr ← do (pure (BitVec.toNat (_get_PMSELR_Type_SEL (← (PMSELR_read ())))))
          bif (Bool.and
               (Bool.and
                 (Bool.and (← (EL2Enabled ()))
                   (Bool.or (BEq.beq (← readReg PSTATE).EL EL0)
                     (BEq.beq (← readReg PSTATE).EL EL1)))
                 (bne (_get_PMSELR_Type_SEL (← (PMSELR_read ()))) (0b11111 : (BitVec 5))))
               (← do
                 (pure ((BitVec.toNat (_get_PMSELR_Type_SEL (← (PMSELR_read ())))) >b ((← (AArch32_GetNumEventCountersAccessible
                           ())) -i 1)))))
          then
            (do
              bif ((BitVec.toNat (_get_PMSELR_Type_SEL (← (PMSELR_read ())))) >b ((← (GetNumEventCounters
                         ())) -i 1))
              then
                (do
                  (R_set t temp)
                  sailThrow ((Error_Undefined ())))
              else
                (do
                  bif (← (ELUsingAArch32 EL2))
                  then
                    (do
                      (R_set t temp)
                      (AArch32_TakeHypTrapException (BitVec.toNat (0x03 : (BitVec 8)))))
                  else
                    (do
                      (R_set t temp)
                      (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat (0x03 : (BitVec 8)))))))
          else
            (do
              bif (BEq.beq pmselr 31)
              then (R_set t (← (PMCCFILTR_read ())))
              else (R_set t (← (PMEVTYPER_read pmselr)))))
      else (pure ())
      bif (BEq.beq opc2 (0b010 : (BitVec 3)))
      then
        (do
          bif (Bool.or
               ((BitVec.toNat (_get_PMSELR_Type_SEL (← (PMSELR_read ())))) >b ((← (GetNumEventCounters
                       ())) -i 1))
               (Bool.and
                 (Bool.and (← (EL2Enabled ()))
                   (Bool.or (BEq.beq (← readReg PSTATE).EL EL0)
                     (BEq.beq (← readReg PSTATE).EL EL1)))
                 (← do
                   (pure ((BitVec.toNat (_get_PMSELR_Type_SEL (← (PMSELR_read ())))) >b ((← (AArch32_GetNumEventCountersAccessible
                             ())) -i 1))))))
          then
            (do
              bif ((BitVec.toNat (_get_PMSELR_Type_SEL (← (PMSELR_read ())))) >b ((← (GetNumEventCounters
                         ())) -i 1))
              then
                (do
                  (R_set t temp)
                  sailThrow ((Error_Undefined ())))
              else
                (do
                  bif (← (ELUsingAArch32 EL2))
                  then
                    (do
                      (R_set t temp)
                      (AArch32_TakeHypTrapException (BitVec.toNat (0x03 : (BitVec 8)))))
                  else
                    (do
                      (R_set t temp)
                      (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat (0x03 : (BitVec 8)))))))
          else
            (do
              let pmselr ← do (pure (BitVec.toNat (_get_PMSELR_Type_SEL (← (PMSELR_read ())))))
              assert (pmselr <b 31) "src/sysregs.sail:1058.34-1058.35"
              (R_set t (Sail.BitVec.extractLsb (← (PMEVCNTR_read pmselr)) 31 0))))
      else (pure ()))
  else (pure ())
  bif (Bool.and
       (Bool.and
         (Bool.and (Bool.and (BEq.beq cp_num 15) (BEq.beq opc1 (0b000 : (BitVec 3))))
           (BEq.beq opc2 (0b000 : (BitVec 3)))) (BEq.beq CRn (0x9 : (BitVec 4))))
       (BEq.beq CRm (0xC : (BitVec 4))))
  then
    (R_set t
      (Sail.BitVec.updateSubrange (← (R_read t)) 15 11
        (integer_subrange (← (AArch32_GetNumEventCountersAccessible ())) 4 0)))
  else (pure ())
  bif (Bool.and
       (Bool.and (Bool.and (BEq.beq cp_num 15) (BEq.beq opc1 (0b000 : (BitVec 3))))
         (BEq.beq CRn (0xE : (BitVec 4))))
       (Bool.or (BEq.beq (Sail.BitVec.extractLsb CRm 3 2) (0b10 : (BitVec 2)))
         (Bool.and (BEq.beq (Sail.BitVec.extractLsb CRm 3 2) (0b11 : (BitVec 2)))
           (bne ((Sail.BitVec.extractLsb CRm 1 0) ++ (Sail.BitVec.extractLsb opc2 2 0))
             (0b11111 : (BitVec 5))))))
  then
    (do
      bif (Bool.or
           ((BitVec.toNat ((Sail.BitVec.extractLsb CRm 1 0) ++ (Sail.BitVec.extractLsb opc2 2 0))) >b ((← (GetNumEventCounters
                   ())) -i 1))
           (Bool.and
             (Bool.and (← (EL2Enabled ()))
               (Bool.or (BEq.beq (← readReg PSTATE).EL EL0) (BEq.beq (← readReg PSTATE).EL EL1)))
             (← do
               (pure ((BitVec.toNat
                     ((Sail.BitVec.extractLsb CRm 1 0) ++ (Sail.BitVec.extractLsb opc2 2 0))) >b ((← (AArch32_GetNumEventCountersAccessible
                         ())) -i 1))))))
      then
        (do
          bif ((BitVec.toNat ((Sail.BitVec.extractLsb CRm 1 0) ++ (Sail.BitVec.extractLsb opc2 2 0))) >b ((← (GetNumEventCounters
                     ())) -i 1))
          then
            (do
              (R_set t temp)
              sailThrow ((Error_Undefined ())))
          else
            (do
              bif (← (ELUsingAArch32 EL2))
              then
                (do
                  (R_set t temp)
                  (AArch32_TakeHypTrapException (BitVec.toNat (0x03 : (BitVec 8)))))
              else
                (do
                  (R_set t temp)
                  (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat (0x03 : (BitVec 8)))))))
      else (pure ()))
  else (pure ())
  bif (Bool.and
       (Bool.and (Bool.and (BEq.beq cp_num 14) (BEq.beq opc1 (0b000 : (BitVec 3))))
         (BEq.beq opc2 (0b110 : (BitVec 3)))) (BEq.beq CRn (0x7 : (BitVec 4))))
  then
    (do
      bif (BEq.beq CRm (0x8 : (BitVec 4)))
      then (R_set t (Sail.BitVec.updateSubrange (← (R_read t)) 7 0 (0xFF : (BitVec 8))))
      else (pure ())
      bif (BEq.beq CRm (0x9 : (BitVec 4)))
      then
        (R_set t
          (Sail.BitVec.updateSubrange (← (R_read t)) 7 0
            (Sail.BitVec.extractLsb (← (DBGCLAIMCLR_read ())) 7 0)))
      else (pure ()))
  else
    (do
      bif (Bool.and
           (Bool.and
             (Bool.and (Bool.and (BEq.beq cp_num 14) (BEq.beq opc1 (0b000 : (BitVec 3))))
               (BEq.beq opc2 (0b010 : (BitVec 3)))) (BEq.beq CRn (0x0 : (BitVec 4))))
           (BEq.beq CRm (0x2 : (BitVec 4))))
      then
        (do
          (R_set t
            (Sail.BitVec.updateSubrange (← (R_read t)) 18 18
              (← do
                bif (BEq.beq (← (CurrentSecurityState ())) SS_NonSecure)
                then (pure (0b1 : (BitVec 1)))
                else (pure (0b0 : (BitVec 1))))))
          bif (HaveEL EL3)
          then
            (do
              bif (Bool.and (← (ELUsingAArch32 EL3))
                   (BEq.beq (_get_SDCR_Type_SPME (← readReg SDCR)) (0b1 : (BitVec 1))))
              then (R_set t (Sail.BitVec.updateSubrange (← (R_read t)) 17 17 (0b0 : (BitVec 1))))
              else
                (do
                  bif (Bool.and (Bool.not (← (ELUsingAArch32 EL3)))
                       (BEq.beq (_get_MDCR_EL3_Type_SPME (← readReg MDCR_EL3)) (0b1 : (BitVec 1))))
                  then
                    (R_set t (Sail.BitVec.updateSubrange (← (R_read t)) 17 17 (0b0 : (BitVec 1))))
                  else
                    (R_set t (Sail.BitVec.updateSubrange (← (R_read t)) 17 17 (0b1 : (BitVec 1))))))
          else (pure ()))
      else
        (do
          bif (Bool.and
               (Bool.and
                 (Bool.and (Bool.and (BEq.beq cp_num 15) (BEq.beq opc1 (0b000 : (BitVec 3))))
                   (BEq.beq opc2 (0b000 : (BitVec 3)))) (BEq.beq CRn (0xC : (BitVec 4))))
               (BEq.beq CRm (0x1 : (BitVec 4))))
          then
            (do
              (R_set t (← (getISR ()))))
          else
            (do
              bif (Bool.and
                   (Bool.and
                     (Bool.and (Bool.and (BEq.beq cp_num 15) (BEq.beq opc1 (0b001 : (BitVec 3))))
                       (Bool.or (BEq.beq opc2 (0b000 : (BitVec 3)))
                         (BEq.beq opc2 (0b010 : (BitVec 3))))) (BEq.beq CRn (0x0 : (BitVec 4))))
                   (BEq.beq CRm (0x0 : (BitVec 4))))
              then
                (do
                  bif (BEq.beq opc2 (0b000 : (BitVec 3)))
                  then
                    (do
                      (R_set t
                        (Sail.BitVec.extractLsb
                          (← (CacheConfigRead (Sail.BitVec.extractLsb (← (CSSELR_read ())) 3 0)))
                          31 0)))
                  else
                    (do
                      (R_set t
                        (Sail.BitVec.extractLsb
                          (← (CacheConfigRead (Sail.BitVec.extractLsb (← (CSSELR_read ())) 3 0)))
                          63 32))))
              else
                (do
                  bif (Bool.and
                       (Bool.and
                         (Bool.and
                           (Bool.and (BEq.beq cp_num 15) (BEq.beq opc1 (0b000 : (BitVec 3))))
                           (BEq.beq CRn (0x5 : (BitVec 4)))) (BEq.beq CRm (0x4 : (BitVec 4))))
                       (Bool.or (BEq.beq opc2 (0b000 : (BitVec 3)))
                         (BEq.beq opc2 (0b100 : (BitVec 3)))))
                  then
                    (do
                      bif (Bool.or
                           (BEq.beq (BitVec.toNat (_get_ERRIDR_Type_NUM (← (ERRIDR_read ()))))
                             (BitVec.toNat (0x0 : (BitVec 4))))
                           (← do
                             (pure ((BitVec.toNat (_get_ERRSELR_Type_SEL (← (ERRSELR_read ())))) ≥b (BitVec.toNat
                                   (_get_ERRIDR_Type_NUM (← (ERRIDR_read ()))))))))
                      then (R_set t (Zeros (n := 32)))
                      else
                        (do
                          let index ← do
                            (pure (BitVec.toNat (_get_ERRSELR_Type_SEL (← (ERRSELR_read ())))))
                          bif (BEq.beq opc2 (0b000 : (BitVec 3)))
                          then
                            (do
                              assert (Bool.and (0 ≤b index) (index <b 4)) "src/sysregs.sail:1125.61-1125.62"
                              (R_set t
                                (Sail.BitVec.extractLsb
                                  (GetElem?.getElem! (← readReg ERRnFR) index) 31 0)))
                          else
                            (do
                              assert (Bool.and (0 ≤b index) (index <b 4)) "src/sysregs.sail:1128.61-1128.62"
                              (R_set t
                                (Sail.BitVec.extractLsb
                                  (GetElem?.getElem! (← readReg ERRnFR) index) 63 32)))))
                  else (pure ())
                  bif (Bool.and
                       (Bool.and
                         (Bool.and
                           (Bool.and (BEq.beq cp_num 14) (BEq.beq opc1 (0b000 : (BitVec 3))))
                           (BEq.beq CRn (0x0 : (BitVec 4)))) (BEq.beq CRm (0x5 : (BitVec 4))))
                       (BEq.beq opc2 (0b000 : (BitVec 3))))
                  then
                    (do
                      (DBGDSCRint_write
                        (_update_DBGDSCRint_Type_RXfull (← (DBGDSCRint_read ()))
                          (0b0 : (BitVec 1))))
                      writeReg MDCCSR_EL0 (Sail.BitVec.updateSubrange (← readReg MDCCSR_EL0) 30 30
                        (0b0 : (BitVec 1)))
                      (DBGDSCRext_write
                        (_update_DBGDSCRext_Type_RXfull (← (DBGDSCRext_read ()))
                          (0b0 : (BitVec 1))))
                      (EDSCR_write
                        (_update_EDSCR_Type_RXfull (← (EDSCR_read ())) (0b0 : (BitVec 1)))))
                  else (pure ())
                  bif (Bool.and
                       (Bool.and
                         (Bool.and
                           (Bool.and (BEq.beq cp_num 15) (BEq.beq opc1 (0b000 : (BitVec 3))))
                           (BEq.beq CRn (0x1 : (BitVec 4)))) (BEq.beq CRm (0x0 : (BitVec 4))))
                       (BEq.beq opc2 (0b010 : (BitVec 3))))
                  then
                    (do
                      bif (Bool.and
                           (Bool.and
                             (Bool.and (BEq.beq (← (CurrentSecurityState ())) SS_NonSecure)
                               (HaveEL EL3)) (← (ELUsingAArch32 EL3)))
                           (BEq.beq (_get_NSACR_Type_cp10 (← readReg NSACR)) (0b0 : (BitVec 1))))
                      then
                        (R_set t
                          (Sail.BitVec.updateSubrange (← (R_read t)) 23 20 (0x0 : (BitVec 4))))
                      else (pure ()))
                  else (pure ())))))

/-- Type quantifiers: cp_num : Int -/
def AArch32_SysRegWriteM (cp_num : Int) (instr : (BitVec 32)) (address : (BitVec 32)) : SailM Unit := do
  let CRd : (BitVec 4) := (Sail.BitVec.extractLsb instr 15 12)
  bif (Bool.and (BEq.beq CRd (0x5 : (BitVec 4)))
       ((BEq.beq cp_num (BitVec.toNat (0xE : (BitVec 4)))) : Bool))
  then (AArch32_LDC (integer_subrange cp_num 3 0) CRd address)
  else (pure ())

/-- Type quantifiers: cp_num : Int, t : Int, t2 : Int -/
def AArch32_SysRegRead64 (cp_num : Int) (instr : (BitVec 32)) (t : Int) (t2 : Int) : SailM Unit := do
  let el ← (( do (undefined_bitvector 2) ) : SailM (BitVec 2) )
  let n ← (( do (undefined_int ()) ) : SailM Int )
  let (_, __tup_1) ← do (ELFromM32 (← readReg PSTATE).M)
  let el : (BitVec 2) := __tup_1
  (pure ())
  let opc1 : (BitVec 4) := (BitVec.slice instr 4 4)
  let CRm : (BitVec 4) := (BitVec.slice instr 0 4)
  bif (Bool.and
       (Bool.and (BEq.beq cp_num 15)
         (let b__0 := (Sail.BitVec.extractLsb CRm 3 1)
         bif (Bool.and (BEq.beq (Sail.BitVec.extractLsb b__0 2 2) (0b0 : (BitVec 1)))
              (BEq.beq (Sail.BitVec.extractLsb b__0 0 0) (0b0 : (BitVec 1))))
         then true
         else false : Bool)) (BEq.beq (BitVec.join1 [(BitVec.access opc1 3)]) (0b0 : (BitVec 1))))
  then
    (do
      let n :=
        (BitVec.toNat ((BitVec.join1 [(BitVec.access CRm 0)]) ++ (Sail.BitVec.extractLsb opc1 2 0)))
      bif (BEq.beq (Sail.BitVec.extractLsb CRm 3 1) (0b000 : (BitVec 3)))
      then
        (do
          bif (n ≥b (BitVec.toNat (_get_AMCGCR_Type_CG0NC (← (AMCGCR_read ())))))
          then sailThrow ((Error_Undefined ()))
          else (pure ()))
      else
        (do
          bif (BEq.beq (Sail.BitVec.extractLsb CRm 3 1) (0b010 : (BitVec 3)))
          then
            (do
              bif (n ≥b (BitVec.toNat (_get_AMCGCR_Type_CG1NC (← (AMCGCR_read ())))))
              then sailThrow ((Error_Undefined ()))
              else (pure ()))
          else (pure ())))
  else (pure ())
  (AArch32_AutoGen_SysRegRead64 el (integer_subrange cp_num 3 0) opc1 CRm t t2)

/-- Type quantifiers: cp_num : Int, t : Int -/
def AArch32_SysRegWrite (cp_num : Int) (instr : (BitVec 32)) (t : Int) : SailM Unit := do
  let el ← (( do (undefined_bitvector 2) ) : SailM (BitVec 2) )
  let temprt ← (( do (R_read t) ) : SailM (BitVec 32) )
  let (_, __tup_1) ← do (ELFromM32 (← readReg PSTATE).M)
  let el : (BitVec 2) := __tup_1
  (pure ())
  let opc1 : (BitVec 3) := (BitVec.slice instr 21 3)
  let CRn : (BitVec 4) := (BitVec.slice instr 16 4)
  let CRm : (BitVec 4) := (BitVec.slice instr 0 4)
  let opc2 : (BitVec 3) := (BitVec.slice instr 5 3)
  let temprt : (BitVec 32) :=
    bif (Bool.and
         (Bool.and (Bool.and (BEq.beq cp_num 14) (BEq.beq opc1 (0b000 : (BitVec 3))))
           (BEq.beq CRn (0x0 : (BitVec 4)))) (BEq.beq opc2 (0b101 : (BitVec 3))))
    then
      (let temprt : (BitVec 32) :=
        (BitVec.update temprt 8 (Bit (BitVec.join1 [(BitVec.access temprt 7)])))
      (BitVec.update temprt 6 (Bit (BitVec.join1 [(BitVec.access temprt 5)]))))
    else temprt
  let temprt ← (( do
    bif (Bool.and
         (Bool.and
           (Bool.and (Bool.and (BEq.beq cp_num 15) (BEq.beq opc1 (0b000 : (BitVec 3))))
             (BEq.beq CRn (0x1 : (BitVec 4)))) (BEq.beq CRm (0x0 : (BitVec 4))))
         (BEq.beq opc2 (0b010 : (BitVec 3))))
    then
      (do
        bif (Bool.and
             (Bool.and
               (Bool.and (BEq.beq (← (CurrentSecurityState ())) SS_NonSecure) (HaveEL EL3))
               (← (ELUsingAArch32 EL3)))
             (BEq.beq (_get_NSACR_Type_cp10 (← readReg NSACR)) (0b0 : (BitVec 1))))
        then
          (do
            let temprt ←
              (pure (Sail.BitVec.updateSubrange temprt 23 22
                  (_get_CPACR_Type_cp11 (← (CPACR_read__1 ())))))
            (pure (Sail.BitVec.updateSubrange temprt 21 20
                (_get_CPACR_Type_cp10 (← (CPACR_read__1 ()))))))
        else (pure temprt))
    else (pure temprt) ) : SailM (BitVec 32) )
  let temprt ← (( do
    bif (Bool.and
         (Bool.and
           (Bool.and (Bool.and (BEq.beq cp_num 15) (BEq.beq opc1 (0b000 : (BitVec 3))))
             (BEq.beq CRn (0x9 : (BitVec 4))))
           (Bool.or (BEq.beq CRm (0xC : (BitVec 4))) (BEq.beq CRm (0xE : (BitVec 4)))))
         (Bool.or (BEq.beq opc2 (0b001 : (BitVec 3)))
           (Bool.or (BEq.beq opc2 (0b010 : (BitVec 3))) (BEq.beq opc2 (0b011 : (BitVec 3))))))
    then
      (do
        let mask ← (( do (pure (Sail.BitVec.extractLsb (← (PMUCounterMask ())) 31 0)) ) : SailM
          (BitVec 32) )
        let temprt ← (( do
          bif (Bool.and (BEq.beq opc2 (0b011 : (BitVec 3))) (BEq.beq CRm (0xC : (BitVec 4))))
          then
            (do
              (pure ((← (PMOVSSET_read ())) &&& (Complement.complement (temprt &&& mask)))))
          else (pure temprt) ) : SailM (BitVec 32) )
        let temprt ← (( do
          bif (Bool.and (BEq.beq opc2 (0b011 : (BitVec 3))) (BEq.beq CRm (0xE : (BitVec 4))))
          then
            (do
              (pure ((← (PMOVSSET_read ())) ||| (temprt &&& mask))))
          else (pure temprt) ) : SailM (BitVec 32) )
        let temprt ← (( do
          bif (Bool.and (BEq.beq opc2 (0b010 : (BitVec 3))) (BEq.beq CRm (0xC : (BitVec 4))))
          then
            (do
              (pure ((← (PMCNTENSET_read ())) &&& (Complement.complement (temprt &&& mask)))))
          else (pure temprt) ) : SailM (BitVec 32) )
        let temprt ← (( do
          bif (Bool.and (BEq.beq opc2 (0b001 : (BitVec 3))) (BEq.beq CRm (0xC : (BitVec 4))))
          then
            (do
              (pure ((← (PMCNTENSET_read ())) ||| (temprt &&& mask))))
          else (pure temprt) ) : SailM (BitVec 32) )
        let temprt ← (( do
          bif (Bool.and (BEq.beq opc2 (0b010 : (BitVec 3))) (BEq.beq CRm (0xE : (BitVec 4))))
          then
            (do
              (pure ((← (PMINTENSET_read ())) &&& (Complement.complement (temprt &&& mask)))))
          else (pure temprt) ) : SailM (BitVec 32) )
        bif (Bool.and (BEq.beq opc2 (0b001 : (BitVec 3))) (BEq.beq CRm (0xE : (BitVec 4))))
        then
          (do
            (pure ((← (PMINTENSET_read ())) ||| (temprt &&& mask))))
        else (pure temprt))
    else (pure temprt) ) : SailM (BitVec 32) )
  bif (Bool.and
       (Bool.and
         (Bool.and (Bool.and (BEq.beq cp_num 15) (BEq.beq opc1 (0b000 : (BitVec 3))))
           (BEq.beq opc2 (0b000 : (BitVec 3)))) (BEq.beq CRn (0x9 : (BitVec 4))))
       (BEq.beq CRm (0xC : (BitVec 4))))
  then
    (do
      bif (Bool.and (BEq.beq (BitVec.join1 [(BitVec.access temprt 3)]) (0b1 : (BitVec 1)))
           (BEq.beq (_get_PMCR_Type_D (← (PMCR_read ()))) (0b0 : (BitVec 1))))
      then writeReg __clock_divider 63
      else (pure ()))
  else (pure ())
  bif (Bool.and
       (Bool.and (Bool.and (BEq.beq cp_num 15) (BEq.beq opc1 (0b000 : (BitVec 3))))
         (BEq.beq CRn (0xE : (BitVec 4))))
       (Bool.or (BEq.beq (Sail.BitVec.extractLsb CRm 3 2) (0b10 : (BitVec 2)))
         (Bool.and (BEq.beq (Sail.BitVec.extractLsb CRm 3 2) (0b11 : (BitVec 2)))
           (bne ((Sail.BitVec.extractLsb CRm 1 0) ++ (Sail.BitVec.extractLsb opc2 2 0))
             (0b11111 : (BitVec 5))))))
  then
    (do
      bif (Bool.or
           (Bool.and
             ((BitVec.toNat ((Sail.BitVec.extractLsb CRm 1 0) ++ (Sail.BitVec.extractLsb opc2 2 0))) >b ((← (GetNumEventCounters
                     ())) -i 1))
             (bne ((Sail.BitVec.extractLsb CRm 1 0) ++ (Sail.BitVec.extractLsb opc2 2 0))
               (0b11111 : (BitVec 5))))
           (Bool.and
             (Bool.and
               (Bool.and (← (EL2Enabled ()))
                 (Bool.or (BEq.beq (← readReg PSTATE).EL EL0)
                   (BEq.beq (← readReg PSTATE).EL EL1)))
               (BEq.beq (_get_PMUSERENR_EL0_Type_EN (← readReg PMUSERENR_EL0)) (0b1 : (BitVec 1))))
             (← do
               (pure ((BitVec.toNat
                     ((Sail.BitVec.extractLsb CRm 1 0) ++ (Sail.BitVec.extractLsb opc2 2 0))) >b ((← (AArch32_GetNumEventCountersAccessible
                         ())) -i 1))))))
      then
        (do
          bif ((BitVec.toNat ((Sail.BitVec.extractLsb CRm 1 0) ++ (Sail.BitVec.extractLsb opc2 2 0))) >b ((← (GetNumEventCounters
                     ())) -i 1))
          then sailThrow ((Error_Undefined ()))
          else
            (do
              bif (← (ELUsingAArch32 EL2))
              then (AArch32_TakeHypTrapException (BitVec.toNat (0x03 : (BitVec 8))))
              else (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat (0x03 : (BitVec 8))))))
      else (pure ()))
  else (pure ())
  bif (Bool.and
       (Bool.and
         (Bool.and (Bool.and (BEq.beq cp_num 15) (BEq.beq opc1 (0b000 : (BitVec 3))))
           (BEq.beq CRn (0x9 : (BitVec 4)))) (BEq.beq CRm (0xD : (BitVec 4))))
       (Bool.or
         (Bool.and (BEq.beq opc2 (0b001 : (BitVec 3)))
           (bne (_get_PMSELR_Type_SEL (← (PMSELR_read ()))) (0b11111 : (BitVec 5))))
         (BEq.beq opc2 (0b010 : (BitVec 3)))))
  then
    (do
      bif (Bool.or
           (Bool.and
             ((BitVec.toNat (_get_PMSELR_Type_SEL (← (PMSELR_read ())))) >b ((← (GetNumEventCounters
                     ())) -i 1))
             (bne (_get_PMSELR_Type_SEL (← (PMSELR_read ()))) (0b11111 : (BitVec 5))))
           (Bool.and
             (Bool.and
               (Bool.and (← (EL2Enabled ()))
                 (Bool.or (BEq.beq (← readReg PSTATE).EL EL0)
                   (BEq.beq (← readReg PSTATE).EL EL1)))
               (BEq.beq (_get_PMUSERENR_EL0_Type_EN (← readReg PMUSERENR_EL0)) (0b1 : (BitVec 1))))
             (← do
               (pure ((BitVec.toNat (_get_PMSELR_Type_SEL (← (PMSELR_read ())))) >b ((← (AArch32_GetNumEventCountersAccessible
                         ())) -i 1))))))
      then
        (do
          bif ((BitVec.toNat (_get_PMSELR_Type_SEL (← (PMSELR_read ())))) >b ((← (GetNumEventCounters
                     ())) -i 1))
          then sailThrow ((Error_Undefined ()))
          else
            (do
              bif (← (ELUsingAArch32 EL2))
              then (AArch32_TakeHypTrapException (BitVec.toNat (0x03 : (BitVec 8))))
              else (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat (0x03 : (BitVec 8))))))
      else (pure ()))
  else (pure ())
  let temprt ← (( do
    bif (Bool.and
         (Bool.and (Bool.and (BEq.beq cp_num 14) (BEq.beq opc1 (0b000 : (BitVec 3))))
           (BEq.beq opc2 (0b110 : (BitVec 3)))) (BEq.beq CRn (0x7 : (BitVec 4))))
    then
      (do
        let temprt ← (( do
          bif (BEq.beq CRm (0x8 : (BitVec 4)))
          then
            (do
              (pure (Sail.BitVec.updateSubrange temprt 7 0
                  ((Sail.BitVec.extractLsb (← (DBGCLAIMCLR_read ())) 7 0) ||| (Sail.BitVec.extractLsb
                      temprt 7 0)))))
          else (pure temprt) ) : SailM (BitVec 32) )
        bif (BEq.beq CRm (0x9 : (BitVec 4)))
        then
          (do
            (pure (Sail.BitVec.updateSubrange temprt 7 0
                ((Sail.BitVec.extractLsb (← (DBGCLAIMCLR_read ())) 7 0) &&& (Complement.complement
                    (Sail.BitVec.extractLsb temprt 7 0))))))
        else (pure temprt))
    else (pure temprt) ) : SailM (BitVec 32) )
  let temprt2 ← (( do (R_read t) ) : SailM (BitVec 32) )
  (R_set t temprt)
  (AArch32_AutoGen_SysRegWrite32 el (integer_subrange cp_num 3 0) opc1 CRn opc2 CRm t)
  (R_set t temprt2)
  bif (Bool.and
       (Bool.and
         (Bool.and (Bool.and (BEq.beq cp_num 14) (BEq.beq opc1 (0b000 : (BitVec 3))))
           (BEq.beq opc2 (0b110 : (BitVec 3)))) (BEq.beq CRn (0x7 : (BitVec 4))))
       (BEq.beq CRm (0x8 : (BitVec 4))))
  then
    (DBGCLAIMCLR_write
      (Mk_DBGCLAIMCLR_Type
        (Sail.BitVec.updateSubrange (← (DBGCLAIMCLR_read ())) 7 0
          (Sail.BitVec.extractLsb temprt 7 0))))
  else (pure ())
  bif (Bool.and
       (Bool.and
         (Bool.and (Bool.and (BEq.beq cp_num 14) (BEq.beq opc1 (0b000 : (BitVec 3))))
           (BEq.beq opc2 (0b100 : (BitVec 3)))) (BEq.beq CRn (0x1 : (BitVec 4))))
       (BEq.beq CRm (0x0 : (BitVec 4))))
  then
    (do
      bif (BEq.beq (BitVec.toNat temprt) (BitVec.toNat (0xC5ACCE55 : (BitVec 32))))
      then
        (do
          (DBGOSLSR_write (_update_DBGOSLSR_Type_OSLK (← (DBGOSLSR_read ())) (0b1 : (BitVec 1))))
          writeReg EDPRSR (Sail.BitVec.updateSubrange (← readReg EDPRSR) 5 5 (0b1 : (BitVec 1)))
          writeReg OSLSR_EL1 (Sail.BitVec.updateSubrange (← readReg OSLSR_EL1) 1 1
            (0b1 : (BitVec 1))))
      else
        (do
          bif (BEq.beq (_get_DBGOSLSR_Type_OSLK (← (DBGOSLSR_read ()))) (0b1 : (BitVec 1)))
          then
            (do
              (DBGOSLSR_write
                (_update_DBGOSLSR_Type_OSLK (← (DBGOSLSR_read ())) (0b0 : (BitVec 1))))
              writeReg EDPRSR (Sail.BitVec.updateSubrange (← readReg EDPRSR) 5 5
                (0b0 : (BitVec 1)))
              writeReg OSLSR_EL1 (Sail.BitVec.updateSubrange (← readReg OSLSR_EL1) 1 1
                (0b0 : (BitVec 1)))
              (CheckOSUnlockCatch ()))
          else (pure ())))
  else (pure ())
  bif (Bool.and
       (Bool.and
         (Bool.and (Bool.and (BEq.beq cp_num 15) (BEq.beq opc1 (0b000 : (BitVec 3))))
           (BEq.beq CRn (0x9 : (BitVec 4))))
         (Bool.or (BEq.beq CRm (0xC : (BitVec 4))) (BEq.beq CRm (0xE : (BitVec 4)))))
       (Bool.or (BEq.beq opc2 (0b001 : (BitVec 3)))
         (Bool.or (BEq.beq opc2 (0b010 : (BitVec 3))) (BEq.beq opc2 (0b011 : (BitVec 3))))))
  then
    (do
      bif (Bool.and (BEq.beq opc2 (0b011 : (BitVec 3))) (BEq.beq CRm (0xC : (BitVec 4))))
      then (PMOVSSET_write (Mk_PMOVSSET_Type temprt))
      else (pure ())
      bif (Bool.and (BEq.beq opc2 (0b011 : (BitVec 3))) (BEq.beq CRm (0xE : (BitVec 4))))
      then (PMOVSR_write (Mk_PMOVSR_Type temprt))
      else (pure ())
      bif (Bool.and (BEq.beq opc2 (0b010 : (BitVec 3))) (BEq.beq CRm (0xC : (BitVec 4))))
      then (PMCNTENSET_write (Mk_PMCNTENSET_Type temprt))
      else (pure ())
      bif (Bool.and (BEq.beq opc2 (0b001 : (BitVec 3))) (BEq.beq CRm (0xC : (BitVec 4))))
      then (PMCNTENCLR_write (Mk_PMCNTENCLR_Type temprt))
      else (pure ())
      bif (Bool.and (BEq.beq opc2 (0b010 : (BitVec 3))) (BEq.beq CRm (0xE : (BitVec 4))))
      then (PMINTENSET_write (Mk_PMINTENSET_Type temprt))
      else (pure ())
      bif (Bool.and (BEq.beq opc2 (0b001 : (BitVec 3))) (BEq.beq CRm (0xE : (BitVec 4))))
      then (PMINTENCLR_write (Mk_PMINTENCLR_Type temprt))
      else (pure ()))
  else (pure ())
  bif (Bool.and
       (Bool.and
         (Bool.and (Bool.and (BEq.beq cp_num 15) (BEq.beq opc1 (0b000 : (BitVec 3))))
           (BEq.beq opc2 (0b000 : (BitVec 3)))) (BEq.beq CRn (0x9 : (BitVec 4))))
       (BEq.beq CRm (0xC : (BitVec 4))))
  then
    (do
      bif (BEq.beq (BitVec.join1 [(BitVec.access temprt 2)]) (0b1 : (BitVec 1)))
      then (PMCCNTR_write (Mk_PMCCNTR_Type (Zeros (n := 64))))
      else (pure ())
      bif (BEq.beq (BitVec.join1 [(BitVec.access temprt 1)]) (0b1 : (BitVec 1)))
      then (AArch32_ClearEventCounters ())
      else (pure ()))
  else (pure ())
  bif (Bool.and
       (Bool.and
         (Bool.and (Bool.and (BEq.beq cp_num 15) (BEq.beq opc1 (0b000 : (BitVec 3))))
           (BEq.beq CRn (0x9 : (BitVec 4)))) (BEq.beq CRm (0xD : (BitVec 4))))
       (Bool.or (BEq.beq opc2 (0b001 : (BitVec 3))) (BEq.beq opc2 (0b010 : (BitVec 3)))))
  then
    (do
      let pmselr ← do (pure (BitVec.toNat (_get_PMSELR_Type_SEL (← (PMSELR_read ())))))
      bif (BEq.beq opc2 (0b001 : (BitVec 3)))
      then
        (do
          bif (BEq.beq pmselr 31)
          then (PMCCFILTR_write (__get_PMCCFILTR (Mk_PMCCFILTR_Type temprt)))
          else (PMEVTYPER_set pmselr (__get_PMEVTYPER (Mk_PMEVTYPER_Type temprt))))
      else (pure ())
      bif (BEq.beq opc2 (0b010 : (BitVec 3)))
      then
        (do
          assert (pmselr <b 31) "src/sysregs.sail:1330.30-1330.31"
          (PMEVCNTR_set pmselr temprt))
      else (pure ()))
  else (pure ())
  bif (Bool.and
       (Bool.and (Bool.and (BEq.beq cp_num 15) (BEq.beq opc1 (0b000 : (BitVec 3))))
         (BEq.beq CRn (0xE : (BitVec 4))))
       (BEq.beq (Sail.BitVec.extractLsb CRm 3 2) (0b11 : (BitVec 2))))
  then
    (do
      let index :=
        (BitVec.toNat ((Sail.BitVec.extractLsb CRm 1 0) ++ (Sail.BitVec.extractLsb opc2 2 0)))
      bif (BEq.beq index 31)
      then (PMCCFILTR_write (__get_PMCCFILTR (Mk_PMCCFILTR_Type temprt)))
      else (PMEVTYPER_set index (__get_PMEVTYPER (Mk_PMEVTYPER_Type temprt))))
  else (pure ())
  bif (Bool.and
       (Bool.and
         (Bool.and (Bool.and (BEq.beq cp_num 15) (BEq.beq opc1 (0b000 : (BitVec 3))))
           (BEq.beq opc2 (0b100 : (BitVec 3)))) (BEq.beq CRn (0x9 : (BitVec 4))))
       (BEq.beq CRm (0xC : (BitVec 4))))
  then (AArch32_PMUSwIncrement temprt)
  else (pure ())
  bif (Bool.and
       (Bool.and
         (Bool.and
           (Bool.and
             (Bool.and (BEq.beq cp_num 15)
               (Bool.or (BEq.beq opc1 (0b000 : (BitVec 3))) (BEq.beq opc1 (0b100 : (BitVec 3)))))
             (BEq.beq CRn (0xC : (BitVec 4)))) (BEq.beq opc2 (0b010 : (BitVec 3))))
         (BEq.beq CRm (0x0 : (BitVec 4))))
       (BEq.beq (BitVec.join1 [(BitVec.access temprt 1)]) (0b1 : (BitVec 1))))
  then (TakeReset false)
  else
    (do
      bif (Bool.and
           (Bool.and
             (Bool.and (Bool.and (BEq.beq cp_num 15) (BEq.beq opc1 (0b000 : (BitVec 3))))
               (Bool.or (BEq.beq opc2 (0b100 : (BitVec 3))) (BEq.beq opc2 (0b111 : (BitVec 3)))))
             (BEq.beq CRn (0x0 : (BitVec 4)))) (BEq.beq CRm (0x0 : (BitVec 4))))
      then (MIDR_write (Mk_MIDR_Type temprt))
      else (pure ()))
  bif (Bool.and
       (Bool.and
         (Bool.and (Bool.and (BEq.beq cp_num 14) (BEq.beq opc1 (0b000 : (BitVec 3))))
           (BEq.beq CRn (0x0 : (BitVec 4)))) (BEq.beq opc2 (0b000 : (BitVec 3))))
       (BEq.beq CRm (0x5 : (BitVec 4))))
  then
    (do
      (DBGDSCRint_write
        (_update_DBGDSCRint_Type_TXfull (← (DBGDSCRint_read ())) (0b1 : (BitVec 1))))
      writeReg MDCCSR_EL0 (Sail.BitVec.updateSubrange (← readReg MDCCSR_EL0) 29 29
        (0b1 : (BitVec 1)))
      (DBGDSCRext_write
        (_update_DBGDSCRext_Type_TXfull (← (DBGDSCRext_read ())) (0b1 : (BitVec 1))))
      (EDSCR_write (_update_EDSCR_Type_TXfull (← (EDSCR_read ())) (0b1 : (BitVec 1)))))
  else (pure ())

/-- Type quantifiers: cp_num : Int, t : Int, t2 : Int -/
def AArch32_SysRegWrite64 (cp_num : Int) (instr : (BitVec 32)) (t : Int) (t2 : Int) : SailM Unit := do
  let el ← (( do (undefined_bitvector 2) ) : SailM (BitVec 2) )
  let n ← (( do (undefined_int ()) ) : SailM Int )
  let (_, __tup_1) ← do (ELFromM32 (← readReg PSTATE).M)
  let el : (BitVec 2) := __tup_1
  (pure ())
  let opc1 : (BitVec 4) := (BitVec.slice instr 4 4)
  let CRm : (BitVec 4) := (BitVec.slice instr 0 4)
  bif (Bool.and
       (Bool.and (BEq.beq cp_num 15)
         (let b__0 := (Sail.BitVec.extractLsb CRm 3 1)
         bif (Bool.and (BEq.beq (Sail.BitVec.extractLsb b__0 2 2) (0b0 : (BitVec 1)))
              (BEq.beq (Sail.BitVec.extractLsb b__0 0 0) (0b0 : (BitVec 1))))
         then true
         else false : Bool)) (BEq.beq (BitVec.join1 [(BitVec.access opc1 3)]) (0b0 : (BitVec 1))))
  then
    (do
      let n :=
        (BitVec.toNat ((BitVec.join1 [(BitVec.access CRm 0)]) ++ (Sail.BitVec.extractLsb opc1 2 0)))
      bif (BEq.beq (Sail.BitVec.extractLsb CRm 3 1) (0b000 : (BitVec 3)))
      then
        (do
          bif (n ≥b (BitVec.toNat (_get_AMCGCR_Type_CG0NC (← (AMCGCR_read ())))))
          then sailThrow ((Error_Undefined ()))
          else (pure ()))
      else
        (do
          bif (BEq.beq (Sail.BitVec.extractLsb CRm 3 1) (0b010 : (BitVec 3)))
          then
            (do
              bif (n ≥b (BitVec.toNat (_get_AMCGCR_Type_CG1NC (← (AMCGCR_read ())))))
              then sailThrow ((Error_Undefined ()))
              else (pure ()))
          else (pure ())))
  else (pure ())
  (AArch32_AutoGen_SysRegWrite64 el (integer_subrange cp_num 3 0) opc1 CRm t t2)

