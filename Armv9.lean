import Armv9.EventClauses

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

def initialize_registers (_ : Unit) : SailM Unit := do
  writeReg SEE (← (undefined_int ()))
  writeReg FeatureImpl (← (undefined_vector 259 (← (undefined_bool ()))))
  writeReg VariantImplemented (← (undefined_vector 16 (← (undefined_bool ()))))
  writeReg __trcclaim_tags (← (undefined_bitvector 32))
  writeReg __cycle_count (← (undefined_int ()))
  writeReg CP15SDISABLE (← (undefined_Signal ()))
  writeReg CP15SDISABLE2 (← (undefined_Signal ()))
  writeReg IsWFIsleep (← (undefined_bool ()))
  writeReg IsWFEsleep (← (undefined_bool ()))
  writeReg _ConfigReg (← (undefined_Configuration_Type ()))
  writeReg _DormantCtlReg (← (undefined_DormantCtl_Type ()))
  writeReg PMUEventAccumulator (← (undefined_vector 31 (← (undefined_int ()))))
  writeReg PMULastThresholdValue (← (undefined_vector 31 (← (undefined_bool ()))))
  writeReg __clock_divider (← (undefined_int ()))
  writeReg PSTATE (← (undefined_ProcState ()))
  writeReg ShouldAdvanceIT (← (undefined_bool ()))
  writeReg ShouldAdvanceSS (← (undefined_bool ()))
  writeReg EventRegister (← (undefined_bitvector 1))
  writeReg R0 (← (undefined_bitvector 64))
  writeReg R1 (← (undefined_bitvector 64))
  writeReg R2 (← (undefined_bitvector 64))
  writeReg R3 (← (undefined_bitvector 64))
  writeReg R4 (← (undefined_bitvector 64))
  writeReg R5 (← (undefined_bitvector 64))
  writeReg R6 (← (undefined_bitvector 64))
  writeReg R7 (← (undefined_bitvector 64))
  writeReg R8 (← (undefined_bitvector 64))
  writeReg R9 (← (undefined_bitvector 64))
  writeReg R10 (← (undefined_bitvector 64))
  writeReg R11 (← (undefined_bitvector 64))
  writeReg R12 (← (undefined_bitvector 64))
  writeReg R13 (← (undefined_bitvector 64))
  writeReg R14 (← (undefined_bitvector 64))
  writeReg R15 (← (undefined_bitvector 64))
  writeReg R16 (← (undefined_bitvector 64))
  writeReg R17 (← (undefined_bitvector 64))
  writeReg R18 (← (undefined_bitvector 64))
  writeReg R19 (← (undefined_bitvector 64))
  writeReg R20 (← (undefined_bitvector 64))
  writeReg R21 (← (undefined_bitvector 64))
  writeReg R22 (← (undefined_bitvector 64))
  writeReg R23 (← (undefined_bitvector 64))
  writeReg R24 (← (undefined_bitvector 64))
  writeReg R25 (← (undefined_bitvector 64))
  writeReg R26 (← (undefined_bitvector 64))
  writeReg R27 (← (undefined_bitvector 64))
  writeReg R28 (← (undefined_bitvector 64))
  writeReg R29 (← (undefined_bitvector 64))
  writeReg R30 (← (undefined_bitvector 64))
  writeReg _PC (← (undefined_bitvector 64))
  writeReg PhysicalCount (← (undefined_bitvector 88))
  writeReg RC (← (undefined_vector 5 (← (undefined_bitvector 64))))
  writeReg InGuardedPage (← (undefined_bool ()))
  writeReg BTypeNext (← (undefined_bitvector 2))
  writeReg BTypeCompatible (← (undefined_bool ()))
  writeReg _Z (← (undefined_vector 32 (← (undefined_bitvector 2048))))
  writeReg _P (← (undefined_vector 16 (← (undefined_bitvector 256))))
  writeReg _FFR (← (undefined_bitvector 256))
  writeReg _ZA (← (undefined_vector 256 (← (undefined_bitvector 2048))))
  writeReg _ZT0 (← (undefined_bitvector 512))
  writeReg FPCR (← (undefined_FPCR_Type ()))
  writeReg FPSR (← (undefined_FPSR_Type ()))
  writeReg ICC_PMR_EL1 (← (undefined_ICC_PMR_EL1_Type ()))
  writeReg TSTATE (← (undefined_TMState ()))
  writeReg SPESampleInFlight (← (undefined_bool ()))
  writeReg SPESampleContextEL1 (← (undefined_bitvector 32))
  writeReg SPESampleContextEL1Valid (← (undefined_bool ()))
  writeReg SPESampleContextEL2 (← (undefined_bitvector 32))
  writeReg SPESampleContextEL2Valid (← (undefined_bool ()))
  writeReg SPESampleInstIsNV2 (← (undefined_bool ()))
  writeReg SPESamplePreviousBranchAddress (← (undefined_bitvector 64))
  writeReg SPESamplePreviousBranchAddressValid (← (undefined_bool ()))
  writeReg SPESampleDataSource (← (undefined_bitvector 16))
  writeReg SPESampleDataSourceValid (← (undefined_bool ()))
  writeReg SPESampleOpType (← (undefined_OpType ()))
  writeReg SPESampleClass (← (undefined_bitvector 2))
  writeReg SPESampleSubclass (← (undefined_bitvector 8))
  writeReg SPESampleSubclassValid (← (undefined_bool ()))
  writeReg SPESampleTimestamp (← (undefined_bitvector 64))
  writeReg SPESampleTimestampValid (← (undefined_bool ()))
  writeReg SPESampleEvents (← (undefined_bitvector 64))
  writeReg __SPE_LFSR (← (undefined_bitvector 24))
  writeReg __SPE_LFSR_initialized (← (undefined_bool ()))
  writeReg SPERecordSize (← (undefined_int ()))
  writeReg __last_cycle_count (← (undefined_int ()))
  writeReg __last_branch_valid (← (undefined_bool ()))
  writeReg DBGEN (← (undefined_Signal ()))
  writeReg NIDEN (← (undefined_Signal ()))
  writeReg SPIDEN (← (undefined_Signal ()))
  writeReg SPNIDEN (← (undefined_Signal ()))
  writeReg RLPIDEN (← (undefined_Signal ()))
  writeReg RTPIDEN (← (undefined_Signal ()))
  writeReg __InstructionStep (← (undefined_bool ()))
  writeReg __CNTReadBase (← (undefined_bitvector 56))
  writeReg __CNTBaseN (← (undefined_bitvector 56))
  writeReg __CNTEL0BaseN (← (undefined_bitvector 56))
  writeReg __CNTCTLBase (← (undefined_bitvector 56))
  writeReg __RD_base (← (undefined_bitvector 56))
  writeReg __SGI_base (← (undefined_bitvector 56))
  writeReg __VLPI_base (← (undefined_bitvector 56))
  writeReg __ETEBase (← (undefined_bitvector 56))
  writeReg __ThisInstr (← (undefined_bitvector 32))
  writeReg __ThisInstrEnc (← (undefined___InstrEnc ()))
  writeReg __currentCond (← (undefined_bitvector 4))
  writeReg Branchtypetaken (← (undefined_BranchType ()))
  writeReg __BranchTaken (← (undefined_bool ()))
  writeReg __ExclusiveMonitorSet (← (undefined_bool ()))
  writeReg __highest_el_aarch32 (← (undefined_bool ()))
  writeReg __ICACHE_CCSIDR_RESET (← (undefined_vector 7 (← (undefined_bitvector 64))))
  writeReg __DCACHE_CCSIDR_RESET (← (undefined_vector 7 (← (undefined_bitvector 64))))
  writeReg sp_rel_access_pc (← (undefined_bitvector 64))
  writeReg SP_mon (← (undefined_bitvector 32))
  writeReg LR_mon (← (undefined_bitvector 32))
  writeReg _Dclone (← (undefined_vector 32 (← (undefined_bitvector 64))))
  writeReg HCR_EL2 (← (undefined_HCR_EL2_Type ()))
  writeReg SCR_EL3 (← (undefined_SCR_EL3_Type ()))
  writeReg SCR (← (undefined_SCR_Type ()))
  writeReg _FPSCR (← (undefined_FPSCR_Type ()))
  writeReg RVBAR (← (undefined_bitvector 32))
  writeReg ERRnFR (← (undefined_vector 4 (← (undefined_ERRnFR_ElemType ()))))
  writeReg CTR_EL0 (← (undefined_CTR_EL0_Type ()))
  writeReg MDCR_EL2 (← (undefined_MDCR_EL2_Type ()))
  writeReg _HDCR (← (undefined_HDCR_Type ()))
  writeReg MDCCSR_EL0 (← (undefined_MDCCSR_EL0_Type ()))
  writeReg _EDSCR (← (undefined_EDSCR_Type ()))
  writeReg PMCNTENCLR_EL0 (← (undefined_PMCNTENCLR_EL0_Type ()))
  writeReg _PMCNTENCLR (← (undefined_PMCNTENCLR_Type ()))
  writeReg PMCR_EL0 (← (undefined_PMCR_EL0_Type ()))
  writeReg _PMCR (← (undefined_PMCR_Type ()))
  writeReg PMINTENCLR_EL1 (← (undefined_PMINTENCLR_EL1_Type ()))
  writeReg _PMINTENCLR (← (undefined_PMINTENCLR_Type ()))
  writeReg PMOVSCLR_EL0 (← (undefined_PMOVSCLR_EL0_Type ()))
  writeReg _PMOVSR (← (undefined_PMOVSR_Type ()))
  writeReg MDCR_EL3 (← (undefined_MDCR_EL3_Type ()))
  writeReg PMCCFILTR_EL0 (← (undefined_PMCCFILTR_EL0_Type ()))
  writeReg _PMCCFILTR (← (undefined_PMCCFILTR_Type ()))
  writeReg PMCNTENSET_EL0 (← (undefined_PMCNTENSET_EL0_Type ()))
  writeReg _PMCNTENSET (← (undefined_PMCNTENSET_Type ()))
  writeReg PMEVTYPER_EL0 (← (undefined_vector 32 (← (undefined_PMEVTYPER_EL0_Type ()))))
  writeReg _PMEVTYPER (← (undefined_vector 31 (← (undefined_PMEVTYPER_Type ()))))
  writeReg PMICFILTR_EL0 (← (undefined_PMICFILTR_EL0_Type ()))
  writeReg SDCR (← (undefined_SDCR_Type ()))
  writeReg SDER32_EL2 (← (undefined_SDER32_EL2_Type ()))
  writeReg _SDER32_EL3 (← (undefined_SDER32_EL3_Type ()))
  writeReg _SDER (← (undefined_SDER_Type ()))
  writeReg PMICNTR_EL0 (← (undefined_PMICNTR_EL0_Type ()))
  writeReg PMOVSSET_EL0 (← (undefined_PMOVSSET_EL0_Type ()))
  writeReg BRBCR_EL1 (← (undefined_BRBCR_EL1_Type ()))
  writeReg BRBCR_EL2 (← (undefined_BRBCR_EL2_Type ()))
  writeReg BRBFCR_EL1 (← (undefined_BRBFCR_EL1_Type ()))
  writeReg BRBTS_EL1 (← (undefined_BRBTS_EL1_Type ()))
  writeReg CNTPOFF_EL2 (← (undefined_bitvector 64))
  writeReg CNTVOFF_EL2 (← (undefined_bitvector 64))
  writeReg CNTHCTL_EL2 (← (undefined_CNTHCTL_EL2_Type ()))
  writeReg EDECR (← (undefined_EDECR_Type ()))
  writeReg DLR_EL0 (← (undefined_bitvector 64))
  writeReg _DLR (← (undefined_bitvector 32))
  writeReg DSPSR_EL0 (← (undefined_DSPSR_EL0_Type ()))
  writeReg _DSPSR (← (undefined_DSPSR_Type ()))
  writeReg _DSPSR2 (← (undefined_DSPSR2_Type ()))
  writeReg TCR_EL1 (← (undefined_TCR_EL1_Type ()))
  writeReg TCR_EL2 (← (undefined_TCR_EL2_Type ()))
  writeReg TCR_EL3 (← (undefined_TCR_EL3_Type ()))
  writeReg BRBIDR0_EL1 (← (undefined_BRBIDR0_EL1_Type ()))
  writeReg Records_INF (← (undefined_vector 64 (← (undefined_BRBINFType ()))))
  writeReg Records_SRC (← (undefined_vector 64 (← (undefined_BRBSRCType ()))))
  writeReg Records_TGT (← (undefined_vector 64 (← (undefined_BRBTGTType ()))))
  writeReg PMSIDR_EL1 (← (undefined_PMSIDR_EL1_Type ()))
  writeReg SPESampleAddress (← (undefined_vector 32 (← (undefined_bitvector 64))))
  writeReg SPESampleAddressValid (← (undefined_vector 32 (← (undefined_bool ()))))
  writeReg PMSCR_EL1 (← (undefined_PMSCR_EL1_Type ()))
  writeReg PMSCR_EL2 (← (undefined_PMSCR_EL2_Type ()))
  writeReg PMBLIMITR_EL1 (← (undefined_PMBLIMITR_EL1_Type ()))
  writeReg PMBSR_EL1 (← (undefined_PMBSR_EL1_Type ()))
  writeReg ZCR_EL1 (← (undefined_ZCR_EL1_Type ()))
  writeReg ZCR_EL2 (← (undefined_ZCR_EL2_Type ()))
  writeReg ZCR_EL3 (← (undefined_ZCR_EL3_Type ()))
  writeReg SMCR_EL1 (← (undefined_SMCR_EL1_Type ()))
  writeReg SMCR_EL2 (← (undefined_SMCR_EL2_Type ()))
  writeReg SMCR_EL3 (← (undefined_SMCR_EL3_Type ()))
  writeReg GCSPR_EL0 (← (undefined_GCSPR_EL0_Type ()))
  writeReg GCSPR_EL1 (← (undefined_GCSPR_EL1_Type ()))
  writeReg GCSPR_EL2 (← (undefined_GCSPR_EL2_Type ()))
  writeReg GCSPR_EL3 (← (undefined_GCSPR_EL3_Type ()))
  writeReg CPACR_EL1 (← (undefined_CPACR_EL1_Type ()))
  writeReg CPTR_EL2 (← (undefined_CPTR_EL2_Type ()))
  writeReg CPTR_EL3 (← (undefined_CPTR_EL3_Type ()))
  writeReg _CPACR (← (undefined_CPACR_Type ()))
  writeReg _HCPTR (← (undefined_HCPTR_Type ()))
  writeReg NSACR (← (undefined_NSACR_Type ()))
  writeReg SP_EL0 (← (undefined_bitvector 64))
  writeReg SP_EL1 (← (undefined_bitvector 64))
  writeReg SP_EL2 (← (undefined_bitvector 64))
  writeReg SP_EL3 (← (undefined_bitvector 64))
  writeReg OSDLR_EL1 (← (undefined_OSDLR_EL1_Type ()))
  writeReg _DBGOSDLR (← (undefined_DBGOSDLR_Type ()))
  writeReg DBGPRCR_EL1 (← (undefined_DBGPRCR_EL1_Type ()))
  writeReg _DBGPRCR (← (undefined_DBGPRCR_Type ()))
  writeReg GCSCR_EL1 (← (undefined_GCSCR_EL1_Type ()))
  writeReg GCSCR_EL2 (← (undefined_GCSCR_EL2_Type ()))
  writeReg GCSCR_EL3 (← (undefined_GCSCR_EL3_Type ()))
  writeReg MDSCR_EL1 (← (undefined_MDSCR_EL1_Type ()))
  writeReg OSLSR_EL1 (← (undefined_OSLSR_EL1_Type ()))
  writeReg _DBGOSLSR (← (undefined_DBGOSLSR_Type ()))
  writeReg _HCR (← (undefined_HCR_Type ()))
  writeReg SCTLR_EL2 (← (undefined_SCTLR_EL2_Type ()))
  writeReg _HSCTLR (← (undefined_HSCTLR_Type ()))
  writeReg SCTLR_EL1 (← (undefined_SCTLR_EL1_Type ()))
  writeReg SCTLR_EL3 (← (undefined_SCTLR_EL3_Type ()))
  writeReg _SCTLR_NS (← (undefined_SCTLR_Type ()))
  writeReg SCTLR_S (← (undefined_SCTLR_Type ()))
  writeReg ESR_EL1 (← (undefined_ESR_EL1_Type ()))
  writeReg ESR_EL2 (← (undefined_ESR_EL2_Type ()))
  writeReg ESR_EL3 (← (undefined_ESR_EL3_Type ()))
  writeReg FAR_EL1 (← (undefined_bitvector 64))
  writeReg FAR_EL2 (← (undefined_bitvector 64))
  writeReg FAR_EL3 (← (undefined_bitvector 64))
  writeReg HPFAR_EL2 (← (undefined_HPFAR_EL2_Type ()))
  writeReg MFAR_EL3 (← (undefined_MFAR_EL3_Type ()))
  writeReg PFAR_EL1 (← (undefined_PFAR_EL1_Type ()))
  writeReg PFAR_EL2 (← (undefined_PFAR_EL2_Type ()))
  writeReg ELR_EL1 (← (undefined_bitvector 64))
  writeReg ELR_EL2 (← (undefined_bitvector 64))
  writeReg ELR_EL3 (← (undefined_bitvector 64))
  writeReg SPSR_EL1 (← (undefined_SPSR_EL1_Type ()))
  writeReg SPSR_EL2 (← (undefined_SPSR_EL2_Type ()))
  writeReg SPSR_EL3 (← (undefined_SPSR_EL3_Type ()))
  writeReg SPSR_abt (← (undefined_SPSR_abt_Type ()))
  writeReg SPSR_fiq (← (undefined_SPSR_fiq_Type ()))
  writeReg _SPSR_hyp (← (undefined_SPSR_hyp_Type ()))
  writeReg SPSR_irq (← (undefined_SPSR_irq_Type ()))
  writeReg SPSR_mon (← (undefined_SPSR_mon_Type ()))
  writeReg _SPSR_svc (← (undefined_SPSR_svc_Type ()))
  writeReg SPSR_und (← (undefined_SPSR_und_Type ()))
  writeReg OSECCR_EL1 (← (undefined_OSECCR_EL1_Type ()))
  writeReg _EDECCR (← (undefined_EDECCR_Type ()))
  writeReg EDESR (← (undefined_EDESR_Type ()))
  writeReg VBAR_EL1 (← (undefined_bitvector 64))
  writeReg VBAR_EL2 (← (undefined_bitvector 64))
  writeReg VBAR_EL3 (← (undefined_bitvector 64))
  writeReg _VBAR_NS (← (undefined_bitvector 32))
  writeReg VBAR_S (← (undefined_bitvector 32))
  writeReg GCSCRE0_EL1 (← (undefined_GCSCRE0_EL1_Type ()))
  writeReg HCRX_EL2 (← (undefined_HCRX_EL2_Type ()))
  writeReg MPAM2_EL2 (← (undefined_MPAM2_EL2_Type ()))
  writeReg _MPAM3_EL3 (← (undefined_MPAM3_EL3_Type ()))
  writeReg _MPAM1_EL1 (← (undefined_MPAM1_EL1_Type ()))
  writeReg MPAMIDR_EL1 (← (undefined_MPAMIDR_EL1_Type ()))
  writeReg MPAMHCR_EL2 (← (undefined_MPAMHCR_EL2_Type ()))
  writeReg MPAMVPM0_EL2 (← (undefined_MPAMVPM0_EL2_Type ()))
  writeReg MPAMVPMV_EL2 (← (undefined_MPAMVPMV_EL2_Type ()))
  writeReg MPAMVPM1_EL2 (← (undefined_MPAMVPM1_EL2_Type ()))
  writeReg MPAMVPM2_EL2 (← (undefined_MPAMVPM2_EL2_Type ()))
  writeReg MPAMVPM3_EL2 (← (undefined_MPAMVPM3_EL2_Type ()))
  writeReg MPAMVPM4_EL2 (← (undefined_MPAMVPM4_EL2_Type ()))
  writeReg MPAMVPM5_EL2 (← (undefined_MPAMVPM5_EL2_Type ()))
  writeReg MPAMVPM6_EL2 (← (undefined_MPAMVPM6_EL2_Type ()))
  writeReg MPAMVPM7_EL2 (← (undefined_MPAMVPM7_EL2_Type ()))
  writeReg MPAM0_EL1 (← (undefined_MPAM0_EL1_Type ()))
  writeReg MPAMSM_EL1 (← (undefined_MPAMSM_EL1_Type ()))
  writeReg CLIDR_EL1 (← (undefined_CLIDR_EL1_Type ()))
  writeReg CONTEXTIDR_EL1 (← (undefined_CONTEXTIDR_EL1_Type ()))
  writeReg _TTBCR_NS (← (undefined_TTBCR_Type ()))
  writeReg TTBCR_S (← (undefined_TTBCR_Type ()))
  writeReg _CONTEXTIDR_NS (← (undefined_CONTEXTIDR_Type ()))
  writeReg CONTEXTIDR_S (← (undefined_CONTEXTIDR_Type ()))
  writeReg TTBR0_NS (← (undefined_TTBR0_Type ()))
  writeReg TTBR0_S (← (undefined_TTBR0_Type ()))
  writeReg _TTBR0_EL1 (← (undefined_TTBR0_EL1_Type ()))
  writeReg HTTBR (← (undefined_HTTBR_Type ()))
  writeReg _TTBR0_EL2 (← (undefined_TTBR0_EL2_Type ()))
  writeReg TTBR1_NS (← (undefined_TTBR1_Type ()))
  writeReg TTBR1_S (← (undefined_TTBR1_Type ()))
  writeReg _TTBR1_EL1 (← (undefined_TTBR1_EL1_Type ()))
  writeReg TTBR1_EL2 (← (undefined_TTBR1_EL2_Type ()))
  writeReg _HDFAR (← (undefined_bitvector 32))
  writeReg _HIFAR (← (undefined_bitvector 32))
  writeReg _HPFAR (← (undefined_HPFAR_Type ()))
  writeReg _HSR (← (undefined_HSR_Type ()))
  writeReg _ELR_hyp (← (undefined_bitvector 32))
  writeReg _HVBAR (← (undefined_bitvector 32))
  writeReg MVBAR (← (undefined_MVBAR_Type ()))
  writeReg _DFAR_NS (← (undefined_bitvector 32))
  writeReg _DFAR_S (← (undefined_bitvector 32))
  writeReg _DFSR_NS (← (undefined_DFSR_Type ()))
  writeReg DFSR_S (← (undefined_DFSR_Type ()))
  writeReg IFSR32_EL2 (← (undefined_IFSR32_EL2_Type ()))
  writeReg _IFSR_NS (← (undefined_IFSR_Type ()))
  writeReg IFSR_S (← (undefined_IFSR_Type ()))
  writeReg _DBGDSCRint (← (undefined_DBGDSCRint_Type ()))
  writeReg _DBGDSCRext (← (undefined_DBGDSCRext_Type ()))
  writeReg _HCR2 (← (undefined_HCR2_Type ()))
  writeReg _IFAR_NS (← (undefined_bitvector 32))
  writeReg _IFAR_S (← (undefined_bitvector 32))
  writeReg SCTLR2_EL1 (← (undefined_SCTLR2_EL1_Type ()))
  writeReg SCTLR2_EL2 (← (undefined_SCTLR2_EL2_Type ()))
  writeReg FPEXC32_EL2 (← (undefined_FPEXC32_EL2_Type ()))
  writeReg _FPEXC (← (undefined_FPEXC_Type ()))
  writeReg CNTHP_CTL_EL2 (← (undefined_CNTHP_CTL_EL2_Type ()))
  writeReg _CNTHP_CTL (← (undefined_CNTHP_CTL_Type ()))
  writeReg CNTHP_CVAL_EL2 (← (undefined_CNTHP_CVAL_EL2_Type ()))
  writeReg _CNTHP_CVAL (← (undefined_CNTHP_CVAL_Type ()))
  writeReg CNTP_CTL_EL0 (← (undefined_CNTP_CTL_EL0_Type ()))
  writeReg _CNTP_CTL_NS (← (undefined_CNTP_CTL_Type ()))
  writeReg CNTP_CTL_S (← (undefined_CNTP_CTL_Type ()))
  writeReg CNTP_CVAL_EL0 (← (undefined_CNTP_CVAL_EL0_Type ()))
  writeReg _CNTP_CVAL_NS (← (undefined_CNTP_CVAL_Type ()))
  writeReg CNTP_CVAL_S (← (undefined_CNTP_CVAL_Type ()))
  writeReg CNTV_CTL_EL0 (← (undefined_CNTV_CTL_EL0_Type ()))
  writeReg CNTV_CVAL_EL0 (← (undefined_CNTV_CVAL_EL0_Type ()))
  writeReg CNTHPS_CTL_EL2 (← (undefined_CNTHPS_CTL_EL2_Type ()))
  writeReg CNTHPS_CVAL_EL2 (← (undefined_CNTHPS_CVAL_EL2_Type ()))
  writeReg CNTHVS_CTL_EL2 (← (undefined_CNTHVS_CTL_EL2_Type ()))
  writeReg CNTHVS_CVAL_EL2 (← (undefined_CNTHVS_CVAL_EL2_Type ()))
  writeReg CNTHV_CTL_EL2 (← (undefined_CNTHV_CTL_EL2_Type ()))
  writeReg CNTHV_CVAL_EL2 (← (undefined_CNTHV_CVAL_EL2_Type ()))
  writeReg CNTPS_CTL_EL1 (← (undefined_CNTPS_CTL_EL1_Type ()))
  writeReg CNTPS_CVAL_EL1 (← (undefined_CNTPS_CVAL_EL1_Type ()))
  writeReg CNTCR (← (undefined_CNTCR_Type ()))
  writeReg CNTSCR (← (undefined_CNTSCR_Type ()))
  writeReg CNTKCTL_EL1 (← (undefined_CNTKCTL_EL1_Type ()))
  writeReg GPCCR_EL3 (← (undefined_GPCCR_EL3_Type ()))
  writeReg GPTBR_EL3 (← (undefined_GPTBR_EL3_Type ()))
  writeReg MAIR2_EL1 (← (undefined_MAIR2_EL1_Type ()))
  writeReg MAIR_EL1 (← (undefined_MAIR_EL1_Type ()))
  writeReg PIRE0_EL1 (← (undefined_PIRE0_EL1_Type ()))
  writeReg PIR_EL1 (← (undefined_PIR_EL1_Type ()))
  writeReg TCR2_EL1 (← (undefined_TCR2_EL1_Type ()))
  writeReg MAIR2_EL2 (← (undefined_MAIR2_EL2_Type ()))
  writeReg MAIR_EL2 (← (undefined_MAIR_EL2_Type ()))
  writeReg PIR_EL2 (← (undefined_PIR_EL2_Type ()))
  writeReg TCR2_EL2 (← (undefined_TCR2_EL2_Type ()))
  writeReg PIRE0_EL2 (← (undefined_PIRE0_EL2_Type ()))
  writeReg MAIR2_EL3 (← (undefined_MAIR2_EL3_Type ()))
  writeReg MAIR_EL3 (← (undefined_MAIR_EL3_Type ()))
  writeReg PIR_EL3 (← (undefined_PIR_EL3_Type ()))
  writeReg SCTLR2_EL3 (← (undefined_SCTLR2_EL3_Type ()))
  writeReg TTBR0_EL3 (← (undefined_TTBR0_EL3_Type ()))
  writeReg APIAKeyHi_EL1 (← (undefined_bitvector 64))
  writeReg APIAKeyLo_EL1 (← (undefined_bitvector 64))
  writeReg APIBKeyHi_EL1 (← (undefined_bitvector 64))
  writeReg APIBKeyLo_EL1 (← (undefined_bitvector 64))
  writeReg APDAKeyHi_EL1 (← (undefined_bitvector 64))
  writeReg APDAKeyLo_EL1 (← (undefined_bitvector 64))
  writeReg APDBKeyHi_EL1 (← (undefined_bitvector 64))
  writeReg APDBKeyLo_EL1 (← (undefined_bitvector 64))
  writeReg APGAKeyHi_EL1 (← (undefined_bitvector 64))
  writeReg APGAKeyLo_EL1 (← (undefined_bitvector 64))
  writeReg _CNTKCTL (← (undefined_CNTKCTL_Type ()))
  writeReg GCR_EL1 (← (undefined_GCR_EL1_Type ()))
  writeReg RGSR_EL1 (← (undefined_RGSR_EL1_Type ()))
  writeReg TFSRE0_EL1 (← (undefined_TFSRE0_EL1_Type ()))
  writeReg TFSR_EL1 (← (undefined_TFSR_EL1_Type ()))
  writeReg TFSR_EL2 (← (undefined_TFSR_EL2_Type ()))
  writeReg TFSR_EL3 (← (undefined_TFSR_EL3_Type ()))
  writeReg CONTEXTIDR_EL2 (← (undefined_CONTEXTIDR_EL2_Type ()))
  writeReg DBGBCR_EL1 (← (undefined_vector 64 (← (undefined_DBGBCR_EL1_Type ()))))
  writeReg DBGBVR_EL1 (← (undefined_vector 64 (← (undefined_DBGBVR_EL1_Type ()))))
  writeReg _EDSCR2 (← (undefined_EDSCR2_Type ()))
  writeReg VTCR_EL2 (← (undefined_VTCR_EL2_Type ()))
  writeReg VTTBR (← (undefined_VTTBR_Type ()))
  writeReg _VTTBR_EL2 (← (undefined_VTTBR_EL2_Type ()))
  writeReg DBGWCR_EL1 (← (undefined_vector 64 (← (undefined_DBGWCR_EL1_Type ()))))
  writeReg DBGWVR_EL1 (← (undefined_vector 64 (← (undefined_DBGWVR_EL1_Type ()))))
  writeReg EDWAR (← (undefined_bitvector 64))
  writeReg POR_EL1 (← (undefined_POR_EL1_Type ()))
  writeReg POR_EL2 (← (undefined_POR_EL2_Type ()))
  writeReg POR_EL3 (← (undefined_POR_EL3_Type ()))
  writeReg POR_EL0 (← (undefined_POR_EL0_Type ()))
  writeReg MECID_P0_EL2 (← (undefined_MECID_P0_EL2_Type ()))
  writeReg VMECID_P_EL2 (← (undefined_VMECID_P_EL2_Type ()))
  writeReg MECID_A0_EL2 (← (undefined_MECID_A0_EL2_Type ()))
  writeReg MECID_A1_EL2 (← (undefined_MECID_A1_EL2_Type ()))
  writeReg MECID_P1_EL2 (← (undefined_MECID_P1_EL2_Type ()))
  writeReg MECID_RL_A_EL3 (← (undefined_MECID_RL_A_EL3_Type ()))
  writeReg S2PIR_EL2 (← (undefined_S2PIR_EL2_Type ()))
  writeReg VSTCR_EL2 (← (undefined_VSTCR_EL2_Type ()))
  writeReg VSTTBR_EL2 (← (undefined_VSTTBR_EL2_Type ()))
  writeReg S2POR_EL1 (← (undefined_S2POR_EL1_Type ()))
  writeReg VMECID_A_EL2 (← (undefined_VMECID_A_EL2_Type ()))
  writeReg SPESampleCounterPending (← (undefined_vector 32 (← (undefined_bool ()))))
  writeReg SPESampleCounterValid (← (undefined_vector 32 (← (undefined_bool ()))))
  writeReg RCWMASK_EL1 (← (undefined_RCWMASK_EL1_Type ()))
  writeReg RCWSMASK_EL1 (← (undefined_RCWSMASK_EL1_Type ()))
  writeReg VNCR_EL2 (← (undefined_VNCR_EL2_Type ()))
  writeReg HFGITR_EL2 (← (undefined_HFGITR_EL2_Type ()))
  writeReg DISR_EL1 (← (undefined_DISR_EL1_Type ()))
  writeReg _DISR (← (undefined_DISR_Type ()))
  writeReg VSESR_EL2 (← (undefined_VSESR_EL2_Type ()))
  writeReg _VDFSR (← (undefined_VDFSR_Type ()))
  writeReg VDISR_EL2 (← (undefined_VDISR_EL2_Type ()))
  writeReg _VDISR (← (undefined_VDISR_Type ()))
  writeReg RVBAR_EL1 (← (undefined_RVBAR_EL1_Type ()))
  writeReg RVBAR_EL2 (← (undefined_RVBAR_EL2_Type ()))
  writeReg RVBAR_EL3 (← (undefined_RVBAR_EL3_Type ()))
  writeReg HSTR_EL2 (← (undefined_HSTR_EL2_Type ()))
  writeReg MDSELR_EL1 (← (undefined_MDSELR_EL1_Type ()))
  writeReg PMEVCNTR_EL0 (← (undefined_vector 32 (← (undefined_bitvector 64))))
  writeReg PMCCNTR_EL0 (← (undefined_PMCCNTR_EL0_Type ()))
  writeReg PMSICR_EL1 (← (undefined_PMSICR_EL1_Type ()))
  writeReg PMSIRR_EL1 (← (undefined_PMSIRR_EL1_Type ()))
  writeReg PMBPTR_EL1 (← (undefined_PMBPTR_EL1_Type ()))
  writeReg PMSDSFR_EL1 (← (undefined_PMSDSFR_EL1_Type ()))
  writeReg PMSEVFR_EL1 (← (undefined_PMSEVFR_EL1_Type ()))
  writeReg PMSFCR_EL1 (← (undefined_PMSFCR_EL1_Type ()))
  writeReg PMSLATFR_EL1 (← (undefined_PMSLATFR_EL1_Type ()))
  writeReg PMSNEVFR_EL1 (← (undefined_PMSNEVFR_EL1_Type ()))
  writeReg PMBIDR_EL1 (← (undefined_PMBIDR_EL1_Type ()))
  writeReg SPERecordData (← (undefined_vector 64 (← (undefined_bitvector 8))))
  writeReg SPESampleCounter (← (undefined_vector 32 (← (undefined_int ()))))
  writeReg BRBINFINJ_EL1 (← (undefined_BRBINFINJ_EL1_Type ()))
  writeReg BRBSRCINJ_EL1 (← (undefined_BRBSRCINJ_EL1_Type ()))
  writeReg BRBTGTINJ_EL1 (← (undefined_BRBTGTINJ_EL1_Type ()))
  writeReg DCZID_EL0 (← (undefined_DCZID_EL0_Type ()))
  writeReg _PRRR_NS (← (undefined_PRRR_Type ()))
  writeReg PRRR_S (← (undefined_PRRR_Type ()))
  writeReg _MAIR0_NS (← (undefined_MAIR0_Type ()))
  writeReg _MAIR0_S (← (undefined_MAIR0_Type ()))
  writeReg _NMRR_NS (← (undefined_NMRR_Type ()))
  writeReg NMRR_S (← (undefined_NMRR_Type ()))
  writeReg _MAIR1_NS (← (undefined_MAIR1_Type ()))
  writeReg _MAIR1_S (← (undefined_MAIR1_Type ()))
  writeReg _TTBCR2_NS (← (undefined_TTBCR2_Type ()))
  writeReg TTBCR2_S (← (undefined_TTBCR2_Type ()))
  writeReg _HMAIR0 (← (undefined_HMAIR0_Type ()))
  writeReg _HMAIR1 (← (undefined_HMAIR1_Type ()))
  writeReg _HTCR (← (undefined_HTCR_Type ()))
  writeReg _VTCR (← (undefined_VTCR_Type ()))
  writeReg DACR32_EL2 (← (undefined_DACR32_EL2_Type ()))
  writeReg _DACR_NS (← (undefined_DACR_Type ()))
  writeReg DACR_S (← (undefined_DACR_Type ()))
  writeReg PAR_NS (← (undefined_PAR_Type ()))
  writeReg PAR_S (← (undefined_PAR_Type ()))
  writeReg _PAR_EL1 (← (undefined_PAR_EL1_Type ()))
  writeReg CTILSR (← (undefined_CTILSR_Type ()))
  writeReg EDLSR (← (undefined_EDLSR_Type ()))
  writeReg PMLSR (← (undefined_PMLSR_Type ()))
  writeReg DBGDTRRX_EL0 (← (undefined_bitvector 64))
  writeReg DBGDTRTX_EL0 (← (undefined_bitvector 64))
  writeReg _DBGDTR_EL0 (← (undefined_DBGDTR_EL0_Type ()))
  writeReg EDPRSR (← (undefined_EDPRSR_Type ()))
  writeReg MDCCINT_EL1 (← (undefined_MDCCINT_EL1_Type ()))
  writeReg _DBGDCCINT (← (undefined_DBGDCCINT_Type ()))
  writeReg CTIDEVCTL (← (undefined_CTIDEVCTL_Type ()))
  writeReg EDVIDSR (← (undefined_EDVIDSR_Type ()))
  writeReg PMPCSR (← (undefined_PMPCSR_Type ()))
  writeReg PMVIDSR (← (undefined_PMVIDSR_Type ()))
  writeReg TRFCR_EL2 (← (undefined_TRFCR_EL2_Type ()))
  writeReg _HTRFCR (← (undefined_HTRFCR_Type ()))
  writeReg TRFCR_EL1 (← (undefined_TRFCR_EL1_Type ()))
  writeReg _TRFCR (← (undefined_TRFCR_Type ()))
  writeReg _DBGBCR (← (undefined_vector 16 (← (undefined_DBGBCR_Type ()))))
  writeReg _DBGBVR (← (undefined_vector 16 (← (undefined_DBGBVR_Type ()))))
  writeReg _DBGBXVR (← (undefined_vector 16 (← (undefined_DBGBXVR_Type ()))))
  writeReg DBGVCR32_EL2 (← (undefined_DBGVCR32_EL2_Type ()))
  writeReg _DBGVCR (← (undefined_DBGVCR_Type ()))
  writeReg _DBGWCR (← (undefined_vector 16 (← (undefined_DBGWCR_Type ()))))
  writeReg _DBGWVR (← (undefined_vector 16 (← (undefined_DBGWVR_Type ()))))
  writeReg _HSTR (← (undefined_HSTR_Type ()))
  writeReg _PMEVCNTR (← (undefined_vector 31 (← (undefined_bitvector 32))))
  writeReg _PMOVSSET (← (undefined_PMOVSSET_Type ()))
  writeReg _PMCCNTR (← (undefined_PMCCNTR_Type ()))
  writeReg ID_MMFR2_EL1 (← (undefined_ID_MMFR2_EL1_Type ()))
  writeReg ID_MMFR4_EL1 (← (undefined_ID_MMFR4_EL1_Type ()))
  writeReg ID_AA64MMFR2_EL1 (← (undefined_ID_AA64MMFR2_EL1_Type ()))
  writeReg HDFGRTR_EL2 (← (undefined_HDFGRTR_EL2_Type ()))
  writeReg ICV_NMIAR1_EL1 (← (undefined_ICV_NMIAR1_EL1_Type ()))
  writeReg ICH_LR_EL2 (← (undefined_vector 16 (← (undefined_ICH_LR_EL2_Type ()))))
  writeReg MVFR0_EL1 (← (undefined_MVFR0_EL1_Type ()))
  writeReg ICC_HPPIR1_EL1 (← (undefined_ICC_HPPIR1_EL1_Type ()))
  writeReg ICC_AP0R_EL1 (← (undefined_vector 4 (← (undefined_bitvector 64))))
  writeReg ID_AA64DFR0_EL1 (← (undefined_ID_AA64DFR0_EL1_Type ()))
  writeReg ICV_BPR1_EL1 (← (undefined_ICV_BPR1_EL1_Type ()))
  writeReg ID_ISAR2_EL1 (← (undefined_ID_ISAR2_EL1_Type ()))
  writeReg PMECR_EL1 (← (undefined_PMECR_EL1_Type ()))
  writeReg AIDR_EL1 (← (undefined_bitvector 64))
  writeReg ICV_EOIR1_EL1 (← (undefined_ICV_EOIR1_EL1_Type ()))
  writeReg RMR_EL1 (← (undefined_RMR_EL1_Type ()))
  writeReg OSLAR_EL1 (← (undefined_OSLAR_EL1_Type ()))
  writeReg ICC_HPPIR0_EL1 (← (undefined_ICC_HPPIR0_EL1_Type ()))
  writeReg HAFGRTR_EL2 (← (undefined_HAFGRTR_EL2_Type ()))
  writeReg ICC_BPR0_EL1 (← (undefined_ICC_BPR0_EL1_Type ()))
  writeReg ID_AA64DFR1_EL1 (← (undefined_ID_AA64DFR1_EL1_Type ()))
  writeReg ACCDATA_EL1 (← (undefined_ACCDATA_EL1_Type ()))
  writeReg REVIDR_EL1 (← (undefined_bitvector 64))
  writeReg PMSSCR_EL1 (← (undefined_PMSSCR_EL1_Type ()))
  writeReg LORID_EL1 (← (undefined_LORID_EL1_Type ()))
  writeReg TPIDR_EL2 (← (undefined_bitvector 64))
  writeReg CNTP_TVAL_EL0 (← (undefined_CNTP_TVAL_EL0_Type ()))
  writeReg ID_AA64ISAR1_EL1 (← (undefined_ID_AA64ISAR1_EL1_Type ()))
  writeReg ID_AA64MMFR4_EL1 (← (undefined_ID_AA64MMFR4_EL1_Type ()))
  writeReg ACTLR_EL2 (← (undefined_bitvector 64))
  writeReg ICH_EISR_EL2 (← (undefined_ICH_EISR_EL2_Type ()))
  writeReg MIDR_EL1 (← (undefined_MIDR_EL1_Type ()))
  writeReg ICC_RPR_EL1 (← (undefined_ICC_RPR_EL1_Type ()))
  writeReg ICH_ELRSR_EL2 (← (undefined_ICH_ELRSR_EL2_Type ()))
  writeReg ICC_SGI0R_EL1 (← (undefined_ICC_SGI0R_EL1_Type ()))
  writeReg SPMACCESSR_EL1 (← (undefined_SPMACCESSR_EL1_Type ()))
  writeReg SPMSELR_EL0 (← (undefined_SPMSELR_EL0_Type ()))
  writeReg ID_AA64PFR1_EL1 (← (undefined_ID_AA64PFR1_EL1_Type ()))
  writeReg ID_AA64PFR0_EL1 (← (undefined_ID_AA64PFR0_EL1_Type ()))
  writeReg ICH_AP1R_EL2 (← (undefined_vector 4 (← (undefined_ICH_AP1R_EL2_Type ()))))
  writeReg ICC_DIR_EL1 (← (undefined_ICC_DIR_EL1_Type ()))
  writeReg PMEVCNTSVR_EL1 (← (undefined_vector 31 (← (undefined_PMEVCNTSVR_EL1_Type ()))))
  writeReg ID_AA64ISAR0_EL1 (← (undefined_ID_AA64ISAR0_EL1_Type ()))
  writeReg PMMIR_EL1 (← (undefined_PMMIR_EL1_Type ()))
  writeReg ICV_IAR0_EL1 (← (undefined_ICV_IAR0_EL1_Type ()))
  writeReg ICC_IGRPEN1_EL1_S (← (undefined_ICC_IGRPEN1_EL1_Type ()))
  writeReg ICC_IGRPEN1_EL1_NS (← (undefined_ICC_IGRPEN1_EL1_Type ()))
  writeReg ID_MMFR5_EL1 (← (undefined_ID_MMFR5_EL1_Type ()))
  writeReg ICC_NMIAR1_EL1 (← (undefined_ICC_NMIAR1_EL1_Type ()))
  writeReg DBGCLAIMSET_EL1 (← (undefined_DBGCLAIMSET_EL1_Type ()))
  writeReg ICC_SRE_EL1_S (← (undefined_ICC_SRE_EL1_Type ()))
  writeReg ICC_SRE_EL1_NS (← (undefined_ICC_SRE_EL1_Type ()))
  writeReg ICH_AP0R_EL2 (← (undefined_vector 4 (← (undefined_ICH_AP0R_EL2_Type ()))))
  writeReg ICC_IAR0_EL1 (← (undefined_ICC_IAR0_EL1_Type ()))
  writeReg TPIDR_EL1 (← (undefined_bitvector 64))
  writeReg ID_ISAR4_EL1 (← (undefined_ID_ISAR4_EL1_Type ()))
  writeReg ID_ISAR1_EL1 (← (undefined_ID_ISAR1_EL1_Type ()))
  writeReg PMUACR_EL1 (← (undefined_PMUACR_EL1_Type ()))
  writeReg ACTLR_EL1 (← (undefined_bitvector 64))
  writeReg RMR_EL2 (← (undefined_RMR_EL2_Type ()))
  writeReg PMSELR_EL0 (← (undefined_PMSELR_EL0_Type ()))
  writeReg ICC_CTLR_EL1_S (← (undefined_ICC_CTLR_EL1_Type ()))
  writeReg ICC_CTLR_EL1_NS (← (undefined_ICC_CTLR_EL1_Type ()))
  writeReg ID_ISAR6_EL1 (← (undefined_ID_ISAR6_EL1_Type ()))
  writeReg ICC_AP1R_EL1_S (← (undefined_vector 4 (← (undefined_ICC_AP1R_EL1_Type ()))))
  writeReg ICC_AP1R_EL1_NS (← (undefined_vector 4 (← (undefined_ICC_AP1R_EL1_Type ()))))
  writeReg HFGITR2_EL2 (← (undefined_bitvector 64))
  writeReg CNTHV_TVAL_EL2 (← (undefined_CNTHV_TVAL_EL2_Type ()))
  writeReg ICH_MISR_EL2 (← (undefined_ICH_MISR_EL2_Type ()))
  writeReg CSSELR_EL1 (← (undefined_CSSELR_EL1_Type ()))
  writeReg ICV_RPR_EL1 (← (undefined_ICV_RPR_EL1_Type ()))
  writeReg ICV_PMR_EL1 (← (undefined_ICV_PMR_EL1_Type ()))
  writeReg ICV_HPPIR0_EL1 (← (undefined_ICV_HPPIR0_EL1_Type ()))
  writeReg ICV_BPR0_EL1 (← (undefined_ICV_BPR0_EL1_Type ()))
  writeReg ISR_EL1 (← (undefined_ISR_EL1_Type ()))
  writeReg ID_ISAR3_EL1 (← (undefined_ID_ISAR3_EL1_Type ()))
  writeReg AFSR1_EL1 (← (undefined_bitvector 64))
  writeReg PMCCNTSVR_EL1 (← (undefined_PMCCNTSVR_EL1_Type ()))
  writeReg MECIDR_EL2 (← (undefined_MECIDR_EL2_Type ()))
  writeReg PMINTENSET_EL1 (← (undefined_PMINTENSET_EL1_Type ()))
  writeReg SMIDR_EL1 (← (undefined_SMIDR_EL1_Type ()))
  writeReg HFGWTR_EL2 (← (undefined_HFGWTR_EL2_Type ()))
  writeReg SMPRI_EL1 (← (undefined_SMPRI_EL1_Type ()))
  writeReg PMUSERENR_EL0 (← (undefined_PMUSERENR_EL0_Type ()))
  writeReg AMAIR2_EL2 (← (undefined_bitvector 64))
  writeReg ICV_AP0R_EL1 (← (undefined_vector 4 (← (undefined_bitvector 64))))
  writeReg AFSR0_EL3 (← (undefined_bitvector 64))
  writeReg CNTFRQ_EL0 (← (undefined_bitvector 64))
  writeReg ICV_CTLR_EL1 (← (undefined_ICV_CTLR_EL1_Type ()))
  writeReg AFSR1_EL2 (← (undefined_bitvector 64))
  writeReg ICV_IAR1_EL1 (← (undefined_ICV_IAR1_EL1_Type ()))
  writeReg ID_PFR0_EL1 (← (undefined_ID_PFR0_EL1_Type ()))
  writeReg MVFR1_EL1 (← (undefined_MVFR1_EL1_Type ()))
  writeReg HDFGWTR2_EL2 (← (undefined_HDFGWTR2_EL2_Type ()))
  writeReg ID_ISAR0_EL1 (← (undefined_ID_ISAR0_EL1_Type ()))
  writeReg AFSR0_EL1 (← (undefined_bitvector 64))
  writeReg CNTHVS_TVAL_EL2 (← (undefined_CNTHVS_TVAL_EL2_Type ()))
  writeReg CNTHP_TVAL_EL2 (← (undefined_CNTHP_TVAL_EL2_Type ()))
  writeReg SPMACCESSR_EL2 (← (undefined_SPMACCESSR_EL2_Type ()))
  writeReg PMZR_EL0 (← (undefined_PMZR_EL0_Type ()))
  writeReg PMICNTSVR_EL1 (← (undefined_PMICNTSVR_EL1_Type ()))
  writeReg MDRAR_EL1 (← (undefined_MDRAR_EL1_Type ()))
  writeReg OSDTRRX_EL1 (← (undefined_bitvector 64))
  writeReg ICC_IGRPEN1_EL3 (← (undefined_ICC_IGRPEN1_EL3_Type ()))
  writeReg ID_MMFR1_EL1 (← (undefined_ID_MMFR1_EL1_Type ()))
  writeReg LORSA_EL1 (← (undefined_LORSA_EL1_Type ()))
  writeReg ID_AA64MMFR1_EL1 (← (undefined_ID_AA64MMFR1_EL1_Type ()))
  writeReg PMSWINC_EL0 (← (undefined_PMSWINC_EL0_Type ()))
  writeReg SCXTNUM_EL2 (← (undefined_bitvector 64))
  writeReg PMIAR_EL1 (← (undefined_PMIAR_EL1_Type ()))
  writeReg TPIDR_EL3 (← (undefined_bitvector 64))
  writeReg ID_MMFR0_EL1 (← (undefined_ID_MMFR0_EL1_Type ()))
  writeReg OSDTRTX_EL1 (← (undefined_bitvector 64))
  writeReg ICH_VMCR_EL2 (← (undefined_ICH_VMCR_EL2_Type ()))
  writeReg VPIDR_EL2 (← (undefined_VPIDR_EL2_Type ()))
  writeReg ACTLR_EL3 (← (undefined_bitvector 64))
  writeReg ICC_CTLR_EL3 (← (undefined_ICC_CTLR_EL3_Type ()))
  writeReg AMAIR_EL2 (← (undefined_bitvector 64))
  writeReg AMAIR_EL3 (← (undefined_bitvector 64))
  writeReg ICC_SRE_EL2 (← (undefined_ICC_SRE_EL2_Type ()))
  writeReg LORC_EL1 (← (undefined_LORC_EL1_Type ()))
  writeReg ID_AA64PFR2_EL1 (← (undefined_ID_AA64PFR2_EL1_Type ()))
  writeReg SCXTNUM_EL1 (← (undefined_bitvector 64))
  writeReg CCSIDR2_EL1 (← (undefined_CCSIDR2_EL1_Type ()))
  writeReg ICC_ASGI1R_EL1 (← (undefined_ICC_ASGI1R_EL1_Type ()))
  writeReg ID_AA64ISAR2_EL1 (← (undefined_ID_AA64ISAR2_EL1_Type ()))
  writeReg HFGRTR2_EL2 (← (undefined_HFGRTR2_EL2_Type ()))
  writeReg TPIDRRO_EL0 (← (undefined_bitvector 64))
  writeReg ID_ISAR5_EL1 (← (undefined_ID_ISAR5_EL1_Type ()))
  writeReg RMR_EL3 (← (undefined_RMR_EL3_Type ()))
  writeReg ICH_HCR_EL2 (← (undefined_ICH_HCR_EL2_Type ()))
  writeReg ICC_IGRPEN0_EL1 (← (undefined_ICC_IGRPEN0_EL1_Type ()))
  writeReg CNTHPS_TVAL_EL2 (← (undefined_CNTHPS_TVAL_EL2_Type ()))
  writeReg ICC_BPR1_EL1_S (← (undefined_ICC_BPR1_EL1_Type ()))
  writeReg ICC_BPR1_EL1_NS (← (undefined_ICC_BPR1_EL1_Type ()))
  writeReg AMAIR_EL1 (← (undefined_bitvector 64))
  writeReg SCXTNUM_EL0 (← (undefined_bitvector 64))
  writeReg ICC_EOIR1_EL1 (← (undefined_ICC_EOIR1_EL1_Type ()))
  writeReg ID_AA64MMFR0_EL1 (← (undefined_ID_AA64MMFR0_EL1_Type ()))
  writeReg TPIDR2_EL0 (← (undefined_bitvector 64))
  writeReg HDFGRTR2_EL2 (← (undefined_HDFGRTR2_EL2_Type ()))
  writeReg VMPIDR_EL2 (← (undefined_VMPIDR_EL2_Type ()))
  writeReg ID_AA64MMFR3_EL1 (← (undefined_ID_AA64MMFR3_EL1_Type ()))
  writeReg ICH_VTR_EL2 (← (undefined_ICH_VTR_EL2_Type ()))
  writeReg ID_PFR1_EL1 (← (undefined_ID_PFR1_EL1_Type ()))
  writeReg ICV_EOIR0_EL1 (← (undefined_ICV_EOIR0_EL1_Type ()))
  writeReg ID_DFR1_EL1 (← (undefined_ID_DFR1_EL1_Type ()))
  writeReg SCXTNUM_EL3 (← (undefined_bitvector 64))
  writeReg TPIDR_EL0 (← (undefined_bitvector 64))
  writeReg ID_AFR0_EL1 (← (undefined_bitvector 64))
  writeReg RNDRRS (← (undefined_RNDRRS_Type ()))
  writeReg LORN_EL1 (← (undefined_LORN_EL1_Type ()))
  writeReg ICV_IGRPEN0_EL1 (← (undefined_ICV_IGRPEN0_EL1_Type ()))
  writeReg CCSIDR_EL1 (← (undefined_CCSIDR_EL1_Type ()))
  writeReg SMPRIMAP_EL2 (← (undefined_SMPRIMAP_EL2_Type ()))
  writeReg RNDR (← (undefined_RNDR_Type ()))
  writeReg HFGRTR_EL2 (← (undefined_HFGRTR_EL2_Type ()))
  writeReg ID_DFR0_EL1 (← (undefined_ID_DFR0_EL1_Type ()))
  writeReg ICV_IGRPEN1_EL1 (← (undefined_ICV_IGRPEN1_EL1_Type ()))
  writeReg PMXEVCNTR_EL0 (← (undefined_PMXEVCNTR_EL0_Type ()))
  writeReg HFGWTR2_EL2 (← (undefined_HFGWTR2_EL2_Type ()))
  writeReg ICC_SGI1R_EL1 (← (undefined_ICC_SGI1R_EL1_Type ()))
  writeReg HACR_EL2 (← (undefined_bitvector 64))
  writeReg MVFR2_EL1 (← (undefined_MVFR2_EL1_Type ()))
  writeReg DBGAUTHSTATUS_EL1 (← (undefined_DBGAUTHSTATUS_EL1_Type ()))
  writeReg AMAIR2_EL3 (← (undefined_bitvector 64))
  writeReg ICC_SRE_EL3 (← (undefined_ICC_SRE_EL3_Type ()))
  writeReg AFSR1_EL3 (← (undefined_bitvector 64))
  writeReg ID_MMFR3_EL1 (← (undefined_ID_MMFR3_EL1_Type ()))
  writeReg HDFGWTR_EL2 (← (undefined_HDFGWTR_EL2_Type ()))
  writeReg PMCEID1_EL0 (← (undefined_PMCEID1_EL0_Type ()))
  writeReg CNTPS_TVAL_EL1 (← (undefined_CNTPS_TVAL_EL1_Type ()))
  writeReg ID_AA64AFR1_EL1 (← (undefined_bitvector 64))
  writeReg ICV_AP1R_EL1 (← (undefined_vector 4 (← (undefined_ICV_AP1R_EL1_Type ()))))
  writeReg LOREA_EL1 (← (undefined_LOREA_EL1_Type ()))
  writeReg CNTV_TVAL_EL0 (← (undefined_CNTV_TVAL_EL0_Type ()))
  writeReg ICV_DIR_EL1 (← (undefined_ICV_DIR_EL1_Type ()))
  writeReg ICC_IAR1_EL1 (← (undefined_ICC_IAR1_EL1_Type ()))
  writeReg MPIDR_EL1 (← (undefined_MPIDR_EL1_Type ()))
  writeReg DBGCLAIMCLR_EL1 (← (undefined_DBGCLAIMCLR_EL1_Type ()))
  writeReg PMCEID0_EL0 (← (undefined_PMCEID0_EL0_Type ()))
  writeReg ICV_HPPIR1_EL1 (← (undefined_ICV_HPPIR1_EL1_Type ()))
  writeReg ID_AA64AFR0_EL1 (← (undefined_bitvector 64))
  writeReg AFSR0_EL2 (← (undefined_bitvector 64))
  writeReg AMAIR2_EL1 (← (undefined_bitvector 64))
  writeReg ID_PFR2_EL1 (← (undefined_ID_PFR2_EL1_Type ()))
  writeReg SPMACCESSR_EL3 (← (undefined_SPMACCESSR_EL3_Type ()))
  writeReg ICC_EOIR0_EL1 (← (undefined_ICC_EOIR0_EL1_Type ()))
  writeReg ID_AA64ZFR0_EL1 (← (undefined_ID_AA64ZFR0_EL1_Type ()))
  writeReg _ICC_SGI1R (← (undefined_ICC_SGI1R_Type ()))
  writeReg DBGDSAR (← (undefined_bitvector 64))
  writeReg _ICC_SGI0R (← (undefined_ICC_SGI0R_Type ()))
  writeReg _CNTVOFF (← (undefined_bitvector 64))
  writeReg _ICC_ASGI1R (← (undefined_ICC_ASGI1R_Type ()))
  writeReg _CNTV_CVAL (← (undefined_CNTV_CVAL_Type ()))
  writeReg _DBGDRAR (← (undefined_DBGDRAR_Type ()))
  writeReg ID_AA64SMFR0_EL1 (← (undefined_ID_AA64SMFR0_EL1_Type ()))
  writeReg GMID_EL1 (← (undefined_GMID_EL1_Type ()))
  writeReg AMEVCNTR1_EL0 (← (undefined_vector 16 (← (undefined_AMEVCNTR1_EL0_Type ()))))
  writeReg AMEVCNTVOFF0_EL2 (← (undefined_vector 16 (← (undefined_bitvector 64))))
  writeReg AMEVCNTR0 (← (undefined_vector 4 (← (undefined_AMEVCNTR0_Type ()))))
  writeReg _AMEVCNTR1 (← (undefined_vector 16 (← (undefined_AMEVCNTR1_Type ()))))
  writeReg AMCR_EL0 (← (undefined_AMCR_EL0_Type ()))
  writeReg AMCNTENSET0_EL0 (← (undefined_AMCNTENSET0_EL0_Type ()))
  writeReg AMCNTENCLR0_EL0 (← (undefined_AMCNTENCLR0_EL0_Type ()))
  writeReg AMEVTYPER0_EL0 (← (undefined_vector 4 (← (undefined_AMEVTYPER0_EL0_Type ()))))
  writeReg AMCNTENSET1_EL0 (← (undefined_AMCNTENSET1_EL0_Type ()))
  writeReg AMCNTENCLR1_EL0 (← (undefined_AMCNTENCLR1_EL0_Type ()))
  writeReg _AMEVCNTR0_EL0 (← (undefined_vector 4 (← (undefined_AMEVCNTR0_EL0_Type ()))))
  writeReg AMCFGR_EL0 (← (undefined_AMCFGR_EL0_Type ()))
  writeReg AMEVCNTVOFF1_EL2 (← (undefined_vector 16 (← (undefined_bitvector 64))))
  writeReg AMUSERENR_EL0 (← (undefined_AMUSERENR_EL0_Type ()))
  writeReg AMCG1IDR_EL0 (← (undefined_AMCG1IDR_EL0_Type ()))
  writeReg AMEVTYPER1_EL0 (← (undefined_vector 16 (← (undefined_AMEVTYPER1_EL0_Type ()))))
  writeReg AMCGCR_EL0 (← (undefined_AMCGCR_EL0_Type ()))
  writeReg ERXADDR_EL1 (← (undefined_bitvector 64))
  writeReg ERXMISC0_EL1 (← (undefined_bitvector 64))
  writeReg ERRIDR_EL1 (← (undefined_ERRIDR_EL1_Type ()))
  writeReg ERXPFGCDN_EL1 (← (undefined_bitvector 64))
  writeReg ERXPFGF_EL1 (← (undefined_bitvector 64))
  writeReg ERRSELR_EL1 (← (undefined_ERRSELR_EL1_Type ()))
  writeReg ERXMISC1_EL1 (← (undefined_bitvector 64))
  writeReg ERXCTLR_EL1 (← (undefined_bitvector 64))
  writeReg ERXSTATUS_EL1 (← (undefined_bitvector 64))
  writeReg ERXFR_EL1 (← (undefined_bitvector 64))
  writeReg ERXGSR_EL1 (← (undefined_ERXGSR_EL1_Type ()))
  writeReg ERXMISC3_EL1 (← (undefined_bitvector 64))
  writeReg ERXMISC2_EL1 (← (undefined_bitvector 64))
  writeReg ERXPFGCTL_EL1 (← (undefined_bitvector 64))
  writeReg BRBINF_EL1 (← (undefined_vector 32 (← (undefined_BRBINF_EL1_Type ()))))
  writeReg BRBTGT_EL1 (← (undefined_vector 32 (← (undefined_BRBTGT_EL1_Type ()))))
  writeReg BRBSRC_EL1 (← (undefined_vector 32 (← (undefined_BRBSRC_EL1_Type ()))))
  writeReg GITS_CREADR (← (undefined_GITS_CREADR_Type ()))
  writeReg GICR_PENDBASER (← (undefined_GICR_PENDBASER_Type ()))
  writeReg GICR_PROPBASER (← (undefined_GICR_PROPBASER_Type ()))
  writeReg GICR_VPROPBASER (← (undefined_GICR_VPROPBASER_Type ()))
  writeReg EDPFR (← (undefined_EDPFR_Type ()))
  writeReg GICR_CLRLPIR (← (undefined_GICR_CLRLPIR_Type ()))
  writeReg GICR_INVALLR (← (undefined_GICR_INVALLR_Type ()))
  writeReg EDHSR (← (undefined_EDHSR_Type ()))
  writeReg EDPCSR (← (undefined_EDPCSR_Type ()))
  writeReg GICR_VPENDBASER (← (undefined_GICR_VPENDBASER_Type ()))
  writeReg GITS_TYPER (← (undefined_GITS_TYPER_Type ()))
  writeReg GITS_SGIR (← (undefined_GITS_SGIR_Type ()))
  writeReg EDDFR1 (← (undefined_EDDFR1_Type ()))
  writeReg GITS_CWRITER (← (undefined_GITS_CWRITER_Type ()))
  writeReg EDDFR (← (undefined_EDDFR_Type ()))
  writeReg GICR_INVLPIR (← (undefined_GICR_INVLPIR_Type ()))
  writeReg EDAA32PFR (← (undefined_EDAA32PFR_Type ()))
  writeReg GITS_CBASER (← (undefined_GITS_CBASER_Type ()))
  writeReg GICR_SETLPIR (← (undefined_GICR_SETLPIR_Type ()))
  writeReg PMCFGR (← (undefined_PMCFGR_Type ()))
  writeReg _PMCNTEN (← (undefined_PMCNTEN_Type ()))
  writeReg PMIIDR (← (undefined_PMIIDR_Type ()))
  writeReg _PMINTEN (← (undefined_PMINTEN_Type ()))
  writeReg _PMOVS (← (undefined_PMOVS_Type ()))
  writeReg PMPCSCTL (← (undefined_PMPCSCTL_Type ()))
  writeReg PMVCIDSR (← (undefined_PMVCIDSR_Type ()))
  writeReg _ICH_ELRSR (← (undefined_ICH_ELRSR_Type ()))
  writeReg _ICC_IAR1 (← (undefined_ICC_IAR1_Type ()))
  writeReg AIFSR_S (← (undefined_bitvector 32))
  writeReg _AIFSR_NS (← (undefined_bitvector 32))
  writeReg _ID_DFR0 (← (undefined_ID_DFR0_Type ()))
  writeReg _CLIDR (← (undefined_CLIDR_Type ()))
  writeReg _HACR (← (undefined_bitvector 32))
  writeReg JOSCR (← (undefined_bitvector 32))
  writeReg _ICV_IGRPEN1 (← (undefined_ICV_IGRPEN1_Type ()))
  writeReg _CTR (← (undefined_CTR_Type ()))
  writeReg _PMUSERENR (← (undefined_PMUSERENR_Type ()))
  writeReg _CNTHPS_CTL (← (undefined_CNTHPS_CTL_Type ()))
  writeReg _PMCEID1 (← (undefined_PMCEID1_Type ()))
  writeReg _DBGAUTHSTATUS (← (undefined_DBGAUTHSTATUS_Type ()))
  writeReg _ICC_IAR0 (← (undefined_ICC_IAR0_Type ()))
  writeReg _ICV_IGRPEN0 (← (undefined_ICV_IGRPEN0_Type ()))
  writeReg _ID_MMFR3 (← (undefined_ID_MMFR3_Type ()))
  writeReg _PMCEID0 (← (undefined_PMCEID0_Type ()))
  writeReg _ICV_CTLR (← (undefined_ICV_CTLR_Type ()))
  writeReg _ID_ISAR6 (← (undefined_ID_ISAR6_Type ()))
  writeReg _HACTLR (← (undefined_bitvector 32))
  writeReg _DBGCLAIMCLR (← (undefined_DBGCLAIMCLR_Type ()))
  writeReg TCMTR (← (undefined_bitvector 32))
  writeReg _ICV_HPPIR1 (← (undefined_ICV_HPPIR1_Type ()))
  writeReg _ID_MMFR5 (← (undefined_ID_MMFR5_Type ()))
  writeReg _ICV_AP0R (← (undefined_vector 4 (← (undefined_bitvector 32))))
  writeReg _HRMR (← (undefined_HRMR_Type ()))
  writeReg _ID_PFR2 (← (undefined_ID_PFR2_Type ()))
  writeReg _ICV_EOIR0 (← (undefined_ICV_EOIR0_Type ()))
  writeReg _ICH_VTR (← (undefined_ICH_VTR_Type ()))
  writeReg CSSELR_S (← (undefined_CSSELR_Type ()))
  writeReg _CSSELR_NS (← (undefined_CSSELR_Type ()))
  writeReg JIDR (← (undefined_bitvector 32))
  writeReg _ICH_VMCR (← (undefined_ICH_VMCR_Type ()))
  writeReg DBGDEVID1 (← (undefined_DBGDEVID1_Type ()))
  writeReg _ICC_BPR1_S (← (undefined_ICC_BPR1_Type ()))
  writeReg _ICC_BPR1_NS (← (undefined_ICC_BPR1_Type ()))
  writeReg _ICV_RPR (← (undefined_ICV_RPR_Type ()))
  writeReg _ID_ISAR0 (← (undefined_ID_ISAR0_Type ()))
  writeReg _ICV_IAR1 (← (undefined_ICV_IAR1_Type ()))
  writeReg _ID_MMFR4 (← (undefined_ID_MMFR4_Type ()))
  writeReg _ICC_EOIR1 (← (undefined_ICC_EOIR1_Type ()))
  writeReg TPIDRURW_S (← (undefined_bitvector 32))
  writeReg _TPIDRURW_NS (← (undefined_bitvector 32))
  writeReg _ICC_BPR0 (← (undefined_ICC_BPR0_Type ()))
  writeReg _ICV_AP1R (← (undefined_vector 4 (← (undefined_bitvector 32))))
  writeReg ADFSR_S (← (undefined_bitvector 32))
  writeReg _ADFSR_NS (← (undefined_bitvector 32))
  writeReg _CNTHCTL (← (undefined_CNTHCTL_Type ()))
  writeReg _ICC_EOIR0 (← (undefined_ICC_EOIR0_Type ()))
  writeReg _REVIDR (← (undefined_bitvector 32))
  writeReg _ID_MMFR1 (← (undefined_ID_MMFR1_Type ()))
  writeReg _ICV_BPR1 (← (undefined_ICV_BPR1_Type ()))
  writeReg _ICC_RPR (← (undefined_ICC_RPR_Type ()))
  writeReg _MVFR2 (← (undefined_MVFR2_Type ()))
  writeReg ICC_MSRE (← (undefined_ICC_MSRE_Type ()))
  writeReg PMMIR (← (undefined_PMMIR_Type ()))
  writeReg _VMPIDR (← (undefined_VMPIDR_Type ()))
  writeReg _ICC_IGRPEN1_S (← (undefined_ICC_IGRPEN1_Type ()))
  writeReg _ICC_IGRPEN1_NS (← (undefined_ICC_IGRPEN1_Type ()))
  writeReg FPSID (← (undefined_FPSID_Type ()))
  writeReg ICC_MCTLR (← (undefined_ICC_MCTLR_Type ()))
  writeReg _ICC_DIR (← (undefined_ICC_DIR_Type ()))
  writeReg _PMSELR (← (undefined_PMSELR_Type ()))
  writeReg _ID_AFR0 (← (undefined_bitvector 32))
  writeReg _DBGCLAIMSET (← (undefined_DBGCLAIMSET_Type ()))
  writeReg TPIDRURO_S (← (undefined_bitvector 32))
  writeReg _TPIDRURO_NS (← (undefined_bitvector 32))
  writeReg _ICC_IGRPEN0 (← (undefined_ICC_IGRPEN0_Type ()))
  writeReg _DBGDTRTXext (← (undefined_DBGDTRTXext_Type ()))
  writeReg ACTLR_S (← (undefined_bitvector 32))
  writeReg _ACTLR_NS (← (undefined_bitvector 32))
  writeReg _MVFR1 (← (undefined_MVFR1_Type ()))
  writeReg _ICC_CTLR_S (← (undefined_ICC_CTLR_Type ()))
  writeReg _ICC_CTLR_NS (← (undefined_ICC_CTLR_Type ()))
  writeReg DBGOSLAR (← (undefined_DBGOSLAR_Type ()))
  writeReg _DBGDTRRXext (← (undefined_DBGDTRRXext_Type ()))
  writeReg _ICC_AP1R_S (← (undefined_vector 4 (← (undefined_bitvector 32))))
  writeReg _ICC_AP1R_NS (← (undefined_vector 4 (← (undefined_bitvector 32))))
  writeReg _CNTHVS_CTL (← (undefined_CNTHVS_CTL_Type ()))
  writeReg _ICH_AP1R (← (undefined_vector 4 (← (undefined_ICH_AP1R_Type ()))))
  writeReg _ID_MMFR0 (← (undefined_ID_MMFR0_Type ()))
  writeReg _ICV_BPR0 (← (undefined_ICV_BPR0_Type ()))
  writeReg _ICH_EISR (← (undefined_ICH_EISR_Type ()))
  writeReg AMAIR0_S (← (undefined_bitvector 32))
  writeReg _AMAIR0_NS (← (undefined_bitvector 32))
  writeReg _MVFR0 (← (undefined_MVFR0_Type ()))
  writeReg _HAMAIR0 (← (undefined_bitvector 32))
  writeReg _ICC_HSRE (← (undefined_ICC_HSRE_Type ()))
  writeReg _ICH_AP0R (← (undefined_vector 4 (← (undefined_ICH_AP0R_Type ()))))
  writeReg _ID_ISAR5 (← (undefined_ID_ISAR5_Type ()))
  writeReg _AIDR (← (undefined_bitvector 32))
  writeReg _ICC_PMR (← (undefined_ICC_PMR_Type ()))
  writeReg _ICV_EOIR1 (← (undefined_ICV_EOIR1_Type ()))
  writeReg _ID_PFR1 (← (undefined_ID_PFR1_Type ()))
  writeReg _ICH_HCR (← (undefined_ICH_HCR_Type ()))
  writeReg _RMR (← (undefined_RMR_Type ()))
  writeReg _PMCEID3 (← (undefined_PMCEID3_Type ()))
  writeReg _ICC_HPPIR0 (← (undefined_ICC_HPPIR0_Type ()))
  writeReg _ID_ISAR4 (← (undefined_ID_ISAR4_Type ()))
  writeReg _PMCEID2 (← (undefined_PMCEID2_Type ()))
  writeReg FCSEIDR (← (undefined_bitvector 32))
  writeReg _ID_DFR1 (← (undefined_ID_DFR1_Type ()))
  writeReg _ICH_LR (← (undefined_vector 16 (← (undefined_ICH_LR_Type ()))))
  writeReg _HADFSR (← (undefined_bitvector 32))
  writeReg JMCR (← (undefined_bitvector 32))
  writeReg _ICV_PMR (← (undefined_ICV_PMR_Type ()))
  writeReg _ICV_HPPIR0 (← (undefined_ICV_HPPIR0_Type ()))
  writeReg DBGWFAR (← (undefined_bitvector 32))
  writeReg _ID_ISAR3 (← (undefined_ID_ISAR3_Type ()))
  writeReg ICC_MGRPEN1 (← (undefined_ICC_MGRPEN1_Type ()))
  writeReg TLBTR (← (undefined_TLBTR_Type ()))
  writeReg _CNTFRQ (← (undefined_bitvector 32))
  writeReg _PMINTENSET (← (undefined_PMINTENSET_Type ()))
  writeReg DBGDEVID (← (undefined_DBGDEVID_Type ()))
  writeReg _DBGOSECCR (← (undefined_DBGOSECCR_Type ()))
  writeReg _CCSIDR2 (← (undefined_CCSIDR2_Type ()))
  writeReg _CNTHV_CTL (← (undefined_CNTHV_CTL_Type ()))
  writeReg _ICH_MISR (← (undefined_ICH_MISR_Type ()))
  writeReg ACTLR2_S (← (undefined_bitvector 32))
  writeReg _ACTLR2_NS (← (undefined_bitvector 32))
  writeReg _ICV_IAR0 (← (undefined_ICV_IAR0_Type ()))
  writeReg _ID_MMFR2 (← (undefined_ID_MMFR2_Type ()))
  writeReg _HAMAIR1 (← (undefined_bitvector 32))
  writeReg _ISR (← (undefined_ISR_Type ()))
  writeReg _HAIFSR (← (undefined_bitvector 32))
  writeReg _ID_PFR0 (← (undefined_ID_PFR0_Type ()))
  writeReg _MIDR (← (undefined_MIDR_Type ()))
  writeReg _ICC_AP0R (← (undefined_vector 4 (← (undefined_bitvector 32))))
  writeReg DBGDIDR (← (undefined_DBGDIDR_Type ()))
  writeReg TPIDRPRW_S (← (undefined_bitvector 32))
  writeReg _TPIDRPRW_NS (← (undefined_bitvector 32))
  writeReg _DBGDTRRXint (← (undefined_DBGDTRRXint_Type ()))
  writeReg _VPIDR (← (undefined_VPIDR_Type ()))
  writeReg _PMSWINC (← (undefined_PMSWINC_Type ()))
  writeReg _CNTV_CTL (← (undefined_CNTV_CTL_Type ()))
  writeReg _HTPIDR (← (undefined_bitvector 32))
  writeReg _ID_ISAR2 (← (undefined_ID_ISAR2_Type ()))
  writeReg _DBGDTRTXint (← (undefined_DBGDTRTXint_Type ()))
  writeReg AMAIR1_S (← (undefined_bitvector 32))
  writeReg _AMAIR1_NS (← (undefined_bitvector 32))
  writeReg _CCSIDR (← (undefined_CCSIDR_Type ()))
  writeReg DBGDEVID2 (← (undefined_bitvector 32))
  writeReg _ICV_DIR (← (undefined_ICV_DIR_Type ()))
  writeReg _MPIDR (← (undefined_MPIDR_Type ()))
  writeReg _ICH_LRC (← (undefined_vector 16 (← (undefined_ICH_LRC_Type ()))))
  writeReg _ICC_HPPIR1 (← (undefined_ICC_HPPIR1_Type ()))
  writeReg _ICC_SRE_S (← (undefined_ICC_SRE_Type ()))
  writeReg _ICC_SRE_NS (← (undefined_ICC_SRE_Type ()))
  writeReg _ID_ISAR1 (← (undefined_ID_ISAR1_Type ()))
  writeReg _AMEVTYPER0 (← (undefined_vector 4 (← (undefined_AMEVTYPER0_Type ()))))
  writeReg _AMUSERENR (← (undefined_AMUSERENR_Type ()))
  writeReg _AMEVTYPER1 (← (undefined_vector 16 (← (undefined_AMEVTYPER1_Type ()))))
  writeReg _AMCGCR (← (undefined_AMCGCR_Type ()))
  writeReg _AMCFGR (← (undefined_AMCFGR_Type ()))
  writeReg _AMCNTENCLR1 (← (undefined_AMCNTENCLR1_Type ()))
  writeReg _AMCNTENSET0 (← (undefined_AMCNTENSET0_Type ()))
  writeReg _AMCNTENCLR0 (← (undefined_AMCNTENCLR0_Type ()))
  writeReg _AMCNTENSET1 (← (undefined_AMCNTENSET1_Type ()))
  writeReg _AMCR (← (undefined_AMCR_Type ()))
  writeReg _ERRIDR (← (undefined_ERRIDR_Type ()))
  writeReg _ERXFR2 (← (undefined_bitvector 32))
  writeReg _ERXMISC2 (← (undefined_bitvector 32))
  writeReg _ERXFR (← (undefined_bitvector 32))
  writeReg _ERXADDR (← (undefined_bitvector 32))
  writeReg _ERXMISC0 (← (undefined_bitvector 32))
  writeReg _ERXMISC5 (← (undefined_bitvector 32))
  writeReg _ERRSELR (← (undefined_ERRSELR_Type ()))
  writeReg _ERXCTLR2 (← (undefined_bitvector 32))
  writeReg _ERXMISC1 (← (undefined_bitvector 32))
  writeReg _ERXCTLR (← (undefined_bitvector 32))
  writeReg _ERXMISC6 (← (undefined_bitvector 32))
  writeReg _ERXMISC4 (← (undefined_bitvector 32))
  writeReg _ERXADDR2 (← (undefined_bitvector 32))
  writeReg _ERXMISC7 (← (undefined_bitvector 32))
  writeReg _ERXMISC3 (← (undefined_bitvector 32))
  writeReg _ERXSTATUS (← (undefined_bitvector 32))
  writeReg GICD_CTLR (← (undefined_GICD_CTLR_Type ()))
  writeReg GICC_IAR (← (undefined_GICC_IAR_Type ()))
  writeReg CTILAR (← (undefined_CTILAR_Type ()))
  writeReg CTIPIDR2 (← (undefined_CTIPIDR2_Type ()))
  writeReg CTICIDR1 (← (undefined_CTICIDR1_Type ()))
  writeReg GICH_MISR (← (undefined_GICH_MISR_Type ()))
  writeReg CTIDEVTYPE (← (undefined_CTIDEVTYPE_Type ()))
  writeReg GITS_CTLR (← (undefined_GITS_CTLR_Type ()))
  writeReg GICR_IIDR (← (undefined_GICR_IIDR_Type ()))
  writeReg EDDEVARCH (← (undefined_EDDEVARCH_Type ()))
  writeReg CTIPIDR1 (← (undefined_CTIPIDR1_Type ()))
  writeReg GICV_IAR (← (undefined_GICV_IAR_Type ()))
  writeReg CNTSR (← (undefined_CNTSR_Type ()))
  writeReg EDCIDR3 (← (undefined_EDCIDR3_Type ()))
  writeReg GICM_SETSPI_NSR (← (undefined_GICM_SETSPI_NSR_Type ()))
  writeReg GICR_WAKER (← (undefined_GICR_WAKER_Type ()))
  writeReg GITS_PARTIDR (← (undefined_GITS_PARTIDR_Type ()))
  writeReg GICV_HPPIR (← (undefined_GICV_HPPIR_Type ()))
  writeReg CTIPIDR0 (← (undefined_CTIPIDR0_Type ()))
  writeReg GICM_SETSPI_SR (← (undefined_GICM_SETSPI_SR_Type ()))
  writeReg GICV_DIR (← (undefined_GICV_DIR_Type ()))
  writeReg CTIDEVID2 (← (undefined_bitvector 32))
  writeReg EDPIDR3 (← (undefined_EDPIDR3_Type ()))
  writeReg GICC_STATUSR (← (undefined_GICC_STATUSR_Type ()))
  writeReg GICM_IIDR (← (undefined_GICM_IIDR_Type ()))
  writeReg GICR_VSGIR (← (undefined_GICR_VSGIR_Type ()))
  writeReg EDDEVTYPE (← (undefined_EDDEVTYPE_Type ()))
  writeReg GICM_TYPER (← (undefined_GICM_TYPER_Type ()))
  writeReg GICD_TYPER2 (← (undefined_GICD_TYPER2_Type ()))
  writeReg GICH_EISR (← (undefined_GICH_EISR_Type ()))
  writeReg GICH_ELRSR (← (undefined_GICH_ELRSR_Type ()))
  writeReg GICM_CLRSPI_NSR (← (undefined_GICM_CLRSPI_NSR_Type ()))
  writeReg GICV_STATUSR (← (undefined_GICV_STATUSR_Type ()))
  writeReg EDPIDR1 (← (undefined_EDPIDR1_Type ()))
  writeReg GICM_CLRSPI_SR (← (undefined_GICM_CLRSPI_SR_Type ()))
  writeReg GICV_AEOIR (← (undefined_GICV_AEOIR_Type ()))
  writeReg GICC_PMR (← (undefined_GICC_PMR_Type ()))
  writeReg GICV_ABPR (← (undefined_GICV_ABPR_Type ()))
  writeReg CTIDEVARCH (← (undefined_CTIDEVARCH_Type ()))
  writeReg GICR_MPAMIDR (← (undefined_GICR_MPAMIDR_Type ()))
  writeReg CTICIDR3 (← (undefined_CTICIDR3_Type ()))
  writeReg GICC_RPR (← (undefined_GICC_RPR_Type ()))
  writeReg GICV_AIAR (← (undefined_GICV_AIAR_Type ()))
  writeReg GICV_RPR (← (undefined_GICV_RPR_Type ()))
  writeReg GICV_AHPPIR (← (undefined_GICV_AHPPIR_Type ()))
  writeReg GICR_CTLR (← (undefined_GICR_CTLR_Type ()))
  writeReg CNTEL0ACR (← (undefined_CNTEL0ACR_Type ()))
  writeReg GICV_BPR (← (undefined_GICV_BPR_Type ()))
  writeReg EDDEVID2 (← (undefined_bitvector 32))
  writeReg GICV_EOIR (← (undefined_GICV_EOIR_Type ()))
  writeReg CNTFID0 (← (undefined_CNTFID0_Type ()))
  writeReg GICD_TYPER (← (undefined_GICD_TYPER_Type ()))
  writeReg CTICIDR0 (← (undefined_CTICIDR0_Type ()))
  writeReg GICC_HPPIR (← (undefined_GICC_HPPIR_Type ()))
  writeReg GICD_CLRSPI_NSR (← (undefined_GICD_CLRSPI_NSR_Type ()))
  writeReg CTIITCTRL (← (undefined_CTIITCTRL_Type ()))
  writeReg GITS_STATUSR (← (undefined_GITS_STATUSR_Type ()))
  writeReg GICH_VTR (← (undefined_GICH_VTR_Type ()))
  writeReg CTIPIDR3 (← (undefined_CTIPIDR3_Type ()))
  writeReg GICC_CTLR (← (undefined_GICC_CTLR_Type ()))
  writeReg EDPIDR4 (← (undefined_EDPIDR4_Type ()))
  writeReg CTICONTROL (← (undefined_CTICONTROL_Type ()))
  writeReg GICR_INMIR0 (← (undefined_GICR_INMIR0_Type ()))
  writeReg GICD_CLRSPI_SR (← (undefined_GICD_CLRSPI_SR_Type ()))
  writeReg GICV_CTLR (← (undefined_GICV_CTLR_Type ()))
  writeReg GICR_PARTIDR (← (undefined_GICR_PARTIDR_Type ()))
  writeReg EDDEVID1 (← (undefined_EDDEVID1_Type ()))
  writeReg EDPRCR (← (undefined_EDPRCR_Type ()))
  writeReg GICR_VSGIPENDR (← (undefined_GICR_VSGIPENDR_Type ()))
  writeReg GICD_STATUSR (← (undefined_GICD_STATUSR_Type ()))
  writeReg GICR_ISENABLER0 (← (undefined_GICR_ISENABLER0_Type ()))
  writeReg CTICIDR2 (← (undefined_CTICIDR2_Type ()))
  writeReg EDRCR (← (undefined_EDRCR_Type ()))
  writeReg GICV_PMR (← (undefined_GICV_PMR_Type ()))
  writeReg EDDEVID (← (undefined_EDDEVID_Type ()))
  writeReg GICC_DIR (← (undefined_GICC_DIR_Type ()))
  writeReg EDCIDR0 (← (undefined_EDCIDR0_Type ()))
  writeReg GITS_MPAMIDR (← (undefined_GITS_MPAMIDR_Type ()))
  writeReg GICD_SGIR (← (undefined_GICD_SGIR_Type ()))
  writeReg GICH_VMCR (← (undefined_GICH_VMCR_Type ()))
  writeReg EDLAR (← (undefined_EDLAR_Type ()))
  writeReg GICC_AEOIR (← (undefined_GICC_AEOIR_Type ()))
  writeReg GICC_AHPPIR (← (undefined_GICC_AHPPIR_Type ()))
  writeReg GICR_SYNCR (← (undefined_GICR_SYNCR_Type ()))
  writeReg GICC_ABPR (← (undefined_GICC_ABPR_Type ()))
  writeReg CTIPIDR4 (← (undefined_CTIPIDR4_Type ()))
  writeReg CTIDEVID1 (← (undefined_bitvector 32))
  writeReg GITS_MPIDR (← (undefined_GITS_MPIDR_Type ()))
  writeReg EDCIDR2 (← (undefined_EDCIDR2_Type ()))
  writeReg GICD_SETSPI_NSR (← (undefined_GICD_SETSPI_NSR_Type ()))
  writeReg CNTID (← (undefined_CNTID_Type ()))
  writeReg GITS_IIDR (← (undefined_GITS_IIDR_Type ()))
  writeReg EDPIDR0 (← (undefined_EDPIDR0_Type ()))
  writeReg CTIAUTHSTATUS (← (undefined_CTIAUTHSTATUS_Type ()))
  writeReg GICH_HCR (← (undefined_GICH_HCR_Type ()))
  writeReg GICC_BPR (← (undefined_GICC_BPR_Type ()))
  writeReg CTIDEVID (← (undefined_CTIDEVID_Type ()))
  writeReg GICD_SETSPI_SR (← (undefined_GICD_SETSPI_SR_Type ()))
  writeReg GICR_STATUSR (← (undefined_GICR_STATUSR_Type ()))
  writeReg GICC_EOIR (← (undefined_GICC_EOIR_Type ()))
  writeReg EDPIDR2 (← (undefined_EDPIDR2_Type ()))
  writeReg CNTNSAR (← (undefined_CNTNSAR_Type ()))
  writeReg EDITCTRL (← (undefined_EDITCTRL_Type ()))
  writeReg GICD_IIDR (← (undefined_GICD_IIDR_Type ()))
  writeReg EDCIDR1 (← (undefined_EDCIDR1_Type ()))
  writeReg GICC_AIAR (← (undefined_GICC_AIAR_Type ()))
  writeReg AMPIDR2 (← (undefined_AMPIDR2_Type ()))
  writeReg AMPIDR4 (← (undefined_AMPIDR4_Type ()))
  writeReg AMIIDR (← (undefined_AMIIDR_Type ()))
  writeReg AMPIDR3 (← (undefined_AMPIDR3_Type ()))
  writeReg AMCIDR3 (← (undefined_AMCIDR3_Type ()))
  writeReg AMDEVARCH (← (undefined_AMDEVARCH_Type ()))
  writeReg AMPIDR0 (← (undefined_AMPIDR0_Type ()))
  writeReg AMCIDR2 (← (undefined_AMCIDR2_Type ()))
  writeReg AMCIDR0 (← (undefined_AMCIDR0_Type ()))
  writeReg AMPIDR1 (← (undefined_AMPIDR1_Type ()))
  writeReg AMCIDR1 (← (undefined_AMCIDR1_Type ()))
  writeReg AMDEVTYPE (← (undefined_AMDEVTYPE_Type ()))
  writeReg _HACTLR2 (← (undefined_bitvector 32))
  writeReg PMAUTHSTATUS (← (undefined_PMAUTHSTATUS_Type ()))
  writeReg PMCGCR0 (← (undefined_PMCGCR0_Type ()))
  writeReg PMCIDR0 (← (undefined_PMCIDR0_Type ()))
  writeReg PMCIDR1 (← (undefined_PMCIDR1_Type ()))
  writeReg PMCIDR2 (← (undefined_PMCIDR2_Type ()))
  writeReg PMCIDR3 (← (undefined_PMCIDR3_Type ()))
  writeReg PMDEVID (← (undefined_PMDEVID_Type ()))
  writeReg PMDEVTYPE (← (undefined_PMDEVTYPE_Type ()))
  writeReg PMITCTRL (← (undefined_PMITCTRL_Type ()))
  writeReg PMLAR (← (undefined_PMLAR_Type ()))
  writeReg PMPIDR0 (← (undefined_PMPIDR0_Type ()))
  writeReg PMPIDR1 (← (undefined_PMPIDR1_Type ()))
  writeReg PMPIDR2 (← (undefined_PMPIDR2_Type ()))
  writeReg PMPIDR3 (← (undefined_PMPIDR3_Type ()))
  writeReg PMPIDR4 (← (undefined_PMPIDR4_Type ()))

def sail_model_init (x_0 : Unit) : SailM Unit := do
  writeReg FEAT_AA32EL0_IMPLEMENTED true
  writeReg FEAT_AA32EL1_IMPLEMENTED false
  writeReg FEAT_AA32EL2_IMPLEMENTED false
  writeReg FEAT_AA32EL3_IMPLEMENTED false
  writeReg FEAT_AA64EL0_IMPLEMENTED true
  writeReg FEAT_AA64EL1_IMPLEMENTED true
  writeReg FEAT_AA64EL2_IMPLEMENTED true
  writeReg FEAT_AA64EL3_IMPLEMENTED true
  writeReg FEAT_EL0_IMPLEMENTED true
  writeReg FEAT_EL1_IMPLEMENTED true
  writeReg FEAT_EL2_IMPLEMENTED true
  writeReg FEAT_EL3_IMPLEMENTED true
  writeReg FEAT_AES_IMPLEMENTED true
  writeReg FEAT_AdvSIMD_IMPLEMENTED true
  writeReg FEAT_CSV2_1p1_IMPLEMENTED true
  writeReg FEAT_CSV2_1p2_IMPLEMENTED true
  writeReg FEAT_CSV2_2_IMPLEMENTED true
  writeReg FEAT_CSV2_3_IMPLEMENTED true
  writeReg FEAT_DoubleLock_IMPLEMENTED true
  writeReg FEAT_ETMv4_IMPLEMENTED false
  writeReg FEAT_ETMv4p1_IMPLEMENTED true
  writeReg FEAT_ETMv4p2_IMPLEMENTED true
  writeReg FEAT_ETMv4p3_IMPLEMENTED true
  writeReg FEAT_ETMv4p4_IMPLEMENTED true
  writeReg FEAT_ETMv4p5_IMPLEMENTED true
  writeReg FEAT_ETMv4p6_IMPLEMENTED true
  writeReg FEAT_ETS2_IMPLEMENTED true
  writeReg FEAT_FP_IMPLEMENTED true
  writeReg FEAT_GICv3_IMPLEMENTED true
  writeReg FEAT_GICv3_LEGACY_IMPLEMENTED true
  writeReg FEAT_GICv3_TDIR_IMPLEMENTED true
  writeReg FEAT_GICv3p1_IMPLEMENTED true
  writeReg FEAT_GICv4_IMPLEMENTED true
  writeReg FEAT_GICv4p1_IMPLEMENTED true
  writeReg FEAT_IVIPT_IMPLEMENTED true
  writeReg FEAT_PCSRv8_IMPLEMENTED true
  writeReg FEAT_PMULL_IMPLEMENTED true
  writeReg FEAT_PMUv3_IMPLEMENTED true
  writeReg FEAT_PMUv3_EXT_IMPLEMENTED true
  writeReg FEAT_PMUv3_EXT32_IMPLEMENTED true
  writeReg FEAT_SHA1_IMPLEMENTED true
  writeReg FEAT_SHA256_IMPLEMENTED true
  writeReg FEAT_TRC_EXT_IMPLEMENTED true
  writeReg FEAT_TRC_SR_IMPLEMENTED true
  writeReg FEAT_nTLBPA_IMPLEMENTED true
  writeReg FEAT_CRC32_IMPLEMENTED true
  writeReg FEAT_Debugv8p1_IMPLEMENTED true
  writeReg FEAT_HAFDBS_IMPLEMENTED true
  writeReg FEAT_HPDS_IMPLEMENTED true
  writeReg FEAT_LOR_IMPLEMENTED true
  writeReg FEAT_LSE_IMPLEMENTED true
  writeReg FEAT_PAN_IMPLEMENTED true
  writeReg FEAT_PMUv3p1_IMPLEMENTED true
  writeReg FEAT_RDM_IMPLEMENTED true
  writeReg FEAT_VHE_IMPLEMENTED true
  writeReg FEAT_VMID16_IMPLEMENTED true
  writeReg FEAT_AA32BF16_IMPLEMENTED true
  writeReg FEAT_AA32HPD_IMPLEMENTED true
  writeReg FEAT_AA32I8MM_IMPLEMENTED true
  writeReg FEAT_ASMv8p2_IMPLEMENTED true
  writeReg FEAT_DPB_IMPLEMENTED true
  writeReg FEAT_Debugv8p2_IMPLEMENTED true
  writeReg FEAT_EDHSR_IMPLEMENTED true
  writeReg FEAT_F32MM_IMPLEMENTED true
  writeReg FEAT_F64MM_IMPLEMENTED true
  writeReg FEAT_FP16_IMPLEMENTED true
  writeReg FEAT_HPDS2_IMPLEMENTED true
  writeReg FEAT_I8MM_IMPLEMENTED true
  writeReg FEAT_IESB_IMPLEMENTED true
  writeReg FEAT_LPA_IMPLEMENTED true
  writeReg FEAT_LSMAOC_IMPLEMENTED true
  writeReg FEAT_LVA_IMPLEMENTED true
  writeReg FEAT_MPAM_IMPLEMENTED true
  writeReg FEAT_PAN2_IMPLEMENTED true
  writeReg FEAT_PCSRv8p2_IMPLEMENTED true
  writeReg FEAT_RAS_IMPLEMENTED true
  writeReg FEAT_SHA3_IMPLEMENTED true
  writeReg FEAT_SHA512_IMPLEMENTED true
  writeReg FEAT_SM3_IMPLEMENTED true
  writeReg FEAT_SM4_IMPLEMENTED true
  writeReg FEAT_SPE_IMPLEMENTED true
  writeReg FEAT_SVE_IMPLEMENTED true
  writeReg FEAT_TTCNP_IMPLEMENTED true
  writeReg FEAT_UAO_IMPLEMENTED true
  writeReg FEAT_VPIPT_IMPLEMENTED true
  writeReg FEAT_XNX_IMPLEMENTED true
  writeReg FEAT_CCIDX_IMPLEMENTED true
  writeReg FEAT_CONSTPACFIELD_IMPLEMENTED false
  writeReg FEAT_EPAC_IMPLEMENTED false
  writeReg FEAT_FCMA_IMPLEMENTED true
  writeReg FEAT_FPAC_IMPLEMENTED true
  writeReg FEAT_FPACCOMBINE_IMPLEMENTED true
  writeReg FEAT_JSCVT_IMPLEMENTED true
  writeReg FEAT_LRCPC_IMPLEMENTED true
  writeReg FEAT_NV_IMPLEMENTED true
  writeReg FEAT_PACIMP_IMPLEMENTED false
  writeReg FEAT_PACQARMA3_IMPLEMENTED false
  writeReg FEAT_PACQARMA5_IMPLEMENTED true
  writeReg FEAT_PAuth_IMPLEMENTED true
  writeReg FEAT_SPEv1p1_IMPLEMENTED true
  writeReg FEAT_AMUv1_IMPLEMENTED true
  writeReg FEAT_BBM_IMPLEMENTED true
  writeReg FEAT_CNTSC_IMPLEMENTED true
  writeReg FEAT_DIT_IMPLEMENTED true
  writeReg FEAT_Debugv8p4_IMPLEMENTED true
  writeReg FEAT_DotProd_IMPLEMENTED true
  writeReg FEAT_DoubleFault_IMPLEMENTED true
  writeReg FEAT_FHM_IMPLEMENTED true
  writeReg FEAT_FlagM_IMPLEMENTED true
  writeReg FEAT_IDST_IMPLEMENTED true
  writeReg FEAT_LRCPC2_IMPLEMENTED true
  writeReg FEAT_LSE2_IMPLEMENTED true
  writeReg FEAT_NV2_IMPLEMENTED true
  writeReg FEAT_PMUv3p4_IMPLEMENTED true
  writeReg FEAT_RASSAv1p1_IMPLEMENTED true
  writeReg FEAT_RASv1p1_IMPLEMENTED true
  writeReg FEAT_S2FWB_IMPLEMENTED true
  writeReg FEAT_SEL2_IMPLEMENTED true
  writeReg FEAT_TLBIOS_IMPLEMENTED true
  writeReg FEAT_TLBIRANGE_IMPLEMENTED true
  writeReg FEAT_TRF_IMPLEMENTED true
  writeReg FEAT_TTL_IMPLEMENTED true
  writeReg FEAT_TTST_IMPLEMENTED true
  writeReg FEAT_BTI_IMPLEMENTED true
  writeReg FEAT_CSV2_IMPLEMENTED true
  writeReg FEAT_CSV3_IMPLEMENTED true
  writeReg FEAT_DPB2_IMPLEMENTED true
  writeReg FEAT_E0PD_IMPLEMENTED true
  writeReg FEAT_EVT_IMPLEMENTED true
  writeReg FEAT_ExS_IMPLEMENTED true
  writeReg FEAT_FRINTTS_IMPLEMENTED true
  writeReg FEAT_FlagM2_IMPLEMENTED true
  writeReg FEAT_GTG_IMPLEMENTED true
  writeReg FEAT_MTE_IMPLEMENTED true
  writeReg FEAT_MTE2_IMPLEMENTED true
  writeReg FEAT_PMUv3p5_IMPLEMENTED true
  writeReg FEAT_RNG_IMPLEMENTED true
  writeReg FEAT_RNG_TRAP_IMPLEMENTED true
  writeReg FEAT_SB_IMPLEMENTED true
  writeReg FEAT_SPECRES_IMPLEMENTED true
  writeReg FEAT_SSBS_IMPLEMENTED true
  writeReg FEAT_SSBS2_IMPLEMENTED true
  writeReg FEAT_AMUv1p1_IMPLEMENTED true
  writeReg FEAT_BF16_IMPLEMENTED true
  writeReg FEAT_DGH_IMPLEMENTED true
  writeReg FEAT_ECV_IMPLEMENTED true
  writeReg FEAT_FGT_IMPLEMENTED true
  writeReg FEAT_HPMN0_IMPLEMENTED true
  writeReg FEAT_MPAMv0p1_IMPLEMENTED true
  writeReg FEAT_MPAMv1p1_IMPLEMENTED true
  writeReg FEAT_MTPMU_IMPLEMENTED true
  writeReg FEAT_PAuth2_IMPLEMENTED true
  writeReg FEAT_TWED_IMPLEMENTED true
  writeReg FEAT_AFP_IMPLEMENTED true
  writeReg FEAT_EBF16_IMPLEMENTED true
  writeReg FEAT_HCX_IMPLEMENTED true
  writeReg FEAT_LPA2_IMPLEMENTED true
  writeReg FEAT_LS64_IMPLEMENTED true
  writeReg FEAT_LS64_ACCDATA_IMPLEMENTED true
  writeReg FEAT_LS64_V_IMPLEMENTED true
  writeReg FEAT_MTE3_IMPLEMENTED true
  writeReg FEAT_PAN3_IMPLEMENTED true
  writeReg FEAT_PMUv3p7_IMPLEMENTED true
  writeReg FEAT_RPRES_IMPLEMENTED true
  writeReg FEAT_SPEv1p2_IMPLEMENTED true
  writeReg FEAT_WFxT_IMPLEMENTED true
  writeReg FEAT_XS_IMPLEMENTED true
  writeReg FEAT_CMOW_IMPLEMENTED true
  writeReg FEAT_Debugv8p8_IMPLEMENTED true
  writeReg FEAT_GICv3_NMI_IMPLEMENTED true
  writeReg FEAT_HBC_IMPLEMENTED true
  writeReg FEAT_MOPS_IMPLEMENTED true
  writeReg FEAT_NMI_IMPLEMENTED true
  writeReg FEAT_PMUv3_EXT64_IMPLEMENTED true
  writeReg FEAT_PMUv3_TH_IMPLEMENTED true
  writeReg FEAT_PMUv3p8_IMPLEMENTED true
  writeReg FEAT_SCTLR2_IMPLEMENTED true
  writeReg FEAT_SPEv1p3_IMPLEMENTED true
  writeReg FEAT_TCR2_IMPLEMENTED true
  writeReg FEAT_TIDCP1_IMPLEMENTED true
  writeReg FEAT_ADERR_IMPLEMENTED true
  writeReg FEAT_AIE_IMPLEMENTED true
  writeReg FEAT_ANERR_IMPLEMENTED true
  writeReg FEAT_CLRBHB_IMPLEMENTED true
  writeReg FEAT_CSSC_IMPLEMENTED true
  writeReg FEAT_Debugv8p9_IMPLEMENTED true
  writeReg FEAT_DoubleFault2_IMPLEMENTED true
  writeReg FEAT_ECBHB_IMPLEMENTED true
  writeReg FEAT_FGT2_IMPLEMENTED true
  writeReg FEAT_HAFT_IMPLEMENTED true
  writeReg FEAT_LRCPC3_IMPLEMENTED true
  writeReg FEAT_MTE4_IMPLEMENTED true
  writeReg FEAT_MTE_ASYM_FAULT_IMPLEMENTED true
  writeReg FEAT_MTE_ASYNC_IMPLEMENTED true
  writeReg FEAT_MTE_CANONICAL_TAGS_IMPLEMENTED true
  writeReg FEAT_MTE_NO_ADDRESS_TAGS_IMPLEMENTED true
  writeReg FEAT_MTE_PERM_IMPLEMENTED true
  writeReg FEAT_MTE_STORE_ONLY_IMPLEMENTED true
  writeReg FEAT_MTE_TAGGED_FAR_IMPLEMENTED true
  writeReg FEAT_PCSRv8p9_IMPLEMENTED true
  writeReg FEAT_PFAR_IMPLEMENTED true
  writeReg FEAT_PMUv3_EDGE_IMPLEMENTED true
  writeReg FEAT_PMUv3_ICNTR_IMPLEMENTED true
  writeReg FEAT_PMUv3_SS_IMPLEMENTED true
  writeReg FEAT_PMUv3p9_IMPLEMENTED true
  writeReg FEAT_PRFMSLC_IMPLEMENTED true
  writeReg FEAT_RASSAv2_IMPLEMENTED true
  writeReg FEAT_RASv2_IMPLEMENTED true
  writeReg FEAT_RPRFM_IMPLEMENTED true
  writeReg FEAT_S1PIE_IMPLEMENTED true
  writeReg FEAT_S1POE_IMPLEMENTED true
  writeReg FEAT_S2PIE_IMPLEMENTED true
  writeReg FEAT_S2POE_IMPLEMENTED true
  writeReg FEAT_SPECRES2_IMPLEMENTED true
  writeReg FEAT_SPE_CRR_IMPLEMENTED true
  writeReg FEAT_SPE_FDS_IMPLEMENTED true
  writeReg FEAT_SPEv1p4_IMPLEMENTED true
  writeReg FEAT_SPMU_IMPLEMENTED true
  writeReg FEAT_THE_IMPLEMENTED true
  writeReg FEAT_DoPD_IMPLEMENTED true
  writeReg FEAT_ETE_IMPLEMENTED true
  writeReg FEAT_SVE2_IMPLEMENTED true
  writeReg FEAT_SVE_AES_IMPLEMENTED true
  writeReg FEAT_SVE_BitPerm_IMPLEMENTED true
  writeReg FEAT_SVE_PMULL128_IMPLEMENTED true
  writeReg FEAT_SVE_SHA3_IMPLEMENTED true
  writeReg FEAT_SVE_SM4_IMPLEMENTED true
  writeReg FEAT_TME_IMPLEMENTED true
  writeReg FEAT_TRBE_IMPLEMENTED true
  writeReg FEAT_ETEv1p1_IMPLEMENTED true
  writeReg FEAT_BRBE_IMPLEMENTED true
  writeReg FEAT_ETEv1p2_IMPLEMENTED true
  writeReg FEAT_RME_IMPLEMENTED true
  writeReg FEAT_SME_IMPLEMENTED true
  writeReg FEAT_SME_F64F64_IMPLEMENTED true
  writeReg FEAT_SME_FA64_IMPLEMENTED true
  writeReg FEAT_SME_I16I64_IMPLEMENTED true
  writeReg FEAT_BRBEv1p1_IMPLEMENTED true
  writeReg FEAT_MEC_IMPLEMENTED true
  writeReg FEAT_SME2_IMPLEMENTED true
  writeReg FEAT_ABLE_IMPLEMENTED true
  writeReg FEAT_CHK_IMPLEMENTED true
  writeReg FEAT_D128_IMPLEMENTED true
  writeReg FEAT_EBEP_IMPLEMENTED true
  writeReg FEAT_ETEv1p3_IMPLEMENTED true
  writeReg FEAT_GCS_IMPLEMENTED true
  writeReg FEAT_ITE_IMPLEMENTED true
  writeReg FEAT_LSE128_IMPLEMENTED true
  writeReg FEAT_LVA3_IMPLEMENTED true
  writeReg FEAT_SEBEP_IMPLEMENTED true
  writeReg FEAT_SME2p1_IMPLEMENTED true
  writeReg FEAT_SME_F16F16_IMPLEMENTED true
  writeReg FEAT_SVE2p1_IMPLEMENTED true
  writeReg FEAT_SVE_B16B16_IMPLEMENTED true
  writeReg FEAT_SYSINSTR128_IMPLEMENTED true
  writeReg FEAT_SYSREG128_IMPLEMENTED true
  writeReg FEAT_TRBE_EXT_IMPLEMENTED true
  writeReg FEAT_TRBE_MPAM_IMPLEMENTED true
  writeReg v8Ap0_IMPLEMENTED true
  writeReg v8Ap1_IMPLEMENTED true
  writeReg v8Ap2_IMPLEMENTED true
  writeReg v8Ap3_IMPLEMENTED true
  writeReg v8Ap4_IMPLEMENTED true
  writeReg v8Ap5_IMPLEMENTED true
  writeReg v8Ap6_IMPLEMENTED true
  writeReg v8Ap7_IMPLEMENTED true
  writeReg v8Ap8_IMPLEMENTED true
  writeReg v8Ap9_IMPLEMENTED true
  writeReg v9Ap0_IMPLEMENTED true
  writeReg v9Ap1_IMPLEMENTED true
  writeReg v9Ap2_IMPLEMENTED true
  writeReg v9Ap3_IMPLEMENTED true
  writeReg v9Ap4_IMPLEMENTED true
  writeReg NUM_AMU_COUNTER_GROUPS 2
  writeReg NUM_AMU_CG0_MONITORS 4
  writeReg NUM_AMU_CG1_MONITORS 16
  writeReg NUM_PMU_COUNTERS 31
  writeReg NUM_BRBE_RECORDS 64
  writeReg NUM_GIC_PREEMPTION_BITS 5
  writeReg NUM_GIC_PRIORITY_BITS 5
  writeReg NUM_GIC_LIST_REGS 16
  writeReg NUM_BREAKPOINTS (Neg.neg 1)
  writeReg NUM_WATCHPOINTS (Neg.neg 1)
  writeReg __apply_effective_shareability true
  writeReg __cpy_mops_option_a_supported true
  writeReg __cpyf_mops_option_a_supported true
  writeReg __empam_force_ns_RAO false
  writeReg __empam_force_ns_implemented false
  writeReg __empam_sdeflt_implemented false
  writeReg __empam_tidr_implemented false
  writeReg __feat_rpres true
  writeReg __has_sme_priority_control true
  writeReg __isb_is_branch true
  writeReg __mpam_frac CFG_MPAM_frac_none
  writeReg __mpam_major CFG_MPAM_none
  writeReg __mte_implemented (0x2 : (BitVec 4))
  writeReg __set_mops_option_a_supported true
  writeReg __setg_mops_option_a_supported true
  writeReg __sme_only false
  writeReg __block_bbm_implemented (BitVec.toNat (0x2 : (BitVec 4)))
  writeReg __has_sve_extended_bf16 2
  writeReg __max_implemented_smeveclen 512
  writeReg __max_implemented_sveveclen 2048
  writeReg __supported_pa_size 56
  writeReg CFG_RVBAR (Sail.BitVec.zeroExtend (0x0 : (BitVec 4)) 64)
  writeReg __impdef_TG0 (0b00 : (BitVec 2))
  writeReg __impdef_TG1 (0b10 : (BitVec 2))
  writeReg __mpam_has_hcr true
  writeReg __mpam_partid_max (Zeros (n := 16))
  writeReg __mpam_pmg_max (Zeros (n := 8))
  writeReg __mpam_vpmr_max (Zeros (n := 3))
  writeReg __GIC_Active none
  writeReg __GIC_Pending none
  writeReg __tlb_enabled false
  writeReg __exclusive_granule_size (0x4 : (BitVec 4))
  writeReg __num_ctx_breakpoints (← readReg NUM_BREAKPOINTS)
  writeReg CFG_MPIDR (0x80000000 : (BitVec 32))
  writeReg __CNTbase_frequency (0x05F5E100 : (BitVec 32))
  writeReg __dczid_log2_block_size (BitVec.toNat (0x8 : (BitVec 4)))
  writeReg __gmid_log2_block_size (BitVec.toNat (0x4 : (BitVec 4)))
  writeReg __mecid_width (0x0 : (BitVec 4))
  writeReg __mpam_has_altsp true
  writeReg __rme_l0gptsz (Zeros (n := 4))
  writeReg __supported_va_size 56
  writeReg __g1_activity_monitor_implemented (0x0000 : (BitVec 16))
  writeReg __g1_activity_monitor_offset_implemented (0x0000 : (BitVec 16))
  writeReg __CTIBase (integer_subrange (BitVec.toNat (0x22020000 : (BitVec 32))) (56 -i 1) 0)
  writeReg __CNTControlBase (integer_subrange (BitVec.toNat (0x16200000 : (BitVec 32))) (56 -i 1) 0)
  writeReg __ExtDebugBase (integer_subrange (BitVec.toNat (0x22010000 : (BitVec 32))) (56 -i 1) 0)
  writeReg __GICCPUInterfaceBase (integer_subrange (BitVec.toNat (0x13082000 : (BitVec 32)))
    (56 -i 1) 0)
  writeReg __GICDistBase (integer_subrange (BitVec.toNat (0x2C010000 : (BitVec 32))) (56 -i 1) 0)
  writeReg __GICITSControlBase (integer_subrange (BitVec.toNat (0x2C120000 : (BitVec 32))) (56 -i 1)
    0)
  writeReg __PMUBase (integer_subrange (BitVec.toNat (0x22030000 : (BitVec 32))) (56 -i 1) 0)
  writeReg __syncAbortOnReadNormCache true
  writeReg __syncAbortOnReadNormNonCache true
  writeReg __syncAbortOnDeviceRead true
  writeReg __syncAbortOnSoRead true
  writeReg __syncAbortOnSoWrite true
  writeReg __syncAbortOnPrefetch true
  writeReg __syncAbortOnTTWCache true
  writeReg __syncAbortOnTTWNonCache true
  writeReg __syncAbortOnWriteNormCache false
  writeReg __syncAbortOnWriteNormNonCache false
  writeReg __syncAbortOnDeviceWrite false
  writeReg __unpred_tsize_aborts true
  writeReg __ignore_rvbar_in_aarch32 false
  writeReg __trickbox_enabled false
  writeReg __mops_forward_copy true
  writeReg __DBG_ROM_ADDR (integer_subrange (BitVec.toNat (0x22000000 : (BitVec 32))) (56 -i 1) 0)
  writeReg CFG_RMR_AA64 (0b1 : (BitVec 1))
  writeReg ZCR_EL3_LEN_VALUE (Neg.neg 1)
  writeReg CPTR_EL3_EZ_VALUE (Neg.neg 1)
  writeReg CPTR_EL3_ESM_VALUE (Neg.neg 1)
  writeReg SMCR_EL3_LEN_VALUE (Neg.neg 1)
  writeReg __has_spe_pseudo_cycles false
  writeReg HEAP_BASE (Sail.BitVec.zeroExtend (0x00000000 : (BitVec 32)) 64)
  writeReg HEAP_LIMIT (Sail.BitVec.zeroExtend (0x0F000000 : (BitVec 32)) 64)
  writeReg STACK_BASE (Sail.BitVec.zeroExtend (0x10000000 : (BitVec 32)) 64)
  writeReg STACK_LIMIT (Sail.BitVec.zeroExtend (0x0F000000 : (BitVec 32)) 64)
  writeReg __emulator_termination_opcode none
  (initialize_registers ())

end Armv9.Functions
