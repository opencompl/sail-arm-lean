import Armv9.Sail.Sail
import Armv9.Sail.BitVec

open PreSail

set_option maxHeartbeats 1_000_000_000
set_option maxRecDepth 1_000_000
set_option linter.unusedVariables false
set_option match.ignoreUnusedAlts true

open Sail

abbrev bits k_n := (BitVec k_n)

/-- Type quantifiers: k_a : Type -/
inductive option (k_a : Type) where
  | Some (_ : k_a)
  | None (_ : Unit)
  deriving Inhabited, BEq

inductive signal where | LOW | HIGH
  deriving Inhabited, BEq

inductive exception where
  | Error_Undefined (_ : Unit)
  | Error_See (_ : String)
  | Error_ImplementationDefined (_ : String)
  | Error_ReservedEncoding (_ : Unit)
  | Error_ExceptionTaken (_ : Unit)
  | Error_Unpredictable (_ : Unit)
  | Error_ConstrainedUnpredictable (_ : Unit)
  | Error_SError (_ : Bool)
  deriving Inhabited, BEq





abbrev vector_length := Int

abbrev predicate_length := Int

abbrev Configuration_Type := (BitVec 32)

abbrev DormantCtl_Type := (BitVec 32)

inductive Feature where | FEAT_AA32EL0 | FEAT_AA32EL1 | FEAT_AA32EL2 | FEAT_AA32EL3 | FEAT_AA64EL0 | FEAT_AA64EL1 | FEAT_AA64EL2 | FEAT_AA64EL3 | FEAT_EL0 | FEAT_EL1 | FEAT_EL2 | FEAT_EL3 | FEAT_AES | FEAT_AdvSIMD | FEAT_CSV2_1p1 | FEAT_CSV2_1p2 | FEAT_CSV2_2 | FEAT_CSV2_3 | FEAT_DoubleLock | FEAT_ETMv4 | FEAT_ETMv4p1 | FEAT_ETMv4p2 | FEAT_ETMv4p3 | FEAT_ETMv4p4 | FEAT_ETMv4p5 | FEAT_ETMv4p6 | FEAT_ETS2 | FEAT_FP | FEAT_GICv3 | FEAT_GICv3_LEGACY | FEAT_GICv3_TDIR | FEAT_GICv3p1 | FEAT_GICv4 | FEAT_GICv4p1 | FEAT_IVIPT | FEAT_PCSRv8 | FEAT_PMULL | FEAT_PMUv3 | FEAT_PMUv3_EXT | FEAT_PMUv3_EXT32 | FEAT_SHA1 | FEAT_SHA256 | FEAT_TRC_EXT | FEAT_TRC_SR | FEAT_nTLBPA | FEAT_CRC32 | FEAT_Debugv8p1 | FEAT_HAFDBS | FEAT_HPDS | FEAT_LOR | FEAT_LSE | FEAT_PAN | FEAT_PMUv3p1 | FEAT_RDM | FEAT_VHE | FEAT_VMID16 | FEAT_AA32BF16 | FEAT_AA32HPD | FEAT_AA32I8MM | FEAT_ASMv8p2 | FEAT_DPB | FEAT_Debugv8p2 | FEAT_EDHSR | FEAT_F32MM | FEAT_F64MM | FEAT_FP16 | FEAT_HPDS2 | FEAT_I8MM | FEAT_IESB | FEAT_LPA | FEAT_LSMAOC | FEAT_LVA | FEAT_MPAM | FEAT_PAN2 | FEAT_PCSRv8p2 | FEAT_RAS | FEAT_SHA3 | FEAT_SHA512 | FEAT_SM3 | FEAT_SM4 | FEAT_SPE | FEAT_SVE | FEAT_TTCNP | FEAT_UAO | FEAT_VPIPT | FEAT_XNX | FEAT_CCIDX | FEAT_CONSTPACFIELD | FEAT_EPAC | FEAT_FCMA | FEAT_FPAC | FEAT_FPACCOMBINE | FEAT_JSCVT | FEAT_LRCPC | FEAT_NV | FEAT_PACIMP | FEAT_PACQARMA3 | FEAT_PACQARMA5 | FEAT_PAuth | FEAT_SPEv1p1 | FEAT_AMUv1 | FEAT_BBM | FEAT_CNTSC | FEAT_DIT | FEAT_Debugv8p4 | FEAT_DotProd | FEAT_DoubleFault | FEAT_FHM | FEAT_FlagM | FEAT_IDST | FEAT_LRCPC2 | FEAT_LSE2 | FEAT_NV2 | FEAT_PMUv3p4 | FEAT_RASSAv1p1 | FEAT_RASv1p1 | FEAT_S2FWB | FEAT_SEL2 | FEAT_TLBIOS | FEAT_TLBIRANGE | FEAT_TRF | FEAT_TTL | FEAT_TTST | FEAT_BTI | FEAT_CSV2 | FEAT_CSV3 | FEAT_DPB2 | FEAT_E0PD | FEAT_EVT | FEAT_ExS | FEAT_FRINTTS | FEAT_FlagM2 | FEAT_GTG | FEAT_MTE | FEAT_MTE2 | FEAT_PMUv3p5 | FEAT_RNG | FEAT_RNG_TRAP | FEAT_SB | FEAT_SPECRES | FEAT_SSBS | FEAT_SSBS2 | FEAT_AMUv1p1 | FEAT_BF16 | FEAT_DGH | FEAT_ECV | FEAT_FGT | FEAT_HPMN0 | FEAT_MPAMv0p1 | FEAT_MPAMv1p1 | FEAT_MTPMU | FEAT_PAuth2 | FEAT_TWED | FEAT_AFP | FEAT_EBF16 | FEAT_HCX | FEAT_LPA2 | FEAT_LS64 | FEAT_LS64_ACCDATA | FEAT_LS64_V | FEAT_MTE3 | FEAT_PAN3 | FEAT_PMUv3p7 | FEAT_RPRES | FEAT_SPEv1p2 | FEAT_WFxT | FEAT_XS | FEAT_CMOW | FEAT_Debugv8p8 | FEAT_GICv3_NMI | FEAT_HBC | FEAT_MOPS | FEAT_NMI | FEAT_PMUv3_EXT64 | FEAT_PMUv3_TH | FEAT_PMUv3p8 | FEAT_SCTLR2 | FEAT_SPEv1p3 | FEAT_TCR2 | FEAT_TIDCP1 | FEAT_ADERR | FEAT_AIE | FEAT_ANERR | FEAT_CLRBHB | FEAT_CSSC | FEAT_Debugv8p9 | FEAT_DoubleFault2 | FEAT_ECBHB | FEAT_FGT2 | FEAT_HAFT | FEAT_LRCPC3 | FEAT_MTE4 | FEAT_MTE_ASYM_FAULT | FEAT_MTE_ASYNC | FEAT_MTE_CANONICAL_TAGS | FEAT_MTE_NO_ADDRESS_TAGS | FEAT_MTE_PERM | FEAT_MTE_STORE_ONLY | FEAT_MTE_TAGGED_FAR | FEAT_PCSRv8p9 | FEAT_PFAR | FEAT_PMUv3_EDGE | FEAT_PMUv3_ICNTR | FEAT_PMUv3_SS | FEAT_PMUv3p9 | FEAT_PRFMSLC | FEAT_RASSAv2 | FEAT_RASv2 | FEAT_RPRFM | FEAT_S1PIE | FEAT_S1POE | FEAT_S2PIE | FEAT_S2POE | FEAT_SPECRES2 | FEAT_SPE_CRR | FEAT_SPE_FDS | FEAT_SPEv1p4 | FEAT_SPMU | FEAT_THE | FEAT_DoPD | FEAT_ETE | FEAT_SVE2 | FEAT_SVE_AES | FEAT_SVE_BitPerm | FEAT_SVE_PMULL128 | FEAT_SVE_SHA3 | FEAT_SVE_SM4 | FEAT_TME | FEAT_TRBE | FEAT_ETEv1p1 | FEAT_BRBE | FEAT_ETEv1p2 | FEAT_RME | FEAT_SME | FEAT_SME_F64F64 | FEAT_SME_FA64 | FEAT_SME_I16I64 | FEAT_BRBEv1p1 | FEAT_MEC | FEAT_SME2 | FEAT_ABLE | FEAT_CHK | FEAT_D128 | FEAT_EBEP | FEAT_ETEv1p3 | FEAT_GCS | FEAT_ITE | FEAT_LSE128 | FEAT_LVA3 | FEAT_SEBEP | FEAT_SME2p1 | FEAT_SME_F16F16 | FEAT_SVE2p1 | FEAT_SVE_B16B16 | FEAT_SYSINSTR128 | FEAT_SYSREG128 | FEAT_TRBE_EXT | FEAT_TRBE_MPAM
  deriving Inhabited, BEq

inductive ArchVersion where | v8Ap0 | v8Ap1 | v8Ap2 | v8Ap3 | v8Ap4 | v8Ap5 | v8Ap6 | v8Ap7 | v8Ap8 | v8Ap9 | v9Ap0 | v9Ap1 | v9Ap2 | v9Ap3 | v9Ap4
  deriving Inhabited, BEq

abbrev SCRType := (BitVec 64)

abbrev SCTLRType := (BitVec 64)

abbrev MAIRType := (BitVec 64)

abbrev S1PIRType := (BitVec 64)

abbrev S1PORType := (BitVec 64)

abbrev S2PIRType := (BitVec 64)

abbrev ESRType := (BitVec 64)

abbrev FPCRType := (BitVec 64)

abbrev BRBSRCType := (BitVec 64)

abbrev BRBTGTType := (BitVec 64)

abbrev BRBINFType := (BitVec 64)

inductive Signal where | Signal_Low | Signal_High
  deriving Inhabited, BEq

inductive SecurityState where | SS_NonSecure | SS_Root | SS_Realm | SS_Secure
  deriving Inhabited, BEq

structure ProcState where
  N : (BitVec 1)
  Z : (BitVec 1)
  C : (BitVec 1)
  V : (BitVec 1)
  D : (BitVec 1)
  A : (BitVec 1)
  I : (BitVec 1)
  F : (BitVec 1)
  EXLOCK : (BitVec 1)
  PAN : (BitVec 1)
  UAO : (BitVec 1)
  DIT : (BitVec 1)
  TCO : (BitVec 1)
  PM : (BitVec 1)
  PPEND : (BitVec 1)
  BTYPE : (BitVec 2)
  ZA : (BitVec 1)
  SM : (BitVec 1)
  ALLINT : (BitVec 1)
  SS : (BitVec 1)
  IL : (BitVec 1)
  EL : (BitVec 2)
  nRW : (BitVec 1)
  SP : (BitVec 1)
  Q : (BitVec 1)
  GE : (BitVec 4)
  SSBS : (BitVec 1)
  IT : (BitVec 8)
  J : (BitVec 1)
  T : (BitVec 1)
  E : (BitVec 1)
  M : (BitVec 5)
  deriving Inhabited, BEq

inductive PrivilegeLevel where | PL3 | PL2 | PL1 | PL0
  deriving Inhabited, BEq

inductive InstrSet where | InstrSet_A64 | InstrSet_A32 | InstrSet_T32
  deriving Inhabited, BEq

inductive DSBAlias where | DSBAlias_SSBB | DSBAlias_PSSBB | DSBAlias_DSB
  deriving Inhabited, BEq

inductive WFxType where | WFxType_WFE | WFxType_WFI | WFxType_WFET | WFxType_WFIT
  deriving Inhabited, BEq

inductive ExceptionalOccurrenceTargetState where | AArch32_NonDebugState | AArch64_NonDebugState | DebugState
  deriving Inhabited, BEq

abbrev PARTIDtype := (BitVec 16)

abbrev PMGtype := (BitVec 8)

inductive PARTIDspaceType where | PIdSpace_Secure | PIdSpace_Root | PIdSpace_Realm | PIdSpace_NonSecure
  deriving Inhabited, BEq

structure MPAMinfo where
  mpam_sp : PARTIDspaceType
  partid : PARTIDtype
  pmg : PMGtype
  deriving Inhabited, BEq

inductive AccessType where | AccessType_IFETCH | AccessType_GPR | AccessType_ASIMD | AccessType_SVE | AccessType_SME | AccessType_IC | AccessType_DC | AccessType_DCZero | AccessType_AT | AccessType_NV2 | AccessType_SPE | AccessType_GCS | AccessType_GPTW | AccessType_TTW
  deriving Inhabited, BEq

inductive MemOp where | MemOp_LOAD | MemOp_STORE | MemOp_PREFETCH
  deriving Inhabited, BEq

inductive VARange where | VARange_LOWER | VARange_UPPER
  deriving Inhabited, BEq

inductive MemAtomicOp where | MemAtomicOp_GCSSS1 | MemAtomicOp_ADD | MemAtomicOp_BIC | MemAtomicOp_EOR | MemAtomicOp_ORR | MemAtomicOp_SMAX | MemAtomicOp_SMIN | MemAtomicOp_UMAX | MemAtomicOp_UMIN | MemAtomicOp_SWP | MemAtomicOp_CAS
  deriving Inhabited, BEq

inductive CacheOp where | CacheOp_Clean | CacheOp_Invalidate | CacheOp_CleanInvalidate
  deriving Inhabited, BEq

inductive CacheOpScope where | CacheOpScope_SetWay | CacheOpScope_PoU | CacheOpScope_PoC | CacheOpScope_PoE | CacheOpScope_PoP | CacheOpScope_PoDP | CacheOpScope_PoPA | CacheOpScope_ALLU | CacheOpScope_ALLUIS
  deriving Inhabited, BEq

inductive CacheType where | CacheType_Data | CacheType_Tag | CacheType_Data_Tag | CacheType_Instruction
  deriving Inhabited, BEq

inductive CachePASpace where | CPAS_NonSecure | CPAS_Any | CPAS_RealmNonSecure | CPAS_Realm | CPAS_Root | CPAS_SecureNonSecure | CPAS_Secure
  deriving Inhabited, BEq

structure AccessDescriptor where
  acctype : AccessType
  el : (BitVec 2)
  ss : SecurityState
  acqsc : Bool
  acqpc : Bool
  relsc : Bool
  limitedordered : Bool
  exclusive : Bool
  atomicop : Bool
  modop : MemAtomicOp
  nontemporal : Bool
  read : Bool
  write : Bool
  cacheop : CacheOp
  opscope : CacheOpScope
  cachetype : CacheType
  pan : Bool
  transactional : Bool
  nonfault : Bool
  firstfault : Bool
  first : Bool
  contiguous : Bool
  streamingsve : Bool
  ls64 : Bool
  mops : Bool
  rcw : Bool
  rcws : Bool
  toplevel : Bool
  varange : VARange
  a32lsmd : Bool
  tagchecked : Bool
  tagaccess : Bool
  mpam : MPAMinfo
  deriving Inhabited, BEq

inductive MemType where | MemType_Normal | MemType_Device
  deriving Inhabited, BEq

inductive DeviceType where | DeviceType_GRE | DeviceType_nGRE | DeviceType_nGnRE | DeviceType_nGnRnE
  deriving Inhabited, BEq

structure MemAttrHints where
  attrs : (BitVec 2)
  hints : (BitVec 2)
  transient : Bool
  deriving Inhabited, BEq

inductive Shareability where | Shareability_NSH | Shareability_ISH | Shareability_OSH
  deriving Inhabited, BEq

inductive MemTagType where | MemTag_Untagged | MemTag_AllocationTagged | MemTag_CanonicallyTagged
  deriving Inhabited, BEq

structure MemoryAttributes where
  memtype : MemType
  device : DeviceType
  inner : MemAttrHints
  outer : MemAttrHints
  shareability : Shareability
  tags : MemTagType
  notagaccess : Bool
  xs : (BitVec 1)
  deriving Inhabited, BEq

inductive PASpace where | PAS_NonSecure | PAS_Secure | PAS_Root | PAS_Realm
  deriving Inhabited, BEq

structure FullAddress where
  paspace : PASpace
  address : (BitVec 56)
  deriving Inhabited, BEq

inductive GPCF where | GPCF_None | GPCF_AddressSize | GPCF_Walk | GPCF_EABT | GPCF_Fail
  deriving Inhabited, BEq

structure GPCFRecord where
  gpf : GPCF
  level : Int
  deriving Inhabited, BEq

inductive Fault where | Fault_None | Fault_AccessFlag | Fault_Alignment | Fault_Background | Fault_Domain | Fault_Permission | Fault_Translation | Fault_AddressSize | Fault_SyncExternal | Fault_SyncExternalOnWalk | Fault_SyncParity | Fault_SyncParityOnWalk | Fault_GPCFOnWalk | Fault_GPCFOnOutput | Fault_AsyncParity | Fault_AsyncExternal | Fault_TagCheck | Fault_Debug | Fault_TLBConflict | Fault_BranchTarget | Fault_HWUpdateAccessFlag | Fault_Lockdown | Fault_Exclusive | Fault_ICacheMaint
  deriving Inhabited, BEq

inductive ErrorState where | ErrorState_UC | ErrorState_UEU | ErrorState_UEO | ErrorState_UER | ErrorState_CE | ErrorState_Uncategorized | ErrorState_IMPDEF
  deriving Inhabited, BEq

structure FaultRecord where
  statuscode : Fault
  access : AccessDescriptor
  ipaddress : FullAddress
  gpcf : GPCFRecord
  paddress : FullAddress
  gpcfs2walk : Bool
  s2fs1walk : Bool
  write : Bool
  s1tagnotdata : Bool
  tagaccess : Bool
  level : Int
  extflag : (BitVec 1)
  secondstage : Bool
  assuredonly : Bool
  toplevel : Bool
  overlay : Bool
  dirtybit : Bool
  domain : (BitVec 4)
  merrorstate : ErrorState
  debugmoe : (BitVec 4)
  deriving Inhabited, BEq

structure PhysMemRetStatus where
  statuscode : Fault
  extflag : (BitVec 1)
  merrorstate : ErrorState
  store64bstatus : (BitVec 64)
  deriving Inhabited, BEq

structure Permissions where
  ap_table : (BitVec 2)
  xn_table : (BitVec 1)
  pxn_table : (BitVec 1)
  uxn_table : (BitVec 1)
  ap : (BitVec 3)
  xn : (BitVec 1)
  uxn : (BitVec 1)
  pxn : (BitVec 1)
  ppi : (BitVec 4)
  upi : (BitVec 4)
  ndirty : (BitVec 1)
  s2pi : (BitVec 4)
  s2dirty : (BitVec 1)
  po_index : (BitVec 4)
  s2po_index : (BitVec 4)
  s2ap : (BitVec 2)
  s2tag_na : (BitVec 1)
  s2xnx : (BitVec 1)
  s2xn : (BitVec 1)
  deriving Inhabited, BEq

structure S1AccessControls where
  r : (BitVec 1)
  w : (BitVec 1)
  x : (BitVec 1)
  gcs : (BitVec 1)
  overlay : Bool
  or : (BitVec 1)
  ow : (BitVec 1)
  ox : (BitVec 1)
  wxn : (BitVec 1)
  deriving Inhabited, BEq

structure S2AccessControls where
  r : (BitVec 1)
  w : (BitVec 1)
  x : (BitVec 1)
  r_rcw : (BitVec 1)
  w_rcw : (BitVec 1)
  r_mmu : (BitVec 1)
  w_mmu : (BitVec 1)
  toplevel0 : (BitVec 1)
  toplevel1 : (BitVec 1)
  overlay : Bool
  or : (BitVec 1)
  ow : (BitVec 1)
  ox : (BitVec 1)
  or_rcw : (BitVec 1)
  ow_rcw : (BitVec 1)
  or_mmu : (BitVec 1)
  ow_mmu : (BitVec 1)
  deriving Inhabited, BEq

inductive MBReqDomain where | MBReqDomain_Nonshareable | MBReqDomain_InnerShareable | MBReqDomain_OuterShareable | MBReqDomain_FullSystem
  deriving Inhabited, BEq

inductive MBReqTypes where | MBReqTypes_Reads | MBReqTypes_Writes | MBReqTypes_All
  deriving Inhabited, BEq

inductive PrefetchHint where | Prefetch_READ | Prefetch_WRITE | Prefetch_EXEC
  deriving Inhabited, BEq

inductive Unpredictable where | Unpredictable_VMSR | Unpredictable_WBOVERLAPLD | Unpredictable_WBOVERLAPST | Unpredictable_LDPOVERLAP | Unpredictable_BASEOVERLAP | Unpredictable_DATAOVERLAP | Unpredictable_DEVPAGE2 | Unpredictable_INSTRDEVICE | Unpredictable_RESCPACR | Unpredictable_RESMAIR | Unpredictable_S1CTAGGED | Unpredictable_S2RESMEMATTR | Unpredictable_RESTEXCB | Unpredictable_RESPRRR | Unpredictable_RESDACR | Unpredictable_RESVTCRS | Unpredictable_RESTnSZ | Unpredictable_RESTCF | Unpredictable_DEVICETAGSTORE | Unpredictable_OORTnSZ | Unpredictable_LARGEIPA | Unpredictable_ESRCONDPASS | Unpredictable_ILZEROIT | Unpredictable_ILZEROT | Unpredictable_BPVECTORCATCHPRI | Unpredictable_VCMATCHHALF | Unpredictable_VCMATCHDAPA | Unpredictable_WPMASKANDBAS | Unpredictable_WPBASCONTIGUOUS | Unpredictable_RESWPMASK | Unpredictable_WPMASKEDBITS | Unpredictable_RESBPWPCTRL | Unpredictable_BPNOTIMPL | Unpredictable_RESBPTYPE | Unpredictable_RESMDSELR | Unpredictable_BPNOTCTXCMP | Unpredictable_BPMATCHHALF | Unpredictable_BPMISMATCHHALF | Unpredictable_BPLINKINGDISABLED | Unpredictable_RESBPMASK | Unpredictable_BPMASK | Unpredictable_BPMASKEDBITS | Unpredictable_BPLINKEDADDRMATCH | Unpredictable_RESTARTALIGNPC | Unpredictable_RESTARTZEROUPPERPC | Unpredictable_ZEROUPPER | Unpredictable_ERETZEROUPPERPC | Unpredictable_A32FORCEALIGNPC | Unpredictable_SMD | Unpredictable_NONFAULT | Unpredictable_SVEZEROUPPER | Unpredictable_SVELDNFDATA | Unpredictable_SVELDNFZERO | Unpredictable_CHECKSPNONEACTIVE | Unpredictable_SMEZEROUPPER | Unpredictable_NVNV1 | Unpredictable_Shareability | Unpredictable_AFUPDATE | Unpredictable_DBUPDATE | Unpredictable_IESBinDebug | Unpredictable_BADPMSFCR | Unpredictable_ZEROBTYPE | Unpredictable_EL2TIMESTAMP | Unpredictable_EL1TIMESTAMP | Unpredictable_RESERVEDNSxB | Unpredictable_WFxTDEBUG | Unpredictable_LS64UNSUPPORTED | Unpredictable_MISALIGNEDATOMIC | Unpredictable_CLEARERRITEZERO | Unpredictable_ALUEXCEPTIONRETURN | Unpredictable_IGNORETRAPINDEBUG | Unpredictable_DBGxVR_RESS | Unpredictable_PMUEVENTCOUNTER | Unpredictable_PMSCR_PCT | Unpredictable_CounterReservedForEL2 | Unpredictable_BRBFILTRATE | Unpredictable_MOPSOVERLAP31 | Unpredictable_STOREONLYTAGCHECKEDCAS | Unpredictable_RESTC
  deriving Inhabited, BEq

inductive Constraint where | Constraint_NONE | Constraint_UNKNOWN | Constraint_UNDEF | Constraint_UNDEFEL0 | Constraint_NOP | Constraint_TRUE | Constraint_FALSE | Constraint_DISABLED | Constraint_UNCOND | Constraint_COND | Constraint_ADDITIONAL_DECODE | Constraint_WBSUPPRESS | Constraint_FAULT | Constraint_LIMITED_ATOMICITY | Constraint_NVNV1_00 | Constraint_NVNV1_01 | Constraint_NVNV1_11 | Constraint_EL1TIMESTAMP | Constraint_EL2TIMESTAMP | Constraint_OSH | Constraint_ISH | Constraint_NSH | Constraint_NC | Constraint_WT | Constraint_WB | Constraint_FORCE | Constraint_FORCENOSLCHECK | Constraint_MAPTOALLOCATED | Constraint_PMSCR_PCT_VIRT
  deriving Inhabited, BEq

structure CacheRecord where
  acctype : AccessType
  cacheop : CacheOp
  opscope : CacheOpScope
  cachetype : CacheType
  regval : (BitVec 64)
  paddress : FullAddress
  vaddress : (BitVec 64)
  setnum : Int
  waynum : Int
  level : Int
  shareability : Shareability
  translated : Bool
  is_vmid_valid : Bool
  vmid : (BitVec 16)
  is_asid_valid : Bool
  asid : (BitVec 16)
  security : SecurityState
  cpas : CachePASpace
  deriving Inhabited, BEq

inductive RestrictType where | RestrictType_DataValue | RestrictType_ControlFlow | RestrictType_CachePrefetch | RestrictType_Other
  deriving Inhabited, BEq

structure ExecutionCntxt where
  is_vmid_valid : Bool
  all_vmid : Bool
  vmid : (BitVec 16)
  is_asid_valid : Bool
  all_asid : Bool
  asid : (BitVec 16)
  target_el : (BitVec 2)
  security : SecurityState
  restriction : RestrictType
  deriving Inhabited, BEq

inductive FPExc where | FPExc_InvalidOp | FPExc_DivideByZero | FPExc_Overflow | FPExc_Underflow | FPExc_Inexact | FPExc_InputDenorm
  deriving Inhabited, BEq

inductive FPRounding where | FPRounding_TIEEVEN | FPRounding_POSINF | FPRounding_NEGINF | FPRounding_ZERO | FPRounding_TIEAWAY | FPRounding_ODD
  deriving Inhabited, BEq

inductive FPType where | FPType_Zero | FPType_Denormal | FPType_Nonzero | FPType_Infinity | FPType_QNaN | FPType_SNaN
  deriving Inhabited, BEq

inductive BranchType where | BranchType_DIRCALL | BranchType_INDCALL | BranchType_ERET | BranchType_DBGEXIT | BranchType_RET | BranchType_DIR | BranchType_INDIR | BranchType_EXCEPTION | BranchType_TMFAIL | BranchType_RESET | BranchType_UNKNOWN
  deriving Inhabited, BEq

inductive InterruptID where | InterruptID_PMUIRQ | InterruptID_COMMIRQ | InterruptID_CTIIRQ | InterruptID_COMMRX | InterruptID_COMMTX | InterruptID_CNTP | InterruptID_CNTHP | InterruptID_CNTHPS | InterruptID_CNTPS | InterruptID_CNTV | InterruptID_CNTHV | InterruptID_CNTHVS | InterruptID_PMBIRQ
  deriving Inhabited, BEq

inductive Exception where | Exception_Uncategorized | Exception_WFxTrap | Exception_CP15RTTrap | Exception_CP15RRTTrap | Exception_CP14RTTrap | Exception_CP14DTTrap | Exception_CP14RRTTrap | Exception_AdvSIMDFPAccessTrap | Exception_FPIDTrap | Exception_LDST64BTrap | Exception_PACTrap | Exception_IllegalState | Exception_SupervisorCall | Exception_HypervisorCall | Exception_MonitorCall | Exception_SystemRegisterTrap | Exception_ERetTrap | Exception_InstructionAbort | Exception_PCAlignment | Exception_DataAbort | Exception_NV2DataAbort | Exception_PACFail | Exception_SPAlignment | Exception_FPTrappedException | Exception_SError | Exception_Breakpoint | Exception_SoftwareStep | Exception_Watchpoint | Exception_NV2Watchpoint | Exception_SoftwareBreakpoint | Exception_VectorCatch | Exception_IRQ | Exception_SVEAccessTrap | Exception_SMEAccessTrap | Exception_TSTARTAccessTrap | Exception_GPC | Exception_BranchTarget | Exception_MemCpyMemSet | Exception_GCSFail | Exception_SystemRegister128Trap | Exception_FIQ
  deriving Inhabited, BEq

structure ExceptionRecord where
  exceptype : Exception
  syndrome : (BitVec 25)
  syndrome2 : (BitVec 24)
  paddress : FullAddress
  vaddress : (BitVec 64)
  ipavalid : Bool
  pavalid : Bool
  NS : (BitVec 1)
  ipaddress : (BitVec 56)
  trappedsyscallinst : Bool
  deriving Inhabited, BEq

inductive TranslationStage where | TranslationStage_1 | TranslationStage_12
  deriving Inhabited, BEq

inductive ATAccess where | ATAccess_Read | ATAccess_Write | ATAccess_ReadPAN | ATAccess_WritePAN
  deriving Inhabited, BEq

inductive Regime where | Regime_EL3 | Regime_EL30 | Regime_EL2 | Regime_EL20 | Regime_EL10
  deriving Inhabited, BEq

inductive TGx where | TGx_4KB | TGx_16KB | TGx_64KB
  deriving Inhabited, BEq

inductive DescriptorType where | DescriptorType_Table | DescriptorType_Leaf | DescriptorType_Invalid
  deriving Inhabited, BEq

inductive SDFType where | SDFType_Table | SDFType_Invalid | SDFType_Supersection | SDFType_Section | SDFType_LargePage | SDFType_SmallPage
  deriving Inhabited, BEq

structure TTWState where
  istable : Bool
  level : Int
  baseaddress : FullAddress
  contiguous : (BitVec 1)
  s1assured : Bool
  s2assuredonly : (BitVec 1)
  disch : (BitVec 1)
  nG : (BitVec 1)
  guardedpage : (BitVec 1)
  sdftype : SDFType
  domain : (BitVec 4)
  memattrs : MemoryAttributes
  permissions : Permissions
  deriving Inhabited, BEq

structure S1TTWParams where
  ha : (BitVec 1)
  hd : (BitVec 1)
  tbi : (BitVec 1)
  tbid : (BitVec 1)
  nfd : (BitVec 1)
  e0pd : (BitVec 1)
  d128 : (BitVec 1)
  aie : (BitVec 1)
  mair2 : MAIRType
  ds : (BitVec 1)
  ps : (BitVec 3)
  txsz : (BitVec 6)
  epan : (BitVec 1)
  dct : (BitVec 1)
  nv1 : (BitVec 1)
  cmow : (BitVec 1)
  pnch : (BitVec 1)
  disch : (BitVec 1)
  haft : (BitVec 1)
  mtx : (BitVec 1)
  skl : (BitVec 2)
  pie : (BitVec 1)
  pir : S1PIRType
  pire0 : S1PIRType
  emec : (BitVec 1)
  amec : (BitVec 1)
  t0sz : (BitVec 3)
  t1sz : (BitVec 3)
  uwxn : (BitVec 1)
  tgx : TGx
  irgn : (BitVec 2)
  orgn : (BitVec 2)
  sh : (BitVec 2)
  hpd : (BitVec 1)
  ee : (BitVec 1)
  wxn : (BitVec 1)
  ntlsmd : (BitVec 1)
  dc : (BitVec 1)
  sif : (BitVec 1)
  mair : MAIRType
  deriving Inhabited, BEq

structure S2TTWParams where
  ha : (BitVec 1)
  hd : (BitVec 1)
  sl2 : (BitVec 1)
  ds : (BitVec 1)
  d128 : (BitVec 1)
  sw : (BitVec 1)
  nsw : (BitVec 1)
  sa : (BitVec 1)
  nsa : (BitVec 1)
  ps : (BitVec 3)
  txsz : (BitVec 6)
  fwb : (BitVec 1)
  cmow : (BitVec 1)
  skl : (BitVec 2)
  s2pie : (BitVec 1)
  s2pir : S2PIRType
  tl0 : (BitVec 1)
  tl1 : (BitVec 1)
  assuredonly : (BitVec 1)
  haft : (BitVec 1)
  emec : (BitVec 1)
  s : (BitVec 1)
  t0sz : (BitVec 4)
  tgx : TGx
  sl0 : (BitVec 2)
  irgn : (BitVec 2)
  orgn : (BitVec 2)
  sh : (BitVec 2)
  ee : (BitVec 1)
  ptw : (BitVec 1)
  vm : (BitVec 1)
  deriving Inhabited, BEq

structure TLBContext where
  ss : SecurityState
  regime : Regime
  vmid : (BitVec 16)
  asid : (BitVec 16)
  nG : (BitVec 1)
  ipaspace : PASpace
  includes_s1_name : Bool
  includes_s2_name : Bool
  includes_gpt_name : Bool
  ia : (BitVec 64)
  tg : TGx
  cnp : (BitVec 1)
  level : Int
  isd128 : Bool
  xs : (BitVec 1)
  deriving Inhabited, BEq

structure TLBRecord where
  context : TLBContext
  walkstate : TTWState
  blocksize : Int
  contigsize : Int
  s1descriptor : (BitVec 128)
  s2descriptor : (BitVec 128)
  deriving Inhabited, BEq

structure AddressDescriptor where
  fault : FaultRecord
  memattrs : MemoryAttributes
  paddress : FullAddress
  tlbcontext : TLBContext
  s1assured : Bool
  s2fs1mro : Bool
  mecid : (BitVec 16)
  vaddress : (BitVec 64)
  deriving Inhabited, BEq

structure TranslationInfo where
  regime : Regime
  vmid : (Option (BitVec 16))
  asid : (Option (BitVec 16))
  va : (BitVec 64)
  s1level : (Option Int)
  s2info : (Option ((BitVec 64) × Int))
  s1params : (Option S1TTWParams)
  s2params : (Option S2TTWParams)
  memattrs : MemoryAttributes
  deriving Inhabited, BEq

structure TranslationStartInfo where
  ss : SecurityState
  regime : Regime
  vmid : (BitVec 16)
  asid : (BitVec 16)
  va : (BitVec 64)
  cnp : (BitVec 1)
  accdesc : AccessDescriptor
  size : Int
  deriving Inhabited, BEq

inductive SVECmp where | Cmp_EQ | Cmp_NE | Cmp_GE | Cmp_GT | Cmp_LT | Cmp_LE | Cmp_UN
  deriving Inhabited, BEq

abbrev MAX_VL : Int := 2048

abbrev MAX_PL : Int := 256

inductive SMEExceptionType where | SMEExceptionType_AccessTrap | SMEExceptionType_Streaming | SMEExceptionType_NotStreaming | SMEExceptionType_InactiveZA | SMEExceptionType_InaccessibleZT0
  deriving Inhabited, BEq

inductive GCSInstruction where | GCSInstType_PRET | GCSInstType_POPM | GCSInstType_PRETAA | GCSInstType_PRETAB | GCSInstType_SS1 | GCSInstType_SS2 | GCSInstType_POPCX | GCSInstType_POPX
  deriving Inhabited, BEq

inductive MOPSStage where | MOPSStage_Prologue | MOPSStage_Main | MOPSStage_Epilogue
  deriving Inhabited, BEq

abbrev FPCR_Type := (BitVec 64)

abbrev FPSR_Type := (BitVec 64)

abbrev ICC_PMR_EL1_Type := (BitVec 64)

structure TMState where
  depth : Int
  Rt : Int
  nPC : (BitVec 64)
  X : (Vector (BitVec 64) 31)
  Z : (Vector (BitVec 2048) 32)
  P : (Vector (BitVec 256) 16)
  FFR : (BitVec 256)
  SP : (BitVec 64)
  FPCR : (BitVec 64)
  FPSR : (BitVec 64)
  ICC_PMR_EL1 : (BitVec 64)
  GCSPR_ELx : (BitVec 64)
  nzcv : (BitVec 4)
  D : (BitVec 1)
  A : (BitVec 1)
  I : (BitVec 1)
  F : (BitVec 1)
  deriving Inhabited, BEq

inductive TMFailure where | TMFailure_CNCL | TMFailure_DBG | TMFailure_ERR | TMFailure_NEST | TMFailure_SIZE | TMFailure_MEM | TMFailure_TRIVIAL | TMFailure_IMP
  deriving Inhabited, BEq

inductive PGSe where | PGS_4KB | PGS_16KB | PGS_64KB
  deriving Inhabited, BEq

structure GPTTable where
  address : (BitVec 56)
  deriving Inhabited, BEq

structure GPTEntry where
  gpi : (BitVec 4)
  size : Int
  contig_size : Int
  level : Int
  pa : (BitVec 56)
  deriving Inhabited, BEq

inductive TimeStamp where | TimeStamp_None | TimeStamp_CoreSight | TimeStamp_Physical | TimeStamp_OffsetPhysical | TimeStamp_Virtual
  deriving Inhabited, BEq

inductive OpType where | OpType_Load | OpType_Store | OpType_LoadAtomic | OpType_Branch | OpType_Other
  deriving Inhabited, BEq

inductive CountOp where | CountOp_CLZ | CountOp_CLS | CountOp_CNT
  deriving Inhabited, BEq

inductive ExtendType where | ExtendType_SXTB | ExtendType_SXTH | ExtendType_SXTW | ExtendType_SXTX | ExtendType_UXTB | ExtendType_UXTH | ExtendType_UXTW | ExtendType_UXTX
  deriving Inhabited, BEq

inductive FPMaxMinOp where | FPMaxMinOp_MAX | FPMaxMinOp_MIN | FPMaxMinOp_MAXNUM | FPMaxMinOp_MINNUM
  deriving Inhabited, BEq

inductive FPUnaryOp where | FPUnaryOp_ABS | FPUnaryOp_MOV | FPUnaryOp_NEG | FPUnaryOp_SQRT
  deriving Inhabited, BEq

inductive FPConvOp where | FPConvOp_CVT_FtoI | FPConvOp_CVT_ItoF | FPConvOp_MOV_FtoI | FPConvOp_MOV_ItoF | FPConvOp_CVT_FtoI_JS
  deriving Inhabited, BEq

inductive MoveWideOp where | MoveWideOp_N | MoveWideOp_Z | MoveWideOp_K
  deriving Inhabited, BEq

inductive ShiftType where | ShiftType_LSL | ShiftType_LSR | ShiftType_ASR | ShiftType_ROR
  deriving Inhabited, BEq

inductive LogicalOp where | LogicalOp_AND | LogicalOp_EOR | LogicalOp_ORR
  deriving Inhabited, BEq

inductive SystemHintOp where | SystemHintOp_NOP | SystemHintOp_YIELD | SystemHintOp_WFE | SystemHintOp_WFI | SystemHintOp_SEV | SystemHintOp_SEVL | SystemHintOp_DGH | SystemHintOp_ESB | SystemHintOp_PSB | SystemHintOp_TSB | SystemHintOp_BTI | SystemHintOp_WFET | SystemHintOp_WFIT | SystemHintOp_CLRBHB | SystemHintOp_GCSB | SystemHintOp_CHKFEAT | SystemHintOp_CSDB
  deriving Inhabited, BEq

inductive PSTATEField where | PSTATEField_DAIFSet | PSTATEField_DAIFClr | PSTATEField_PAN | PSTATEField_UAO | PSTATEField_DIT | PSTATEField_SSBS | PSTATEField_TCO | PSTATEField_SVCRSM | PSTATEField_SVCRZA | PSTATEField_SVCRSMZA | PSTATEField_ALLINT | PSTATEField_PM | PSTATEField_SP
  deriving Inhabited, BEq

inductive TLBILevel where | TLBILevel_Any | TLBILevel_Last
  deriving Inhabited, BEq

inductive TLBIOp where | TLBIOp_DALL | TLBIOp_DASID | TLBIOp_DVA | TLBIOp_IALL | TLBIOp_IASID | TLBIOp_IVA | TLBIOp_ALL | TLBIOp_ASID | TLBIOp_IPAS2 | TLBIPOp_IPAS2 | TLBIOp_VAA | TLBIOp_VA | TLBIPOp_VAA | TLBIPOp_VA | TLBIOp_VMALL | TLBIOp_VMALLS12 | TLBIOp_RIPAS2 | TLBIPOp_RIPAS2 | TLBIOp_RVAA | TLBIOp_RVA | TLBIPOp_RVAA | TLBIPOp_RVA | TLBIOp_RPA | TLBIOp_PAALL
  deriving Inhabited, BEq

inductive TLBIMemAttr where | TLBI_AllAttr | TLBI_ExcludeXS
  deriving Inhabited, BEq

structure TLBIRecord where
  op : TLBIOp
  from_aarch64 : Bool
  security : SecurityState
  regime : Regime
  vmid : (BitVec 16)
  asid : (BitVec 16)
  level : TLBILevel
  attr : TLBIMemAttr
  ipaspace : PASpace
  address : (BitVec 64)
  end_address_name : (BitVec 64)
  d64 : Bool
  d128 : Bool
  ttl : (BitVec 4)
  tg : (BitVec 2)
  deriving Inhabited, BEq

inductive VBitOp where | VBitOp_VBIF | VBitOp_VBIT | VBitOp_VBSL | VBitOp_VEOR
  deriving Inhabited, BEq

inductive CompareOp where | CompareOp_GT | CompareOp_GE | CompareOp_EQ | CompareOp_LE | CompareOp_LT
  deriving Inhabited, BEq

inductive ImmediateOp where | ImmediateOp_MOVI | ImmediateOp_MVNI | ImmediateOp_ORR | ImmediateOp_BIC
  deriving Inhabited, BEq

inductive ReduceOp where | ReduceOp_FMINNUM | ReduceOp_FMAXNUM | ReduceOp_FMIN | ReduceOp_FMAX | ReduceOp_FADD | ReduceOp_ADD
  deriving Inhabited, BEq

inductive CrossTriggerIn where | CrossTriggerIn_CrossHalt | CrossTriggerIn_PMUOverflow | CrossTriggerIn_RSVD2 | CrossTriggerIn_RSVD3 | CrossTriggerIn_TraceExtOut0 | CrossTriggerIn_TraceExtOut1 | CrossTriggerIn_TraceExtOut2 | CrossTriggerIn_TraceExtOut3
  deriving Inhabited, BEq

structure TLBLine where
  tlbrecord : TLBRecord
  valid_name : Bool
  deriving Inhabited, BEq

structure GPTTLBLine where
  gpt_entry : GPTEntry
  valid_name : Bool
  deriving Inhabited, BEq

structure InterruptReq where
  take_SE : Bool
  take_vSE : Bool
  take_IRQ : Bool
  take_vIRQ : Bool
  take_FIQ : Bool
  take_vFIQ : Bool
  iesb_req : Bool
  deriving Inhabited, BEq

inductive __InstrEnc where | __A64 | __A32 | __T16 | __T32
  deriving Inhabited, BEq

inductive SRType where | SRType_LSL | SRType_LSR | SRType_ASR | SRType_ROR | SRType_RRX
  deriving Inhabited, BEq

inductive VCGEType where | VCGEType_signed | VCGEType_unsigned | VCGEType_fp
  deriving Inhabited, BEq

inductive VFPNegMul where | VFPNegMul_VNMLA | VFPNegMul_VNMLS | VFPNegMul_VNMUL
  deriving Inhabited, BEq

inductive VCGTtype where | VCGTtype_signed | VCGTtype_unsigned | VCGTtype_fp
  deriving Inhabited, BEq

inductive VBitOps where | VBitOps_VBIF | VBitOps_VBIT | VBitOps_VBSL
  deriving Inhabited, BEq

abbrev HCR_EL2_Type := (BitVec 64)

abbrev SCR_EL3_Type := (BitVec 64)

abbrev SCR_Type := (BitVec 32)

abbrev FPSCR_Type := (BitVec 32)

abbrev ERRnFR_ElemType := (BitVec 64)

abbrev CTR_EL0_Type := (BitVec 64)

abbrev HDCR_Type := (BitVec 32)

abbrev MDCR_EL2_Type := (BitVec 64)

abbrev EDSCR_Type := (BitVec 32)

abbrev MDCCSR_EL0_Type := (BitVec 64)

abbrev PMCNTENCLR_EL0_Type := (BitVec 64)

abbrev PMCNTENCLR_Type := (BitVec 32)

abbrev PMCR_EL0_Type := (BitVec 64)

abbrev PMCR_Type := (BitVec 32)

abbrev PMINTENCLR_EL1_Type := (BitVec 64)

abbrev PMINTENCLR_Type := (BitVec 32)

abbrev PMOVSCLR_EL0_Type := (BitVec 64)

abbrev PMOVSR_Type := (BitVec 32)

abbrev MDCR_EL3_Type := (BitVec 64)

abbrev PMCCFILTR_EL0_Type := (BitVec 64)

abbrev PMCCFILTR_Type := (BitVec 32)

abbrev PMCNTENSET_EL0_Type := (BitVec 64)

abbrev PMCNTENSET_Type := (BitVec 32)

abbrev PMEVTYPER_EL0_Type := (BitVec 64)

abbrev PMEVTYPER_Type := (BitVec 32)

abbrev PMICFILTR_EL0_Type := (BitVec 64)

abbrev SDCR_Type := (BitVec 32)

abbrev SDER32_EL2_Type := (BitVec 64)

abbrev SDER32_EL3_Type := (BitVec 64)

abbrev SDER_Type := (BitVec 32)

abbrev PMICNTR_EL0_Type := (BitVec 64)

abbrev PMOVSSET_EL0_Type := (BitVec 64)

abbrev BRBCR_EL1_Type := (BitVec 64)

abbrev BRBCR_EL2_Type := (BitVec 64)

abbrev BRBFCR_EL1_Type := (BitVec 64)

abbrev BRBTS_EL1_Type := (BitVec 64)

abbrev CNTPOFF_EL2_Type := (BitVec 64)

abbrev CNTVOFF_EL2_Type := (BitVec 64)

abbrev CNTHCTL_EL2_Type := (BitVec 64)

abbrev EDECR_Type := (BitVec 32)

abbrev DLR_EL0_Type := (BitVec 64)

abbrev DLR_Type := (BitVec 32)

abbrev DSPSR_EL0_Type := (BitVec 64)

abbrev DSPSR_Type := (BitVec 32)

abbrev DSPSR2_Type := (BitVec 32)

abbrev TCR_EL1_Type := (BitVec 64)

abbrev TCR_EL2_Type := (BitVec 64)

abbrev TCR_EL3_Type := (BitVec 64)

abbrev BRBIDR0_EL1_Type := (BitVec 64)

abbrev PMSIDR_EL1_Type := (BitVec 64)

abbrev PMSCR_EL1_Type := (BitVec 64)

abbrev PMSCR_EL2_Type := (BitVec 64)

abbrev PMBLIMITR_EL1_Type := (BitVec 64)

abbrev PMBSR_EL1_Type := (BitVec 64)

abbrev ZCR_EL1_Type := (BitVec 64)

abbrev ZCR_EL2_Type := (BitVec 64)

abbrev ZCR_EL3_Type := (BitVec 64)

abbrev SMCR_EL1_Type := (BitVec 64)

abbrev SMCR_EL2_Type := (BitVec 64)

abbrev SMCR_EL3_Type := (BitVec 64)

abbrev GCSPR_EL0_Type := (BitVec 64)

abbrev GCSPR_EL1_Type := (BitVec 64)

abbrev GCSPR_EL2_Type := (BitVec 64)

abbrev GCSPR_EL3_Type := (BitVec 64)

abbrev CPACR_EL1_Type := (BitVec 64)

abbrev CPTR_EL2_Type := (BitVec 64)

abbrev CPTR_EL3_Type := (BitVec 64)

abbrev CPACR_Type := (BitVec 32)

abbrev HCPTR_Type := (BitVec 32)

abbrev NSACR_Type := (BitVec 32)

abbrev SP_EL0_Type := (BitVec 64)

abbrev SP_EL1_Type := (BitVec 64)

abbrev SP_EL2_Type := (BitVec 64)

abbrev SP_EL3_Type := (BitVec 64)

abbrev DBGOSDLR_Type := (BitVec 32)

abbrev OSDLR_EL1_Type := (BitVec 64)

abbrev DBGPRCR_EL1_Type := (BitVec 64)

abbrev DBGPRCR_Type := (BitVec 32)

abbrev GCSCR_EL1_Type := (BitVec 64)

abbrev GCSCR_EL2_Type := (BitVec 64)

abbrev GCSCR_EL3_Type := (BitVec 64)

abbrev MDSCR_EL1_Type := (BitVec 64)

abbrev OSLSR_EL1_Type := (BitVec 64)

abbrev DBGOSLSR_Type := (BitVec 32)

abbrev HCR_Type := (BitVec 32)

abbrev HSCTLR_Type := (BitVec 32)

abbrev SCTLR_EL2_Type := (BitVec 64)

abbrev SCTLR_EL1_Type := (BitVec 64)

abbrev SCTLR_EL3_Type := (BitVec 64)

abbrev SCTLR_Type := (BitVec 32)

abbrev ESR_EL1_Type := (BitVec 64)

abbrev ESR_EL2_Type := (BitVec 64)

abbrev ESR_EL3_Type := (BitVec 64)

abbrev FAR_EL1_Type := (BitVec 64)

abbrev FAR_EL2_Type := (BitVec 64)

abbrev FAR_EL3_Type := (BitVec 64)

abbrev HPFAR_EL2_Type := (BitVec 64)

abbrev MFAR_EL3_Type := (BitVec 64)

abbrev PFAR_EL1_Type := (BitVec 64)

abbrev PFAR_EL2_Type := (BitVec 64)

abbrev ELR_EL1_Type := (BitVec 64)

abbrev ELR_EL2_Type := (BitVec 64)

abbrev ELR_EL3_Type := (BitVec 64)

abbrev SPSR_EL1_Type := (BitVec 64)

abbrev SPSR_EL2_Type := (BitVec 64)

abbrev SPSR_EL3_Type := (BitVec 64)

abbrev SPSR_abt_Type := (BitVec 64)

abbrev SPSR_fiq_Type := (BitVec 64)

abbrev SPSR_hyp_Type := (BitVec 32)

abbrev SPSR_irq_Type := (BitVec 64)

abbrev SPSR_mon_Type := (BitVec 32)

abbrev SPSR_svc_Type := (BitVec 32)

abbrev SPSR_und_Type := (BitVec 64)

abbrev EDECCR_Type := (BitVec 32)

abbrev OSECCR_EL1_Type := (BitVec 64)

abbrev EDESR_Type := (BitVec 32)

abbrev VBAR_EL1_Type := (BitVec 64)

abbrev VBAR_EL2_Type := (BitVec 64)

abbrev VBAR_EL3_Type := (BitVec 64)

abbrev VBAR_Type := (BitVec 32)

abbrev GCSCRE0_EL1_Type := (BitVec 64)

abbrev HCRX_EL2_Type := (BitVec 64)

abbrev MPAM2_EL2_Type := (BitVec 64)

abbrev MPAM3_EL3_Type := (BitVec 64)

abbrev MPAM1_EL1_Type := (BitVec 64)

abbrev MPAMIDR_EL1_Type := (BitVec 64)

abbrev MPAMHCR_EL2_Type := (BitVec 64)

abbrev MPAMVPM0_EL2_Type := (BitVec 64)

abbrev MPAMVPMV_EL2_Type := (BitVec 64)

abbrev MPAMVPM1_EL2_Type := (BitVec 64)

abbrev MPAMVPM2_EL2_Type := (BitVec 64)

abbrev MPAMVPM3_EL2_Type := (BitVec 64)

abbrev MPAMVPM4_EL2_Type := (BitVec 64)

abbrev MPAMVPM5_EL2_Type := (BitVec 64)

abbrev MPAMVPM6_EL2_Type := (BitVec 64)

abbrev MPAMVPM7_EL2_Type := (BitVec 64)

abbrev MPAM0_EL1_Type := (BitVec 64)

abbrev MPAMSM_EL1_Type := (BitVec 64)

abbrev CLIDR_EL1_Type := (BitVec 64)

abbrev CONTEXTIDR_EL1_Type := (BitVec 64)

abbrev TTBCR_Type := (BitVec 32)

abbrev CONTEXTIDR_Type := (BitVec 32)

abbrev TTBR0_Type := (BitVec 64)

abbrev TTBR0_EL1_Type := (BitVec 128)

abbrev HTTBR_Type := (BitVec 64)

abbrev TTBR0_EL2_Type := (BitVec 128)

abbrev TTBR1_Type := (BitVec 64)

abbrev TTBR1_EL1_Type := (BitVec 128)

abbrev TTBR1_EL2_Type := (BitVec 128)

abbrev HDFAR_Type := (BitVec 32)

abbrev HIFAR_Type := (BitVec 32)

abbrev HPFAR_Type := (BitVec 32)

abbrev HSR_Type := (BitVec 32)

abbrev ELR_hyp_Type := (BitVec 32)

abbrev HVBAR_Type := (BitVec 32)

abbrev MVBAR_Type := (BitVec 32)

abbrev DFAR_Type := (BitVec 32)

abbrev DFSR_Type := (BitVec 32)

abbrev IFSR32_EL2_Type := (BitVec 64)

abbrev IFSR_Type := (BitVec 32)

abbrev DBGDSCRext_Type := (BitVec 32)

abbrev DBGDSCRint_Type := (BitVec 32)

abbrev HCR2_Type := (BitVec 32)

abbrev IFAR_Type := (BitVec 32)

abbrev SCTLR2_EL1_Type := (BitVec 64)

abbrev SCTLR2_EL2_Type := (BitVec 64)

abbrev FPEXC32_EL2_Type := (BitVec 64)

abbrev FPEXC_Type := (BitVec 32)

abbrev CNTHP_CTL_EL2_Type := (BitVec 64)

abbrev CNTHP_CTL_Type := (BitVec 32)

abbrev CNTHP_CVAL_EL2_Type := (BitVec 64)

abbrev CNTHP_CVAL_Type := (BitVec 64)

abbrev CNTP_CTL_EL0_Type := (BitVec 64)

abbrev CNTP_CTL_Type := (BitVec 32)

abbrev CNTP_CVAL_EL0_Type := (BitVec 64)

abbrev CNTP_CVAL_Type := (BitVec 64)

abbrev CNTV_CTL_EL0_Type := (BitVec 64)

abbrev CNTV_CVAL_EL0_Type := (BitVec 64)

abbrev CNTHPS_CTL_EL2_Type := (BitVec 64)

abbrev CNTHPS_CVAL_EL2_Type := (BitVec 64)

abbrev CNTHVS_CTL_EL2_Type := (BitVec 64)

abbrev CNTHVS_CVAL_EL2_Type := (BitVec 64)

abbrev CNTHV_CTL_EL2_Type := (BitVec 64)

abbrev CNTHV_CVAL_EL2_Type := (BitVec 64)

abbrev CNTPS_CTL_EL1_Type := (BitVec 64)

abbrev CNTPS_CVAL_EL1_Type := (BitVec 64)

abbrev CNTCR_Type := (BitVec 32)

abbrev CNTSCR_Type := (BitVec 32)

abbrev CNTKCTL_EL1_Type := (BitVec 64)

abbrev GPCCR_EL3_Type := (BitVec 64)

abbrev GPTBR_EL3_Type := (BitVec 64)

abbrev GICC_CTLR_Type := (BitVec 32)

inductive arm_acc_type where
  | SAcc_ASIMD (_ : Bool)
  | SAcc_SVE (_ : Bool)
  | SAcc_SME (_ : Bool)
  | SAcc_IC (_ : Unit)
  | SAcc_DC (_ : Unit)
  | SAcc_DCZero (_ : Unit)
  | SAcc_AT (_ : Unit)
  | SAcc_NV2 (_ : Unit)
  | SAcc_SPE (_ : Unit)
  | SAcc_GCS (_ : Unit)
  | SAcc_GPTW (_ : Unit)
  deriving Inhabited, BEq

abbrev MAIR2_EL1_Type := (BitVec 64)

abbrev MAIR_EL1_Type := (BitVec 64)

abbrev PIRE0_EL1_Type := (BitVec 64)

abbrev PIR_EL1_Type := (BitVec 64)

abbrev TCR2_EL1_Type := (BitVec 64)

abbrev MAIR2_EL2_Type := (BitVec 64)

abbrev MAIR_EL2_Type := (BitVec 64)

abbrev PIR_EL2_Type := (BitVec 64)

abbrev TCR2_EL2_Type := (BitVec 64)

abbrev PIRE0_EL2_Type := (BitVec 64)

abbrev MAIR2_EL3_Type := (BitVec 64)

abbrev MAIR_EL3_Type := (BitVec 64)

abbrev PIR_EL3_Type := (BitVec 64)

abbrev SCTLR2_EL3_Type := (BitVec 64)

abbrev TTBR0_EL3_Type := (BitVec 64)

abbrev APIAKeyHi_EL1_Type := (BitVec 64)

abbrev APIAKeyLo_EL1_Type := (BitVec 64)

abbrev APIBKeyHi_EL1_Type := (BitVec 64)

abbrev APIBKeyLo_EL1_Type := (BitVec 64)

abbrev APDAKeyHi_EL1_Type := (BitVec 64)

abbrev APDAKeyLo_EL1_Type := (BitVec 64)

abbrev APDBKeyHi_EL1_Type := (BitVec 64)

abbrev APDBKeyLo_EL1_Type := (BitVec 64)

abbrev APGAKeyHi_EL1_Type := (BitVec 64)

abbrev APGAKeyLo_EL1_Type := (BitVec 64)

abbrev CNTKCTL_Type := (BitVec 32)

abbrev GCR_EL1_Type := (BitVec 64)

abbrev RGSR_EL1_Type := (BitVec 64)

abbrev TFSRE0_EL1_Type := (BitVec 64)

abbrev TFSR_EL1_Type := (BitVec 64)

abbrev TFSR_EL2_Type := (BitVec 64)

abbrev TFSR_EL3_Type := (BitVec 64)

abbrev CONTEXTIDR_EL2_Type := (BitVec 64)

abbrev DBGBCR_EL1_Type := (BitVec 64)

abbrev DBGBVR_EL1_Type := (BitVec 64)

abbrev EDSCR2_Type := (BitVec 32)

abbrev VTCR_EL2_Type := (BitVec 64)

abbrev VTTBR_Type := (BitVec 64)

abbrev VTTBR_EL2_Type := (BitVec 128)

abbrev DBGWCR_EL1_Type := (BitVec 64)

abbrev DBGWVR_EL1_Type := (BitVec 64)

abbrev EDWAR_Type := (BitVec 64)

abbrev POR_EL1_Type := (BitVec 64)

abbrev POR_EL2_Type := (BitVec 64)

abbrev POR_EL3_Type := (BitVec 64)

abbrev POR_EL0_Type := (BitVec 64)

abbrev MECID_P0_EL2_Type := (BitVec 64)

abbrev VMECID_P_EL2_Type := (BitVec 64)

abbrev MECID_A0_EL2_Type := (BitVec 64)

abbrev MECID_A1_EL2_Type := (BitVec 64)

abbrev MECID_P1_EL2_Type := (BitVec 64)

abbrev MECID_RL_A_EL3_Type := (BitVec 64)

abbrev S2PIR_EL2_Type := (BitVec 64)

abbrev VSTCR_EL2_Type := (BitVec 64)

abbrev VSTTBR_EL2_Type := (BitVec 64)

abbrev S2POR_EL1_Type := (BitVec 64)

abbrev VMECID_A_EL2_Type := (BitVec 64)

abbrev RCWMASK_EL1_Type := (BitVec 128)

abbrev RCWSMASK_EL1_Type := (BitVec 128)

abbrev VNCR_EL2_Type := (BitVec 64)

abbrev HFGITR_EL2_Type := (BitVec 64)

abbrev DISR_EL1_Type := (BitVec 64)

abbrev DISR_Type := (BitVec 32)

abbrev VDFSR_Type := (BitVec 32)

abbrev VSESR_EL2_Type := (BitVec 64)

abbrev VDISR_EL2_Type := (BitVec 64)

abbrev VDISR_Type := (BitVec 32)

abbrev RVBAR_EL1_Type := (BitVec 64)

abbrev RVBAR_EL2_Type := (BitVec 64)

abbrev RVBAR_EL3_Type := (BitVec 64)

abbrev AMCIDR0_Type := (BitVec 32)

abbrev AMCIDR1_Type := (BitVec 32)

abbrev AMCIDR2_Type := (BitVec 32)

abbrev AMCIDR3_Type := (BitVec 32)

abbrev AMDEVTYPE_Type := (BitVec 32)

abbrev AMPIDR0_Type := (BitVec 32)

abbrev AMPIDR1_Type := (BitVec 32)

abbrev AMPIDR2_Type := (BitVec 32)

abbrev AMPIDR3_Type := (BitVec 32)

abbrev AMPIDR4_Type := (BitVec 32)

abbrev CNTEL0ACR_Type := (BitVec 32)

abbrev CNTID_Type := (BitVec 32)

abbrev CNTNSAR_Type := (BitVec 32)

abbrev CNTSR_Type := (BitVec 32)

abbrev CTIAUTHSTATUS_Type := (BitVec 32)

abbrev CTICIDR0_Type := (BitVec 32)

abbrev CTICIDR1_Type := (BitVec 32)

abbrev CTICIDR2_Type := (BitVec 32)

abbrev CTICIDR3_Type := (BitVec 32)

abbrev CTICONTROL_Type := (BitVec 32)

abbrev CTIDEVCTL_Type := (BitVec 32)

abbrev CTIDEVID_Type := (BitVec 32)

abbrev CTIDEVID1_Type := (BitVec 32)

abbrev CTIDEVID2_Type := (BitVec 32)

abbrev CTIDEVTYPE_Type := (BitVec 32)

abbrev CTIITCTRL_Type := (BitVec 32)

abbrev CTILAR_Type := (BitVec 32)

abbrev CTILSR_Type := (BitVec 32)

abbrev CTIPIDR0_Type := (BitVec 32)

abbrev CTIPIDR1_Type := (BitVec 32)

abbrev CTIPIDR2_Type := (BitVec 32)

abbrev CTIPIDR3_Type := (BitVec 32)

abbrev CTIPIDR4_Type := (BitVec 32)

abbrev DBGDEVID1_Type := (BitVec 32)

abbrev DBGDEVID2_Type := (BitVec 32)

abbrev DBGDIDR_Type := (BitVec 32)

abbrev DBGDSAR_Type := (BitVec 64)

abbrev DBGWFAR_Type := (BitVec 32)

abbrev EDAA32PFR_Type := (BitVec 64)

abbrev EDCIDR0_Type := (BitVec 32)

abbrev EDCIDR1_Type := (BitVec 32)

abbrev EDCIDR2_Type := (BitVec 32)

abbrev EDCIDR3_Type := (BitVec 32)

abbrev EDDEVID_Type := (BitVec 32)

abbrev EDDEVID1_Type := (BitVec 32)

abbrev EDDEVID2_Type := (BitVec 32)

abbrev EDDEVTYPE_Type := (BitVec 32)

abbrev EDDFR_Type := (BitVec 64)

abbrev EDDFR1_Type := (BitVec 64)

abbrev EDHSR_Type := (BitVec 64)

abbrev EDITCTRL_Type := (BitVec 32)

abbrev EDLAR_Type := (BitVec 32)

abbrev EDLSR_Type := (BitVec 32)

abbrev EDPCSR_Type := (BitVec 64)

abbrev EDPFR_Type := (BitVec 64)

abbrev EDPIDR0_Type := (BitVec 32)

abbrev EDPIDR1_Type := (BitVec 32)

abbrev EDPIDR2_Type := (BitVec 32)

abbrev EDPIDR3_Type := (BitVec 32)

abbrev EDPIDR4_Type := (BitVec 32)

abbrev EDPRCR_Type := (BitVec 32)

abbrev EDPRSR_Type := (BitVec 32)

abbrev EDRCR_Type := (BitVec 32)

abbrev EDVIDSR_Type := (BitVec 32)

abbrev FCSEIDR_Type := (BitVec 32)

abbrev GICC_ABPR_Type := (BitVec 32)

abbrev GICC_AEOIR_Type := (BitVec 32)

abbrev GICC_AHPPIR_Type := (BitVec 32)

abbrev GICC_AIAR_Type := (BitVec 32)

abbrev GICC_BPR_Type := (BitVec 32)

abbrev GICC_DIR_Type := (BitVec 32)

abbrev GICC_EOIR_Type := (BitVec 32)

abbrev GICC_HPPIR_Type := (BitVec 32)

abbrev GICC_IAR_Type := (BitVec 32)

abbrev GICC_PMR_Type := (BitVec 32)

abbrev GICC_RPR_Type := (BitVec 32)

abbrev GICC_STATUSR_Type := (BitVec 32)

abbrev GICD_CLRSPI_NSR_Type := (BitVec 32)

abbrev GICD_CLRSPI_SR_Type := (BitVec 32)

abbrev GICD_CTLR_Type := (BitVec 32)

abbrev GICD_IIDR_Type := (BitVec 32)

abbrev GICD_SETSPI_NSR_Type := (BitVec 32)

abbrev GICD_SETSPI_SR_Type := (BitVec 32)

abbrev GICD_SGIR_Type := (BitVec 32)

abbrev GICD_STATUSR_Type := (BitVec 32)

abbrev GICD_TYPER2_Type := (BitVec 32)

abbrev GICH_EISR_Type := (BitVec 32)

abbrev GICH_ELRSR_Type := (BitVec 32)

abbrev GICH_HCR_Type := (BitVec 32)

abbrev GICH_MISR_Type := (BitVec 32)

abbrev GICH_VMCR_Type := (BitVec 32)

abbrev GICH_VTR_Type := (BitVec 32)

abbrev GICM_CLRSPI_NSR_Type := (BitVec 32)

abbrev GICM_CLRSPI_SR_Type := (BitVec 32)

abbrev GICM_IIDR_Type := (BitVec 32)

abbrev GICM_SETSPI_NSR_Type := (BitVec 32)

abbrev GICM_SETSPI_SR_Type := (BitVec 32)

abbrev GICM_TYPER_Type := (BitVec 32)

abbrev GICR_CLRLPIR_Type := (BitVec 64)

abbrev GICR_CTLR_Type := (BitVec 32)

abbrev GICR_IIDR_Type := (BitVec 32)

abbrev GICR_INMIR0_Type := (BitVec 32)

abbrev GICR_INVALLR_Type := (BitVec 64)

abbrev GICR_INVLPIR_Type := (BitVec 64)

abbrev GICR_ISENABLER0_Type := (BitVec 32)

abbrev GICR_MPAMIDR_Type := (BitVec 32)

abbrev GICR_PARTIDR_Type := (BitVec 32)

abbrev GICR_PENDBASER_Type := (BitVec 64)

abbrev GICR_PROPBASER_Type := (BitVec 64)

abbrev GICR_SETLPIR_Type := (BitVec 64)

abbrev GICR_STATUSR_Type := (BitVec 32)

abbrev GICR_SYNCR_Type := (BitVec 32)

abbrev GICR_VPENDBASER_Type := (BitVec 64)

abbrev GICR_VPROPBASER_Type := (BitVec 64)

abbrev GICR_VSGIPENDR_Type := (BitVec 32)

abbrev GICR_VSGIR_Type := (BitVec 32)

abbrev GICR_WAKER_Type := (BitVec 32)

abbrev GICV_ABPR_Type := (BitVec 32)

abbrev GICV_AEOIR_Type := (BitVec 32)

abbrev GICV_AHPPIR_Type := (BitVec 32)

abbrev GICV_AIAR_Type := (BitVec 32)

abbrev GICV_BPR_Type := (BitVec 32)

abbrev GICV_CTLR_Type := (BitVec 32)

abbrev GICV_DIR_Type := (BitVec 32)

abbrev GICV_EOIR_Type := (BitVec 32)

abbrev GICV_HPPIR_Type := (BitVec 32)

abbrev GICV_IAR_Type := (BitVec 32)

abbrev GICV_PMR_Type := (BitVec 32)

abbrev GICV_RPR_Type := (BitVec 32)

abbrev GICV_STATUSR_Type := (BitVec 32)

abbrev GITS_CBASER_Type := (BitVec 64)

abbrev GITS_CREADR_Type := (BitVec 64)

abbrev GITS_CTLR_Type := (BitVec 32)

abbrev GITS_CWRITER_Type := (BitVec 64)

abbrev GITS_IIDR_Type := (BitVec 32)

abbrev GITS_MPAMIDR_Type := (BitVec 32)

abbrev GITS_MPIDR_Type := (BitVec 32)

abbrev GITS_PARTIDR_Type := (BitVec 32)

abbrev GITS_SGIR_Type := (BitVec 64)

abbrev GITS_STATUSR_Type := (BitVec 32)

abbrev GITS_TYPER_Type := (BitVec 64)

abbrev ICC_MCTLR_Type := (BitVec 32)

abbrev ICC_MGRPEN1_Type := (BitVec 32)

abbrev ICC_MSRE_Type := (BitVec 32)

abbrev JIDR_Type := (BitVec 32)

abbrev JMCR_Type := (BitVec 32)

abbrev JOSCR_Type := (BitVec 32)

abbrev PMAUTHSTATUS_Type := (BitVec 32)

abbrev PMCFGR_Type := (BitVec 64)

abbrev PMCGCR0_Type := (BitVec 32)

abbrev PMCIDR0_Type := (BitVec 32)

abbrev PMCIDR1_Type := (BitVec 32)

abbrev PMCIDR2_Type := (BitVec 32)

abbrev PMCIDR3_Type := (BitVec 32)

abbrev PMDEVID_Type := (BitVec 32)

abbrev PMDEVTYPE_Type := (BitVec 32)

abbrev PMIIDR_Type := (BitVec 64)

abbrev PMITCTRL_Type := (BitVec 32)

abbrev PMLAR_Type := (BitVec 32)

abbrev PMLSR_Type := (BitVec 32)

abbrev PMMIR_Type := (BitVec 32)

abbrev PMPCSCTL_Type := (BitVec 64)

abbrev PMPCSR_Type := (BitVec 64)

abbrev PMPIDR0_Type := (BitVec 32)

abbrev PMPIDR1_Type := (BitVec 32)

abbrev PMPIDR2_Type := (BitVec 32)

abbrev PMPIDR3_Type := (BitVec 32)

abbrev PMPIDR4_Type := (BitVec 32)

abbrev PMVCIDSR_Type := (BitVec 64)

abbrev PMVIDSR_Type := (BitVec 32)

abbrev AMCFGR_EL0_Type := (BitVec 64)

abbrev AMCFGR_Type := (BitVec 32)

abbrev AMCGCR_EL0_Type := (BitVec 64)

abbrev AMCGCR_Type := (BitVec 32)

abbrev AMCNTENCLR0_EL0_Type := (BitVec 64)

abbrev AMCNTENCLR0_Type := (BitVec 32)

abbrev AMCNTENCLR1_EL0_Type := (BitVec 64)

abbrev AMCNTENCLR1_Type := (BitVec 32)

abbrev AMCNTENSET0_EL0_Type := (BitVec 64)

abbrev AMCNTENSET0_Type := (BitVec 32)

abbrev AMCNTENSET1_EL0_Type := (BitVec 64)

abbrev AMCNTENSET1_Type := (BitVec 32)

abbrev AMCR_EL0_Type := (BitVec 64)

abbrev AMCR_Type := (BitVec 32)

abbrev AMUSERENR_EL0_Type := (BitVec 64)

abbrev AMUSERENR_Type := (BitVec 32)

abbrev CCSIDR2_EL1_Type := (BitVec 64)

abbrev CCSIDR2_Type := (BitVec 32)

abbrev CCSIDR_EL1_Type := (BitVec 64)

abbrev CCSIDR_Type := (BitVec 32)

abbrev CNTHCTL_Type := (BitVec 32)

abbrev CNTHPS_CTL_Type := (BitVec 32)

abbrev CNTHVS_CTL_Type := (BitVec 32)

abbrev CNTHV_CTL_Type := (BitVec 32)

abbrev CNTV_CTL_Type := (BitVec 32)

abbrev CSSELR_Type := (BitVec 32)

abbrev CSSELR_EL1_Type := (BitVec 64)

abbrev CTR_Type := (BitVec 32)

abbrev DBGAUTHSTATUS_EL1_Type := (BitVec 64)

abbrev DBGAUTHSTATUS_Type := (BitVec 32)

abbrev DBGCLAIMCLR_EL1_Type := (BitVec 64)

abbrev DBGCLAIMCLR_Type := (BitVec 32)

abbrev DBGCLAIMSET_EL1_Type := (BitVec 64)

abbrev DBGCLAIMSET_Type := (BitVec 32)

abbrev MDCCINT_EL1_Type := (BitVec 64)

abbrev DBGDCCINT_Type := (BitVec 32)

abbrev MDRAR_EL1_Type := (BitVec 64)

abbrev DBGDRAR_Type := (BitVec 64)

abbrev DBGVCR32_EL2_Type := (BitVec 64)

abbrev DBGVCR_Type := (BitVec 32)

abbrev ERRIDR_EL1_Type := (BitVec 64)

abbrev ERRIDR_Type := (BitVec 32)

abbrev ERRSELR_EL1_Type := (BitVec 64)

abbrev ERRSELR_Type := (BitVec 32)

abbrev RMR_EL2_Type := (BitVec 64)

abbrev HRMR_Type := (BitVec 32)

abbrev HSTR_EL2_Type := (BitVec 64)

abbrev HSTR_Type := (BitVec 32)

abbrev HTCR_Type := (BitVec 32)

abbrev TRFCR_EL2_Type := (BitVec 64)

abbrev HTRFCR_Type := (BitVec 32)

abbrev ICC_ASGI1R_EL1_Type := (BitVec 64)

abbrev ICC_ASGI1R_Type := (BitVec 64)

abbrev ICC_BPR0_EL1_Type := (BitVec 64)

abbrev ICC_BPR0_Type := (BitVec 32)

abbrev ICC_BPR1_EL1_Type := (BitVec 64)

abbrev ICC_BPR1_Type := (BitVec 32)

abbrev ICC_CTLR_EL1_Type := (BitVec 64)

abbrev ICC_CTLR_Type := (BitVec 32)

abbrev ICC_DIR_EL1_Type := (BitVec 64)

abbrev ICC_DIR_Type := (BitVec 32)

abbrev ICC_EOIR0_EL1_Type := (BitVec 64)

abbrev ICC_EOIR0_Type := (BitVec 32)

abbrev ICC_EOIR1_EL1_Type := (BitVec 64)

abbrev ICC_EOIR1_Type := (BitVec 32)

abbrev ICC_HPPIR0_EL1_Type := (BitVec 64)

abbrev ICC_HPPIR0_Type := (BitVec 32)

abbrev ICC_HPPIR1_EL1_Type := (BitVec 64)

abbrev ICC_HPPIR1_Type := (BitVec 32)

abbrev ICC_SRE_EL2_Type := (BitVec 64)

abbrev ICC_HSRE_Type := (BitVec 32)

abbrev ICC_IAR0_EL1_Type := (BitVec 64)

abbrev ICC_IAR0_Type := (BitVec 32)

abbrev ICC_IAR1_EL1_Type := (BitVec 64)

abbrev ICC_IAR1_Type := (BitVec 32)

abbrev ICC_IGRPEN0_EL1_Type := (BitVec 64)

abbrev ICC_IGRPEN0_Type := (BitVec 32)

abbrev ICC_IGRPEN1_EL1_Type := (BitVec 64)

abbrev ICC_IGRPEN1_Type := (BitVec 32)

abbrev ICC_PMR_Type := (BitVec 32)

abbrev ICC_RPR_EL1_Type := (BitVec 64)

abbrev ICC_RPR_Type := (BitVec 32)

abbrev ICC_SGI0R_EL1_Type := (BitVec 64)

abbrev ICC_SGI0R_Type := (BitVec 64)

abbrev ICC_SGI1R_EL1_Type := (BitVec 64)

abbrev ICC_SGI1R_Type := (BitVec 64)

abbrev ICC_SRE_EL1_Type := (BitVec 64)

abbrev ICC_SRE_Type := (BitVec 32)

abbrev ICH_EISR_EL2_Type := (BitVec 64)

abbrev ICH_EISR_Type := (BitVec 32)

abbrev ICH_ELRSR_EL2_Type := (BitVec 64)

abbrev ICH_ELRSR_Type := (BitVec 32)

abbrev ICH_HCR_EL2_Type := (BitVec 64)

abbrev ICH_HCR_Type := (BitVec 32)

abbrev ICH_MISR_EL2_Type := (BitVec 64)

abbrev ICH_MISR_Type := (BitVec 32)

abbrev ICH_VMCR_EL2_Type := (BitVec 64)

abbrev ICH_VMCR_Type := (BitVec 32)

abbrev ICH_VTR_EL2_Type := (BitVec 64)

abbrev ICH_VTR_Type := (BitVec 32)

abbrev ICV_BPR0_EL1_Type := (BitVec 64)

abbrev ICV_BPR0_Type := (BitVec 32)

abbrev ICV_BPR1_EL1_Type := (BitVec 64)

abbrev ICV_BPR1_Type := (BitVec 32)

abbrev ICV_CTLR_EL1_Type := (BitVec 64)

abbrev ICV_CTLR_Type := (BitVec 32)

abbrev ICV_DIR_EL1_Type := (BitVec 64)

abbrev ICV_DIR_Type := (BitVec 32)

abbrev ICV_EOIR0_EL1_Type := (BitVec 64)

abbrev ICV_EOIR0_Type := (BitVec 32)

abbrev ICV_EOIR1_EL1_Type := (BitVec 64)

abbrev ICV_EOIR1_Type := (BitVec 32)

abbrev ICV_HPPIR0_EL1_Type := (BitVec 64)

abbrev ICV_HPPIR0_Type := (BitVec 32)

abbrev ICV_HPPIR1_EL1_Type := (BitVec 64)

abbrev ICV_HPPIR1_Type := (BitVec 32)

abbrev ICV_IAR0_EL1_Type := (BitVec 64)

abbrev ICV_IAR0_Type := (BitVec 32)

abbrev ICV_IAR1_EL1_Type := (BitVec 64)

abbrev ICV_IAR1_Type := (BitVec 32)

abbrev ICV_IGRPEN0_EL1_Type := (BitVec 64)

abbrev ICV_IGRPEN0_Type := (BitVec 32)

abbrev ICV_IGRPEN1_EL1_Type := (BitVec 64)

abbrev ICV_IGRPEN1_Type := (BitVec 32)

abbrev ICV_PMR_EL1_Type := (BitVec 64)

abbrev ICV_PMR_Type := (BitVec 32)

abbrev ICV_RPR_EL1_Type := (BitVec 64)

abbrev ICV_RPR_Type := (BitVec 32)

abbrev ID_AFR0_EL1_Type := (BitVec 64)

abbrev ID_AFR0_Type := (BitVec 32)

abbrev ID_DFR1_EL1_Type := (BitVec 64)

abbrev ID_DFR1_Type := (BitVec 32)

abbrev ID_ISAR0_EL1_Type := (BitVec 64)

abbrev ID_ISAR0_Type := (BitVec 32)

abbrev ID_ISAR5_EL1_Type := (BitVec 64)

abbrev ID_ISAR5_Type := (BitVec 32)

abbrev ID_MMFR5_EL1_Type := (BitVec 64)

abbrev ID_MMFR5_Type := (BitVec 32)

abbrev ID_PFR2_EL1_Type := (BitVec 64)

abbrev ID_PFR2_Type := (BitVec 32)

abbrev ISR_EL1_Type := (BitVec 64)

abbrev ISR_Type := (BitVec 32)

abbrev MPIDR_EL1_Type := (BitVec 64)

abbrev MPIDR_Type := (BitVec 32)

abbrev MVFR2_EL1_Type := (BitVec 64)

abbrev MVFR2_Type := (BitVec 32)

abbrev PAR_Type := (BitVec 64)

abbrev PMCNTEN_Type := (BitVec 64)

abbrev PMINTENSET_EL1_Type := (BitVec 64)

abbrev PMINTEN_Type := (BitVec 64)

abbrev PMOVS_Type := (BitVec 64)

abbrev PMSELR_EL0_Type := (BitVec 64)

abbrev PMSELR_Type := (BitVec 32)

abbrev PMSWINC_EL0_Type := (BitVec 64)

abbrev PMSWINC_Type := (BitVec 32)

abbrev PMUSERENR_EL0_Type := (BitVec 64)

abbrev PMUSERENR_Type := (BitVec 32)

abbrev PRRR_Type := (BitVec 32)

abbrev RMR_EL1_Type := (BitVec 64)

abbrev RMR_EL3_Type := (BitVec 64)

abbrev RMR_Type := (BitVec 32)

abbrev TRFCR_EL1_Type := (BitVec 64)

abbrev TRFCR_Type := (BitVec 32)

abbrev TTBCR2_Type := (BitVec 32)

abbrev VMPIDR_EL2_Type := (BitVec 64)

abbrev VMPIDR_Type := (BitVec 32)

abbrev VPIDR_EL2_Type := (BitVec 64)

abbrev VPIDR_Type := (BitVec 32)

abbrev VTCR_Type := (BitVec 32)

abbrev DBGDEVID_Type := (BitVec 32)

abbrev FPSID_Type := (BitVec 32)

abbrev ID_DFR0_EL1_Type := (BitVec 64)

abbrev TLBTR_Type := (BitVec 32)

abbrev CLIDR_Type := (BitVec 32)

abbrev ID_DFR0_Type := (BitVec 32)

abbrev ID_ISAR1_EL1_Type := (BitVec 64)

abbrev ID_ISAR1_Type := (BitVec 32)

abbrev ID_ISAR2_EL1_Type := (BitVec 64)

abbrev ID_ISAR2_Type := (BitVec 32)

abbrev ID_ISAR3_EL1_Type := (BitVec 64)

abbrev ID_ISAR3_Type := (BitVec 32)

abbrev ID_ISAR4_EL1_Type := (BitVec 64)

abbrev ID_ISAR4_Type := (BitVec 32)

abbrev ID_ISAR6_EL1_Type := (BitVec 64)

abbrev ID_ISAR6_Type := (BitVec 32)

abbrev ID_MMFR0_EL1_Type := (BitVec 64)

abbrev ID_MMFR0_Type := (BitVec 32)

abbrev ID_MMFR1_EL1_Type := (BitVec 64)

abbrev ID_MMFR1_Type := (BitVec 32)

abbrev ID_MMFR2_EL1_Type := (BitVec 64)

abbrev ID_MMFR2_Type := (BitVec 32)

abbrev ID_MMFR3_EL1_Type := (BitVec 64)

abbrev ID_MMFR3_Type := (BitVec 32)

abbrev ID_MMFR4_EL1_Type := (BitVec 64)

abbrev ID_MMFR4_Type := (BitVec 32)

abbrev ID_PFR0_EL1_Type := (BitVec 64)

abbrev ID_PFR0_Type := (BitVec 32)

abbrev ID_PFR1_EL1_Type := (BitVec 64)

abbrev ID_PFR1_Type := (BitVec 32)

abbrev MIDR_EL1_Type := (BitVec 64)

abbrev MIDR_Type := (BitVec 32)

abbrev MVFR0_EL1_Type := (BitVec 64)

abbrev MVFR0_Type := (BitVec 32)

abbrev MVFR1_EL1_Type := (BitVec 64)

abbrev MVFR1_Type := (BitVec 32)

abbrev NMRR_Type := (BitVec 32)

abbrev PMCEID0_EL0_Type := (BitVec 64)

abbrev PMCEID0_Type := (BitVec 32)

abbrev PMCEID1_EL0_Type := (BitVec 64)

abbrev PMCEID1_Type := (BitVec 32)

abbrev PMCEID2_Type := (BitVec 32)

abbrev PMCEID3_Type := (BitVec 32)

abbrev ACCDATA_EL1_Type := (BitVec 64)

abbrev AMCG1IDR_EL0_Type := (BitVec 64)

abbrev BRBINFINJ_EL1_Type := (BitVec 64)

abbrev CNTFRQ_EL0_Type := (BitVec 64)

abbrev CNTHPS_TVAL_EL2_Type := (BitVec 64)

abbrev CNTHP_TVAL_EL2_Type := (BitVec 64)

abbrev CNTHVS_TVAL_EL2_Type := (BitVec 64)

abbrev CNTHV_TVAL_EL2_Type := (BitVec 64)

abbrev CNTPS_TVAL_EL1_Type := (BitVec 64)

abbrev CNTP_TVAL_EL0_Type := (BitVec 64)

abbrev CNTV_TVAL_EL0_Type := (BitVec 64)

abbrev DACR32_EL2_Type := (BitVec 64)

abbrev DBGDTRRX_EL0_Type := (BitVec 64)

abbrev DBGDTRTX_EL0_Type := (BitVec 64)

abbrev DCZID_EL0_Type := (BitVec 64)

abbrev GMID_EL1_Type := (BitVec 64)

abbrev HAFGRTR_EL2_Type := (BitVec 64)

abbrev HDFGRTR2_EL2_Type := (BitVec 64)

abbrev HDFGRTR_EL2_Type := (BitVec 64)

abbrev HDFGWTR2_EL2_Type := (BitVec 64)

abbrev HDFGWTR_EL2_Type := (BitVec 64)

abbrev HFGITR2_EL2_Type := (BitVec 64)

abbrev HFGRTR2_EL2_Type := (BitVec 64)

abbrev HFGRTR_EL2_Type := (BitVec 64)

abbrev HFGWTR2_EL2_Type := (BitVec 64)

abbrev HFGWTR_EL2_Type := (BitVec 64)

abbrev ICC_CTLR_EL3_Type := (BitVec 64)

abbrev ICC_IGRPEN1_EL3_Type := (BitVec 64)

abbrev ICC_NMIAR1_EL1_Type := (BitVec 64)

abbrev ICC_SRE_EL3_Type := (BitVec 64)

abbrev ICV_NMIAR1_EL1_Type := (BitVec 64)

abbrev ID_AA64AFR0_EL1_Type := (BitVec 64)

abbrev ID_AA64AFR1_EL1_Type := (BitVec 64)

abbrev ID_AA64ISAR0_EL1_Type := (BitVec 64)

abbrev ID_AA64ISAR2_EL1_Type := (BitVec 64)

abbrev ID_AA64MMFR0_EL1_Type := (BitVec 64)

abbrev ID_AA64MMFR2_EL1_Type := (BitVec 64)

abbrev ID_AA64MMFR3_EL1_Type := (BitVec 64)

abbrev ID_AA64MMFR4_EL1_Type := (BitVec 64)

abbrev ID_AA64PFR1_EL1_Type := (BitVec 64)

abbrev ID_AA64PFR2_EL1_Type := (BitVec 64)

abbrev ID_AA64SMFR0_EL1_Type := (BitVec 64)

abbrev ID_AA64ZFR0_EL1_Type := (BitVec 64)

abbrev LORC_EL1_Type := (BitVec 64)

abbrev LOREA_EL1_Type := (BitVec 64)

abbrev LORID_EL1_Type := (BitVec 64)

abbrev LORN_EL1_Type := (BitVec 64)

abbrev LORSA_EL1_Type := (BitVec 64)

abbrev MDSELR_EL1_Type := (BitVec 64)

abbrev MECIDR_EL2_Type := (BitVec 64)

abbrev OSDTRRX_EL1_Type := (BitVec 64)

abbrev OSDTRTX_EL1_Type := (BitVec 64)

abbrev OSLAR_EL1_Type := (BitVec 64)

abbrev PMBIDR_EL1_Type := (BitVec 64)

abbrev PMECR_EL1_Type := (BitVec 64)

abbrev PMMIR_EL1_Type := (BitVec 64)

abbrev PMSEVFR_EL1_Type := (BitVec 64)

abbrev PMSFCR_EL1_Type := (BitVec 64)

abbrev PMSICR_EL1_Type := (BitVec 64)

abbrev PMSIRR_EL1_Type := (BitVec 64)

abbrev PMSLATFR_EL1_Type := (BitVec 64)

abbrev PMSNEVFR_EL1_Type := (BitVec 64)

abbrev PMSSCR_EL1_Type := (BitVec 64)

abbrev PMUACR_EL1_Type := (BitVec 64)

abbrev PMXEVCNTR_EL0_Type := (BitVec 64)

abbrev PMZR_EL0_Type := (BitVec 64)

abbrev SMIDR_EL1_Type := (BitVec 64)

abbrev SMPRI_EL1_Type := (BitVec 64)

abbrev SPMSELR_EL0_Type := (BitVec 64)

abbrev PAR_EL1_Type := (BitVec 128)

abbrev AMDEVARCH_Type := (BitVec 32)

abbrev AMEVTYPER0_EL0_Type := (BitVec 64)

abbrev AMIIDR_Type := (BitVec 32)

abbrev CNTFID0_Type := (BitVec 32)

abbrev CTIDEVARCH_Type := (BitVec 32)

abbrev EDDEVARCH_Type := (BitVec 32)

abbrev GICD_TYPER_Type := (BitVec 32)

abbrev ID_AA64DFR0_EL1_Type := (BitVec 64)

abbrev ID_AA64DFR1_EL1_Type := (BitVec 64)

abbrev ID_AA64ISAR1_EL1_Type := (BitVec 64)

abbrev ID_AA64MMFR1_EL1_Type := (BitVec 64)

abbrev ID_AA64PFR0_EL1_Type := (BitVec 64)

abbrev PMEVCNTR_EL0_Type := (BitVec 64)

abbrev PMCCNTR_EL0_Type := (BitVec 64)

abbrev PMBPTR_EL1_Type := (BitVec 64)

abbrev PMSDSFR_EL1_Type := (BitVec 64)

abbrev BRBSRCINJ_EL1_Type := (BitVec 64)

abbrev BRBTGTINJ_EL1_Type := (BitVec 64)

structure TLBIInfo where
  rec' : TLBIRecord
  shareability : Shareability
  deriving Inhabited, BEq

abbrev MAIR0_Type := (BitVec 32)

abbrev MAIR1_Type := (BitVec 32)

abbrev HMAIR0_Type := (BitVec 32)

abbrev HMAIR1_Type := (BitVec 32)

abbrev DACR_Type := (BitVec 32)

abbrev DBGDTR_EL0_Type := (BitVec 64)

abbrev DBGBCR_Type := (BitVec 32)

abbrev DBGBVR_Type := (BitVec 32)

abbrev DBGBXVR_Type := (BitVec 32)

abbrev DBGWCR_Type := (BitVec 32)

abbrev DBGWVR_Type := (BitVec 32)

abbrev PMEVCNTR_Type := (BitVec 32)

abbrev PMOVSSET_Type := (BitVec 32)

abbrev PMCCNTR_Type := (BitVec 64)

abbrev ICH_LR_EL2_Type := (BitVec 64)

abbrev ICC_AP0R_EL1_Type := (BitVec 64)

abbrev AIDR_EL1_Type := (BitVec 64)

abbrev REVIDR_EL1_Type := (BitVec 64)

abbrev TPIDR_EL2_Type := (BitVec 64)

abbrev ACTLR_EL2_Type := (BitVec 64)

abbrev SPMACCESSR_EL1_Type := (BitVec 64)

abbrev ICH_AP1R_EL2_Type := (BitVec 64)

abbrev PMEVCNTSVR_EL1_Type := (BitVec 64)

abbrev ICH_AP0R_EL2_Type := (BitVec 64)

abbrev TPIDR_EL1_Type := (BitVec 64)

abbrev ACTLR_EL1_Type := (BitVec 64)

abbrev ICC_AP1R_EL1_Type := (BitVec 64)

abbrev AFSR1_EL1_Type := (BitVec 64)

abbrev PMCCNTSVR_EL1_Type := (BitVec 64)

abbrev AMAIR2_EL2_Type := (BitVec 64)

abbrev ICV_AP0R_EL1_Type := (BitVec 64)

abbrev AFSR0_EL3_Type := (BitVec 64)

abbrev AFSR1_EL2_Type := (BitVec 64)

abbrev AFSR0_EL1_Type := (BitVec 64)

abbrev SPMACCESSR_EL2_Type := (BitVec 64)

abbrev PMICNTSVR_EL1_Type := (BitVec 64)

abbrev SCXTNUM_EL2_Type := (BitVec 64)

abbrev PMIAR_EL1_Type := (BitVec 64)

abbrev TPIDR_EL3_Type := (BitVec 64)

abbrev ACTLR_EL3_Type := (BitVec 64)

abbrev AMAIR_EL2_Type := (BitVec 64)

abbrev AMAIR_EL3_Type := (BitVec 64)

abbrev SCXTNUM_EL1_Type := (BitVec 64)

abbrev TPIDRRO_EL0_Type := (BitVec 64)

abbrev AMAIR_EL1_Type := (BitVec 64)

abbrev SCXTNUM_EL0_Type := (BitVec 64)

abbrev TPIDR2_EL0_Type := (BitVec 64)

abbrev SCXTNUM_EL3_Type := (BitVec 64)

abbrev TPIDR_EL0_Type := (BitVec 64)

abbrev RNDRRS_Type := (BitVec 64)

abbrev SMPRIMAP_EL2_Type := (BitVec 64)

abbrev RNDR_Type := (BitVec 64)

abbrev HACR_EL2_Type := (BitVec 64)

abbrev AMAIR2_EL3_Type := (BitVec 64)

abbrev AFSR1_EL3_Type := (BitVec 64)

abbrev ICV_AP1R_EL1_Type := (BitVec 64)

abbrev AFSR0_EL2_Type := (BitVec 64)

abbrev AMAIR2_EL1_Type := (BitVec 64)

abbrev SPMACCESSR_EL3_Type := (BitVec 64)

abbrev CNTVOFF_Type := (BitVec 64)

abbrev CNTV_CVAL_Type := (BitVec 64)

abbrev AMEVCNTR1_EL0_Type := (BitVec 64)

abbrev AMEVCNTVOFF0_EL2_Type := (BitVec 64)

abbrev AMEVCNTR0_Type := (BitVec 64)

abbrev AMEVCNTR1_Type := (BitVec 64)

abbrev AMEVCNTR0_EL0_Type := (BitVec 64)

abbrev AMEVCNTVOFF1_EL2_Type := (BitVec 64)

abbrev AMEVTYPER1_EL0_Type := (BitVec 64)

abbrev ERXADDR_EL1_Type := (BitVec 64)

abbrev ERXMISC0_EL1_Type := (BitVec 64)

abbrev ERXPFGCDN_EL1_Type := (BitVec 64)

abbrev ERXPFGF_EL1_Type := (BitVec 64)

abbrev ERXMISC1_EL1_Type := (BitVec 64)

abbrev ERXCTLR_EL1_Type := (BitVec 64)

abbrev ERXSTATUS_EL1_Type := (BitVec 64)

abbrev ERXFR_EL1_Type := (BitVec 64)

abbrev ERXGSR_EL1_Type := (BitVec 64)

abbrev ERXMISC3_EL1_Type := (BitVec 64)

abbrev ERXMISC2_EL1_Type := (BitVec 64)

abbrev ERXPFGCTL_EL1_Type := (BitVec 64)

abbrev BRBINF_EL1_Type := (BitVec 64)

abbrev BRBTGT_EL1_Type := (BitVec 64)

abbrev BRBSRC_EL1_Type := (BitVec 64)

abbrev AIFSR_Type := (BitVec 32)

abbrev HACR_Type := (BitVec 32)

abbrev HACTLR_Type := (BitVec 32)

abbrev TCMTR_Type := (BitVec 32)

abbrev ICV_AP0R_Type := (BitVec 32)

abbrev TPIDRURW_Type := (BitVec 32)

abbrev ICV_AP1R_Type := (BitVec 32)

abbrev ADFSR_Type := (BitVec 32)

abbrev REVIDR_Type := (BitVec 32)

abbrev TPIDRURO_Type := (BitVec 32)

abbrev DBGDTRTXext_Type := (BitVec 32)

abbrev ACTLR_Type := (BitVec 32)

abbrev DBGOSLAR_Type := (BitVec 32)

abbrev DBGDTRRXext_Type := (BitVec 32)

abbrev ICC_AP1R_Type := (BitVec 32)

abbrev ICH_AP1R_Type := (BitVec 32)

abbrev AMAIR0_Type := (BitVec 32)

abbrev HAMAIR0_Type := (BitVec 32)

abbrev ICH_AP0R_Type := (BitVec 32)

abbrev AIDR_Type := (BitVec 32)

abbrev ICH_LR_Type := (BitVec 32)

abbrev HADFSR_Type := (BitVec 32)

abbrev CNTFRQ_Type := (BitVec 32)

abbrev PMINTENSET_Type := (BitVec 32)

abbrev DBGOSECCR_Type := (BitVec 32)

abbrev ACTLR2_Type := (BitVec 32)

abbrev HAMAIR1_Type := (BitVec 32)

abbrev HAIFSR_Type := (BitVec 32)

abbrev ICC_AP0R_Type := (BitVec 32)

abbrev TPIDRPRW_Type := (BitVec 32)

abbrev DBGDTRRXint_Type := (BitVec 32)

abbrev HTPIDR_Type := (BitVec 32)

abbrev DBGDTRTXint_Type := (BitVec 32)

abbrev AMAIR1_Type := (BitVec 32)

abbrev ICH_LRC_Type := (BitVec 32)

abbrev AMEVTYPER0_Type := (BitVec 32)

abbrev AMEVTYPER1_Type := (BitVec 32)

abbrev ERXFR2_Type := (BitVec 32)

abbrev ERXMISC2_Type := (BitVec 32)

abbrev ERXFR_Type := (BitVec 32)

abbrev ERXADDR_Type := (BitVec 32)

abbrev ERXMISC0_Type := (BitVec 32)

abbrev ERXMISC5_Type := (BitVec 32)

abbrev ERXCTLR2_Type := (BitVec 32)

abbrev ERXMISC1_Type := (BitVec 32)

abbrev ERXCTLR_Type := (BitVec 32)

abbrev ERXMISC6_Type := (BitVec 32)

abbrev ERXMISC4_Type := (BitVec 32)

abbrev ERXADDR2_Type := (BitVec 32)

abbrev ERXMISC7_Type := (BitVec 32)

abbrev ERXMISC3_Type := (BitVec 32)

abbrev ERXSTATUS_Type := (BitVec 32)

abbrev HACTLR2_Type := (BitVec 32)

structure DxB where
  domain : MBReqDomain
  types : MBReqTypes
  nXS : Bool
  deriving Inhabited, BEq

inductive Barrier where
  | Barrier_DSB (_ : DxB)
  | Barrier_DMB (_ : DxB)
  | Barrier_ISB (_ : Unit)
  | Barrier_SSBB (_ : Unit)
  | Barrier_PSSBB (_ : Unit)
  | Barrier_SB (_ : Unit)
  deriving Inhabited, BEq

inductive Register : Type where
  | __emulator_termination_opcode
  | _HACTLR2
  | _ERXSTATUS
  | _ERXMISC3
  | _ERXMISC7
  | _ERXADDR2
  | _ERXMISC4
  | _ERXMISC6
  | _ERXCTLR
  | _ERXMISC1
  | _ERXCTLR2
  | _ERXMISC5
  | _ERXMISC0
  | _ERXADDR
  | _ERXFR
  | _ERXMISC2
  | _ERXFR2
  | _AMEVTYPER1
  | _AMEVTYPER0
  | _ICH_LRC
  | _AMAIR1_NS
  | AMAIR1_S
  | _DBGDTRTXint
  | _HTPIDR
  | _DBGDTRRXint
  | _TPIDRPRW_NS
  | TPIDRPRW_S
  | _ICC_AP0R
  | _HAIFSR
  | _HAMAIR1
  | _ACTLR2_NS
  | ACTLR2_S
  | _DBGOSECCR
  | _PMINTENSET
  | _CNTFRQ
  | _HADFSR
  | _ICH_LR
  | _AIDR
  | _ICH_AP0R
  | _HAMAIR0
  | _AMAIR0_NS
  | AMAIR0_S
  | _ICH_AP1R
  | _ICC_AP1R_NS
  | _ICC_AP1R_S
  | _DBGDTRRXext
  | DBGOSLAR
  | _ACTLR_NS
  | ACTLR_S
  | _DBGDTRTXext
  | _TPIDRURO_NS
  | TPIDRURO_S
  | _REVIDR
  | _ADFSR_NS
  | ADFSR_S
  | _ICV_AP1R
  | _TPIDRURW_NS
  | TPIDRURW_S
  | _ICV_AP0R
  | TCMTR
  | _HACTLR
  | _HACR
  | _AIFSR_NS
  | AIFSR_S
  | BRBSRC_EL1
  | BRBTGT_EL1
  | BRBINF_EL1
  | ERXPFGCTL_EL1
  | ERXMISC2_EL1
  | ERXMISC3_EL1
  | ERXGSR_EL1
  | ERXFR_EL1
  | ERXSTATUS_EL1
  | ERXCTLR_EL1
  | ERXMISC1_EL1
  | ERXPFGF_EL1
  | ERXPFGCDN_EL1
  | ERXMISC0_EL1
  | ERXADDR_EL1
  | AMEVTYPER1_EL0
  | AMEVCNTVOFF1_EL2
  | _AMEVCNTR0_EL0
  | _AMEVCNTR1
  | AMEVCNTR0
  | AMEVCNTVOFF0_EL2
  | AMEVCNTR1_EL0
  | _CNTV_CVAL
  | _CNTVOFF
  | SPMACCESSR_EL3
  | AMAIR2_EL1
  | AFSR0_EL2
  | ICV_AP1R_EL1
  | AFSR1_EL3
  | AMAIR2_EL3
  | HACR_EL2
  | RNDR
  | SMPRIMAP_EL2
  | RNDRRS
  | TPIDR_EL0
  | SCXTNUM_EL3
  | TPIDR2_EL0
  | SCXTNUM_EL0
  | AMAIR_EL1
  | TPIDRRO_EL0
  | SCXTNUM_EL1
  | AMAIR_EL3
  | AMAIR_EL2
  | ACTLR_EL3
  | TPIDR_EL3
  | PMIAR_EL1
  | SCXTNUM_EL2
  | PMICNTSVR_EL1
  | SPMACCESSR_EL2
  | AFSR0_EL1
  | AFSR1_EL2
  | AFSR0_EL3
  | ICV_AP0R_EL1
  | AMAIR2_EL2
  | PMCCNTSVR_EL1
  | AFSR1_EL1
  | ICC_AP1R_EL1_NS
  | ICC_AP1R_EL1_S
  | ACTLR_EL1
  | TPIDR_EL1
  | ICH_AP0R_EL2
  | PMEVCNTSVR_EL1
  | ICH_AP1R_EL2
  | SPMACCESSR_EL1
  | ACTLR_EL2
  | TPIDR_EL2
  | REVIDR_EL1
  | AIDR_EL1
  | ICC_AP0R_EL1
  | ICH_LR_EL2
  | _PMCCNTR
  | _PMOVSSET
  | _PMEVCNTR
  | _DBGWVR
  | _DBGWCR
  | _DBGBXVR
  | _DBGBVR
  | _DBGBCR
  | STACK_LIMIT
  | STACK_BASE
  | HEAP_LIMIT
  | HEAP_BASE
  | __has_spe_pseudo_cycles
  | SMCR_EL3_LEN_VALUE
  | CPTR_EL3_ESM_VALUE
  | CPTR_EL3_EZ_VALUE
  | ZCR_EL3_LEN_VALUE
  | CFG_RMR_AA64
  | __DBG_ROM_ADDR
  | __mops_forward_copy
  | __trickbox_enabled
  | __ignore_rvbar_in_aarch32
  | __unpred_tsize_aborts
  | __syncAbortOnDeviceWrite
  | __syncAbortOnWriteNormNonCache
  | __syncAbortOnWriteNormCache
  | __syncAbortOnTTWNonCache
  | __syncAbortOnTTWCache
  | __syncAbortOnPrefetch
  | __syncAbortOnSoWrite
  | __syncAbortOnSoRead
  | __syncAbortOnDeviceRead
  | __syncAbortOnReadNormNonCache
  | __syncAbortOnReadNormCache
  | __PMUBase
  | __GICITSControlBase
  | __GICDistBase
  | __GICCPUInterfaceBase
  | __ExtDebugBase
  | __CNTControlBase
  | __CTIBase
  | _DBGDTR_EL0
  | DACR_S
  | _DACR_NS
  | _HMAIR1
  | _HMAIR0
  | _MAIR1_S
  | _MAIR1_NS
  | _MAIR0_S
  | _MAIR0_NS
  | BRBTGTINJ_EL1
  | BRBSRCINJ_EL1
  | SPESampleCounter
  | SPERecordData
  | PMSDSFR_EL1
  | PMBPTR_EL1
  | PMCCNTR_EL0
  | PMEVCNTR_EL0
  | __g1_activity_monitor_offset_implemented
  | __g1_activity_monitor_implemented
  | __supported_va_size
  | __rme_l0gptsz
  | __mpam_has_altsp
  | __mecid_width
  | __gmid_log2_block_size
  | __dczid_log2_block_size
  | __CNTbase_frequency
  | ID_AA64PFR0_EL1
  | ID_AA64MMFR1_EL1
  | ID_AA64ISAR1_EL1
  | ID_AA64DFR1_EL1
  | ID_AA64DFR0_EL1
  | GICD_TYPER
  | EDDEVARCH
  | CTIDEVARCH
  | CNTFID0
  | CFG_MPIDR
  | AMIIDR
  | AMEVTYPER0_EL0
  | AMDEVARCH
  | _PAR_EL1
  | SPMSELR_EL0
  | SMPRI_EL1
  | SMIDR_EL1
  | PMZR_EL0
  | PMXEVCNTR_EL0
  | PMUACR_EL1
  | PMSSCR_EL1
  | PMSNEVFR_EL1
  | PMSLATFR_EL1
  | PMSIRR_EL1
  | PMSICR_EL1
  | PMSFCR_EL1
  | PMSEVFR_EL1
  | PMMIR_EL1
  | PMECR_EL1
  | PMBIDR_EL1
  | OSLAR_EL1
  | OSDTRTX_EL1
  | OSDTRRX_EL1
  | MECIDR_EL2
  | MDSELR_EL1
  | LORSA_EL1
  | LORN_EL1
  | LORID_EL1
  | LOREA_EL1
  | LORC_EL1
  | ID_AA64ZFR0_EL1
  | ID_AA64SMFR0_EL1
  | ID_AA64PFR2_EL1
  | ID_AA64PFR1_EL1
  | ID_AA64MMFR4_EL1
  | ID_AA64MMFR3_EL1
  | ID_AA64MMFR2_EL1
  | ID_AA64MMFR0_EL1
  | ID_AA64ISAR2_EL1
  | ID_AA64ISAR0_EL1
  | ID_AA64AFR1_EL1
  | ID_AA64AFR0_EL1
  | ICV_NMIAR1_EL1
  | ICC_SRE_EL3
  | ICC_NMIAR1_EL1
  | ICC_IGRPEN1_EL3
  | ICC_CTLR_EL3
  | HFGWTR_EL2
  | HFGWTR2_EL2
  | HFGRTR_EL2
  | HFGRTR2_EL2
  | HFGITR2_EL2
  | HDFGWTR_EL2
  | HDFGWTR2_EL2
  | HDFGRTR_EL2
  | HDFGRTR2_EL2
  | HAFGRTR_EL2
  | GMID_EL1
  | DCZID_EL0
  | DBGDTRTX_EL0
  | DBGDTRRX_EL0
  | DACR32_EL2
  | CNTV_TVAL_EL0
  | CNTP_TVAL_EL0
  | CNTPS_TVAL_EL1
  | CNTHV_TVAL_EL2
  | CNTHVS_TVAL_EL2
  | CNTHP_TVAL_EL2
  | CNTHPS_TVAL_EL2
  | CNTFRQ_EL0
  | BRBINFINJ_EL1
  | AMCG1IDR_EL0
  | ACCDATA_EL1
  | _PMCEID3
  | _PMCEID2
  | _PMCEID1
  | PMCEID1_EL0
  | _PMCEID0
  | PMCEID0_EL0
  | _NMRR_NS
  | NMRR_S
  | _MVFR1
  | MVFR1_EL1
  | _MVFR0
  | MVFR0_EL1
  | _MIDR
  | MIDR_EL1
  | _ID_PFR1
  | ID_PFR1_EL1
  | _ID_PFR0
  | ID_PFR0_EL1
  | _ID_MMFR4
  | ID_MMFR4_EL1
  | _ID_MMFR3
  | ID_MMFR3_EL1
  | _ID_MMFR2
  | ID_MMFR2_EL1
  | _ID_MMFR1
  | ID_MMFR1_EL1
  | _ID_MMFR0
  | ID_MMFR0_EL1
  | _ID_ISAR6
  | ID_ISAR6_EL1
  | _ID_ISAR4
  | ID_ISAR4_EL1
  | _ID_ISAR3
  | ID_ISAR3_EL1
  | _ID_ISAR2
  | ID_ISAR2_EL1
  | _ID_ISAR1
  | ID_ISAR1_EL1
  | _ID_DFR0
  | _CLIDR
  | __num_ctx_breakpoints
  | __exclusive_granule_size
  | TLBTR
  | ID_DFR0_EL1
  | FPSID
  | DBGDEVID
  | _VTCR
  | _VPIDR
  | VPIDR_EL2
  | _VMPIDR
  | VMPIDR_EL2
  | _TTBCR2_NS
  | TTBCR2_S
  | _TRFCR
  | TRFCR_EL1
  | _RMR
  | RMR_EL3
  | RMR_EL1
  | _PRRR_NS
  | PRRR_S
  | _PMUSERENR
  | PMUSERENR_EL0
  | _PMSWINC
  | PMSWINC_EL0
  | _PMSELR
  | PMSELR_EL0
  | _PMOVS
  | _PMINTEN
  | PMINTENSET_EL1
  | _PMCNTEN
  | PAR_S
  | PAR_NS
  | _MVFR2
  | MVFR2_EL1
  | _MPIDR
  | MPIDR_EL1
  | _ISR
  | ISR_EL1
  | _ID_PFR2
  | ID_PFR2_EL1
  | _ID_MMFR5
  | ID_MMFR5_EL1
  | _ID_ISAR5
  | ID_ISAR5_EL1
  | _ID_ISAR0
  | ID_ISAR0_EL1
  | _ID_DFR1
  | ID_DFR1_EL1
  | _ID_AFR0
  | ID_AFR0_EL1
  | _ICV_RPR
  | ICV_RPR_EL1
  | _ICV_PMR
  | ICV_PMR_EL1
  | _ICV_IGRPEN1
  | ICV_IGRPEN1_EL1
  | _ICV_IGRPEN0
  | ICV_IGRPEN0_EL1
  | _ICV_IAR1
  | ICV_IAR1_EL1
  | _ICV_IAR0
  | ICV_IAR0_EL1
  | _ICV_HPPIR1
  | ICV_HPPIR1_EL1
  | _ICV_HPPIR0
  | ICV_HPPIR0_EL1
  | _ICV_EOIR1
  | ICV_EOIR1_EL1
  | _ICV_EOIR0
  | ICV_EOIR0_EL1
  | _ICV_DIR
  | ICV_DIR_EL1
  | _ICV_CTLR
  | ICV_CTLR_EL1
  | _ICV_BPR1
  | ICV_BPR1_EL1
  | _ICV_BPR0
  | ICV_BPR0_EL1
  | _ICH_VTR
  | ICH_VTR_EL2
  | _ICH_VMCR
  | ICH_VMCR_EL2
  | _ICH_MISR
  | ICH_MISR_EL2
  | _ICH_HCR
  | ICH_HCR_EL2
  | _ICH_ELRSR
  | ICH_ELRSR_EL2
  | _ICH_EISR
  | ICH_EISR_EL2
  | _ICC_SRE_S
  | ICC_SRE_EL1_S
  | _ICC_SRE_NS
  | ICC_SRE_EL1_NS
  | _ICC_SGI1R
  | ICC_SGI1R_EL1
  | _ICC_SGI0R
  | ICC_SGI0R_EL1
  | _ICC_RPR
  | ICC_RPR_EL1
  | _ICC_PMR
  | _ICC_IGRPEN1_S
  | ICC_IGRPEN1_EL1_S
  | _ICC_IGRPEN1_NS
  | ICC_IGRPEN1_EL1_NS
  | _ICC_IGRPEN0
  | ICC_IGRPEN0_EL1
  | _ICC_IAR1
  | ICC_IAR1_EL1
  | _ICC_IAR0
  | ICC_IAR0_EL1
  | _ICC_HSRE
  | ICC_SRE_EL2
  | _ICC_HPPIR1
  | ICC_HPPIR1_EL1
  | _ICC_HPPIR0
  | ICC_HPPIR0_EL1
  | _ICC_EOIR1
  | ICC_EOIR1_EL1
  | _ICC_EOIR0
  | ICC_EOIR0_EL1
  | _ICC_DIR
  | ICC_DIR_EL1
  | _ICC_CTLR_S
  | ICC_CTLR_EL1_S
  | _ICC_CTLR_NS
  | ICC_CTLR_EL1_NS
  | _ICC_BPR1_S
  | ICC_BPR1_EL1_S
  | _ICC_BPR1_NS
  | ICC_BPR1_EL1_NS
  | _ICC_BPR0
  | ICC_BPR0_EL1
  | _ICC_ASGI1R
  | ICC_ASGI1R_EL1
  | _HTRFCR
  | TRFCR_EL2
  | _HTCR
  | _HSTR
  | HSTR_EL2
  | _HRMR
  | RMR_EL2
  | _ERRSELR
  | ERRSELR_EL1
  | _ERRIDR
  | ERRIDR_EL1
  | _DBGVCR
  | DBGVCR32_EL2
  | _DBGDRAR
  | MDRAR_EL1
  | _DBGDCCINT
  | MDCCINT_EL1
  | _DBGCLAIMSET
  | DBGCLAIMSET_EL1
  | _DBGCLAIMCLR
  | DBGCLAIMCLR_EL1
  | _DBGAUTHSTATUS
  | DBGAUTHSTATUS_EL1
  | _CTR
  | _CSSELR_NS
  | CSSELR_EL1
  | CSSELR_S
  | _CNTV_CTL
  | _CNTHV_CTL
  | _CNTHVS_CTL
  | _CNTHPS_CTL
  | _CNTHCTL
  | _CCSIDR
  | CCSIDR_EL1
  | _CCSIDR2
  | CCSIDR2_EL1
  | _AMUSERENR
  | AMUSERENR_EL0
  | _AMCR
  | AMCR_EL0
  | _AMCNTENSET1
  | AMCNTENSET1_EL0
  | _AMCNTENSET0
  | AMCNTENSET0_EL0
  | _AMCNTENCLR1
  | AMCNTENCLR1_EL0
  | _AMCNTENCLR0
  | AMCNTENCLR0_EL0
  | _AMCGCR
  | AMCGCR_EL0
  | _AMCFGR
  | AMCFGR_EL0
  | PMVIDSR
  | PMVCIDSR
  | PMPIDR4
  | PMPIDR3
  | PMPIDR2
  | PMPIDR1
  | PMPIDR0
  | PMPCSR
  | PMPCSCTL
  | PMMIR
  | PMLSR
  | PMLAR
  | PMITCTRL
  | PMIIDR
  | PMDEVTYPE
  | PMDEVID
  | PMCIDR3
  | PMCIDR2
  | PMCIDR1
  | PMCIDR0
  | PMCGCR0
  | PMCFGR
  | PMAUTHSTATUS
  | JOSCR
  | JMCR
  | JIDR
  | ICC_MSRE
  | ICC_MGRPEN1
  | ICC_MCTLR
  | GITS_TYPER
  | GITS_STATUSR
  | GITS_SGIR
  | GITS_PARTIDR
  | GITS_MPIDR
  | GITS_MPAMIDR
  | GITS_IIDR
  | GITS_CWRITER
  | GITS_CTLR
  | GITS_CREADR
  | GITS_CBASER
  | GICV_STATUSR
  | GICV_RPR
  | GICV_PMR
  | GICV_IAR
  | GICV_HPPIR
  | GICV_EOIR
  | GICV_DIR
  | GICV_CTLR
  | GICV_BPR
  | GICV_AIAR
  | GICV_AHPPIR
  | GICV_AEOIR
  | GICV_ABPR
  | GICR_WAKER
  | GICR_VSGIR
  | GICR_VSGIPENDR
  | GICR_VPROPBASER
  | GICR_VPENDBASER
  | GICR_SYNCR
  | GICR_STATUSR
  | GICR_SETLPIR
  | GICR_PROPBASER
  | GICR_PENDBASER
  | GICR_PARTIDR
  | GICR_MPAMIDR
  | GICR_ISENABLER0
  | GICR_INVLPIR
  | GICR_INVALLR
  | GICR_INMIR0
  | GICR_IIDR
  | GICR_CTLR
  | GICR_CLRLPIR
  | GICM_TYPER
  | GICM_SETSPI_SR
  | GICM_SETSPI_NSR
  | GICM_IIDR
  | GICM_CLRSPI_SR
  | GICM_CLRSPI_NSR
  | GICH_VTR
  | GICH_VMCR
  | GICH_MISR
  | GICH_HCR
  | GICH_ELRSR
  | GICH_EISR
  | GICD_TYPER2
  | GICD_STATUSR
  | GICD_SGIR
  | GICD_SETSPI_SR
  | GICD_SETSPI_NSR
  | GICD_IIDR
  | GICD_CTLR
  | GICD_CLRSPI_SR
  | GICD_CLRSPI_NSR
  | GICC_STATUSR
  | GICC_RPR
  | GICC_PMR
  | GICC_IAR
  | GICC_HPPIR
  | GICC_EOIR
  | GICC_DIR
  | GICC_BPR
  | GICC_AIAR
  | GICC_AHPPIR
  | GICC_AEOIR
  | GICC_ABPR
  | FCSEIDR
  | EDVIDSR
  | EDRCR
  | EDPRSR
  | EDPRCR
  | EDPIDR4
  | EDPIDR3
  | EDPIDR2
  | EDPIDR1
  | EDPIDR0
  | EDPFR
  | EDPCSR
  | EDLSR
  | EDLAR
  | EDITCTRL
  | EDHSR
  | EDDFR1
  | EDDFR
  | EDDEVTYPE
  | EDDEVID2
  | EDDEVID1
  | EDDEVID
  | EDCIDR3
  | EDCIDR2
  | EDCIDR1
  | EDCIDR0
  | EDAA32PFR
  | DBGWFAR
  | DBGDSAR
  | DBGDIDR
  | DBGDEVID2
  | DBGDEVID1
  | CTIPIDR4
  | CTIPIDR3
  | CTIPIDR2
  | CTIPIDR1
  | CTIPIDR0
  | CTILSR
  | CTILAR
  | CTIITCTRL
  | CTIDEVTYPE
  | CTIDEVID2
  | CTIDEVID1
  | CTIDEVID
  | CTIDEVCTL
  | CTICONTROL
  | CTICIDR3
  | CTICIDR2
  | CTICIDR1
  | CTICIDR0
  | CTIAUTHSTATUS
  | CNTSR
  | CNTNSAR
  | CNTID
  | CNTEL0ACR
  | AMPIDR4
  | AMPIDR3
  | AMPIDR2
  | AMPIDR1
  | AMPIDR0
  | AMDEVTYPE
  | AMCIDR3
  | AMCIDR2
  | AMCIDR1
  | AMCIDR0
  | RVBAR_EL3
  | RVBAR_EL2
  | RVBAR_EL1
  | _VDISR
  | VDISR_EL2
  | _VDFSR
  | VSESR_EL2
  | _DISR
  | DISR_EL1
  | HFGITR_EL2
  | VNCR_EL2
  | RCWSMASK_EL1
  | RCWMASK_EL1
  | SPESampleCounterValid
  | SPESampleCounterPending
  | VMECID_A_EL2
  | S2POR_EL1
  | VSTTBR_EL2
  | VSTCR_EL2
  | S2PIR_EL2
  | MECID_RL_A_EL3
  | MECID_P1_EL2
  | MECID_A1_EL2
  | MECID_A0_EL2
  | VMECID_P_EL2
  | MECID_P0_EL2
  | POR_EL0
  | POR_EL3
  | POR_EL2
  | POR_EL1
  | EDWAR
  | DBGWVR_EL1
  | DBGWCR_EL1
  | _VTTBR_EL2
  | VTTBR
  | VTCR_EL2
  | _EDSCR2
  | DBGBVR_EL1
  | DBGBCR_EL1
  | CONTEXTIDR_EL2
  | TFSR_EL3
  | TFSR_EL2
  | TFSR_EL1
  | TFSRE0_EL1
  | RGSR_EL1
  | GCR_EL1
  | _CNTKCTL
  | APGAKeyLo_EL1
  | APGAKeyHi_EL1
  | APDBKeyLo_EL1
  | APDBKeyHi_EL1
  | APDAKeyLo_EL1
  | APDAKeyHi_EL1
  | APIBKeyLo_EL1
  | APIBKeyHi_EL1
  | APIAKeyLo_EL1
  | APIAKeyHi_EL1
  | TTBR0_EL3
  | SCTLR2_EL3
  | PIR_EL3
  | MAIR_EL3
  | MAIR2_EL3
  | PIRE0_EL2
  | TCR2_EL2
  | PIR_EL2
  | MAIR_EL2
  | MAIR2_EL2
  | TCR2_EL1
  | PIR_EL1
  | PIRE0_EL1
  | MAIR_EL1
  | MAIR2_EL1
  | GICC_CTLR
  | __tlb_enabled
  | GPTBR_EL3
  | GPCCR_EL3
  | CNTKCTL_EL1
  | CNTSCR
  | CNTCR
  | CNTPS_CVAL_EL1
  | CNTPS_CTL_EL1
  | CNTHV_CVAL_EL2
  | CNTHV_CTL_EL2
  | CNTHVS_CVAL_EL2
  | CNTHVS_CTL_EL2
  | CNTHPS_CVAL_EL2
  | CNTHPS_CTL_EL2
  | CNTV_CVAL_EL0
  | CNTV_CTL_EL0
  | CNTP_CVAL_S
  | _CNTP_CVAL_NS
  | CNTP_CVAL_EL0
  | CNTP_CTL_S
  | _CNTP_CTL_NS
  | CNTP_CTL_EL0
  | _CNTHP_CVAL
  | CNTHP_CVAL_EL2
  | _CNTHP_CTL
  | CNTHP_CTL_EL2
  | _FPEXC
  | FPEXC32_EL2
  | SCTLR2_EL2
  | SCTLR2_EL1
  | _IFAR_S
  | _IFAR_NS
  | _HCR2
  | _DBGDSCRext
  | _DBGDSCRint
  | IFSR_S
  | _IFSR_NS
  | IFSR32_EL2
  | DFSR_S
  | _DFSR_NS
  | _DFAR_S
  | _DFAR_NS
  | MVBAR
  | _HVBAR
  | _ELR_hyp
  | _HSR
  | _HPFAR
  | _HIFAR
  | _HDFAR
  | TTBR1_EL2
  | _TTBR1_EL1
  | TTBR1_S
  | TTBR1_NS
  | _TTBR0_EL2
  | HTTBR
  | _TTBR0_EL1
  | TTBR0_S
  | TTBR0_NS
  | CONTEXTIDR_S
  | _CONTEXTIDR_NS
  | TTBCR_S
  | _TTBCR_NS
  | CONTEXTIDR_EL1
  | CLIDR_EL1
  | MPAMSM_EL1
  | MPAM0_EL1
  | MPAMVPM7_EL2
  | MPAMVPM6_EL2
  | MPAMVPM5_EL2
  | MPAMVPM4_EL2
  | MPAMVPM3_EL2
  | MPAMVPM2_EL2
  | MPAMVPM1_EL2
  | MPAMVPMV_EL2
  | MPAMVPM0_EL2
  | MPAMHCR_EL2
  | MPAMIDR_EL1
  | _MPAM1_EL1
  | _MPAM3_EL3
  | MPAM2_EL2
  | HCRX_EL2
  | GCSCRE0_EL1
  | VBAR_S
  | _VBAR_NS
  | VBAR_EL3
  | VBAR_EL2
  | VBAR_EL1
  | EDESR
  | _EDECCR
  | OSECCR_EL1
  | SPSR_und
  | _SPSR_svc
  | SPSR_mon
  | SPSR_irq
  | _SPSR_hyp
  | SPSR_fiq
  | SPSR_abt
  | SPSR_EL3
  | SPSR_EL2
  | SPSR_EL1
  | ELR_EL3
  | ELR_EL2
  | ELR_EL1
  | PFAR_EL2
  | PFAR_EL1
  | MFAR_EL3
  | HPFAR_EL2
  | FAR_EL3
  | FAR_EL2
  | FAR_EL1
  | ESR_EL3
  | ESR_EL2
  | ESR_EL1
  | SCTLR_S
  | _SCTLR_NS
  | SCTLR_EL3
  | SCTLR_EL1
  | _HSCTLR
  | SCTLR_EL2
  | _HCR
  | _DBGOSLSR
  | OSLSR_EL1
  | MDSCR_EL1
  | GCSCR_EL3
  | GCSCR_EL2
  | GCSCR_EL1
  | __GIC_Pending
  | __GIC_Active
  | _DBGPRCR
  | DBGPRCR_EL1
  | _DBGOSDLR
  | OSDLR_EL1
  | SP_EL3
  | SP_EL2
  | SP_EL1
  | SP_EL0
  | NSACR
  | _HCPTR
  | _CPACR
  | CPTR_EL3
  | CPTR_EL2
  | CPACR_EL1
  | GCSPR_EL3
  | GCSPR_EL2
  | GCSPR_EL1
  | GCSPR_EL0
  | SMCR_EL3
  | SMCR_EL2
  | SMCR_EL1
  | ZCR_EL3
  | ZCR_EL2
  | ZCR_EL1
  | PMBSR_EL1
  | PMBLIMITR_EL1
  | PMSCR_EL2
  | PMSCR_EL1
  | SPESampleAddressValid
  | SPESampleAddress
  | PMSIDR_EL1
  | Records_TGT
  | Records_SRC
  | Records_INF
  | BRBIDR0_EL1
  | TCR_EL3
  | TCR_EL2
  | TCR_EL1
  | _DSPSR2
  | _DSPSR
  | DSPSR_EL0
  | _DLR
  | DLR_EL0
  | EDECR
  | __mpam_vpmr_max
  | __mpam_pmg_max
  | __mpam_partid_max
  | __mpam_has_hcr
  | __impdef_TG1
  | __impdef_TG0
  | CFG_RVBAR
  | CNTHCTL_EL2
  | CNTVOFF_EL2
  | CNTPOFF_EL2
  | BRBTS_EL1
  | BRBFCR_EL1
  | BRBCR_EL2
  | BRBCR_EL1
  | PMOVSSET_EL0
  | PMICNTR_EL0
  | _SDER
  | _SDER32_EL3
  | SDER32_EL2
  | SDCR
  | PMICFILTR_EL0
  | _PMEVTYPER
  | PMEVTYPER_EL0
  | _PMCNTENSET
  | PMCNTENSET_EL0
  | _PMCCFILTR
  | PMCCFILTR_EL0
  | MDCR_EL3
  | _PMOVSR
  | PMOVSCLR_EL0
  | _PMINTENCLR
  | PMINTENCLR_EL1
  | _PMCR
  | PMCR_EL0
  | _PMCNTENCLR
  | PMCNTENCLR_EL0
  | _EDSCR
  | MDCCSR_EL0
  | _HDCR
  | MDCR_EL2
  | __supported_pa_size
  | __max_implemented_sveveclen
  | __max_implemented_smeveclen
  | __has_sve_extended_bf16
  | __block_bbm_implemented
  | CTR_EL0
  | ERRnFR
  | RVBAR
  | _FPSCR
  | __sme_only
  | __setg_mops_option_a_supported
  | __set_mops_option_a_supported
  | __mte_implemented
  | __mpam_major
  | __mpam_frac
  | __isb_is_branch
  | __has_sme_priority_control
  | __feat_rpres
  | __empam_tidr_implemented
  | __empam_sdeflt_implemented
  | __empam_force_ns_implemented
  | __empam_force_ns_RAO
  | __cpyf_mops_option_a_supported
  | __cpy_mops_option_a_supported
  | __apply_effective_shareability
  | SCR
  | SCR_EL3
  | HCR_EL2
  | _Dclone
  | LR_mon
  | SP_mon
  | sp_rel_access_pc
  | __DCACHE_CCSIDR_RESET
  | __ICACHE_CCSIDR_RESET
  | __highest_el_aarch32
  | __ExclusiveMonitorSet
  | __BranchTaken
  | Branchtypetaken
  | __currentCond
  | __ThisInstrEnc
  | __ThisInstr
  | __ETEBase
  | __VLPI_base
  | __SGI_base
  | __RD_base
  | __CNTCTLBase
  | __CNTEL0BaseN
  | __CNTBaseN
  | __CNTReadBase
  | __InstructionStep
  | RTPIDEN
  | RLPIDEN
  | SPNIDEN
  | SPIDEN
  | NIDEN
  | DBGEN
  | __last_branch_valid
  | __last_cycle_count
  | SPERecordSize
  | __SPE_LFSR_initialized
  | __SPE_LFSR
  | SPESampleEvents
  | SPESampleTimestampValid
  | SPESampleTimestamp
  | SPESampleSubclassValid
  | SPESampleSubclass
  | SPESampleClass
  | SPESampleOpType
  | SPESampleDataSourceValid
  | SPESampleDataSource
  | SPESamplePreviousBranchAddressValid
  | SPESamplePreviousBranchAddress
  | SPESampleInstIsNV2
  | SPESampleContextEL2Valid
  | SPESampleContextEL2
  | SPESampleContextEL1Valid
  | SPESampleContextEL1
  | SPESampleInFlight
  | TSTATE
  | ICC_PMR_EL1
  | FPSR
  | FPCR
  | _ZT0
  | _ZA
  | _FFR
  | _P
  | _Z
  | BTypeCompatible
  | BTypeNext
  | InGuardedPage
  | RC
  | PhysicalCount
  | _PC
  | R30
  | R29
  | R28
  | R27
  | R26
  | R25
  | R24
  | R23
  | R22
  | R21
  | R20
  | R19
  | R18
  | R17
  | R16
  | R15
  | R14
  | R13
  | R12
  | R11
  | R10
  | R9
  | R8
  | R7
  | R6
  | R5
  | R4
  | R3
  | R2
  | R1
  | R0
  | EventRegister
  | ShouldAdvanceSS
  | ShouldAdvanceIT
  | PSTATE
  | __clock_divider
  | PMULastThresholdValue
  | PMUEventAccumulator
  | _DormantCtlReg
  | _ConfigReg
  | IsWFEsleep
  | IsWFIsleep
  | CP15SDISABLE2
  | CP15SDISABLE
  | __cycle_count
  | __trcclaim_tags
  | NUM_WATCHPOINTS
  | NUM_BREAKPOINTS
  | NUM_GIC_LIST_REGS
  | NUM_GIC_PRIORITY_BITS
  | NUM_GIC_PREEMPTION_BITS
  | NUM_BRBE_RECORDS
  | NUM_PMU_COUNTERS
  | NUM_AMU_CG1_MONITORS
  | NUM_AMU_CG0_MONITORS
  | NUM_AMU_COUNTER_GROUPS
  | VariantImplemented
  | FeatureImpl
  | v9Ap4_IMPLEMENTED
  | v9Ap3_IMPLEMENTED
  | v9Ap2_IMPLEMENTED
  | v9Ap1_IMPLEMENTED
  | v9Ap0_IMPLEMENTED
  | v8Ap9_IMPLEMENTED
  | v8Ap8_IMPLEMENTED
  | v8Ap7_IMPLEMENTED
  | v8Ap6_IMPLEMENTED
  | v8Ap5_IMPLEMENTED
  | v8Ap4_IMPLEMENTED
  | v8Ap3_IMPLEMENTED
  | v8Ap2_IMPLEMENTED
  | v8Ap1_IMPLEMENTED
  | v8Ap0_IMPLEMENTED
  | FEAT_TRBE_MPAM_IMPLEMENTED
  | FEAT_TRBE_EXT_IMPLEMENTED
  | FEAT_SYSREG128_IMPLEMENTED
  | FEAT_SYSINSTR128_IMPLEMENTED
  | FEAT_SVE_B16B16_IMPLEMENTED
  | FEAT_SVE2p1_IMPLEMENTED
  | FEAT_SME_F16F16_IMPLEMENTED
  | FEAT_SME2p1_IMPLEMENTED
  | FEAT_SEBEP_IMPLEMENTED
  | FEAT_LVA3_IMPLEMENTED
  | FEAT_LSE128_IMPLEMENTED
  | FEAT_ITE_IMPLEMENTED
  | FEAT_GCS_IMPLEMENTED
  | FEAT_ETEv1p3_IMPLEMENTED
  | FEAT_EBEP_IMPLEMENTED
  | FEAT_D128_IMPLEMENTED
  | FEAT_CHK_IMPLEMENTED
  | FEAT_ABLE_IMPLEMENTED
  | FEAT_SME2_IMPLEMENTED
  | FEAT_MEC_IMPLEMENTED
  | FEAT_BRBEv1p1_IMPLEMENTED
  | FEAT_SME_I16I64_IMPLEMENTED
  | FEAT_SME_FA64_IMPLEMENTED
  | FEAT_SME_F64F64_IMPLEMENTED
  | FEAT_SME_IMPLEMENTED
  | FEAT_RME_IMPLEMENTED
  | FEAT_ETEv1p2_IMPLEMENTED
  | FEAT_BRBE_IMPLEMENTED
  | FEAT_ETEv1p1_IMPLEMENTED
  | FEAT_TRBE_IMPLEMENTED
  | FEAT_TME_IMPLEMENTED
  | FEAT_SVE_SM4_IMPLEMENTED
  | FEAT_SVE_SHA3_IMPLEMENTED
  | FEAT_SVE_PMULL128_IMPLEMENTED
  | FEAT_SVE_BitPerm_IMPLEMENTED
  | FEAT_SVE_AES_IMPLEMENTED
  | FEAT_SVE2_IMPLEMENTED
  | FEAT_ETE_IMPLEMENTED
  | FEAT_DoPD_IMPLEMENTED
  | FEAT_THE_IMPLEMENTED
  | FEAT_SPMU_IMPLEMENTED
  | FEAT_SPEv1p4_IMPLEMENTED
  | FEAT_SPE_FDS_IMPLEMENTED
  | FEAT_SPE_CRR_IMPLEMENTED
  | FEAT_SPECRES2_IMPLEMENTED
  | FEAT_S2POE_IMPLEMENTED
  | FEAT_S2PIE_IMPLEMENTED
  | FEAT_S1POE_IMPLEMENTED
  | FEAT_S1PIE_IMPLEMENTED
  | FEAT_RPRFM_IMPLEMENTED
  | FEAT_RASv2_IMPLEMENTED
  | FEAT_RASSAv2_IMPLEMENTED
  | FEAT_PRFMSLC_IMPLEMENTED
  | FEAT_PMUv3p9_IMPLEMENTED
  | FEAT_PMUv3_SS_IMPLEMENTED
  | FEAT_PMUv3_ICNTR_IMPLEMENTED
  | FEAT_PMUv3_EDGE_IMPLEMENTED
  | FEAT_PFAR_IMPLEMENTED
  | FEAT_PCSRv8p9_IMPLEMENTED
  | FEAT_MTE_TAGGED_FAR_IMPLEMENTED
  | FEAT_MTE_STORE_ONLY_IMPLEMENTED
  | FEAT_MTE_PERM_IMPLEMENTED
  | FEAT_MTE_NO_ADDRESS_TAGS_IMPLEMENTED
  | FEAT_MTE_CANONICAL_TAGS_IMPLEMENTED
  | FEAT_MTE_ASYNC_IMPLEMENTED
  | FEAT_MTE_ASYM_FAULT_IMPLEMENTED
  | FEAT_MTE4_IMPLEMENTED
  | FEAT_LRCPC3_IMPLEMENTED
  | FEAT_HAFT_IMPLEMENTED
  | FEAT_FGT2_IMPLEMENTED
  | FEAT_ECBHB_IMPLEMENTED
  | FEAT_DoubleFault2_IMPLEMENTED
  | FEAT_Debugv8p9_IMPLEMENTED
  | FEAT_CSSC_IMPLEMENTED
  | FEAT_CLRBHB_IMPLEMENTED
  | FEAT_ANERR_IMPLEMENTED
  | FEAT_AIE_IMPLEMENTED
  | FEAT_ADERR_IMPLEMENTED
  | FEAT_TIDCP1_IMPLEMENTED
  | FEAT_TCR2_IMPLEMENTED
  | FEAT_SPEv1p3_IMPLEMENTED
  | FEAT_SCTLR2_IMPLEMENTED
  | FEAT_PMUv3p8_IMPLEMENTED
  | FEAT_PMUv3_TH_IMPLEMENTED
  | FEAT_PMUv3_EXT64_IMPLEMENTED
  | FEAT_NMI_IMPLEMENTED
  | FEAT_MOPS_IMPLEMENTED
  | FEAT_HBC_IMPLEMENTED
  | FEAT_GICv3_NMI_IMPLEMENTED
  | FEAT_Debugv8p8_IMPLEMENTED
  | FEAT_CMOW_IMPLEMENTED
  | FEAT_XS_IMPLEMENTED
  | FEAT_WFxT_IMPLEMENTED
  | FEAT_SPEv1p2_IMPLEMENTED
  | FEAT_RPRES_IMPLEMENTED
  | FEAT_PMUv3p7_IMPLEMENTED
  | FEAT_PAN3_IMPLEMENTED
  | FEAT_MTE3_IMPLEMENTED
  | FEAT_LS64_V_IMPLEMENTED
  | FEAT_LS64_ACCDATA_IMPLEMENTED
  | FEAT_LS64_IMPLEMENTED
  | FEAT_LPA2_IMPLEMENTED
  | FEAT_HCX_IMPLEMENTED
  | FEAT_EBF16_IMPLEMENTED
  | FEAT_AFP_IMPLEMENTED
  | FEAT_TWED_IMPLEMENTED
  | FEAT_PAuth2_IMPLEMENTED
  | FEAT_MTPMU_IMPLEMENTED
  | FEAT_MPAMv1p1_IMPLEMENTED
  | FEAT_MPAMv0p1_IMPLEMENTED
  | FEAT_HPMN0_IMPLEMENTED
  | FEAT_FGT_IMPLEMENTED
  | FEAT_ECV_IMPLEMENTED
  | FEAT_DGH_IMPLEMENTED
  | FEAT_BF16_IMPLEMENTED
  | FEAT_AMUv1p1_IMPLEMENTED
  | FEAT_SSBS2_IMPLEMENTED
  | FEAT_SSBS_IMPLEMENTED
  | FEAT_SPECRES_IMPLEMENTED
  | FEAT_SB_IMPLEMENTED
  | FEAT_RNG_TRAP_IMPLEMENTED
  | FEAT_RNG_IMPLEMENTED
  | FEAT_PMUv3p5_IMPLEMENTED
  | FEAT_MTE2_IMPLEMENTED
  | FEAT_MTE_IMPLEMENTED
  | FEAT_GTG_IMPLEMENTED
  | FEAT_FlagM2_IMPLEMENTED
  | FEAT_FRINTTS_IMPLEMENTED
  | FEAT_ExS_IMPLEMENTED
  | FEAT_EVT_IMPLEMENTED
  | FEAT_E0PD_IMPLEMENTED
  | FEAT_DPB2_IMPLEMENTED
  | FEAT_CSV3_IMPLEMENTED
  | FEAT_CSV2_IMPLEMENTED
  | FEAT_BTI_IMPLEMENTED
  | FEAT_TTST_IMPLEMENTED
  | FEAT_TTL_IMPLEMENTED
  | FEAT_TRF_IMPLEMENTED
  | FEAT_TLBIRANGE_IMPLEMENTED
  | FEAT_TLBIOS_IMPLEMENTED
  | FEAT_SEL2_IMPLEMENTED
  | FEAT_S2FWB_IMPLEMENTED
  | FEAT_RASv1p1_IMPLEMENTED
  | FEAT_RASSAv1p1_IMPLEMENTED
  | FEAT_PMUv3p4_IMPLEMENTED
  | FEAT_NV2_IMPLEMENTED
  | FEAT_LSE2_IMPLEMENTED
  | FEAT_LRCPC2_IMPLEMENTED
  | FEAT_IDST_IMPLEMENTED
  | FEAT_FlagM_IMPLEMENTED
  | FEAT_FHM_IMPLEMENTED
  | FEAT_DoubleFault_IMPLEMENTED
  | FEAT_DotProd_IMPLEMENTED
  | FEAT_Debugv8p4_IMPLEMENTED
  | FEAT_DIT_IMPLEMENTED
  | FEAT_CNTSC_IMPLEMENTED
  | FEAT_BBM_IMPLEMENTED
  | FEAT_AMUv1_IMPLEMENTED
  | FEAT_SPEv1p1_IMPLEMENTED
  | FEAT_PAuth_IMPLEMENTED
  | FEAT_PACQARMA5_IMPLEMENTED
  | FEAT_PACQARMA3_IMPLEMENTED
  | FEAT_PACIMP_IMPLEMENTED
  | FEAT_NV_IMPLEMENTED
  | FEAT_LRCPC_IMPLEMENTED
  | FEAT_JSCVT_IMPLEMENTED
  | FEAT_FPACCOMBINE_IMPLEMENTED
  | FEAT_FPAC_IMPLEMENTED
  | FEAT_FCMA_IMPLEMENTED
  | FEAT_EPAC_IMPLEMENTED
  | FEAT_CONSTPACFIELD_IMPLEMENTED
  | FEAT_CCIDX_IMPLEMENTED
  | FEAT_XNX_IMPLEMENTED
  | FEAT_VPIPT_IMPLEMENTED
  | FEAT_UAO_IMPLEMENTED
  | FEAT_TTCNP_IMPLEMENTED
  | FEAT_SVE_IMPLEMENTED
  | FEAT_SPE_IMPLEMENTED
  | FEAT_SM4_IMPLEMENTED
  | FEAT_SM3_IMPLEMENTED
  | FEAT_SHA512_IMPLEMENTED
  | FEAT_SHA3_IMPLEMENTED
  | FEAT_RAS_IMPLEMENTED
  | FEAT_PCSRv8p2_IMPLEMENTED
  | FEAT_PAN2_IMPLEMENTED
  | FEAT_MPAM_IMPLEMENTED
  | FEAT_LVA_IMPLEMENTED
  | FEAT_LSMAOC_IMPLEMENTED
  | FEAT_LPA_IMPLEMENTED
  | FEAT_IESB_IMPLEMENTED
  | FEAT_I8MM_IMPLEMENTED
  | FEAT_HPDS2_IMPLEMENTED
  | FEAT_FP16_IMPLEMENTED
  | FEAT_F64MM_IMPLEMENTED
  | FEAT_F32MM_IMPLEMENTED
  | FEAT_EDHSR_IMPLEMENTED
  | FEAT_Debugv8p2_IMPLEMENTED
  | FEAT_DPB_IMPLEMENTED
  | FEAT_ASMv8p2_IMPLEMENTED
  | FEAT_AA32I8MM_IMPLEMENTED
  | FEAT_AA32HPD_IMPLEMENTED
  | FEAT_AA32BF16_IMPLEMENTED
  | FEAT_VMID16_IMPLEMENTED
  | FEAT_VHE_IMPLEMENTED
  | FEAT_RDM_IMPLEMENTED
  | FEAT_PMUv3p1_IMPLEMENTED
  | FEAT_PAN_IMPLEMENTED
  | FEAT_LSE_IMPLEMENTED
  | FEAT_LOR_IMPLEMENTED
  | FEAT_HPDS_IMPLEMENTED
  | FEAT_HAFDBS_IMPLEMENTED
  | FEAT_Debugv8p1_IMPLEMENTED
  | FEAT_CRC32_IMPLEMENTED
  | FEAT_nTLBPA_IMPLEMENTED
  | FEAT_TRC_SR_IMPLEMENTED
  | FEAT_TRC_EXT_IMPLEMENTED
  | FEAT_SHA256_IMPLEMENTED
  | FEAT_SHA1_IMPLEMENTED
  | FEAT_PMUv3_EXT32_IMPLEMENTED
  | FEAT_PMUv3_EXT_IMPLEMENTED
  | FEAT_PMUv3_IMPLEMENTED
  | FEAT_PMULL_IMPLEMENTED
  | FEAT_PCSRv8_IMPLEMENTED
  | FEAT_IVIPT_IMPLEMENTED
  | FEAT_GICv4p1_IMPLEMENTED
  | FEAT_GICv4_IMPLEMENTED
  | FEAT_GICv3p1_IMPLEMENTED
  | FEAT_GICv3_TDIR_IMPLEMENTED
  | FEAT_GICv3_LEGACY_IMPLEMENTED
  | FEAT_GICv3_IMPLEMENTED
  | FEAT_FP_IMPLEMENTED
  | FEAT_ETS2_IMPLEMENTED
  | FEAT_ETMv4p6_IMPLEMENTED
  | FEAT_ETMv4p5_IMPLEMENTED
  | FEAT_ETMv4p4_IMPLEMENTED
  | FEAT_ETMv4p3_IMPLEMENTED
  | FEAT_ETMv4p2_IMPLEMENTED
  | FEAT_ETMv4p1_IMPLEMENTED
  | FEAT_ETMv4_IMPLEMENTED
  | FEAT_DoubleLock_IMPLEMENTED
  | FEAT_CSV2_3_IMPLEMENTED
  | FEAT_CSV2_2_IMPLEMENTED
  | FEAT_CSV2_1p2_IMPLEMENTED
  | FEAT_CSV2_1p1_IMPLEMENTED
  | FEAT_AdvSIMD_IMPLEMENTED
  | FEAT_AES_IMPLEMENTED
  | FEAT_EL3_IMPLEMENTED
  | FEAT_EL2_IMPLEMENTED
  | FEAT_EL1_IMPLEMENTED
  | FEAT_EL0_IMPLEMENTED
  | FEAT_AA64EL3_IMPLEMENTED
  | FEAT_AA64EL2_IMPLEMENTED
  | FEAT_AA64EL1_IMPLEMENTED
  | FEAT_AA64EL0_IMPLEMENTED
  | FEAT_AA32EL3_IMPLEMENTED
  | FEAT_AA32EL2_IMPLEMENTED
  | FEAT_AA32EL1_IMPLEMENTED
  | FEAT_AA32EL0_IMPLEMENTED
  | SEE
  deriving DecidableEq, Hashable
open Register

abbrev RegisterType : Register → Type
  | .__emulator_termination_opcode => (Option (BitVec 32))
  | ._HACTLR2 => (BitVec 32)
  | ._ERXSTATUS => (BitVec 32)
  | ._ERXMISC3 => (BitVec 32)
  | ._ERXMISC7 => (BitVec 32)
  | ._ERXADDR2 => (BitVec 32)
  | ._ERXMISC4 => (BitVec 32)
  | ._ERXMISC6 => (BitVec 32)
  | ._ERXCTLR => (BitVec 32)
  | ._ERXMISC1 => (BitVec 32)
  | ._ERXCTLR2 => (BitVec 32)
  | ._ERXMISC5 => (BitVec 32)
  | ._ERXMISC0 => (BitVec 32)
  | ._ERXADDR => (BitVec 32)
  | ._ERXFR => (BitVec 32)
  | ._ERXMISC2 => (BitVec 32)
  | ._ERXFR2 => (BitVec 32)
  | ._AMEVTYPER1 => (Vector (BitVec 32) 16)
  | ._AMEVTYPER0 => (Vector (BitVec 32) 4)
  | ._ICH_LRC => (Vector (BitVec 32) 16)
  | ._AMAIR1_NS => (BitVec 32)
  | .AMAIR1_S => (BitVec 32)
  | ._DBGDTRTXint => (BitVec 32)
  | ._HTPIDR => (BitVec 32)
  | ._DBGDTRRXint => (BitVec 32)
  | ._TPIDRPRW_NS => (BitVec 32)
  | .TPIDRPRW_S => (BitVec 32)
  | ._ICC_AP0R => (Vector (BitVec 32) 4)
  | ._HAIFSR => (BitVec 32)
  | ._HAMAIR1 => (BitVec 32)
  | ._ACTLR2_NS => (BitVec 32)
  | .ACTLR2_S => (BitVec 32)
  | ._DBGOSECCR => (BitVec 32)
  | ._PMINTENSET => (BitVec 32)
  | ._CNTFRQ => (BitVec 32)
  | ._HADFSR => (BitVec 32)
  | ._ICH_LR => (Vector (BitVec 32) 16)
  | ._AIDR => (BitVec 32)
  | ._ICH_AP0R => (Vector (BitVec 32) 4)
  | ._HAMAIR0 => (BitVec 32)
  | ._AMAIR0_NS => (BitVec 32)
  | .AMAIR0_S => (BitVec 32)
  | ._ICH_AP1R => (Vector (BitVec 32) 4)
  | ._ICC_AP1R_NS => (Vector (BitVec 32) 4)
  | ._ICC_AP1R_S => (Vector (BitVec 32) 4)
  | ._DBGDTRRXext => (BitVec 32)
  | .DBGOSLAR => (BitVec 32)
  | ._ACTLR_NS => (BitVec 32)
  | .ACTLR_S => (BitVec 32)
  | ._DBGDTRTXext => (BitVec 32)
  | ._TPIDRURO_NS => (BitVec 32)
  | .TPIDRURO_S => (BitVec 32)
  | ._REVIDR => (BitVec 32)
  | ._ADFSR_NS => (BitVec 32)
  | .ADFSR_S => (BitVec 32)
  | ._ICV_AP1R => (Vector (BitVec 32) 4)
  | ._TPIDRURW_NS => (BitVec 32)
  | .TPIDRURW_S => (BitVec 32)
  | ._ICV_AP0R => (Vector (BitVec 32) 4)
  | .TCMTR => (BitVec 32)
  | ._HACTLR => (BitVec 32)
  | ._HACR => (BitVec 32)
  | ._AIFSR_NS => (BitVec 32)
  | .AIFSR_S => (BitVec 32)
  | .BRBSRC_EL1 => (Vector (BitVec 64) 32)
  | .BRBTGT_EL1 => (Vector (BitVec 64) 32)
  | .BRBINF_EL1 => (Vector (BitVec 64) 32)
  | .ERXPFGCTL_EL1 => (BitVec 64)
  | .ERXMISC2_EL1 => (BitVec 64)
  | .ERXMISC3_EL1 => (BitVec 64)
  | .ERXGSR_EL1 => (BitVec 64)
  | .ERXFR_EL1 => (BitVec 64)
  | .ERXSTATUS_EL1 => (BitVec 64)
  | .ERXCTLR_EL1 => (BitVec 64)
  | .ERXMISC1_EL1 => (BitVec 64)
  | .ERXPFGF_EL1 => (BitVec 64)
  | .ERXPFGCDN_EL1 => (BitVec 64)
  | .ERXMISC0_EL1 => (BitVec 64)
  | .ERXADDR_EL1 => (BitVec 64)
  | .AMEVTYPER1_EL0 => (Vector (BitVec 64) 16)
  | .AMEVCNTVOFF1_EL2 => (Vector (BitVec 64) 16)
  | ._AMEVCNTR0_EL0 => (Vector (BitVec 64) 4)
  | ._AMEVCNTR1 => (Vector (BitVec 64) 16)
  | .AMEVCNTR0 => (Vector (BitVec 64) 4)
  | .AMEVCNTVOFF0_EL2 => (Vector (BitVec 64) 16)
  | .AMEVCNTR1_EL0 => (Vector (BitVec 64) 16)
  | ._CNTV_CVAL => (BitVec 64)
  | ._CNTVOFF => (BitVec 64)
  | .SPMACCESSR_EL3 => (BitVec 64)
  | .AMAIR2_EL1 => (BitVec 64)
  | .AFSR0_EL2 => (BitVec 64)
  | .ICV_AP1R_EL1 => (Vector (BitVec 64) 4)
  | .AFSR1_EL3 => (BitVec 64)
  | .AMAIR2_EL3 => (BitVec 64)
  | .HACR_EL2 => (BitVec 64)
  | .RNDR => (BitVec 64)
  | .SMPRIMAP_EL2 => (BitVec 64)
  | .RNDRRS => (BitVec 64)
  | .TPIDR_EL0 => (BitVec 64)
  | .SCXTNUM_EL3 => (BitVec 64)
  | .TPIDR2_EL0 => (BitVec 64)
  | .SCXTNUM_EL0 => (BitVec 64)
  | .AMAIR_EL1 => (BitVec 64)
  | .TPIDRRO_EL0 => (BitVec 64)
  | .SCXTNUM_EL1 => (BitVec 64)
  | .AMAIR_EL3 => (BitVec 64)
  | .AMAIR_EL2 => (BitVec 64)
  | .ACTLR_EL3 => (BitVec 64)
  | .TPIDR_EL3 => (BitVec 64)
  | .PMIAR_EL1 => (BitVec 64)
  | .SCXTNUM_EL2 => (BitVec 64)
  | .PMICNTSVR_EL1 => (BitVec 64)
  | .SPMACCESSR_EL2 => (BitVec 64)
  | .AFSR0_EL1 => (BitVec 64)
  | .AFSR1_EL2 => (BitVec 64)
  | .AFSR0_EL3 => (BitVec 64)
  | .ICV_AP0R_EL1 => (Vector (BitVec 64) 4)
  | .AMAIR2_EL2 => (BitVec 64)
  | .PMCCNTSVR_EL1 => (BitVec 64)
  | .AFSR1_EL1 => (BitVec 64)
  | .ICC_AP1R_EL1_NS => (Vector (BitVec 64) 4)
  | .ICC_AP1R_EL1_S => (Vector (BitVec 64) 4)
  | .ACTLR_EL1 => (BitVec 64)
  | .TPIDR_EL1 => (BitVec 64)
  | .ICH_AP0R_EL2 => (Vector (BitVec 64) 4)
  | .PMEVCNTSVR_EL1 => (Vector (BitVec 64) 31)
  | .ICH_AP1R_EL2 => (Vector (BitVec 64) 4)
  | .SPMACCESSR_EL1 => (BitVec 64)
  | .ACTLR_EL2 => (BitVec 64)
  | .TPIDR_EL2 => (BitVec 64)
  | .REVIDR_EL1 => (BitVec 64)
  | .AIDR_EL1 => (BitVec 64)
  | .ICC_AP0R_EL1 => (Vector (BitVec 64) 4)
  | .ICH_LR_EL2 => (Vector (BitVec 64) 16)
  | ._PMCCNTR => (BitVec 64)
  | ._PMOVSSET => (BitVec 32)
  | ._PMEVCNTR => (Vector (BitVec 32) 31)
  | ._DBGWVR => (Vector (BitVec 32) 16)
  | ._DBGWCR => (Vector (BitVec 32) 16)
  | ._DBGBXVR => (Vector (BitVec 32) 16)
  | ._DBGBVR => (Vector (BitVec 32) 16)
  | ._DBGBCR => (Vector (BitVec 32) 16)
  | .STACK_LIMIT => (BitVec 64)
  | .STACK_BASE => (BitVec 64)
  | .HEAP_LIMIT => (BitVec 64)
  | .HEAP_BASE => (BitVec 64)
  | .__has_spe_pseudo_cycles => Bool
  | .SMCR_EL3_LEN_VALUE => Int
  | .CPTR_EL3_ESM_VALUE => Int
  | .CPTR_EL3_EZ_VALUE => Int
  | .ZCR_EL3_LEN_VALUE => Int
  | .CFG_RMR_AA64 => (BitVec 1)
  | .__DBG_ROM_ADDR => (BitVec 56)
  | .__mops_forward_copy => Bool
  | .__trickbox_enabled => Bool
  | .__ignore_rvbar_in_aarch32 => Bool
  | .__unpred_tsize_aborts => Bool
  | .__syncAbortOnDeviceWrite => Bool
  | .__syncAbortOnWriteNormNonCache => Bool
  | .__syncAbortOnWriteNormCache => Bool
  | .__syncAbortOnTTWNonCache => Bool
  | .__syncAbortOnTTWCache => Bool
  | .__syncAbortOnPrefetch => Bool
  | .__syncAbortOnSoWrite => Bool
  | .__syncAbortOnSoRead => Bool
  | .__syncAbortOnDeviceRead => Bool
  | .__syncAbortOnReadNormNonCache => Bool
  | .__syncAbortOnReadNormCache => Bool
  | .__PMUBase => (BitVec 56)
  | .__GICITSControlBase => (BitVec 56)
  | .__GICDistBase => (BitVec 56)
  | .__GICCPUInterfaceBase => (BitVec 56)
  | .__ExtDebugBase => (BitVec 56)
  | .__CNTControlBase => (BitVec 56)
  | .__CTIBase => (BitVec 56)
  | ._DBGDTR_EL0 => (BitVec 64)
  | .DACR_S => (BitVec 32)
  | ._DACR_NS => (BitVec 32)
  | ._HMAIR1 => (BitVec 32)
  | ._HMAIR0 => (BitVec 32)
  | ._MAIR1_S => (BitVec 32)
  | ._MAIR1_NS => (BitVec 32)
  | ._MAIR0_S => (BitVec 32)
  | ._MAIR0_NS => (BitVec 32)
  | .BRBTGTINJ_EL1 => (BitVec 64)
  | .BRBSRCINJ_EL1 => (BitVec 64)
  | .SPESampleCounter => (Vector Int 32)
  | .SPERecordData => (Vector (BitVec 8) 64)
  | .PMSDSFR_EL1 => (BitVec 64)
  | .PMBPTR_EL1 => (BitVec 64)
  | .PMCCNTR_EL0 => (BitVec 64)
  | .PMEVCNTR_EL0 => (Vector (BitVec 64) 32)
  | .__g1_activity_monitor_offset_implemented => (BitVec 16)
  | .__g1_activity_monitor_implemented => (BitVec 16)
  | .__supported_va_size => Int
  | .__rme_l0gptsz => (BitVec 4)
  | .__mpam_has_altsp => Bool
  | .__mecid_width => (BitVec 4)
  | .__gmid_log2_block_size => Int
  | .__dczid_log2_block_size => Int
  | .__CNTbase_frequency => (BitVec 32)
  | .ID_AA64PFR0_EL1 => (BitVec 64)
  | .ID_AA64MMFR1_EL1 => (BitVec 64)
  | .ID_AA64ISAR1_EL1 => (BitVec 64)
  | .ID_AA64DFR1_EL1 => (BitVec 64)
  | .ID_AA64DFR0_EL1 => (BitVec 64)
  | .GICD_TYPER => (BitVec 32)
  | .EDDEVARCH => (BitVec 32)
  | .CTIDEVARCH => (BitVec 32)
  | .CNTFID0 => (BitVec 32)
  | .CFG_MPIDR => (BitVec 32)
  | .AMIIDR => (BitVec 32)
  | .AMEVTYPER0_EL0 => (Vector (BitVec 64) 4)
  | .AMDEVARCH => (BitVec 32)
  | ._PAR_EL1 => (BitVec 128)
  | .SPMSELR_EL0 => (BitVec 64)
  | .SMPRI_EL1 => (BitVec 64)
  | .SMIDR_EL1 => (BitVec 64)
  | .PMZR_EL0 => (BitVec 64)
  | .PMXEVCNTR_EL0 => (BitVec 64)
  | .PMUACR_EL1 => (BitVec 64)
  | .PMSSCR_EL1 => (BitVec 64)
  | .PMSNEVFR_EL1 => (BitVec 64)
  | .PMSLATFR_EL1 => (BitVec 64)
  | .PMSIRR_EL1 => (BitVec 64)
  | .PMSICR_EL1 => (BitVec 64)
  | .PMSFCR_EL1 => (BitVec 64)
  | .PMSEVFR_EL1 => (BitVec 64)
  | .PMMIR_EL1 => (BitVec 64)
  | .PMECR_EL1 => (BitVec 64)
  | .PMBIDR_EL1 => (BitVec 64)
  | .OSLAR_EL1 => (BitVec 64)
  | .OSDTRTX_EL1 => (BitVec 64)
  | .OSDTRRX_EL1 => (BitVec 64)
  | .MECIDR_EL2 => (BitVec 64)
  | .MDSELR_EL1 => (BitVec 64)
  | .LORSA_EL1 => (BitVec 64)
  | .LORN_EL1 => (BitVec 64)
  | .LORID_EL1 => (BitVec 64)
  | .LOREA_EL1 => (BitVec 64)
  | .LORC_EL1 => (BitVec 64)
  | .ID_AA64ZFR0_EL1 => (BitVec 64)
  | .ID_AA64SMFR0_EL1 => (BitVec 64)
  | .ID_AA64PFR2_EL1 => (BitVec 64)
  | .ID_AA64PFR1_EL1 => (BitVec 64)
  | .ID_AA64MMFR4_EL1 => (BitVec 64)
  | .ID_AA64MMFR3_EL1 => (BitVec 64)
  | .ID_AA64MMFR2_EL1 => (BitVec 64)
  | .ID_AA64MMFR0_EL1 => (BitVec 64)
  | .ID_AA64ISAR2_EL1 => (BitVec 64)
  | .ID_AA64ISAR0_EL1 => (BitVec 64)
  | .ID_AA64AFR1_EL1 => (BitVec 64)
  | .ID_AA64AFR0_EL1 => (BitVec 64)
  | .ICV_NMIAR1_EL1 => (BitVec 64)
  | .ICC_SRE_EL3 => (BitVec 64)
  | .ICC_NMIAR1_EL1 => (BitVec 64)
  | .ICC_IGRPEN1_EL3 => (BitVec 64)
  | .ICC_CTLR_EL3 => (BitVec 64)
  | .HFGWTR_EL2 => (BitVec 64)
  | .HFGWTR2_EL2 => (BitVec 64)
  | .HFGRTR_EL2 => (BitVec 64)
  | .HFGRTR2_EL2 => (BitVec 64)
  | .HFGITR2_EL2 => (BitVec 64)
  | .HDFGWTR_EL2 => (BitVec 64)
  | .HDFGWTR2_EL2 => (BitVec 64)
  | .HDFGRTR_EL2 => (BitVec 64)
  | .HDFGRTR2_EL2 => (BitVec 64)
  | .HAFGRTR_EL2 => (BitVec 64)
  | .GMID_EL1 => (BitVec 64)
  | .DCZID_EL0 => (BitVec 64)
  | .DBGDTRTX_EL0 => (BitVec 64)
  | .DBGDTRRX_EL0 => (BitVec 64)
  | .DACR32_EL2 => (BitVec 64)
  | .CNTV_TVAL_EL0 => (BitVec 64)
  | .CNTP_TVAL_EL0 => (BitVec 64)
  | .CNTPS_TVAL_EL1 => (BitVec 64)
  | .CNTHV_TVAL_EL2 => (BitVec 64)
  | .CNTHVS_TVAL_EL2 => (BitVec 64)
  | .CNTHP_TVAL_EL2 => (BitVec 64)
  | .CNTHPS_TVAL_EL2 => (BitVec 64)
  | .CNTFRQ_EL0 => (BitVec 64)
  | .BRBINFINJ_EL1 => (BitVec 64)
  | .AMCG1IDR_EL0 => (BitVec 64)
  | .ACCDATA_EL1 => (BitVec 64)
  | ._PMCEID3 => (BitVec 32)
  | ._PMCEID2 => (BitVec 32)
  | ._PMCEID1 => (BitVec 32)
  | .PMCEID1_EL0 => (BitVec 64)
  | ._PMCEID0 => (BitVec 32)
  | .PMCEID0_EL0 => (BitVec 64)
  | ._NMRR_NS => (BitVec 32)
  | .NMRR_S => (BitVec 32)
  | ._MVFR1 => (BitVec 32)
  | .MVFR1_EL1 => (BitVec 64)
  | ._MVFR0 => (BitVec 32)
  | .MVFR0_EL1 => (BitVec 64)
  | ._MIDR => (BitVec 32)
  | .MIDR_EL1 => (BitVec 64)
  | ._ID_PFR1 => (BitVec 32)
  | .ID_PFR1_EL1 => (BitVec 64)
  | ._ID_PFR0 => (BitVec 32)
  | .ID_PFR0_EL1 => (BitVec 64)
  | ._ID_MMFR4 => (BitVec 32)
  | .ID_MMFR4_EL1 => (BitVec 64)
  | ._ID_MMFR3 => (BitVec 32)
  | .ID_MMFR3_EL1 => (BitVec 64)
  | ._ID_MMFR2 => (BitVec 32)
  | .ID_MMFR2_EL1 => (BitVec 64)
  | ._ID_MMFR1 => (BitVec 32)
  | .ID_MMFR1_EL1 => (BitVec 64)
  | ._ID_MMFR0 => (BitVec 32)
  | .ID_MMFR0_EL1 => (BitVec 64)
  | ._ID_ISAR6 => (BitVec 32)
  | .ID_ISAR6_EL1 => (BitVec 64)
  | ._ID_ISAR4 => (BitVec 32)
  | .ID_ISAR4_EL1 => (BitVec 64)
  | ._ID_ISAR3 => (BitVec 32)
  | .ID_ISAR3_EL1 => (BitVec 64)
  | ._ID_ISAR2 => (BitVec 32)
  | .ID_ISAR2_EL1 => (BitVec 64)
  | ._ID_ISAR1 => (BitVec 32)
  | .ID_ISAR1_EL1 => (BitVec 64)
  | ._ID_DFR0 => (BitVec 32)
  | ._CLIDR => (BitVec 32)
  | .__num_ctx_breakpoints => Int
  | .__exclusive_granule_size => (BitVec 4)
  | .TLBTR => (BitVec 32)
  | .ID_DFR0_EL1 => (BitVec 64)
  | .FPSID => (BitVec 32)
  | .DBGDEVID => (BitVec 32)
  | ._VTCR => (BitVec 32)
  | ._VPIDR => (BitVec 32)
  | .VPIDR_EL2 => (BitVec 64)
  | ._VMPIDR => (BitVec 32)
  | .VMPIDR_EL2 => (BitVec 64)
  | ._TTBCR2_NS => (BitVec 32)
  | .TTBCR2_S => (BitVec 32)
  | ._TRFCR => (BitVec 32)
  | .TRFCR_EL1 => (BitVec 64)
  | ._RMR => (BitVec 32)
  | .RMR_EL3 => (BitVec 64)
  | .RMR_EL1 => (BitVec 64)
  | ._PRRR_NS => (BitVec 32)
  | .PRRR_S => (BitVec 32)
  | ._PMUSERENR => (BitVec 32)
  | .PMUSERENR_EL0 => (BitVec 64)
  | ._PMSWINC => (BitVec 32)
  | .PMSWINC_EL0 => (BitVec 64)
  | ._PMSELR => (BitVec 32)
  | .PMSELR_EL0 => (BitVec 64)
  | ._PMOVS => (BitVec 64)
  | ._PMINTEN => (BitVec 64)
  | .PMINTENSET_EL1 => (BitVec 64)
  | ._PMCNTEN => (BitVec 64)
  | .PAR_S => (BitVec 64)
  | .PAR_NS => (BitVec 64)
  | ._MVFR2 => (BitVec 32)
  | .MVFR2_EL1 => (BitVec 64)
  | ._MPIDR => (BitVec 32)
  | .MPIDR_EL1 => (BitVec 64)
  | ._ISR => (BitVec 32)
  | .ISR_EL1 => (BitVec 64)
  | ._ID_PFR2 => (BitVec 32)
  | .ID_PFR2_EL1 => (BitVec 64)
  | ._ID_MMFR5 => (BitVec 32)
  | .ID_MMFR5_EL1 => (BitVec 64)
  | ._ID_ISAR5 => (BitVec 32)
  | .ID_ISAR5_EL1 => (BitVec 64)
  | ._ID_ISAR0 => (BitVec 32)
  | .ID_ISAR0_EL1 => (BitVec 64)
  | ._ID_DFR1 => (BitVec 32)
  | .ID_DFR1_EL1 => (BitVec 64)
  | ._ID_AFR0 => (BitVec 32)
  | .ID_AFR0_EL1 => (BitVec 64)
  | ._ICV_RPR => (BitVec 32)
  | .ICV_RPR_EL1 => (BitVec 64)
  | ._ICV_PMR => (BitVec 32)
  | .ICV_PMR_EL1 => (BitVec 64)
  | ._ICV_IGRPEN1 => (BitVec 32)
  | .ICV_IGRPEN1_EL1 => (BitVec 64)
  | ._ICV_IGRPEN0 => (BitVec 32)
  | .ICV_IGRPEN0_EL1 => (BitVec 64)
  | ._ICV_IAR1 => (BitVec 32)
  | .ICV_IAR1_EL1 => (BitVec 64)
  | ._ICV_IAR0 => (BitVec 32)
  | .ICV_IAR0_EL1 => (BitVec 64)
  | ._ICV_HPPIR1 => (BitVec 32)
  | .ICV_HPPIR1_EL1 => (BitVec 64)
  | ._ICV_HPPIR0 => (BitVec 32)
  | .ICV_HPPIR0_EL1 => (BitVec 64)
  | ._ICV_EOIR1 => (BitVec 32)
  | .ICV_EOIR1_EL1 => (BitVec 64)
  | ._ICV_EOIR0 => (BitVec 32)
  | .ICV_EOIR0_EL1 => (BitVec 64)
  | ._ICV_DIR => (BitVec 32)
  | .ICV_DIR_EL1 => (BitVec 64)
  | ._ICV_CTLR => (BitVec 32)
  | .ICV_CTLR_EL1 => (BitVec 64)
  | ._ICV_BPR1 => (BitVec 32)
  | .ICV_BPR1_EL1 => (BitVec 64)
  | ._ICV_BPR0 => (BitVec 32)
  | .ICV_BPR0_EL1 => (BitVec 64)
  | ._ICH_VTR => (BitVec 32)
  | .ICH_VTR_EL2 => (BitVec 64)
  | ._ICH_VMCR => (BitVec 32)
  | .ICH_VMCR_EL2 => (BitVec 64)
  | ._ICH_MISR => (BitVec 32)
  | .ICH_MISR_EL2 => (BitVec 64)
  | ._ICH_HCR => (BitVec 32)
  | .ICH_HCR_EL2 => (BitVec 64)
  | ._ICH_ELRSR => (BitVec 32)
  | .ICH_ELRSR_EL2 => (BitVec 64)
  | ._ICH_EISR => (BitVec 32)
  | .ICH_EISR_EL2 => (BitVec 64)
  | ._ICC_SRE_S => (BitVec 32)
  | .ICC_SRE_EL1_S => (BitVec 64)
  | ._ICC_SRE_NS => (BitVec 32)
  | .ICC_SRE_EL1_NS => (BitVec 64)
  | ._ICC_SGI1R => (BitVec 64)
  | .ICC_SGI1R_EL1 => (BitVec 64)
  | ._ICC_SGI0R => (BitVec 64)
  | .ICC_SGI0R_EL1 => (BitVec 64)
  | ._ICC_RPR => (BitVec 32)
  | .ICC_RPR_EL1 => (BitVec 64)
  | ._ICC_PMR => (BitVec 32)
  | ._ICC_IGRPEN1_S => (BitVec 32)
  | .ICC_IGRPEN1_EL1_S => (BitVec 64)
  | ._ICC_IGRPEN1_NS => (BitVec 32)
  | .ICC_IGRPEN1_EL1_NS => (BitVec 64)
  | ._ICC_IGRPEN0 => (BitVec 32)
  | .ICC_IGRPEN0_EL1 => (BitVec 64)
  | ._ICC_IAR1 => (BitVec 32)
  | .ICC_IAR1_EL1 => (BitVec 64)
  | ._ICC_IAR0 => (BitVec 32)
  | .ICC_IAR0_EL1 => (BitVec 64)
  | ._ICC_HSRE => (BitVec 32)
  | .ICC_SRE_EL2 => (BitVec 64)
  | ._ICC_HPPIR1 => (BitVec 32)
  | .ICC_HPPIR1_EL1 => (BitVec 64)
  | ._ICC_HPPIR0 => (BitVec 32)
  | .ICC_HPPIR0_EL1 => (BitVec 64)
  | ._ICC_EOIR1 => (BitVec 32)
  | .ICC_EOIR1_EL1 => (BitVec 64)
  | ._ICC_EOIR0 => (BitVec 32)
  | .ICC_EOIR0_EL1 => (BitVec 64)
  | ._ICC_DIR => (BitVec 32)
  | .ICC_DIR_EL1 => (BitVec 64)
  | ._ICC_CTLR_S => (BitVec 32)
  | .ICC_CTLR_EL1_S => (BitVec 64)
  | ._ICC_CTLR_NS => (BitVec 32)
  | .ICC_CTLR_EL1_NS => (BitVec 64)
  | ._ICC_BPR1_S => (BitVec 32)
  | .ICC_BPR1_EL1_S => (BitVec 64)
  | ._ICC_BPR1_NS => (BitVec 32)
  | .ICC_BPR1_EL1_NS => (BitVec 64)
  | ._ICC_BPR0 => (BitVec 32)
  | .ICC_BPR0_EL1 => (BitVec 64)
  | ._ICC_ASGI1R => (BitVec 64)
  | .ICC_ASGI1R_EL1 => (BitVec 64)
  | ._HTRFCR => (BitVec 32)
  | .TRFCR_EL2 => (BitVec 64)
  | ._HTCR => (BitVec 32)
  | ._HSTR => (BitVec 32)
  | .HSTR_EL2 => (BitVec 64)
  | ._HRMR => (BitVec 32)
  | .RMR_EL2 => (BitVec 64)
  | ._ERRSELR => (BitVec 32)
  | .ERRSELR_EL1 => (BitVec 64)
  | ._ERRIDR => (BitVec 32)
  | .ERRIDR_EL1 => (BitVec 64)
  | ._DBGVCR => (BitVec 32)
  | .DBGVCR32_EL2 => (BitVec 64)
  | ._DBGDRAR => (BitVec 64)
  | .MDRAR_EL1 => (BitVec 64)
  | ._DBGDCCINT => (BitVec 32)
  | .MDCCINT_EL1 => (BitVec 64)
  | ._DBGCLAIMSET => (BitVec 32)
  | .DBGCLAIMSET_EL1 => (BitVec 64)
  | ._DBGCLAIMCLR => (BitVec 32)
  | .DBGCLAIMCLR_EL1 => (BitVec 64)
  | ._DBGAUTHSTATUS => (BitVec 32)
  | .DBGAUTHSTATUS_EL1 => (BitVec 64)
  | ._CTR => (BitVec 32)
  | ._CSSELR_NS => (BitVec 32)
  | .CSSELR_EL1 => (BitVec 64)
  | .CSSELR_S => (BitVec 32)
  | ._CNTV_CTL => (BitVec 32)
  | ._CNTHV_CTL => (BitVec 32)
  | ._CNTHVS_CTL => (BitVec 32)
  | ._CNTHPS_CTL => (BitVec 32)
  | ._CNTHCTL => (BitVec 32)
  | ._CCSIDR => (BitVec 32)
  | .CCSIDR_EL1 => (BitVec 64)
  | ._CCSIDR2 => (BitVec 32)
  | .CCSIDR2_EL1 => (BitVec 64)
  | ._AMUSERENR => (BitVec 32)
  | .AMUSERENR_EL0 => (BitVec 64)
  | ._AMCR => (BitVec 32)
  | .AMCR_EL0 => (BitVec 64)
  | ._AMCNTENSET1 => (BitVec 32)
  | .AMCNTENSET1_EL0 => (BitVec 64)
  | ._AMCNTENSET0 => (BitVec 32)
  | .AMCNTENSET0_EL0 => (BitVec 64)
  | ._AMCNTENCLR1 => (BitVec 32)
  | .AMCNTENCLR1_EL0 => (BitVec 64)
  | ._AMCNTENCLR0 => (BitVec 32)
  | .AMCNTENCLR0_EL0 => (BitVec 64)
  | ._AMCGCR => (BitVec 32)
  | .AMCGCR_EL0 => (BitVec 64)
  | ._AMCFGR => (BitVec 32)
  | .AMCFGR_EL0 => (BitVec 64)
  | .PMVIDSR => (BitVec 32)
  | .PMVCIDSR => (BitVec 64)
  | .PMPIDR4 => (BitVec 32)
  | .PMPIDR3 => (BitVec 32)
  | .PMPIDR2 => (BitVec 32)
  | .PMPIDR1 => (BitVec 32)
  | .PMPIDR0 => (BitVec 32)
  | .PMPCSR => (BitVec 64)
  | .PMPCSCTL => (BitVec 64)
  | .PMMIR => (BitVec 32)
  | .PMLSR => (BitVec 32)
  | .PMLAR => (BitVec 32)
  | .PMITCTRL => (BitVec 32)
  | .PMIIDR => (BitVec 64)
  | .PMDEVTYPE => (BitVec 32)
  | .PMDEVID => (BitVec 32)
  | .PMCIDR3 => (BitVec 32)
  | .PMCIDR2 => (BitVec 32)
  | .PMCIDR1 => (BitVec 32)
  | .PMCIDR0 => (BitVec 32)
  | .PMCGCR0 => (BitVec 32)
  | .PMCFGR => (BitVec 64)
  | .PMAUTHSTATUS => (BitVec 32)
  | .JOSCR => (BitVec 32)
  | .JMCR => (BitVec 32)
  | .JIDR => (BitVec 32)
  | .ICC_MSRE => (BitVec 32)
  | .ICC_MGRPEN1 => (BitVec 32)
  | .ICC_MCTLR => (BitVec 32)
  | .GITS_TYPER => (BitVec 64)
  | .GITS_STATUSR => (BitVec 32)
  | .GITS_SGIR => (BitVec 64)
  | .GITS_PARTIDR => (BitVec 32)
  | .GITS_MPIDR => (BitVec 32)
  | .GITS_MPAMIDR => (BitVec 32)
  | .GITS_IIDR => (BitVec 32)
  | .GITS_CWRITER => (BitVec 64)
  | .GITS_CTLR => (BitVec 32)
  | .GITS_CREADR => (BitVec 64)
  | .GITS_CBASER => (BitVec 64)
  | .GICV_STATUSR => (BitVec 32)
  | .GICV_RPR => (BitVec 32)
  | .GICV_PMR => (BitVec 32)
  | .GICV_IAR => (BitVec 32)
  | .GICV_HPPIR => (BitVec 32)
  | .GICV_EOIR => (BitVec 32)
  | .GICV_DIR => (BitVec 32)
  | .GICV_CTLR => (BitVec 32)
  | .GICV_BPR => (BitVec 32)
  | .GICV_AIAR => (BitVec 32)
  | .GICV_AHPPIR => (BitVec 32)
  | .GICV_AEOIR => (BitVec 32)
  | .GICV_ABPR => (BitVec 32)
  | .GICR_WAKER => (BitVec 32)
  | .GICR_VSGIR => (BitVec 32)
  | .GICR_VSGIPENDR => (BitVec 32)
  | .GICR_VPROPBASER => (BitVec 64)
  | .GICR_VPENDBASER => (BitVec 64)
  | .GICR_SYNCR => (BitVec 32)
  | .GICR_STATUSR => (BitVec 32)
  | .GICR_SETLPIR => (BitVec 64)
  | .GICR_PROPBASER => (BitVec 64)
  | .GICR_PENDBASER => (BitVec 64)
  | .GICR_PARTIDR => (BitVec 32)
  | .GICR_MPAMIDR => (BitVec 32)
  | .GICR_ISENABLER0 => (BitVec 32)
  | .GICR_INVLPIR => (BitVec 64)
  | .GICR_INVALLR => (BitVec 64)
  | .GICR_INMIR0 => (BitVec 32)
  | .GICR_IIDR => (BitVec 32)
  | .GICR_CTLR => (BitVec 32)
  | .GICR_CLRLPIR => (BitVec 64)
  | .GICM_TYPER => (BitVec 32)
  | .GICM_SETSPI_SR => (BitVec 32)
  | .GICM_SETSPI_NSR => (BitVec 32)
  | .GICM_IIDR => (BitVec 32)
  | .GICM_CLRSPI_SR => (BitVec 32)
  | .GICM_CLRSPI_NSR => (BitVec 32)
  | .GICH_VTR => (BitVec 32)
  | .GICH_VMCR => (BitVec 32)
  | .GICH_MISR => (BitVec 32)
  | .GICH_HCR => (BitVec 32)
  | .GICH_ELRSR => (BitVec 32)
  | .GICH_EISR => (BitVec 32)
  | .GICD_TYPER2 => (BitVec 32)
  | .GICD_STATUSR => (BitVec 32)
  | .GICD_SGIR => (BitVec 32)
  | .GICD_SETSPI_SR => (BitVec 32)
  | .GICD_SETSPI_NSR => (BitVec 32)
  | .GICD_IIDR => (BitVec 32)
  | .GICD_CTLR => (BitVec 32)
  | .GICD_CLRSPI_SR => (BitVec 32)
  | .GICD_CLRSPI_NSR => (BitVec 32)
  | .GICC_STATUSR => (BitVec 32)
  | .GICC_RPR => (BitVec 32)
  | .GICC_PMR => (BitVec 32)
  | .GICC_IAR => (BitVec 32)
  | .GICC_HPPIR => (BitVec 32)
  | .GICC_EOIR => (BitVec 32)
  | .GICC_DIR => (BitVec 32)
  | .GICC_BPR => (BitVec 32)
  | .GICC_AIAR => (BitVec 32)
  | .GICC_AHPPIR => (BitVec 32)
  | .GICC_AEOIR => (BitVec 32)
  | .GICC_ABPR => (BitVec 32)
  | .FCSEIDR => (BitVec 32)
  | .EDVIDSR => (BitVec 32)
  | .EDRCR => (BitVec 32)
  | .EDPRSR => (BitVec 32)
  | .EDPRCR => (BitVec 32)
  | .EDPIDR4 => (BitVec 32)
  | .EDPIDR3 => (BitVec 32)
  | .EDPIDR2 => (BitVec 32)
  | .EDPIDR1 => (BitVec 32)
  | .EDPIDR0 => (BitVec 32)
  | .EDPFR => (BitVec 64)
  | .EDPCSR => (BitVec 64)
  | .EDLSR => (BitVec 32)
  | .EDLAR => (BitVec 32)
  | .EDITCTRL => (BitVec 32)
  | .EDHSR => (BitVec 64)
  | .EDDFR1 => (BitVec 64)
  | .EDDFR => (BitVec 64)
  | .EDDEVTYPE => (BitVec 32)
  | .EDDEVID2 => (BitVec 32)
  | .EDDEVID1 => (BitVec 32)
  | .EDDEVID => (BitVec 32)
  | .EDCIDR3 => (BitVec 32)
  | .EDCIDR2 => (BitVec 32)
  | .EDCIDR1 => (BitVec 32)
  | .EDCIDR0 => (BitVec 32)
  | .EDAA32PFR => (BitVec 64)
  | .DBGWFAR => (BitVec 32)
  | .DBGDSAR => (BitVec 64)
  | .DBGDIDR => (BitVec 32)
  | .DBGDEVID2 => (BitVec 32)
  | .DBGDEVID1 => (BitVec 32)
  | .CTIPIDR4 => (BitVec 32)
  | .CTIPIDR3 => (BitVec 32)
  | .CTIPIDR2 => (BitVec 32)
  | .CTIPIDR1 => (BitVec 32)
  | .CTIPIDR0 => (BitVec 32)
  | .CTILSR => (BitVec 32)
  | .CTILAR => (BitVec 32)
  | .CTIITCTRL => (BitVec 32)
  | .CTIDEVTYPE => (BitVec 32)
  | .CTIDEVID2 => (BitVec 32)
  | .CTIDEVID1 => (BitVec 32)
  | .CTIDEVID => (BitVec 32)
  | .CTIDEVCTL => (BitVec 32)
  | .CTICONTROL => (BitVec 32)
  | .CTICIDR3 => (BitVec 32)
  | .CTICIDR2 => (BitVec 32)
  | .CTICIDR1 => (BitVec 32)
  | .CTICIDR0 => (BitVec 32)
  | .CTIAUTHSTATUS => (BitVec 32)
  | .CNTSR => (BitVec 32)
  | .CNTNSAR => (BitVec 32)
  | .CNTID => (BitVec 32)
  | .CNTEL0ACR => (BitVec 32)
  | .AMPIDR4 => (BitVec 32)
  | .AMPIDR3 => (BitVec 32)
  | .AMPIDR2 => (BitVec 32)
  | .AMPIDR1 => (BitVec 32)
  | .AMPIDR0 => (BitVec 32)
  | .AMDEVTYPE => (BitVec 32)
  | .AMCIDR3 => (BitVec 32)
  | .AMCIDR2 => (BitVec 32)
  | .AMCIDR1 => (BitVec 32)
  | .AMCIDR0 => (BitVec 32)
  | .RVBAR_EL3 => (BitVec 64)
  | .RVBAR_EL2 => (BitVec 64)
  | .RVBAR_EL1 => (BitVec 64)
  | ._VDISR => (BitVec 32)
  | .VDISR_EL2 => (BitVec 64)
  | ._VDFSR => (BitVec 32)
  | .VSESR_EL2 => (BitVec 64)
  | ._DISR => (BitVec 32)
  | .DISR_EL1 => (BitVec 64)
  | .HFGITR_EL2 => (BitVec 64)
  | .VNCR_EL2 => (BitVec 64)
  | .RCWSMASK_EL1 => (BitVec 128)
  | .RCWMASK_EL1 => (BitVec 128)
  | .SPESampleCounterValid => (Vector Bool 32)
  | .SPESampleCounterPending => (Vector Bool 32)
  | .VMECID_A_EL2 => (BitVec 64)
  | .S2POR_EL1 => (BitVec 64)
  | .VSTTBR_EL2 => (BitVec 64)
  | .VSTCR_EL2 => (BitVec 64)
  | .S2PIR_EL2 => (BitVec 64)
  | .MECID_RL_A_EL3 => (BitVec 64)
  | .MECID_P1_EL2 => (BitVec 64)
  | .MECID_A1_EL2 => (BitVec 64)
  | .MECID_A0_EL2 => (BitVec 64)
  | .VMECID_P_EL2 => (BitVec 64)
  | .MECID_P0_EL2 => (BitVec 64)
  | .POR_EL0 => (BitVec 64)
  | .POR_EL3 => (BitVec 64)
  | .POR_EL2 => (BitVec 64)
  | .POR_EL1 => (BitVec 64)
  | .EDWAR => (BitVec 64)
  | .DBGWVR_EL1 => (Vector (BitVec 64) 64)
  | .DBGWCR_EL1 => (Vector (BitVec 64) 64)
  | ._VTTBR_EL2 => (BitVec 128)
  | .VTTBR => (BitVec 64)
  | .VTCR_EL2 => (BitVec 64)
  | ._EDSCR2 => (BitVec 32)
  | .DBGBVR_EL1 => (Vector (BitVec 64) 64)
  | .DBGBCR_EL1 => (Vector (BitVec 64) 64)
  | .CONTEXTIDR_EL2 => (BitVec 64)
  | .TFSR_EL3 => (BitVec 64)
  | .TFSR_EL2 => (BitVec 64)
  | .TFSR_EL1 => (BitVec 64)
  | .TFSRE0_EL1 => (BitVec 64)
  | .RGSR_EL1 => (BitVec 64)
  | .GCR_EL1 => (BitVec 64)
  | ._CNTKCTL => (BitVec 32)
  | .APGAKeyLo_EL1 => (BitVec 64)
  | .APGAKeyHi_EL1 => (BitVec 64)
  | .APDBKeyLo_EL1 => (BitVec 64)
  | .APDBKeyHi_EL1 => (BitVec 64)
  | .APDAKeyLo_EL1 => (BitVec 64)
  | .APDAKeyHi_EL1 => (BitVec 64)
  | .APIBKeyLo_EL1 => (BitVec 64)
  | .APIBKeyHi_EL1 => (BitVec 64)
  | .APIAKeyLo_EL1 => (BitVec 64)
  | .APIAKeyHi_EL1 => (BitVec 64)
  | .TTBR0_EL3 => (BitVec 64)
  | .SCTLR2_EL3 => (BitVec 64)
  | .PIR_EL3 => (BitVec 64)
  | .MAIR_EL3 => (BitVec 64)
  | .MAIR2_EL3 => (BitVec 64)
  | .PIRE0_EL2 => (BitVec 64)
  | .TCR2_EL2 => (BitVec 64)
  | .PIR_EL2 => (BitVec 64)
  | .MAIR_EL2 => (BitVec 64)
  | .MAIR2_EL2 => (BitVec 64)
  | .TCR2_EL1 => (BitVec 64)
  | .PIR_EL1 => (BitVec 64)
  | .PIRE0_EL1 => (BitVec 64)
  | .MAIR_EL1 => (BitVec 64)
  | .MAIR2_EL1 => (BitVec 64)
  | .GICC_CTLR => (BitVec 32)
  | .__tlb_enabled => Bool
  | .GPTBR_EL3 => (BitVec 64)
  | .GPCCR_EL3 => (BitVec 64)
  | .CNTKCTL_EL1 => (BitVec 64)
  | .CNTSCR => (BitVec 32)
  | .CNTCR => (BitVec 32)
  | .CNTPS_CVAL_EL1 => (BitVec 64)
  | .CNTPS_CTL_EL1 => (BitVec 64)
  | .CNTHV_CVAL_EL2 => (BitVec 64)
  | .CNTHV_CTL_EL2 => (BitVec 64)
  | .CNTHVS_CVAL_EL2 => (BitVec 64)
  | .CNTHVS_CTL_EL2 => (BitVec 64)
  | .CNTHPS_CVAL_EL2 => (BitVec 64)
  | .CNTHPS_CTL_EL2 => (BitVec 64)
  | .CNTV_CVAL_EL0 => (BitVec 64)
  | .CNTV_CTL_EL0 => (BitVec 64)
  | .CNTP_CVAL_S => (BitVec 64)
  | ._CNTP_CVAL_NS => (BitVec 64)
  | .CNTP_CVAL_EL0 => (BitVec 64)
  | .CNTP_CTL_S => (BitVec 32)
  | ._CNTP_CTL_NS => (BitVec 32)
  | .CNTP_CTL_EL0 => (BitVec 64)
  | ._CNTHP_CVAL => (BitVec 64)
  | .CNTHP_CVAL_EL2 => (BitVec 64)
  | ._CNTHP_CTL => (BitVec 32)
  | .CNTHP_CTL_EL2 => (BitVec 64)
  | ._FPEXC => (BitVec 32)
  | .FPEXC32_EL2 => (BitVec 64)
  | .SCTLR2_EL2 => (BitVec 64)
  | .SCTLR2_EL1 => (BitVec 64)
  | ._IFAR_S => (BitVec 32)
  | ._IFAR_NS => (BitVec 32)
  | ._HCR2 => (BitVec 32)
  | ._DBGDSCRext => (BitVec 32)
  | ._DBGDSCRint => (BitVec 32)
  | .IFSR_S => (BitVec 32)
  | ._IFSR_NS => (BitVec 32)
  | .IFSR32_EL2 => (BitVec 64)
  | .DFSR_S => (BitVec 32)
  | ._DFSR_NS => (BitVec 32)
  | ._DFAR_S => (BitVec 32)
  | ._DFAR_NS => (BitVec 32)
  | .MVBAR => (BitVec 32)
  | ._HVBAR => (BitVec 32)
  | ._ELR_hyp => (BitVec 32)
  | ._HSR => (BitVec 32)
  | ._HPFAR => (BitVec 32)
  | ._HIFAR => (BitVec 32)
  | ._HDFAR => (BitVec 32)
  | .TTBR1_EL2 => (BitVec 128)
  | ._TTBR1_EL1 => (BitVec 128)
  | .TTBR1_S => (BitVec 64)
  | .TTBR1_NS => (BitVec 64)
  | ._TTBR0_EL2 => (BitVec 128)
  | .HTTBR => (BitVec 64)
  | ._TTBR0_EL1 => (BitVec 128)
  | .TTBR0_S => (BitVec 64)
  | .TTBR0_NS => (BitVec 64)
  | .CONTEXTIDR_S => (BitVec 32)
  | ._CONTEXTIDR_NS => (BitVec 32)
  | .TTBCR_S => (BitVec 32)
  | ._TTBCR_NS => (BitVec 32)
  | .CONTEXTIDR_EL1 => (BitVec 64)
  | .CLIDR_EL1 => (BitVec 64)
  | .MPAMSM_EL1 => (BitVec 64)
  | .MPAM0_EL1 => (BitVec 64)
  | .MPAMVPM7_EL2 => (BitVec 64)
  | .MPAMVPM6_EL2 => (BitVec 64)
  | .MPAMVPM5_EL2 => (BitVec 64)
  | .MPAMVPM4_EL2 => (BitVec 64)
  | .MPAMVPM3_EL2 => (BitVec 64)
  | .MPAMVPM2_EL2 => (BitVec 64)
  | .MPAMVPM1_EL2 => (BitVec 64)
  | .MPAMVPMV_EL2 => (BitVec 64)
  | .MPAMVPM0_EL2 => (BitVec 64)
  | .MPAMHCR_EL2 => (BitVec 64)
  | .MPAMIDR_EL1 => (BitVec 64)
  | ._MPAM1_EL1 => (BitVec 64)
  | ._MPAM3_EL3 => (BitVec 64)
  | .MPAM2_EL2 => (BitVec 64)
  | .HCRX_EL2 => (BitVec 64)
  | .GCSCRE0_EL1 => (BitVec 64)
  | .VBAR_S => (BitVec 32)
  | ._VBAR_NS => (BitVec 32)
  | .VBAR_EL3 => (BitVec 64)
  | .VBAR_EL2 => (BitVec 64)
  | .VBAR_EL1 => (BitVec 64)
  | .EDESR => (BitVec 32)
  | ._EDECCR => (BitVec 32)
  | .OSECCR_EL1 => (BitVec 64)
  | .SPSR_und => (BitVec 64)
  | ._SPSR_svc => (BitVec 32)
  | .SPSR_mon => (BitVec 32)
  | .SPSR_irq => (BitVec 64)
  | ._SPSR_hyp => (BitVec 32)
  | .SPSR_fiq => (BitVec 64)
  | .SPSR_abt => (BitVec 64)
  | .SPSR_EL3 => (BitVec 64)
  | .SPSR_EL2 => (BitVec 64)
  | .SPSR_EL1 => (BitVec 64)
  | .ELR_EL3 => (BitVec 64)
  | .ELR_EL2 => (BitVec 64)
  | .ELR_EL1 => (BitVec 64)
  | .PFAR_EL2 => (BitVec 64)
  | .PFAR_EL1 => (BitVec 64)
  | .MFAR_EL3 => (BitVec 64)
  | .HPFAR_EL2 => (BitVec 64)
  | .FAR_EL3 => (BitVec 64)
  | .FAR_EL2 => (BitVec 64)
  | .FAR_EL1 => (BitVec 64)
  | .ESR_EL3 => (BitVec 64)
  | .ESR_EL2 => (BitVec 64)
  | .ESR_EL1 => (BitVec 64)
  | .SCTLR_S => (BitVec 32)
  | ._SCTLR_NS => (BitVec 32)
  | .SCTLR_EL3 => (BitVec 64)
  | .SCTLR_EL1 => (BitVec 64)
  | ._HSCTLR => (BitVec 32)
  | .SCTLR_EL2 => (BitVec 64)
  | ._HCR => (BitVec 32)
  | ._DBGOSLSR => (BitVec 32)
  | .OSLSR_EL1 => (BitVec 64)
  | .MDSCR_EL1 => (BitVec 64)
  | .GCSCR_EL3 => (BitVec 64)
  | .GCSCR_EL2 => (BitVec 64)
  | .GCSCR_EL1 => (BitVec 64)
  | .__GIC_Pending => (Option InterruptID)
  | .__GIC_Active => (Option InterruptID)
  | ._DBGPRCR => (BitVec 32)
  | .DBGPRCR_EL1 => (BitVec 64)
  | ._DBGOSDLR => (BitVec 32)
  | .OSDLR_EL1 => (BitVec 64)
  | .SP_EL3 => (BitVec 64)
  | .SP_EL2 => (BitVec 64)
  | .SP_EL1 => (BitVec 64)
  | .SP_EL0 => (BitVec 64)
  | .NSACR => (BitVec 32)
  | ._HCPTR => (BitVec 32)
  | ._CPACR => (BitVec 32)
  | .CPTR_EL3 => (BitVec 64)
  | .CPTR_EL2 => (BitVec 64)
  | .CPACR_EL1 => (BitVec 64)
  | .GCSPR_EL3 => (BitVec 64)
  | .GCSPR_EL2 => (BitVec 64)
  | .GCSPR_EL1 => (BitVec 64)
  | .GCSPR_EL0 => (BitVec 64)
  | .SMCR_EL3 => (BitVec 64)
  | .SMCR_EL2 => (BitVec 64)
  | .SMCR_EL1 => (BitVec 64)
  | .ZCR_EL3 => (BitVec 64)
  | .ZCR_EL2 => (BitVec 64)
  | .ZCR_EL1 => (BitVec 64)
  | .PMBSR_EL1 => (BitVec 64)
  | .PMBLIMITR_EL1 => (BitVec 64)
  | .PMSCR_EL2 => (BitVec 64)
  | .PMSCR_EL1 => (BitVec 64)
  | .SPESampleAddressValid => (Vector Bool 32)
  | .SPESampleAddress => (Vector (BitVec 64) 32)
  | .PMSIDR_EL1 => (BitVec 64)
  | .Records_TGT => (Vector (BitVec 64) 64)
  | .Records_SRC => (Vector (BitVec 64) 64)
  | .Records_INF => (Vector (BitVec 64) 64)
  | .BRBIDR0_EL1 => (BitVec 64)
  | .TCR_EL3 => (BitVec 64)
  | .TCR_EL2 => (BitVec 64)
  | .TCR_EL1 => (BitVec 64)
  | ._DSPSR2 => (BitVec 32)
  | ._DSPSR => (BitVec 32)
  | .DSPSR_EL0 => (BitVec 64)
  | ._DLR => (BitVec 32)
  | .DLR_EL0 => (BitVec 64)
  | .EDECR => (BitVec 32)
  | .__mpam_vpmr_max => (BitVec 3)
  | .__mpam_pmg_max => (BitVec 8)
  | .__mpam_partid_max => (BitVec 16)
  | .__mpam_has_hcr => Bool
  | .__impdef_TG1 => (BitVec 2)
  | .__impdef_TG0 => (BitVec 2)
  | .CFG_RVBAR => (BitVec 64)
  | .CNTHCTL_EL2 => (BitVec 64)
  | .CNTVOFF_EL2 => (BitVec 64)
  | .CNTPOFF_EL2 => (BitVec 64)
  | .BRBTS_EL1 => (BitVec 64)
  | .BRBFCR_EL1 => (BitVec 64)
  | .BRBCR_EL2 => (BitVec 64)
  | .BRBCR_EL1 => (BitVec 64)
  | .PMOVSSET_EL0 => (BitVec 64)
  | .PMICNTR_EL0 => (BitVec 64)
  | ._SDER => (BitVec 32)
  | ._SDER32_EL3 => (BitVec 64)
  | .SDER32_EL2 => (BitVec 64)
  | .SDCR => (BitVec 32)
  | .PMICFILTR_EL0 => (BitVec 64)
  | ._PMEVTYPER => (Vector (BitVec 32) 31)
  | .PMEVTYPER_EL0 => (Vector (BitVec 64) 32)
  | ._PMCNTENSET => (BitVec 32)
  | .PMCNTENSET_EL0 => (BitVec 64)
  | ._PMCCFILTR => (BitVec 32)
  | .PMCCFILTR_EL0 => (BitVec 64)
  | .MDCR_EL3 => (BitVec 64)
  | ._PMOVSR => (BitVec 32)
  | .PMOVSCLR_EL0 => (BitVec 64)
  | ._PMINTENCLR => (BitVec 32)
  | .PMINTENCLR_EL1 => (BitVec 64)
  | ._PMCR => (BitVec 32)
  | .PMCR_EL0 => (BitVec 64)
  | ._PMCNTENCLR => (BitVec 32)
  | .PMCNTENCLR_EL0 => (BitVec 64)
  | ._EDSCR => (BitVec 32)
  | .MDCCSR_EL0 => (BitVec 64)
  | ._HDCR => (BitVec 32)
  | .MDCR_EL2 => (BitVec 64)
  | .__supported_pa_size => Int
  | .__max_implemented_sveveclen => Int
  | .__max_implemented_smeveclen => Int
  | .__has_sve_extended_bf16 => Int
  | .__block_bbm_implemented => Int
  | .CTR_EL0 => (BitVec 64)
  | .ERRnFR => (Vector (BitVec 64) 4)
  | .RVBAR => (BitVec 32)
  | ._FPSCR => (BitVec 32)
  | .__sme_only => Bool
  | .__setg_mops_option_a_supported => Bool
  | .__set_mops_option_a_supported => Bool
  | .__mte_implemented => (BitVec 4)
  | .__mpam_major => (BitVec 4)
  | .__mpam_frac => (BitVec 4)
  | .__isb_is_branch => Bool
  | .__has_sme_priority_control => Bool
  | .__feat_rpres => Bool
  | .__empam_tidr_implemented => Bool
  | .__empam_sdeflt_implemented => Bool
  | .__empam_force_ns_implemented => Bool
  | .__empam_force_ns_RAO => Bool
  | .__cpyf_mops_option_a_supported => Bool
  | .__cpy_mops_option_a_supported => Bool
  | .__apply_effective_shareability => Bool
  | .SCR => (BitVec 32)
  | .SCR_EL3 => (BitVec 64)
  | .HCR_EL2 => (BitVec 64)
  | ._Dclone => (Vector (BitVec 64) 32)
  | .LR_mon => (BitVec 32)
  | .SP_mon => (BitVec 32)
  | .sp_rel_access_pc => (BitVec 64)
  | .__DCACHE_CCSIDR_RESET => (Vector (BitVec 64) 7)
  | .__ICACHE_CCSIDR_RESET => (Vector (BitVec 64) 7)
  | .__highest_el_aarch32 => Bool
  | .__ExclusiveMonitorSet => Bool
  | .__BranchTaken => Bool
  | .Branchtypetaken => BranchType
  | .__currentCond => (BitVec 4)
  | .__ThisInstrEnc => __InstrEnc
  | .__ThisInstr => (BitVec 32)
  | .__ETEBase => (BitVec 56)
  | .__VLPI_base => (BitVec 56)
  | .__SGI_base => (BitVec 56)
  | .__RD_base => (BitVec 56)
  | .__CNTCTLBase => (BitVec 56)
  | .__CNTEL0BaseN => (BitVec 56)
  | .__CNTBaseN => (BitVec 56)
  | .__CNTReadBase => (BitVec 56)
  | .__InstructionStep => Bool
  | .RTPIDEN => Signal
  | .RLPIDEN => Signal
  | .SPNIDEN => Signal
  | .SPIDEN => Signal
  | .NIDEN => Signal
  | .DBGEN => Signal
  | .__last_branch_valid => Bool
  | .__last_cycle_count => Int
  | .SPERecordSize => Int
  | .__SPE_LFSR_initialized => Bool
  | .__SPE_LFSR => (BitVec 24)
  | .SPESampleEvents => (BitVec 64)
  | .SPESampleTimestampValid => Bool
  | .SPESampleTimestamp => (BitVec 64)
  | .SPESampleSubclassValid => Bool
  | .SPESampleSubclass => (BitVec 8)
  | .SPESampleClass => (BitVec 2)
  | .SPESampleOpType => OpType
  | .SPESampleDataSourceValid => Bool
  | .SPESampleDataSource => (BitVec 16)
  | .SPESamplePreviousBranchAddressValid => Bool
  | .SPESamplePreviousBranchAddress => (BitVec 64)
  | .SPESampleInstIsNV2 => Bool
  | .SPESampleContextEL2Valid => Bool
  | .SPESampleContextEL2 => (BitVec 32)
  | .SPESampleContextEL1Valid => Bool
  | .SPESampleContextEL1 => (BitVec 32)
  | .SPESampleInFlight => Bool
  | .TSTATE => TMState
  | .ICC_PMR_EL1 => (BitVec 64)
  | .FPSR => (BitVec 64)
  | .FPCR => (BitVec 64)
  | ._ZT0 => (BitVec 512)
  | ._ZA => (Vector (BitVec 2048) 256)
  | ._FFR => (BitVec 256)
  | ._P => (Vector (BitVec 256) 16)
  | ._Z => (Vector (BitVec 2048) 32)
  | .BTypeCompatible => Bool
  | .BTypeNext => (BitVec 2)
  | .InGuardedPage => Bool
  | .RC => (Vector (BitVec 64) 5)
  | .PhysicalCount => (BitVec 88)
  | ._PC => (BitVec 64)
  | .R30 => (BitVec 64)
  | .R29 => (BitVec 64)
  | .R28 => (BitVec 64)
  | .R27 => (BitVec 64)
  | .R26 => (BitVec 64)
  | .R25 => (BitVec 64)
  | .R24 => (BitVec 64)
  | .R23 => (BitVec 64)
  | .R22 => (BitVec 64)
  | .R21 => (BitVec 64)
  | .R20 => (BitVec 64)
  | .R19 => (BitVec 64)
  | .R18 => (BitVec 64)
  | .R17 => (BitVec 64)
  | .R16 => (BitVec 64)
  | .R15 => (BitVec 64)
  | .R14 => (BitVec 64)
  | .R13 => (BitVec 64)
  | .R12 => (BitVec 64)
  | .R11 => (BitVec 64)
  | .R10 => (BitVec 64)
  | .R9 => (BitVec 64)
  | .R8 => (BitVec 64)
  | .R7 => (BitVec 64)
  | .R6 => (BitVec 64)
  | .R5 => (BitVec 64)
  | .R4 => (BitVec 64)
  | .R3 => (BitVec 64)
  | .R2 => (BitVec 64)
  | .R1 => (BitVec 64)
  | .R0 => (BitVec 64)
  | .EventRegister => (BitVec 1)
  | .ShouldAdvanceSS => Bool
  | .ShouldAdvanceIT => Bool
  | .PSTATE => ProcState
  | .__clock_divider => Int
  | .PMULastThresholdValue => (Vector Bool 31)
  | .PMUEventAccumulator => (Vector Int 31)
  | ._DormantCtlReg => (BitVec 32)
  | ._ConfigReg => (BitVec 32)
  | .IsWFEsleep => Bool
  | .IsWFIsleep => Bool
  | .CP15SDISABLE2 => Signal
  | .CP15SDISABLE => Signal
  | .__cycle_count => Int
  | .__trcclaim_tags => (BitVec 32)
  | .NUM_WATCHPOINTS => Int
  | .NUM_BREAKPOINTS => Int
  | .NUM_GIC_LIST_REGS => Int
  | .NUM_GIC_PRIORITY_BITS => Int
  | .NUM_GIC_PREEMPTION_BITS => Int
  | .NUM_BRBE_RECORDS => Int
  | .NUM_PMU_COUNTERS => Int
  | .NUM_AMU_CG1_MONITORS => Int
  | .NUM_AMU_CG0_MONITORS => Int
  | .NUM_AMU_COUNTER_GROUPS => Int
  | .VariantImplemented => (Vector Bool 16)
  | .FeatureImpl => (Vector Bool 259)
  | .v9Ap4_IMPLEMENTED => Bool
  | .v9Ap3_IMPLEMENTED => Bool
  | .v9Ap2_IMPLEMENTED => Bool
  | .v9Ap1_IMPLEMENTED => Bool
  | .v9Ap0_IMPLEMENTED => Bool
  | .v8Ap9_IMPLEMENTED => Bool
  | .v8Ap8_IMPLEMENTED => Bool
  | .v8Ap7_IMPLEMENTED => Bool
  | .v8Ap6_IMPLEMENTED => Bool
  | .v8Ap5_IMPLEMENTED => Bool
  | .v8Ap4_IMPLEMENTED => Bool
  | .v8Ap3_IMPLEMENTED => Bool
  | .v8Ap2_IMPLEMENTED => Bool
  | .v8Ap1_IMPLEMENTED => Bool
  | .v8Ap0_IMPLEMENTED => Bool
  | .FEAT_TRBE_MPAM_IMPLEMENTED => Bool
  | .FEAT_TRBE_EXT_IMPLEMENTED => Bool
  | .FEAT_SYSREG128_IMPLEMENTED => Bool
  | .FEAT_SYSINSTR128_IMPLEMENTED => Bool
  | .FEAT_SVE_B16B16_IMPLEMENTED => Bool
  | .FEAT_SVE2p1_IMPLEMENTED => Bool
  | .FEAT_SME_F16F16_IMPLEMENTED => Bool
  | .FEAT_SME2p1_IMPLEMENTED => Bool
  | .FEAT_SEBEP_IMPLEMENTED => Bool
  | .FEAT_LVA3_IMPLEMENTED => Bool
  | .FEAT_LSE128_IMPLEMENTED => Bool
  | .FEAT_ITE_IMPLEMENTED => Bool
  | .FEAT_GCS_IMPLEMENTED => Bool
  | .FEAT_ETEv1p3_IMPLEMENTED => Bool
  | .FEAT_EBEP_IMPLEMENTED => Bool
  | .FEAT_D128_IMPLEMENTED => Bool
  | .FEAT_CHK_IMPLEMENTED => Bool
  | .FEAT_ABLE_IMPLEMENTED => Bool
  | .FEAT_SME2_IMPLEMENTED => Bool
  | .FEAT_MEC_IMPLEMENTED => Bool
  | .FEAT_BRBEv1p1_IMPLEMENTED => Bool
  | .FEAT_SME_I16I64_IMPLEMENTED => Bool
  | .FEAT_SME_FA64_IMPLEMENTED => Bool
  | .FEAT_SME_F64F64_IMPLEMENTED => Bool
  | .FEAT_SME_IMPLEMENTED => Bool
  | .FEAT_RME_IMPLEMENTED => Bool
  | .FEAT_ETEv1p2_IMPLEMENTED => Bool
  | .FEAT_BRBE_IMPLEMENTED => Bool
  | .FEAT_ETEv1p1_IMPLEMENTED => Bool
  | .FEAT_TRBE_IMPLEMENTED => Bool
  | .FEAT_TME_IMPLEMENTED => Bool
  | .FEAT_SVE_SM4_IMPLEMENTED => Bool
  | .FEAT_SVE_SHA3_IMPLEMENTED => Bool
  | .FEAT_SVE_PMULL128_IMPLEMENTED => Bool
  | .FEAT_SVE_BitPerm_IMPLEMENTED => Bool
  | .FEAT_SVE_AES_IMPLEMENTED => Bool
  | .FEAT_SVE2_IMPLEMENTED => Bool
  | .FEAT_ETE_IMPLEMENTED => Bool
  | .FEAT_DoPD_IMPLEMENTED => Bool
  | .FEAT_THE_IMPLEMENTED => Bool
  | .FEAT_SPMU_IMPLEMENTED => Bool
  | .FEAT_SPEv1p4_IMPLEMENTED => Bool
  | .FEAT_SPE_FDS_IMPLEMENTED => Bool
  | .FEAT_SPE_CRR_IMPLEMENTED => Bool
  | .FEAT_SPECRES2_IMPLEMENTED => Bool
  | .FEAT_S2POE_IMPLEMENTED => Bool
  | .FEAT_S2PIE_IMPLEMENTED => Bool
  | .FEAT_S1POE_IMPLEMENTED => Bool
  | .FEAT_S1PIE_IMPLEMENTED => Bool
  | .FEAT_RPRFM_IMPLEMENTED => Bool
  | .FEAT_RASv2_IMPLEMENTED => Bool
  | .FEAT_RASSAv2_IMPLEMENTED => Bool
  | .FEAT_PRFMSLC_IMPLEMENTED => Bool
  | .FEAT_PMUv3p9_IMPLEMENTED => Bool
  | .FEAT_PMUv3_SS_IMPLEMENTED => Bool
  | .FEAT_PMUv3_ICNTR_IMPLEMENTED => Bool
  | .FEAT_PMUv3_EDGE_IMPLEMENTED => Bool
  | .FEAT_PFAR_IMPLEMENTED => Bool
  | .FEAT_PCSRv8p9_IMPLEMENTED => Bool
  | .FEAT_MTE_TAGGED_FAR_IMPLEMENTED => Bool
  | .FEAT_MTE_STORE_ONLY_IMPLEMENTED => Bool
  | .FEAT_MTE_PERM_IMPLEMENTED => Bool
  | .FEAT_MTE_NO_ADDRESS_TAGS_IMPLEMENTED => Bool
  | .FEAT_MTE_CANONICAL_TAGS_IMPLEMENTED => Bool
  | .FEAT_MTE_ASYNC_IMPLEMENTED => Bool
  | .FEAT_MTE_ASYM_FAULT_IMPLEMENTED => Bool
  | .FEAT_MTE4_IMPLEMENTED => Bool
  | .FEAT_LRCPC3_IMPLEMENTED => Bool
  | .FEAT_HAFT_IMPLEMENTED => Bool
  | .FEAT_FGT2_IMPLEMENTED => Bool
  | .FEAT_ECBHB_IMPLEMENTED => Bool
  | .FEAT_DoubleFault2_IMPLEMENTED => Bool
  | .FEAT_Debugv8p9_IMPLEMENTED => Bool
  | .FEAT_CSSC_IMPLEMENTED => Bool
  | .FEAT_CLRBHB_IMPLEMENTED => Bool
  | .FEAT_ANERR_IMPLEMENTED => Bool
  | .FEAT_AIE_IMPLEMENTED => Bool
  | .FEAT_ADERR_IMPLEMENTED => Bool
  | .FEAT_TIDCP1_IMPLEMENTED => Bool
  | .FEAT_TCR2_IMPLEMENTED => Bool
  | .FEAT_SPEv1p3_IMPLEMENTED => Bool
  | .FEAT_SCTLR2_IMPLEMENTED => Bool
  | .FEAT_PMUv3p8_IMPLEMENTED => Bool
  | .FEAT_PMUv3_TH_IMPLEMENTED => Bool
  | .FEAT_PMUv3_EXT64_IMPLEMENTED => Bool
  | .FEAT_NMI_IMPLEMENTED => Bool
  | .FEAT_MOPS_IMPLEMENTED => Bool
  | .FEAT_HBC_IMPLEMENTED => Bool
  | .FEAT_GICv3_NMI_IMPLEMENTED => Bool
  | .FEAT_Debugv8p8_IMPLEMENTED => Bool
  | .FEAT_CMOW_IMPLEMENTED => Bool
  | .FEAT_XS_IMPLEMENTED => Bool
  | .FEAT_WFxT_IMPLEMENTED => Bool
  | .FEAT_SPEv1p2_IMPLEMENTED => Bool
  | .FEAT_RPRES_IMPLEMENTED => Bool
  | .FEAT_PMUv3p7_IMPLEMENTED => Bool
  | .FEAT_PAN3_IMPLEMENTED => Bool
  | .FEAT_MTE3_IMPLEMENTED => Bool
  | .FEAT_LS64_V_IMPLEMENTED => Bool
  | .FEAT_LS64_ACCDATA_IMPLEMENTED => Bool
  | .FEAT_LS64_IMPLEMENTED => Bool
  | .FEAT_LPA2_IMPLEMENTED => Bool
  | .FEAT_HCX_IMPLEMENTED => Bool
  | .FEAT_EBF16_IMPLEMENTED => Bool
  | .FEAT_AFP_IMPLEMENTED => Bool
  | .FEAT_TWED_IMPLEMENTED => Bool
  | .FEAT_PAuth2_IMPLEMENTED => Bool
  | .FEAT_MTPMU_IMPLEMENTED => Bool
  | .FEAT_MPAMv1p1_IMPLEMENTED => Bool
  | .FEAT_MPAMv0p1_IMPLEMENTED => Bool
  | .FEAT_HPMN0_IMPLEMENTED => Bool
  | .FEAT_FGT_IMPLEMENTED => Bool
  | .FEAT_ECV_IMPLEMENTED => Bool
  | .FEAT_DGH_IMPLEMENTED => Bool
  | .FEAT_BF16_IMPLEMENTED => Bool
  | .FEAT_AMUv1p1_IMPLEMENTED => Bool
  | .FEAT_SSBS2_IMPLEMENTED => Bool
  | .FEAT_SSBS_IMPLEMENTED => Bool
  | .FEAT_SPECRES_IMPLEMENTED => Bool
  | .FEAT_SB_IMPLEMENTED => Bool
  | .FEAT_RNG_TRAP_IMPLEMENTED => Bool
  | .FEAT_RNG_IMPLEMENTED => Bool
  | .FEAT_PMUv3p5_IMPLEMENTED => Bool
  | .FEAT_MTE2_IMPLEMENTED => Bool
  | .FEAT_MTE_IMPLEMENTED => Bool
  | .FEAT_GTG_IMPLEMENTED => Bool
  | .FEAT_FlagM2_IMPLEMENTED => Bool
  | .FEAT_FRINTTS_IMPLEMENTED => Bool
  | .FEAT_ExS_IMPLEMENTED => Bool
  | .FEAT_EVT_IMPLEMENTED => Bool
  | .FEAT_E0PD_IMPLEMENTED => Bool
  | .FEAT_DPB2_IMPLEMENTED => Bool
  | .FEAT_CSV3_IMPLEMENTED => Bool
  | .FEAT_CSV2_IMPLEMENTED => Bool
  | .FEAT_BTI_IMPLEMENTED => Bool
  | .FEAT_TTST_IMPLEMENTED => Bool
  | .FEAT_TTL_IMPLEMENTED => Bool
  | .FEAT_TRF_IMPLEMENTED => Bool
  | .FEAT_TLBIRANGE_IMPLEMENTED => Bool
  | .FEAT_TLBIOS_IMPLEMENTED => Bool
  | .FEAT_SEL2_IMPLEMENTED => Bool
  | .FEAT_S2FWB_IMPLEMENTED => Bool
  | .FEAT_RASv1p1_IMPLEMENTED => Bool
  | .FEAT_RASSAv1p1_IMPLEMENTED => Bool
  | .FEAT_PMUv3p4_IMPLEMENTED => Bool
  | .FEAT_NV2_IMPLEMENTED => Bool
  | .FEAT_LSE2_IMPLEMENTED => Bool
  | .FEAT_LRCPC2_IMPLEMENTED => Bool
  | .FEAT_IDST_IMPLEMENTED => Bool
  | .FEAT_FlagM_IMPLEMENTED => Bool
  | .FEAT_FHM_IMPLEMENTED => Bool
  | .FEAT_DoubleFault_IMPLEMENTED => Bool
  | .FEAT_DotProd_IMPLEMENTED => Bool
  | .FEAT_Debugv8p4_IMPLEMENTED => Bool
  | .FEAT_DIT_IMPLEMENTED => Bool
  | .FEAT_CNTSC_IMPLEMENTED => Bool
  | .FEAT_BBM_IMPLEMENTED => Bool
  | .FEAT_AMUv1_IMPLEMENTED => Bool
  | .FEAT_SPEv1p1_IMPLEMENTED => Bool
  | .FEAT_PAuth_IMPLEMENTED => Bool
  | .FEAT_PACQARMA5_IMPLEMENTED => Bool
  | .FEAT_PACQARMA3_IMPLEMENTED => Bool
  | .FEAT_PACIMP_IMPLEMENTED => Bool
  | .FEAT_NV_IMPLEMENTED => Bool
  | .FEAT_LRCPC_IMPLEMENTED => Bool
  | .FEAT_JSCVT_IMPLEMENTED => Bool
  | .FEAT_FPACCOMBINE_IMPLEMENTED => Bool
  | .FEAT_FPAC_IMPLEMENTED => Bool
  | .FEAT_FCMA_IMPLEMENTED => Bool
  | .FEAT_EPAC_IMPLEMENTED => Bool
  | .FEAT_CONSTPACFIELD_IMPLEMENTED => Bool
  | .FEAT_CCIDX_IMPLEMENTED => Bool
  | .FEAT_XNX_IMPLEMENTED => Bool
  | .FEAT_VPIPT_IMPLEMENTED => Bool
  | .FEAT_UAO_IMPLEMENTED => Bool
  | .FEAT_TTCNP_IMPLEMENTED => Bool
  | .FEAT_SVE_IMPLEMENTED => Bool
  | .FEAT_SPE_IMPLEMENTED => Bool
  | .FEAT_SM4_IMPLEMENTED => Bool
  | .FEAT_SM3_IMPLEMENTED => Bool
  | .FEAT_SHA512_IMPLEMENTED => Bool
  | .FEAT_SHA3_IMPLEMENTED => Bool
  | .FEAT_RAS_IMPLEMENTED => Bool
  | .FEAT_PCSRv8p2_IMPLEMENTED => Bool
  | .FEAT_PAN2_IMPLEMENTED => Bool
  | .FEAT_MPAM_IMPLEMENTED => Bool
  | .FEAT_LVA_IMPLEMENTED => Bool
  | .FEAT_LSMAOC_IMPLEMENTED => Bool
  | .FEAT_LPA_IMPLEMENTED => Bool
  | .FEAT_IESB_IMPLEMENTED => Bool
  | .FEAT_I8MM_IMPLEMENTED => Bool
  | .FEAT_HPDS2_IMPLEMENTED => Bool
  | .FEAT_FP16_IMPLEMENTED => Bool
  | .FEAT_F64MM_IMPLEMENTED => Bool
  | .FEAT_F32MM_IMPLEMENTED => Bool
  | .FEAT_EDHSR_IMPLEMENTED => Bool
  | .FEAT_Debugv8p2_IMPLEMENTED => Bool
  | .FEAT_DPB_IMPLEMENTED => Bool
  | .FEAT_ASMv8p2_IMPLEMENTED => Bool
  | .FEAT_AA32I8MM_IMPLEMENTED => Bool
  | .FEAT_AA32HPD_IMPLEMENTED => Bool
  | .FEAT_AA32BF16_IMPLEMENTED => Bool
  | .FEAT_VMID16_IMPLEMENTED => Bool
  | .FEAT_VHE_IMPLEMENTED => Bool
  | .FEAT_RDM_IMPLEMENTED => Bool
  | .FEAT_PMUv3p1_IMPLEMENTED => Bool
  | .FEAT_PAN_IMPLEMENTED => Bool
  | .FEAT_LSE_IMPLEMENTED => Bool
  | .FEAT_LOR_IMPLEMENTED => Bool
  | .FEAT_HPDS_IMPLEMENTED => Bool
  | .FEAT_HAFDBS_IMPLEMENTED => Bool
  | .FEAT_Debugv8p1_IMPLEMENTED => Bool
  | .FEAT_CRC32_IMPLEMENTED => Bool
  | .FEAT_nTLBPA_IMPLEMENTED => Bool
  | .FEAT_TRC_SR_IMPLEMENTED => Bool
  | .FEAT_TRC_EXT_IMPLEMENTED => Bool
  | .FEAT_SHA256_IMPLEMENTED => Bool
  | .FEAT_SHA1_IMPLEMENTED => Bool
  | .FEAT_PMUv3_EXT32_IMPLEMENTED => Bool
  | .FEAT_PMUv3_EXT_IMPLEMENTED => Bool
  | .FEAT_PMUv3_IMPLEMENTED => Bool
  | .FEAT_PMULL_IMPLEMENTED => Bool
  | .FEAT_PCSRv8_IMPLEMENTED => Bool
  | .FEAT_IVIPT_IMPLEMENTED => Bool
  | .FEAT_GICv4p1_IMPLEMENTED => Bool
  | .FEAT_GICv4_IMPLEMENTED => Bool
  | .FEAT_GICv3p1_IMPLEMENTED => Bool
  | .FEAT_GICv3_TDIR_IMPLEMENTED => Bool
  | .FEAT_GICv3_LEGACY_IMPLEMENTED => Bool
  | .FEAT_GICv3_IMPLEMENTED => Bool
  | .FEAT_FP_IMPLEMENTED => Bool
  | .FEAT_ETS2_IMPLEMENTED => Bool
  | .FEAT_ETMv4p6_IMPLEMENTED => Bool
  | .FEAT_ETMv4p5_IMPLEMENTED => Bool
  | .FEAT_ETMv4p4_IMPLEMENTED => Bool
  | .FEAT_ETMv4p3_IMPLEMENTED => Bool
  | .FEAT_ETMv4p2_IMPLEMENTED => Bool
  | .FEAT_ETMv4p1_IMPLEMENTED => Bool
  | .FEAT_ETMv4_IMPLEMENTED => Bool
  | .FEAT_DoubleLock_IMPLEMENTED => Bool
  | .FEAT_CSV2_3_IMPLEMENTED => Bool
  | .FEAT_CSV2_2_IMPLEMENTED => Bool
  | .FEAT_CSV2_1p2_IMPLEMENTED => Bool
  | .FEAT_CSV2_1p1_IMPLEMENTED => Bool
  | .FEAT_AdvSIMD_IMPLEMENTED => Bool
  | .FEAT_AES_IMPLEMENTED => Bool
  | .FEAT_EL3_IMPLEMENTED => Bool
  | .FEAT_EL2_IMPLEMENTED => Bool
  | .FEAT_EL1_IMPLEMENTED => Bool
  | .FEAT_EL0_IMPLEMENTED => Bool
  | .FEAT_AA64EL3_IMPLEMENTED => Bool
  | .FEAT_AA64EL2_IMPLEMENTED => Bool
  | .FEAT_AA64EL1_IMPLEMENTED => Bool
  | .FEAT_AA64EL0_IMPLEMENTED => Bool
  | .FEAT_AA32EL3_IMPLEMENTED => Bool
  | .FEAT_AA32EL2_IMPLEMENTED => Bool
  | .FEAT_AA32EL1_IMPLEMENTED => Bool
  | .FEAT_AA32EL0_IMPLEMENTED => Bool
  | .SEE => Int

instance : Inhabited (RegisterRef RegisterType BranchType) where
  default := .Reg Branchtypetaken
instance : Inhabited (RegisterRef RegisterType OpType) where
  default := .Reg SPESampleOpType
instance : Inhabited (RegisterRef RegisterType ProcState) where
  default := .Reg PSTATE
instance : Inhabited (RegisterRef RegisterType Signal) where
  default := .Reg CP15SDISABLE
instance : Inhabited (RegisterRef RegisterType TMState) where
  default := .Reg TSTATE
instance : Inhabited (RegisterRef RegisterType __InstrEnc) where
  default := .Reg __ThisInstrEnc
instance : Inhabited (RegisterRef RegisterType (BitVec 1)) where
  default := .Reg EventRegister
instance : Inhabited (RegisterRef RegisterType (BitVec 128)) where
  default := .Reg _TTBR0_EL1
instance : Inhabited (RegisterRef RegisterType (BitVec 16)) where
  default := .Reg SPESampleDataSource
instance : Inhabited (RegisterRef RegisterType (BitVec 2)) where
  default := .Reg BTypeNext
instance : Inhabited (RegisterRef RegisterType (BitVec 24)) where
  default := .Reg __SPE_LFSR
instance : Inhabited (RegisterRef RegisterType (BitVec 256)) where
  default := .Reg _FFR
instance : Inhabited (RegisterRef RegisterType (BitVec 3)) where
  default := .Reg __mpam_vpmr_max
instance : Inhabited (RegisterRef RegisterType (BitVec 32)) where
  default := .Reg __trcclaim_tags
instance : Inhabited (RegisterRef RegisterType (BitVec 4)) where
  default := .Reg __currentCond
instance : Inhabited (RegisterRef RegisterType (BitVec 512)) where
  default := .Reg _ZT0
instance : Inhabited (RegisterRef RegisterType (BitVec 56)) where
  default := .Reg __CNTReadBase
instance : Inhabited (RegisterRef RegisterType (BitVec 64)) where
  default := .Reg R0
instance : Inhabited (RegisterRef RegisterType (BitVec 8)) where
  default := .Reg SPESampleSubclass
instance : Inhabited (RegisterRef RegisterType (BitVec 88)) where
  default := .Reg PhysicalCount
instance : Inhabited (RegisterRef RegisterType Bool) where
  default := .Reg FEAT_AA32EL0_IMPLEMENTED
instance : Inhabited (RegisterRef RegisterType Int) where
  default := .Reg SEE
instance : Inhabited (RegisterRef RegisterType (Option InterruptID)) where
  default := .Reg __GIC_Active
instance : Inhabited (RegisterRef RegisterType (Option (BitVec 32))) where
  default := .Reg __emulator_termination_opcode
instance : Inhabited (RegisterRef RegisterType (Vector (BitVec 256) 16)) where
  default := .Reg _P
instance : Inhabited (RegisterRef RegisterType (Vector (BitVec 32) 16)) where
  default := .Reg _DBGBCR
instance : Inhabited (RegisterRef RegisterType (Vector (BitVec 64) 16)) where
  default := .Reg ICH_LR_EL2
instance : Inhabited (RegisterRef RegisterType (Vector Bool 16)) where
  default := .Reg VariantImplemented
instance : Inhabited (RegisterRef RegisterType (Vector (BitVec 2048) 256)) where
  default := .Reg _ZA
instance : Inhabited (RegisterRef RegisterType (Vector Bool 259)) where
  default := .Reg FeatureImpl
instance : Inhabited (RegisterRef RegisterType (Vector (BitVec 32) 31)) where
  default := .Reg _PMEVTYPER
instance : Inhabited (RegisterRef RegisterType (Vector (BitVec 64) 31)) where
  default := .Reg PMEVCNTSVR_EL1
instance : Inhabited (RegisterRef RegisterType (Vector Bool 31)) where
  default := .Reg PMULastThresholdValue
instance : Inhabited (RegisterRef RegisterType (Vector Int 31)) where
  default := .Reg PMUEventAccumulator
instance : Inhabited (RegisterRef RegisterType (Vector (BitVec 2048) 32)) where
  default := .Reg _Z
instance : Inhabited (RegisterRef RegisterType (Vector (BitVec 64) 32)) where
  default := .Reg _Dclone
instance : Inhabited (RegisterRef RegisterType (Vector Bool 32)) where
  default := .Reg SPESampleAddressValid
instance : Inhabited (RegisterRef RegisterType (Vector Int 32)) where
  default := .Reg SPESampleCounter
instance : Inhabited (RegisterRef RegisterType (Vector (BitVec 32) 4)) where
  default := .Reg _ICV_AP0R
instance : Inhabited (RegisterRef RegisterType (Vector (BitVec 64) 4)) where
  default := .Reg ERRnFR
instance : Inhabited (RegisterRef RegisterType (Vector (BitVec 64) 5)) where
  default := .Reg RC
instance : Inhabited (RegisterRef RegisterType (Vector (BitVec 64) 64)) where
  default := .Reg Records_INF
instance : Inhabited (RegisterRef RegisterType (Vector (BitVec 8) 64)) where
  default := .Reg SPERecordData
instance : Inhabited (RegisterRef RegisterType (Vector (BitVec 64) 7)) where
  default := .Reg __ICACHE_CCSIDR_RESET
abbrev SailM := PreSailM RegisterType trivialChoiceSource exception

instance : Arch where
  va_size := 64
  pa := (BitVec 56)
  abort := Fault
  translation := (Option TranslationInfo)
  trans_start := TranslationStartInfo
  trans_end := AddressDescriptor
  fault := (Option FaultRecord)
  tlb_op := TLBIInfo
  cache_op := CacheRecord
  barrier := Barrier
  arch_ak := arm_acc_type
  sys_reg_id := Unit

