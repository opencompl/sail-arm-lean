import Armv9.String

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

/-- Type quantifiers: k_n : Nat, k_n ∈ {8, 16, 32, 64, 128} -/
def reverse_endianness (xs : (BitVec k_n)) : (BitVec k_n) :=
  let len := (Sail.BitVec.length xs)
  bif (len == 8)
  then xs
  else
    (bif (len == 16)
    then ((Sail.BitVec.extractLsb xs 7 0) ++ (Sail.BitVec.extractLsb xs 15 8))
    else
      (bif (len == 32)
      then
        ((Sail.BitVec.extractLsb xs 7 0) ++ ((Sail.BitVec.extractLsb xs 15 8) ++ ((Sail.BitVec.extractLsb
                xs 23 16) ++ (Sail.BitVec.extractLsb xs 31 24))))
      else
        (bif (len == 64)
        then
          ((Sail.BitVec.extractLsb xs 7 0) ++ ((Sail.BitVec.extractLsb xs 15 8) ++ ((Sail.BitVec.extractLsb
                  xs 23 16) ++ ((Sail.BitVec.extractLsb xs 31 24) ++ ((Sail.BitVec.extractLsb xs 39
                      32) ++ ((Sail.BitVec.extractLsb xs 47 40) ++ ((Sail.BitVec.extractLsb xs 55 48) ++ (Sail.BitVec.extractLsb
                          xs 63 56))))))))
        else
          ((Sail.BitVec.extractLsb xs 7 0) ++ ((Sail.BitVec.extractLsb xs 15 8) ++ ((Sail.BitVec.extractLsb
                  xs 23 16) ++ ((Sail.BitVec.extractLsb xs 31 24) ++ ((Sail.BitVec.extractLsb xs 39
                      32) ++ ((Sail.BitVec.extractLsb xs 47 40) ++ ((Sail.BitVec.extractLsb xs 55 48) ++ ((Sail.BitVec.extractLsb
                            xs 63 56) ++ ((Sail.BitVec.extractLsb xs 71 64) ++ ((Sail.BitVec.extractLsb
                                xs 79 72) ++ ((Sail.BitVec.extractLsb xs 87 80) ++ ((Sail.BitVec.extractLsb
                                    xs 95 88) ++ ((Sail.BitVec.extractLsb xs 103 96) ++ ((Sail.BitVec.extractLsb
                                        xs 111 104) ++ ((Sail.BitVec.extractLsb xs 119 112) ++ (Sail.BitVec.extractLsb
                                          xs 127 120)))))))))))))))))))

