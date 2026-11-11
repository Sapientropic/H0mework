import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalArithmeticState.ParticleWave.Fock.Runtime.SourceHistory.Operation.Calculation.Admission.Inquiry.Continuation.Residual.PaidNativeMethod.Source
import H0mework.Versions.R2.Fock.PrimeField.Action.Consumer
import H0mework.Versions.R2.Fock.Cofinal.OperationNative

set_option autoImplicit false
set_option Elab.async false
set_option maxErrors 1
set_option maxHeartbeats 600000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourcePhysicalCalculationAdmission.Inquiry.Continuation.Residual.PaidNativeMethod
open RootInquiryCompletion SourceOperationEffects SourceOperationExecution SourceOperationNative
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFock
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockOperationPrefix
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockNativeConsumer
open SourcePrimeHistoryRecovery SourcePrimeCompletion
open SourceGeneratedObservationAction SourceGeneratedScalarDifferentialResidual
attribute [local instance] zeroGroups
open private installedFaces paidQueryStock completePairOutput preserves_right from
 H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalArithmeticState.ParticleWave.Fock.Runtime.SourceHistory.Operation.Calculation.Admission.Inquiry.Continuation.Residual.PaidNativeMethod.Source

namespace J
export SourceOperationInquiry.Context.Faces.Execution.Activation.InventoryProgramme.Pair.Residual.Joint
 (complete_written_preserves)
end J
namespace Res
export SourceOperationInquiry.Context.Faces.Execution.Activation.InventoryProgramme.Pair.Residual
 (pairInventory priorPairInventory)
end Res

variable (sourceRuntime : LivingRuntimeState process)
abbrev physicalRuntime (count : Nat) := sourceRuntime.advance (11+count)
def actualValue (count : Nat) : W parentSort × W parentSort :=
 (R.actionResultAt (actualFrame sourceRuntime count) (configuration sourceRuntime)
  (S.actualOccurrence (actualFrame sourceRuntime count))).2.2.1
abbrev actualPair (count : Nat) := (actualValue sourceRuntime count).1

def installedWord (count : Nat) : Carrier process :=
 (N.input ((installedFaces sourceRuntime (actualFrame sourceRuntime count)).packet.2.1.paid)).environment
  (Sum.inr PUnit.unit) PUnit.unit

private theorem installed_word_readback (count : Nat) :
 installedWord sourceRuntime count = activeWord sourceRuntime count := rfl

private theorem runtime_at_eq (runtime : LivingRuntimeState process) : runtimeAt runtime.state = runtime :=
 LivingRuntimeState.ext (runtimeAt_state runtime.state)

private def PrimeStep (runtime : LivingRuntimeState process)
 (word nextWord : Carrier process) (prime : Nat.Primes) : Prop :=
 let payload := payloadAt runtime
 let read := sourceRow prime 0
 let joint := canonicalResidual (jointObservation payload.nativeRuntimeAction read) word
 payload.nativeRuntimeAction word = nextWord ∧
 jointCurrent payload.nativeRuntimeAction read joint = canonicalResidual read word ∧
 jointNext payload.nativeRuntimeAction read joint = canonicalResidual read nextWord ∧
 read nextWord = read word + (if cut prime ≤ 0 then 0 else word (cut prime-1)) ∧
 payload.nativeWrite = runtime.emittedOccurrence.2.write ∧
 payload.targetState = payload.sourceState+payload.forcedTrace ∧
 runtimeFacade.readoutAt runtime .particleWave = .inl ⟨activeAt runtime, payload⟩ ∧
 HEq runtime.tick.generated.wholeLedgerWriteBack
  (runtime.current.root.toAuthoritativeRoot.toLedgerRoot.generatedLedgerAt runtime.current.visit.current) ∧
 runtime.tick.nextCurrent = runtimeFacade.process.stateAt (runtimeFacade.process.successor runtime.state)

private theorem prime_at (runtime : LivingRuntimeState process) (prime : Nat.Primes) :
 PrimeStep runtime (point runtime) (point runtime.tick.next) prime := by
 have original := SourcePrimeObservationAction.runtime_action_joint_fibre_ledger_next runtime.state prime
 change PrimeStep (runtimeAt runtime.state) (point (runtimeAt runtime.state))
  (point (runtimeAt runtime.state).tick.next) prime at original
 exact Eq.mp (congrArg (fun actual => PrimeStep actual (point actual) (point actual.tick.next) prime)
  (runtime_at_eq runtime)) original

theorem actual_prime_step (count : Nat) (prime : Nat.Primes) :
 PrimeStep (physicalRuntime sourceRuntime count) (activeWord sourceRuntime count)
  (activeWord sourceRuntime (count+1)) prime := by
 rw [active_word_actual, active_word_actual]
 exact prime_at (physicalRuntime sourceRuntime count) prime

theorem installed_prime_step (count : Nat) (prime : Nat.Primes) :
 PrimeStep (physicalRuntime sourceRuntime count) (installedWord sourceRuntime count)
  (installedWord sourceRuntime (count+1)) prime := by
 rw [installed_word_readback, installed_word_readback]
 exact actual_prime_step sourceRuntime count prime

theorem actual_source_materialization (count : Nat) :
 materialization (activeWord sourceRuntime count) = (payloadAt (physicalRuntime sourceRuntime count)).sourceState := by
 rw [active_word_actual]
 exact materialization_current (physicalRuntime sourceRuntime count)

private structure PhysicalReadback (runtime : LivingRuntimeState process)
 (value : W parentSort × W parentSort) : Prop where
 target : value.1.1 = (payloadAt runtime).targetState
 target_index : value.1.1 = sourceStateAt (payloadAt runtime).nativeWrite.target
 sum : value.1.2 = (payloadAt runtime.tick.next).operationValues.sum
 update : value.1.1+value.1.2 = (payloadAt runtime.tick.next).targetState
 terms : value.1.2 =
  (evaluateEffectTerms operationEffectTrace (sourceFieldAt runtime.tick.next.current.visit.current)
   (sourceFieldAt (payloadAt runtime.tick.next).nativeWrite.target -
    sourceFieldAt runtime.tick.next.current.visit.current)).sum
 fibre : ∀ alternative : ParentCarrier,
  jointMeasurement alternative = jointMeasurement value.1.1 ↔
   alternative-value.1.1 ∈ JointMeasurementKernel

private theorem physical_readback (runtime : LivingRuntimeState process)
 (value : W parentSort × W parentSort)
 (generated : value = (((payloadAt runtime.tick.next).sourceState,
  (payloadAt runtime.tick.next).forcedTrace),0)) : PhysicalReadback runtime value := by
 have first := congrArg (fun item : W parentSort × W parentSort => item.1.1) generated
 have second := congrArg (fun item : W parentSort × W parentSort => item.1.2) generated
 have target : value.1.1 = (payloadAt runtime).targetState :=
  first.trans ((materialization_current runtime.tick.next).symm.trans (materialization_next runtime))
 have targetIndex : value.1.1 = sourceStateAt (payloadAt runtime).nativeWrite.target := by
  rw [(payloadAt runtime).nativeWrite_eq]
  exact target.trans (payloadAt runtime).targetState_eq
 have sum := second.trans (payloadAt runtime.tick.next).forcedTrace_sum
 have update := (congrArg₂ (· + ·) first second).trans (payloadAt runtime.tick.next).stateUpdate.symm
 have values := (payloadAt runtime.tick.next).operationValues_eq
 rw [(payloadAt runtime.tick.next).operationTrace_eq] at values
 have terms := sum.trans (congrArg List.sum values)
 have fibre : ∀ alternative : ParentCarrier,
  jointMeasurement alternative = jointMeasurement value.1.1 ↔
   alternative-value.1.1 ∈ JointMeasurementKernel := by
  intro alternative
  rw [target]
  exact (payloadAt runtime).inverseFibreLaw alternative
 exact { target := target, target_index := targetIndex, sum := sum,
         update := update, terms := terms, fibre := fibre }

private theorem actual_readback (count : Nat) :
 PhysicalReadback (physicalRuntime sourceRuntime count) (actualValue sourceRuntime count) :=
 physical_readback (physicalRuntime sourceRuntime count) (actualValue sourceRuntime count)
  (actual_native_value sourceRuntime count)

theorem actual_target_materialization (count : Nat) :
 (actualValue sourceRuntime count).1.1 = (payloadAt (physicalRuntime sourceRuntime count)).targetState :=
 (@PhysicalReadback.target (physicalRuntime sourceRuntime count) (actualValue sourceRuntime count) (actual_readback sourceRuntime count))

theorem actual_target_index (count : Nat) :
 (actualValue sourceRuntime count).1.1 = sourceStateAt (payloadAt (physicalRuntime sourceRuntime count)).nativeWrite.target :=
 (@PhysicalReadback.target_index (physicalRuntime sourceRuntime count) (actualValue sourceRuntime count) (actual_readback sourceRuntime count))

theorem actual_four_term_update (count : Nat) :
 (actualValue sourceRuntime count).1.2 = (payloadAt (physicalRuntime sourceRuntime count).tick.next).operationValues.sum ∧
 (actualValue sourceRuntime count).1.1+(actualValue sourceRuntime count).1.2 =
  (payloadAt (physicalRuntime sourceRuntime count).tick.next).targetState :=
 ⟨(@PhysicalReadback.sum (physicalRuntime sourceRuntime count) (actualValue sourceRuntime count) (actual_readback sourceRuntime count)), (@PhysicalReadback.update (physicalRuntime sourceRuntime count) (actualValue sourceRuntime count) (actual_readback sourceRuntime count))⟩

theorem actual_four_term_source (count : Nat) :
 (actualValue sourceRuntime count).1.2 =
  (evaluateEffectTerms operationEffectTrace
   (sourceFieldAt (physicalRuntime sourceRuntime count).tick.next.current.visit.current)
   (sourceFieldAt (payloadAt (physicalRuntime sourceRuntime count).tick.next).nativeWrite.target -
    sourceFieldAt (physicalRuntime sourceRuntime count).tick.next.current.visit.current)).sum :=
 (@PhysicalReadback.terms (physicalRuntime sourceRuntime count) (actualValue sourceRuntime count) (actual_readback sourceRuntime count))

theorem actual_target_fibre (count : Nat) (alternative : ParentCarrier) :
 jointMeasurement alternative = jointMeasurement (actualValue sourceRuntime count).1.1 ↔
 alternative-(actualValue sourceRuntime count).1.1 ∈ JointMeasurementKernel :=
 (@PhysicalReadback.fibre (physicalRuntime sourceRuntime count) (actualValue sourceRuntime count) (actual_readback sourceRuntime count)) alternative

private theorem paid_trace_written (frame : PhysicalFrame) :
 ∀ event ∈ (SourceOperationPaidRelations.exposure (R.actualMaterial frame (method sourceRuntime)).state.2).trace,
 event ∈ (PM.Generic.birthStock frame (sourceProgramme sourceRuntime)).trace := by
 have carried := PM.Generic.birth_keeps_callback frame (sourceProgramme sourceRuntime)
  (completePairOutput sourceRuntime frame) rfl
 intro event present
 exact carried event (preserves_right _ _ event
  ((SourceHistoryCommon.parallel_left _ _ _).1 event present))

private theorem born_stock_consumed (frame : PhysicalFrame) :
 ∀ event ∈ (PM.Generic.birthStock frame (sourceProgramme sourceRuntime)).trace,
 event ∈ (PM.completeQueryWritten 0 (S.nextBorn frame (configuration sourceRuntime))).trace := by
 let born := S.nextBorn frame (configuration sourceRuntime)
 have pairEq : (A.epoch born).pairInventory = some (PM.Generic.birthStock frame (sourceProgramme sourceRuntime)) :=
  PM.Generic.birth_stock frame (sourceProgramme sourceRuntime)
 intro event present
 apply J.complete_written_preserves (I.seed born) (A.epoch born) (S.actualOccurrence born) event
 unfold Res.pairInventory Res.priorPairInventory
 rw [pairEq]
 exact (SourceHistoryCommon.parallel_left _ _ _).1 event
  ((SourceHistoryCommon.parallel_left _ _ _).1 event present)

private theorem native_trace_consumed (frame : PhysicalFrame) :
 ∀ event ∈ (SourceOperationPaidRelations.exposure (R.actualMaterial frame (method sourceRuntime)).state.2).trace,
 event ∈ (PM.completeQueryWritten 0 (S.nextBorn frame (configuration sourceRuntime))).trace := by
 intro event present
 exact born_stock_consumed sourceRuntime frame event (paid_trace_written sourceRuntime frame event present)

private theorem source_segment (start fuel : Nat) :
 (fun word : Carrier process => sourceAction process word)^[fuel] (activeWord sourceRuntime start) =
 activeWord sourceRuntime (start+fuel) := by
 induction fuel with
 | zero => rfl
 | succ fuel prior =>
  rw [Function.iterate_succ_apply', prior]
  simpa only [Nat.add_assoc] using next_active_word sourceRuntime (start+fuel)

def methodHistory (start : Nat) :=
 let cfg := configuration sourceRuntime
 let receipt := S.Complete.receipt cfg (initial sourceRuntime) start
 SourceNativeInquiryRuntime.runFrom (runtime := inquiry sourceRuntime) (receipt.1+1)
  ((inquiry sourceRuntime).stateAt start)

-- The complete source word, query value and physical consumers use the same selected stop.
def physical_source_method (start : Nat) (prime : Nat.Primes) :=
 let cfg := configuration sourceRuntime
 let receipt := S.Complete.receipt cfg (initial sourceRuntime) start
 let stop := start+receipt.1
 let physical := physicalRuntime sourceRuntime stop
 let native := SourceGeneratedRuntimeMaterialStageAt.generate physical
 let selected := S.Complete.atReceipt cfg (initial sourceRuntime) start
 PProd.mk (source_target_consumer sourceRuntime start) <|
 PProd.mk ((installedFaces sourceRuntime (actualFrame sourceRuntime stop)).source_readback) <|
 PProd.mk (installed_word_readback sourceRuntime stop) <|
 PProd.mk (active_word_actual sourceRuntime stop) <|
 PProd.mk (next_active_word sourceRuntime stop) <|
 PProd.mk (installed_prime_step sourceRuntime stop prime) <|
 PProd.mk (actual_native_value sourceRuntime stop) <|
 PProd.mk (paid_trace_written sourceRuntime selected) <|
 PProd.mk (born_stock_consumed sourceRuntime selected) <|
 PProd.mk (native_trace_consumed sourceRuntime selected) <|
 PProd.mk (actual_source_materialization sourceRuntime stop) <|
 PProd.mk (actual_readback sourceRuntime stop) <|
 PProd.mk ((payloadAt physical).nativeRuntimeAction_target) <|
 PProd.mk ((payloadAt physical).sourceOccurrence_eq) <|
 PProd.mk (point_factorizes physical) <|
 PProd.mk (material_next_is_native_target native) <|
 PProd.mk (source_segment sourceRuntime start (receipt.1+1))
 (methodHistory sourceRuntime start)

def finite_physical_source_method (fuel : Nat) := (inquiry sourceRuntime).run fuel

end SourcePhysicalCalculationAdmission.Inquiry.Continuation.Residual.PaidNativeMethod
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
