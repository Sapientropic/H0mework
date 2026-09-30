import H0mework.Fock.CopyGraph.SharedNextPhaseSupport
import H0mework.Fock.CopyGraph.Missing

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceCopyPhaseRecovery

open SourceCopyCurrentCoordinates (Coordinates maximumIndex sourceRead realize residual jointObserver jointModelEquiv)
open SourceCopySharedNext (NextPacket gain nativePacket)
open SourceCopyNativeModelStep (sourceValue)
open SourceCopyTimeModel (finitePhases time hilbert)
open SourceCopyRecordedRecurrence (cutoff)
open SourceGeneratedAcquisitionContinuation SourceGeneratedActionObservationHistory
open SourceGeneratedActionWords.Fock SourceGeneratedActionWords.Fock.Dynamic
open SourceGeneratedRuntimeHistoryProbability SourceWeightedRecovery
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime
noncomputable section
attribute [local instance] SourceCompleteGraph.completeUniform SourceCompleteGraph.completeMeasurable
  SourceCompleteGraph.completeBorel SourceCompleteGraph.completeT2

theorem no_model_decoder_without_phase (runtime : LivingRuntimeState process)
    (omitted : Fin ((maximumIndex runtime.tick.next).val + 1)) :
    ¬ ∃ decoder : Model SourceJointClockGraph.action.toLinearMap (jointObserver runtime) →
      ({ phase : Fin ((maximumIndex runtime.tick.next).val + 1) // phase ≠ omitted } → SourceJointClockGraph.Carrier) →
        Model SourceJointClockGraph.action.toLinearMap (jointObserver runtime.tick.next),
      ∀ target : SourceJointClockGraph.Carrier,
        decoder (projection SourceJointClockGraph.action.toLinearMap (jointObserver runtime) target)
          (observedWithout runtime omitted (finitePhases runtime.tick.next (maximumIndex runtime.tick.next) 0 (SourceJointClockGraph.action target))) =
          projection SourceJointClockGraph.action.toLinearMap (jointObserver runtime.tick.next) (SourceJointClockGraph.action target) := by
  rintro ⟨decoder, recovers⟩
  apply no_decoder_without_phase runtime omitted
  refine ⟨fun previous packet => jointModelEquiv runtime.tick.next (decoder ((jointModelEquiv runtime).symm previous) packet), ?_⟩
  intro target
  dsimp only
  rw [← SourceCopyCurrentCoordinates.joint_model_source runtime target, LinearEquiv.symm_apply_apply,
    recovers, SourceCopyCurrentCoordinates.joint_model_source]

theorem phase_conditional (runtime : LivingRuntimeState process) (target : SourceJointClockGraph.Carrier)
    (phase : Fin ((maximumIndex runtime.tick.next).val + 1)) (atom : Complete.Carrier 0)
    (supported : atom ∈ (observed (historyPMF (inventoryBound runtime.tick.next)) (Hilbert.read 0 (inventoryBound runtime.tick.next))).support) :
    SourceColumnForcing.forcing (inventoryBound runtime.tick.next) (inventoryBound runtime.tick.next) (maximumIndex runtime.tick.next)
      (Hilbert.read 0 (inventoryBound runtime.tick.next))
      (SourceCopyGraph.action (inventoryBound runtime.tick.next) (maximumIndex runtime.tick.next)
        (finitePhases runtime.tick.next (maximumIndex runtime.tick.next) 0 (SourceJointClockGraph.action target) phase)) atom =
      conditionalMean (historyPMF (inventoryBound runtime.tick.next)) (Hilbert.read 0 (inventoryBound runtime.tick.next))
        (SourceColumnForcing.samples (inventoryBound runtime.tick.next) (inventoryBound runtime.tick.next) (maximumIndex runtime.tick.next)
          (time phase.val (SourceJointClockGraph.action target))) atom supported := by
  have forcing : SourceColumnForcing.forcing (inventoryBound runtime.tick.next) (inventoryBound runtime.tick.next) (maximumIndex runtime.tick.next)
      (Hilbert.read 0 (inventoryBound runtime.tick.next))
      (SourceCopyGraph.action (inventoryBound runtime.tick.next) (maximumIndex runtime.tick.next)
        (finitePhases runtime.tick.next (maximumIndex runtime.tick.next) 0 (SourceJointClockGraph.action target) phase)) =
      SourceColumnForcing.forcing (inventoryBound runtime.tick.next) (inventoryBound runtime.tick.next) (maximumIndex runtime.tick.next)
        (Hilbert.read 0 (inventoryBound runtime.tick.next)) (time phase.val (SourceJointClockGraph.action target)) :=
    SourceCopySharedNext.packet_forcing runtime.tick.next (maximumIndex runtime.tick.next) 0
      (Hilbert.read 0 (inventoryBound runtime.tick.next)) (SourceJointClockGraph.action target) phase
  rw [forcing]
  exact SourceColumnForcing.forcing_conditional _ _ _ _ _ atom supported

theorem native_gain_zero (runtime : LivingRuntimeState process) :
    gain runtime (SourceCopyCurrentCoordinates.shared runtime) (nativePacket runtime) = 0 := by
  have budget := SourceCopySharedNext.native_budget runtime
  rw [native_tail_zero runtime, native_tail_zero runtime.tick.next, norm_zero, zero_pow (by decide : 2 ≠ 0), add_zero] at budget
  apply norm_eq_zero.mp
  apply sq_eq_zero_iff.mp
  dsimp only [nativePacket]
  with_reducible exact budget

theorem native_phase_zero (runtime : LivingRuntimeState process)
    (phase : Fin ((maximumIndex runtime.tick.next).val + 1)) :
    phaseGain runtime (SourceCopyCurrentCoordinates.shared runtime) (nativePacket runtime) phase = 0 := by
  simp only [phaseGain, native_gain_zero, map_zero, slice]
  convert map_zero (realize runtime.tick.next (maximumIndex runtime.tick.next) 0) using 1
  apply congrArg (realize runtime.tick.next (maximumIndex runtime.tick.next) 0)
  apply Prod.ext
  · funext coordinate
    simp
  · rfl

end
end SourceCopyPhaseRecovery
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
