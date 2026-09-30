import H0mework.Versions.X.Fock.CopyGraph.DecoderComparison
import H0mework.Versions.X.Fock.CopyGraph.DecoderInteraction
import H0mework.Versions.X.Fock.CopyGraph.ConditionalField

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceConditionalGraphDecoder

open SourceWeightedRecovery SourceGeneratedRuntimeHistoryProbability
open SourceGeneratedAcquisitionMeasure SourceGeneratedAcquisitionJoint SourceGeneratedJointClockGraph
open SourceGeneratedActionWords.Fock.OriginalHilbert
open SourceCopyProgram (Index)
noncomputable section
universe u
variable {Observed : Type u} [MeasurableSpace Observed]

def realizeObserved (depth bound : Nat) (observer : Fin (bound + 1) → Observed) :
    Space (observed (historyPMF bound) observer) →L[ℂ] FieldSpace depth bound :=
  (Actor.currentTransfer depth bound).comp (pullback (historyPMF bound) observer).toContinuousLinearMap

def fieldDecode (depth bound : Nat) (index : Index depth) (observer : Fin (bound + 1) → Observed) :
    SourceJointClockGraph.Carrier →L[ℂ] FieldSpace depth bound :=
  (realizeObserved depth bound observer).comp (decode depth bound index observer)

theorem realized_samples (depth bound : Nat) (observer : Fin (bound + 1) → Observed)
    (value : Space (observed (historyPMF bound) observer)) :
    Actor.currentPullback depth bound (realizeObserved depth bound observer value) =
      pullback (historyPMF bound) observer value := actor_transfer_samples depth bound _

theorem realized_action (depth bound : Nat) (index : Index depth) (observer : Fin (bound + 1) → Observed)
    (value : Space (observed (historyPMF bound) observer)) :
    SourceCopyGraph.action depth index (fieldRead depth bound (realizeObserved depth bound observer value)) =
      action depth bound index observer value :=
  (SourceConditionalGraph.copy_transferred depth bound index _).trans (action_source depth bound index observer value).symm

theorem original_minimum (depth bound : Nat) (index : Index depth) (observer : Fin (bound + 1) → Observed)
    (target : SourceJointClockGraph.Carrier) :
    fieldDecode depth bound index observer target ∈ Set.range (realizeObserved depth bound observer) ∧
      IsMinOn (fun proposal : FieldSpace depth bound =>
        ‖target - SourceCopyGraph.action depth index (fieldRead depth bound proposal)‖ ^ 2)
        (Set.range (realizeObserved depth bound observer)) (fieldDecode depth bound index observer target) := by
  constructor
  · exact ⟨decode depth bound index observer target, rfl⟩
  · intro proposal represented
    rcases represented with ⟨data, rfl⟩
    change ‖target - SourceCopyGraph.action depth index
      (fieldRead depth bound (realizeObserved depth bound observer (decode depth bound index observer target)))‖ ^ 2 ≤ _
    dsimp only
    rw [realized_action, realized_action]
    exact (isMinOn_univ_iff.mp (source_minimum depth bound index observer target)) data

theorem original_reconstruction (depth bound : Nat) (index : Index depth) (observer : Fin (bound + 1) → Observed)
    (target : SourceJointClockGraph.Carrier) :
    SourceCopyGraph.action depth index (fieldRead depth bound (fieldDecode depth bound index observer target)) +
      residual depth bound index observer target = target := by
  change SourceCopyGraph.action depth index
    (fieldRead depth bound (realizeObserved depth bound observer (decode depth bound index observer target))) + _ = target
  rw [realized_action]
  exact reconstruction depth bound index observer target

theorem source_residual (depth bound : Nat) (index : Index depth) (observer : Fin (bound + 1) → Observed)
    (value : Space (historyPMF bound)) :
    residual depth bound index observer (SourceConditionalGraph.copyRead depth bound index value) =
      SourceConditionalGraph.copyRead depth bound index
        (value - pullback (historyPMF bound) observer (decode depth bound index observer (SourceConditionalGraph.copyRead depth bound index value))) := by
  have whole := reconstruction depth bound index observer (SourceConditionalGraph.copyRead depth bound index value)
  rw [action_source] at whole
  rw [map_sub]
  exact eq_sub_iff_add_eq.mpr ((add_comm _ _).trans whole)

theorem original_residual (depth bound : Nat) (index : Index depth) (observer : Fin (bound + 1) → Observed)
    (value : FieldSpace depth bound) :
    residual depth bound index observer (SourceCopyGraph.action depth index (fieldRead depth bound value)) =
      SourceCopyGraph.action depth index (fieldRead depth bound
        (value - fieldDecode depth bound index observer (SourceCopyGraph.action depth index (fieldRead depth bound value)))) := by
  have whole := original_reconstruction depth bound index observer (SourceCopyGraph.action depth index (fieldRead depth bound value))
  rw [map_sub, map_sub]
  exact eq_sub_iff_add_eq.mpr ((add_comm _ _).trans whole)

theorem normal_moments (depth bound : Nat) (index : Index depth) (observer : Fin (bound + 1) → Observed)
    (value : Space (historyPMF bound)) (proposal : Space (observed (historyPMF bound) observer)) :
    let remaining := value - pullback (historyPMF bound) observer
      (decode depth bound index observer (SourceConditionalGraph.copyRead depth bound index value))
    inner ℂ (pullback (historyPMF bound) observer proposal) remaining +
      starRingEnd ℂ (SourceSuccessorBoundary.mass ℂ (SourceHistoryWord.word bound (pullback (historyPMF bound) observer proposal))) *
        SourceSuccessorBoundary.mass ℂ (SourceHistoryWord.word bound remaining) +
      (SourceCopyProgram.scale depth index : ℂ) ^ 2 *
        (starRingEnd ℂ (SourceClockComplex.clock (SourceHistoryWord.word bound (pullback (historyPMF bound) observer proposal))) *
          SourceClockComplex.clock (SourceHistoryWord.word bound remaining)) = 0 := by
  have normal := source_orthogonal depth bound index observer (SourceConditionalGraph.copyRead depth bound index value) proposal
  rw [source_residual, action_source, copy_inner] at normal
  exact normal

theorem original_residual_energy (depth bound : Nat) (index : Index depth) (observer : Fin (bound + 1) → Observed)
    (value : FieldSpace depth bound) :
    let remaining := value - fieldDecode depth bound index observer
      (SourceCopyGraph.action depth index (fieldRead depth bound value))
    ‖residual depth bound index observer (SourceCopyGraph.action depth index (fieldRead depth bound value))‖ ^ 2 =
      ‖remaining‖ ^ 2 + (bound + 1 : ℝ) *
        ‖∫ actor, Actor.currentPullback depth bound remaining actor ∂(historyPMF bound).toMeasure‖ ^ 2 +
        (SourceCopyProgram.scale depth index : ℝ) ^ 2 * ‖SourceClockComplex.clock (word depth bound remaining)‖ ^ 2 := by
  rw [original_residual]
  exact SourceCopyGraph.original_copy_energy depth bound index _

theorem original_residual_realization (round depth bound : Nat) (index : Index depth)
    (observer : Fin (bound + 1) → Observed) (value : FieldSpace depth bound) :
    let remaining := value - fieldDecode depth bound index observer
      (SourceCopyGraph.action depth index (fieldRead depth bound value))
    let copied := SourceCopyGraph.complexAction depth index (word depth bound remaining)
    fieldRead (SourceGeneratedAcquisitionJoint.depth (sourceRound round copied))
      (SourceGeneratedAcquisitionContinuation.inventoryBound (sourceRound round copied)) (realizeWord round copied) =
        residual depth bound index observer (SourceCopyGraph.action depth index (fieldRead depth bound value)) := by
  exact (SourceCopyGraph.original_copy_realization round depth bound index _).trans
    (original_residual depth bound index observer value).symm

end
end SourceConditionalGraphDecoder
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
