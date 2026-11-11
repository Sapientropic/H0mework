import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKCofinalFullBranchFibre.Source
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.GammaSource.OutsideHistory.Faithful

set_option autoImplicit false
set_option Elab.async false
noncomputable section

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalKCofinalFullBranchFibre.OutsideHistory

open BurnolPhysicalState OriginalRSourceJointContact.OutsideHistory
open SourceGeneratedActionObservationHistory

/-- The current read is the literal outside branch of the original pair. -/
def outsideRead : SourcePair →ₗ[ℂ] BurnolL2 := LinearMap.snd ℂ BurnolL2 BurnolL2

variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬ ∃ n : Nat, observation.coordinate = -2 * (n+1))
variable (half : OriginalKCombCalculation.Half observation)
local notation "A" => sourceStep observation nontrivial half
local notation "c" => burnolDivisionZeroCompletedMellinCoordinate observation half.down
local notation "R" => burnolDirectRightResolventCLM
local notation "T" => Inv.pairTotal

private theorem step_total (pair : SourcePair) : T (A pair) = R c (T pair) := by
  change P.physicalProjection (P.R observation nontrivial half (T pair)) +
    P.physicalRemainder (P.R observation nontrivial half (T pair)) = _
  exact (Full.split_complete _).trans (OriginalKCombCofinalRAction.original_R_direct observation nontrivial half _)

private theorem total_iterate (pair : SourcePair) (n : ℕ) :
    T ((A ^ n) pair) = (R c ^ n) (T pair) := by
  induction n with
  | zero => rfl
  | succ n prior =>
    rw [pow_succ', Module.End.mul_apply, step_total, prior, pow_succ']
    rfl

private theorem successor_read (pair : SourcePair) (n : ℕ) :
    outsideRead ((A ^ (n+1)) pair) = P.physicalRemainder ((R c ^ (n+1)) (T pair)) := by
  rw [pow_succ', Module.End.mul_apply]
  change P.physicalRemainder (R c (T ((A ^ n) pair))) = _
  rw [total_iterate, pow_succ']
  rfl

/-- The actual successor observations determine precisely the sum of the two old branches. -/
theorem successor_total_fibre (left right : SourcePair) :
    (∀ n : ℕ, outsideRead ((A ^ (n+1)) left) = outsideRead ((A ^ (n+1)) right)) ↔ T left = T right := by
  constructor
  · intro same
    apply Faithful.eq_of_same_successors c
    intro n
    simpa only [successor_read] using same n
  · intro same n
    simp only [successor_read, same]

private theorem kernel_le_total :
    LinearMap.ker (sourceMap A outsideRead) ≤ LinearMap.ker T := by
  intro pair invisible
  change sourceMap A outsideRead pair = 0 at invisible
  have same : sourceMap A outsideRead pair = sourceMap A outsideRead 0 := by rwa [map_zero]
  have total := (successor_total_fibre observation nontrivial half pair 0).mp
    (fun n => (source_fibre_iff A outsideRead pair 0).mp same (n+1))
  change T pair = 0
  simpa only [map_zero] using total

private def totalReadback : Model A outsideRead →ₗ[ℂ] BurnolL2 :=
  (LinearMap.ker (sourceMap A outsideRead)).liftQ T (kernel_le_total observation nontrivial half)

/-- The existing Model supplies the total from its successors and the second slot from its head. -/
def recoverPair : Model A outsideRead →ₗ[ℂ] SourcePair :=
  (totalReadback observation nontrivial half - modelReadout A outsideRead).prod
    (modelReadout A outsideRead)

theorem recover_projection (pair : SourcePair) :
    recoverPair observation nontrivial half (projection A outsideRead pair) = pair := by
  change (pair.1 + pair.2 - pair.2, pair.2) = pair
  exact Prod.ext (add_sub_cancel_right _ _) rfl

theorem complete_outside_injective : Function.Injective (sourceMap A outsideRead) := by
  intro left right same
  have model : projection A outsideRead left = projection A outsideRead right :=
    (model_fibre_iff A outsideRead left right).mpr ((source_fibre_iff A outsideRead left right).mp same)
  simpa only [recover_projection] using congrArg (recoverPair observation nontrivial half) model

end OriginalKCofinalFullBranchFibre.OutsideHistory
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
