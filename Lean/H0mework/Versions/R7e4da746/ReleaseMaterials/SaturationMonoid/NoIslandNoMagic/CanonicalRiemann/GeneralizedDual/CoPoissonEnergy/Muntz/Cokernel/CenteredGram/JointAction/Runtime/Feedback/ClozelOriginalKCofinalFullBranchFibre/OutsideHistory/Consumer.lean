import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKCofinalFullBranchFibre.OutsideHistory.Kernel

set_option autoImplicit false
set_option Elab.async false
noncomputable section

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalKCofinalFullBranchFibre.OutsideHistory

open BurnolPhysicalState SourceGeneratedActionObservationHistory
open OriginalKDirectRCofinalDivision.DirectRDivisionControls (actual_division_action_same_root)

variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬ ∃ n : Nat, observation.coordinate = -2 * (n+1))
variable (half : OriginalKCombCalculation.Half observation) (depth ordinal : ℕ)
local notation "A" => sourceStep observation nontrivial half
local notation "source" => D.input observation nontrivial half depth

/-- Every bound reads the original cofinal second slot with its literal offset. -/
theorem actual_recorded_outside (bound : ℕ) (index : Fin (bound+1)) :
    stageRead A outsideRead bound (sourceMap A outsideRead (source ordinal)) index =
      (source (ordinal+index.val)).2 := by
  rw [source_reads_stage, actual_source_iterate]
  rfl

/-- The independent outside history recovers the current source pair. The same Model update gives
its actual next pair, with the original Division action, position gap, relation, and whole. -/
theorem actual_division_recovered_from_outside (candidate : SourcePair)
    (read : ∀ n : ℕ, stageRead A outsideRead n (sourceMap A outsideRead candidate) (Fin.last n) =
      (source (ordinal+n)).2) :
    candidate = source ordinal ∧
    recoverPair observation nontrivial half
      (modelAction A outsideRead (projection A outsideRead candidate)) = source (ordinal+1) ∧
    type_of% (actual_division_action_same_root observation nontrivial half depth ordinal) := by
  have exactSource : candidate = source ordinal := by
    apply complete_outside_injective observation nontrivial half
    apply (source_fibre_iff A outsideRead candidate (source ordinal)).mpr
    intro n
    have same := (read n).trans
      (actual_recorded_outside observation nontrivial half depth ordinal n (Fin.last n)).symm
    rw [source_reads_stage, source_reads_stage] at same
    exact same
  refine ⟨exactSource, ?_, actual_division_action_same_root observation nontrivial half depth ordinal⟩
  rw [modelAction_source, recover_projection, exactSource, actual_source_step]

-- Keep the rooted disposition's full dependent type out of the editor suggestion index.
run_cmd Lean.modifyEnv fun env =>
  Lean.LibrarySuggestions.nameDenyListExt.addEntry env "actual_division_recovered_from_outside"

end OriginalKCofinalFullBranchFibre.OutsideHistory
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
