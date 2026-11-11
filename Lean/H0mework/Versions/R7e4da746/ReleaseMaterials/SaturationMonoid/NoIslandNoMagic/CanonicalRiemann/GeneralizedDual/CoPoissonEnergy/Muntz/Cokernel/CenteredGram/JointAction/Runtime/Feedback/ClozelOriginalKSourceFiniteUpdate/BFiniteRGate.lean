import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKSourceFiniteUpdate.BFiniteRReceipt
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKSourceFiniteUpdate.BFiniteRControls

set_option autoImplicit false
set_option Elab.async false
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1400000
noncomputable section

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalKSourceFiniteUpdate.OriginalBFiniteRAction

open Complex MeasureTheory BurnolPhysicalState
open OriginalRieszFiniteSource OriginalKSourceResolventReconstruction
open OriginalKFullAdjointSource
open scoped InnerProductSpace

private theorem fixed_nonnegative : 0 ≤ Real.log stageZeroSonineQ := by
  apply Real.log_nonneg
  norm_num [stageZeroSonineQ]

variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬∃ n:Nat,observation.coordinate=-2*(n+1))
variable (half : OriginalKCombCalculation.Half observation) (depth ordinal : Nat)
local notation "c" => OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half
local notation "h" => Real.log stageZeroSonineQ
local notation "receipt" => installedOriginalKReceiptAt observation nontrivial half.down

include depth ordinal

/-- The deleted physical source is priced on the same installed residual. -/
theorem actual_B_R_deleted_loss_effect :
    (receipt).fixedResidual - deletedSourceResidual c h =
      inner ℂ (sourceAdjointField c) (sourceLossInput c h) := by
  have actual := (actual_B_R_source_on_original_whole_next
    observation nontrivial half depth ordinal).2.2.2.1
  have kernel := (actual_finite_source_on_original_whole_next
    observation nontrivial half depth ordinal).2.1
  rw [kernel] at actual
  have original := original_fixedResidual_calculated_source c observation.mathlibZero h fixed_nonnegative rfl
  have same : (receipt).fixedResidual = burnolPaFixedShiftResidual c observation.mathlibZero :=
    actual.trans original.symm
  rw [same]
  exact original_residual_deleted_loss_effect c observation.mathlibZero h fixed_nonnegative rfl

/-- The original whole-next consumes the complete source action, actual R omission price and source-preserving zero shift. -/
theorem actual_B_R_source_gate :
    type_of% (actual_B_R_source_on_original_whole_next observation nontrivial half depth ordinal) ∧
    type_of% (deleted_loss_full_R_effect c h fixed_nonnegative) ∧
    type_of% (actual_B_R_deleted_loss_effect observation nontrivial half depth ordinal) ∧
    type_of% (full_R_source_zero_override c) :=
  ⟨actual_B_R_source_on_original_whole_next observation nontrivial half depth ordinal,
    deleted_loss_full_R_effect c h fixed_nonnegative,
    actual_B_R_deleted_loss_effect observation nontrivial half depth ordinal,
    full_R_source_zero_override c⟩

run_cmd Lean.modifyEnv fun env => Lean.LibrarySuggestions.nameDenyListExt.addEntry env "actual_B_R_source_gate"

end OriginalKSourceFiniteUpdate.OriginalBFiniteRAction
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
