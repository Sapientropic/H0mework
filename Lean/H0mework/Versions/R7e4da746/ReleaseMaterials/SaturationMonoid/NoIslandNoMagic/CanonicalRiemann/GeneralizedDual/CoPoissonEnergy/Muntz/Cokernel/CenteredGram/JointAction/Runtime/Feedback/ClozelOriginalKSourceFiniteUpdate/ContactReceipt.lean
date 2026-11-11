import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKSourceFiniteUpdate.ContactAction
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKSourceFiniteUpdate.Gate

set_option autoImplicit false
set_option Elab.async false
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKSourceFiniteUpdate
open Complex MeasureTheory Set BurnolPhysicalState
open OriginalRieszSource OriginalRieszFiniteSource OriginalKFixedBoundarySourceFibre
open scoped InnerProductSpace
variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬∃ n:Nat,observation.coordinate=-2*(n+1))
variable (half : OriginalKCombCalculation.Half observation) (depth ordinal : Nat)
local notation "c" => OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half
local notation "h" => Real.log stageZeroSonineQ
local notation "receipt" => installedOriginalKReceiptAt observation nontrivial half.down

/-- Source endpoint generation replaces both actual contact slots on the same installed mathematical reads. -/
def consume_actual_contact_source {Result : Sort u}
    (consumer :
      (contactSourceBoundary c h = sourceFiniteBoundary c h) →
      ((receipt).fixedResidual = -inner ℂ (receipt).kernel (sourceFiniteBoundary c h)) →
      (((receipt).boundary h : BurnolL2) = (burnolEvenAmbientProjection (sourceFiniteBoundary c h) : BurnolL2)) →
      (sourceFiniteBoundary c h - ((receipt).boundary h : BurnolL2) = sourceProjectionLoss c h) →
      (‖sourceFiniteBoundary c h‖^2 = ‖((receipt).boundary h : BurnolL2)‖^2 + ‖sourceProjectionLoss c h‖^2) → Result) : Result :=
  consumer (contact_source_word_actual c h)
    (actual_finite_source_on_original_whole_next observation nontrivial half depth ordinal).2.2.2.1
    (actual_finite_source_on_original_whole_next observation nontrivial half depth ordinal).2.2.2.2.1
    (actual_finite_source_on_original_whole_next observation nontrivial half depth ordinal).2.2.2.2.2.2.1
    (actual_finite_source_on_original_whole_next observation nontrivial half depth ordinal).2.2.2.2.2.2.2

/-- The complete original whole-next consumes the explicit compact endpoints, retaining both slots and every physical fee. -/
theorem actual_contact_source_on_original_whole_next :
    type_of% (actual_finite_source_gate observation nontrivial half depth ordinal) ∧
    (contactSourceBoundary c h = sourceFiniteBoundary c h) ∧
    ((receipt).fixedResidual = -inner ℂ (receipt).kernel (contactSourceBoundary c h)) ∧
    (((receipt).boundary h : BurnolL2) = (burnolEvenAmbientProjection (contactSourceBoundary c h) : BurnolL2)) ∧
    (contactSourceBoundary c h - ((receipt).boundary h : BurnolL2) = sourceProjectionLoss c h) ∧
    (‖contactSourceBoundary c h‖^2 = ‖((receipt).boundary h : BurnolL2)‖^2 + ‖sourceProjectionLoss c h‖^2) := by
  refine ⟨actual_finite_source_gate observation nontrivial half depth ordinal,?_⟩
  apply consume_actual_contact_source observation nontrivial half depth ordinal
  intro word price boundary loss energy
  rw [←word] at price boundary loss energy
  exact ⟨word,price,boundary,loss,energy⟩

run_cmd Lean.modifyEnv fun env => Lean.LibrarySuggestions.nameDenyListExt.addEntry env "actual_contact_source_on_original_whole_next"

end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKSourceFiniteUpdate
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
