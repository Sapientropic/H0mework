import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKSourceFiniteUpdate.BFiniteRSource
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKSourceFiniteUpdate.ContactGate
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKSourceReciprocity.HSource

set_option autoImplicit false
set_option Elab.async false
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1400000
noncomputable section
universe u

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalKSourceFiniteUpdate.OriginalBFiniteRAction

open Complex MeasureTheory BurnolPhysicalState
open OriginalRieszSource OriginalRieszFiniteSource
open OriginalKSourceResolventReconstruction OriginalKSourceGramAction OriginalKFixedBoundarySourceFibre
open OriginalKFullAdjointSource OriginalKDirectRCofinalOutsideVolterraSource
open OriginalKSourceReciprocity
open scoped InnerProductSpace

private theorem fixed_shift_nonnegative : 0 ≤ Real.log stageZeroSonineQ := by
  apply Real.log_nonneg
  norm_num [stageZeroSonineQ]

variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬∃ n:Nat,observation.coordinate=-2*(n+1))
variable (half : OriginalKCombCalculation.Half observation) (depth ordinal : Nat)
local notation "c" => OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half
local notation "h" => Real.log stageZeroSonineQ
local notation "receipt" => installedOriginalKReceiptAt observation nontrivial half.down

/-- The original installed reads consume the actual new B input and original-R effect. -/
def consume_actual_B_R_source {Result : Sort u}
    (consumer :
      (calculatedBoundaryInput c h = boundaryInput c h) →
      (calculatedSourceNormal c h = contactSourceBoundary c h) →
      (∀ i j : Fin 2, sourceOrbitGram c h i j = calculatedSourceGram c h i j) →
      type_of% (actual_contact_source_on_original_whole_next observation nontrivial half depth ordinal) →
      ((receipt).kernel = generatedK c) →
      type_of% (reciprocal_K_full_inventory c observation.mathlibZero) → Result) : Result :=
  consumer (calculated_boundary_input_actual c h fixed_shift_nonnegative)
    (calculated_source_normal_actual c h fixed_shift_nonnegative)
    (fun i j => (source_finite_Gram_action c h i j).symm.trans
      (calculated_source_Gram_actual c h fixed_shift_nonnegative i j))
    (actual_contact_source_on_original_whole_next observation nontrivial half depth ordinal)
    (actual_finite_source_on_original_whole_next observation nontrivial half depth ordinal).2.1
    (reciprocal_K_full_inventory c observation.mathlibZero)

/-- No finite f0 primitive is supplied to the original R calculation or its whole-next consumer. -/
theorem actual_B_R_source_on_original_whole_next :
    type_of% (actual_contact_source_gate observation nontrivial half depth ordinal) ∧
    (calculatedBoundaryInput c h = boundaryInput c h) ∧
    ((receipt).fixedResidual = ∑ i : Fin 2, ∑ j : Fin 2,
      star (sourceCoefficients c i) * sourceCoefficients c j * calculatedSourceGram c h i j) ∧
    ((receipt).fixedResidual = -inner ℂ (receipt).kernel (calculatedSourceNormal c h)) ∧
    (((receipt).boundary h : BurnolL2) =
      (burnolEvenAmbientProjection (calculatedSourceNormal c h) : BurnolL2)) ∧
    (calculatedSourceNormal c h - ((receipt).boundary h : BurnolL2) = sourceProjectionLoss c h) ∧
    (‖calculatedSourceNormal c h‖^2 = ‖((receipt).boundary h : BurnolL2)‖^2 +
      ‖sourceProjectionLoss c h‖^2) ∧
    ((burnolEvenAmbientProjection (sourceReciprocity c (receipt).kernel) : BurnolL2) =
        -fourierL2 ((receipt).kernel + sourceRate c • hPhysicalField c) ∧
      (OriginalKCombCofinalPaAction.E (sourceReciprocity c (receipt).kernel) : BurnolL2) =
        -sourceRate c • fourierL2 (paAdjointSource c : BurnolL2) ∧
      (OriginalKCombCofinalPaAction.Q (sourceReciprocity c (receipt).kernel) : BurnolL2) =
        -fourierL2 ((receipt).kernel + sourceRate c • hQField c) ∧
      sourceReciprocity c (receipt).kernel -
        (burnolEvenAmbientProjection (sourceReciprocity c (receipt).kernel) : BurnolL2) =
        -sourceRate c • fourierL2 (hQuarterAmplitude c • hPowerPhysicalCorrection c) ∧
      ‖sourceReciprocity c (receipt).kernel‖^2 -
        ‖(burnolEvenAmbientProjection (sourceReciprocity c (receipt).kernel) : BurnolL2)‖^2 =
        ‖sourceRate c‖^2 * ‖hQuarterAmplitude c‖^2 * ‖hPowerPhysicalCorrection c‖^2) := by
  refine ⟨actual_contact_source_gate observation nontrivial half depth ordinal, ?_⟩
  apply consume_actual_B_R_source observation nontrivial half depth ordinal
  intro input word matrix prior kernel stock
  have matrixPrice := prior.1.1.2.2.1
  simp only [matrix] at matrixPrice
  have price := prior.2.2.1
  have boundary := prior.2.2.2.1
  have loss := prior.2.2.2.2.1
  have energy := prior.2.2.2.2.2
  rw [←word] at price boundary loss energy
  rw [←kernel] at stock
  exact ⟨input, matrixPrice, price, boundary, loss, energy, stock⟩

run_cmd Lean.modifyEnv fun env => Lean.LibrarySuggestions.nameDenyListExt.addEntry env "actual_B_R_source_on_original_whole_next"

end OriginalKSourceFiniteUpdate.OriginalBFiniteRAction
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
