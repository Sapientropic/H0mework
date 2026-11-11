import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKSourceFiniteUpdate.Source
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKDirectRCofinalOutsideVolterraSource.HProjectionReceipt

set_option autoImplicit false
set_option Elab.async false
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1400000
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKSourceFiniteUpdate
open Complex MeasureTheory Set BurnolPhysicalState
open OriginalRieszSource OriginalRieszFiniteSource
open OriginalKSourceResolventReconstruction OriginalKSourceGramAction OriginalKFixedBoundarySourceFibre
open scoped InnerProductSpace

private theorem source_price_aggregate (coordinate : BurnolCompletedMellinCoordinate) (shift : ℝ) :
    (∑ i : Fin 2, ∑ j : Fin 2, star (sourceCoefficients coordinate i) * sourceCoefficients coordinate j *
      sourceOrbitGram coordinate shift i j) =
        -inner ℂ (generatedK coordinate) (sourceFiniteBoundary coordinate shift) := by
  have kernel : generatedK coordinate =
      ∑ i : Fin 2, sourceCoefficients coordinate i • (regularColumns coordinate i + jumpColumns i) := by
    rw [Fin.sum_univ_two, ←sourceColumns_from_regular_resolvent coordinate 0,
      ←sourceColumns_from_regular_resolvent coordinate 1]
    rfl
  rw [kernel]
  unfold sourceFiniteBoundary sourceOrbitGram
  simp only [Fin.sum_univ_two, inner_add_left, inner_add_right, inner_smul_left,
    inner_smul_right, starRingEnd_apply]
  ring

variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬∃ n:Nat,observation.coordinate=-2*(n+1))
variable (half : OriginalKCombCalculation.Half observation) (depth ordinal : Nat)
local notation "c" => OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half
local notation "h" => Real.log stageZeroSonineQ
local notation "receipt" => installedOriginalKReceiptAt observation nontrivial half.down

/-- Actual source laws compute new reads on the installed receipt's own coordinate. -/
def consume_actual_finite_source {Result : Sort u}
    (consumer :
      type_of% (installedOriginalKReceiptAt_eq_source observation nontrivial half.down) →
      type_of% (generatedK_eq_original c) →
      type_of% (original_fixedResidual_source_Gram c observation.mathlibZero) →
      (∀ i j : Fin 2, sourceFiniteGram c h i j = sourceOrbitGram c h i j) →
      type_of% (generatedK_boundary_action c h) →
      type_of% (sourceProjectionLoss_actual c h) →
      type_of% (source_fibre_loss_energy c h) → Result) : Result :=
  consumer (installedOriginalKReceiptAt_eq_source observation nontrivial half.down)
    (generatedK_eq_original c) (original_fixedResidual_source_Gram c observation.mathlibZero)
    (source_finite_Gram_action c h) (generatedK_boundary_action c h)
    (sourceProjectionLoss_actual c h) (source_fibre_loss_energy c h)

/-- The original whole-next reads the complete forcing orbit, both source slots, and its actual physical loss. -/
theorem actual_finite_source_on_original_whole_next :
    type_of% (OriginalKDirectRCofinalOutsideVolterraSource.actual_h_projection_on_original_whole_next
      observation nontrivial half depth ordinal) ∧
    ((receipt).kernel = generatedK c) ∧
    ((receipt).fixedResidual =
      ∑ i : Fin 2, ∑ j : Fin 2, star (sourceCoefficients c i) * sourceCoefficients c j * sourceOrbitGram c h i j) ∧
    ((receipt).fixedResidual = -inner ℂ (receipt).kernel (sourceFiniteBoundary c h)) ∧
    (((receipt).boundary h : BurnolL2) = (burnolEvenAmbientProjection (sourceFiniteBoundary c h) : BurnolL2)) ∧
    (sourceNormal c h = sourceFiniteBoundary c h) ∧
    (sourceFiniteBoundary c h - ((receipt).boundary h : BurnolL2) = sourceProjectionLoss c h) ∧
    (‖sourceFiniteBoundary c h‖^2 = ‖((receipt).boundary h : BurnolL2)‖^2 + ‖sourceProjectionLoss c h‖^2) := by
  have prior := OriginalKDirectRCofinalOutsideVolterraSource.actual_h_projection_on_original_whole_next
    observation nontrivial half depth ordinal
  refine ⟨prior,?_⟩
  apply consume_actual_finite_source observation nontrivial half
  intro anchor sourceIdentity originalGram updatedGram vector lossValue energy
  have originalKernel : (receipt).kernel = (burnolCompletedMellinRieszVector c : BurnolL2) :=
    congrArg (fun value : OriginalRieszFiniteSource.Receipt => value.kernel) anchor
  have kernel : (receipt).kernel = generatedK c := originalKernel.trans sourceIdentity.symm
  have residual : (receipt).fixedResidual = burnolPaFixedShiftResidual c observation.mathlibZero :=
    congrArg (fun value : OriginalRieszFiniteSource.Receipt => value.fixedResidual) anchor
  have matrix : (receipt).fixedResidual =
      ∑ i : Fin 2, ∑ j : Fin 2, star (sourceCoefficients c i) * sourceCoefficients c j * sourceOrbitGram c h i j := by
    rw [residual, originalGram]
    simp only [updatedGram]
  have price : (receipt).fixedResidual = -inner ℂ (receipt).kernel (sourceFiniteBoundary c h) := by
    rw [kernel]
    exact matrix.trans (source_price_aggregate c h)
  have normal : sourceNormal c h = sourceFiniteBoundary c h := (sourceNormal_generated c h).trans vector
  have originalBoundary : ((receipt).boundary h : BurnolL2) =
      burnolDirectRightResolvent ((c).value/2) (boundaryInput c h) + boundaryJump c h :=
    (congrArg (fun value : OriginalRieszFiniteSource.Receipt => (value.boundary h : BurnolL2)) anchor).trans
      (fixedShiftBoundary_source_fibre c observation.mathlibZero)
  have boundary : ((receipt).boundary h : BurnolL2) =
      (burnolEvenAmbientProjection (sourceFiniteBoundary c h) : BurnolL2) := by
    rw [originalBoundary, ←source_fibre_projection, normal]
  have loss : sourceFiniteBoundary c h - ((receipt).boundary h : BurnolL2) = sourceProjectionLoss c h := by
    rw [boundary, ←normal]
    exact lossValue.symm
  have actualEnergy : ‖sourceFiniteBoundary c h‖^2 =
      ‖((receipt).boundary h : BurnolL2)‖^2 + ‖sourceProjectionLoss c h‖^2 := by
    rw [←normal, originalBoundary]
    exact energy
  exact ⟨kernel,matrix,price,boundary,normal,loss,actualEnergy⟩

run_cmd Lean.modifyEnv fun env => Lean.LibrarySuggestions.nameDenyListExt.addEntry env "actual_finite_source_on_original_whole_next"

end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKSourceFiniteUpdate
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
