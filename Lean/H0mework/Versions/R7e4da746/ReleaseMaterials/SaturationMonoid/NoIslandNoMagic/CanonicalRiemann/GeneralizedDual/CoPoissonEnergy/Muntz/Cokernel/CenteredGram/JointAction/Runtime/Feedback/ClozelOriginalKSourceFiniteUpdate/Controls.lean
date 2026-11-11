import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKSourceFiniteUpdate.Receipt

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKSourceFiniteUpdate
open Complex MeasureTheory Set BurnolPhysicalState
open OriginalRieszSource OriginalRieszFiniteSource OriginalRieszFiniteColumns
open OriginalKSourceResolventReconstruction OriginalKSourceGramAction OriginalKFixedBoundarySourceFibre
open OriginalRieszFinitePairing.CoPoisson.Ward
open scoped InnerProductSpace

/-- The deleted constructor keeps both exponential and shifted jump terms. -/
def secondOrbitWithoutContact (coordinate : BurnolCompletedMellinCoordinate) (shift : ℝ) : BurnolL2 :=
  Complex.exp (-sourceRate coordinate * (shift : ℂ)) • regularColumns coordinate 1 +
    fourierL2 (backwardIntegral (sourceRate coordinate) (regularForcing coordinate 0) shift) +
      burnolMultiplicativeDilation shift (jumpColumns 1)

def boundaryWithoutSecondContact (coordinate : BurnolCompletedMellinCoordinate) (shift : ℝ) : BurnolL2 :=
  sourceCoefficients coordinate 0 • sourceFiniteBoundaryColumn coordinate shift 0 +
    sourceCoefficients coordinate 1 •
      (pairedMellinTranslationCharacter coordinate.value shift • (regularColumns coordinate 1 + jumpColumns 1) -
        (1/2 : ℂ) • (secondOrbitWithoutContact coordinate shift + secondOrbitWithoutContact coordinate (-shift)))

/-- Omitting the Fourier cochain contact changes the complete source boundary by this full L2 vector. -/
theorem boundary_delete_second_contact (coordinate : BurnolCompletedMellinCoordinate) (shift : ℝ) :
    sourceFiniteBoundary coordinate shift - boundaryWithoutSecondContact coordinate shift =
      -(sourceCoefficients coordinate 1 * sourceRate coordinate) •
        (nativeIntegral (sourceRate coordinate) (fourierL2 ConstantDual.seed) shift +
          nativeIntegral (sourceRate coordinate) (fourierL2 ConstantDual.seed) (-shift)) := by
  unfold sourceFiniteBoundary boundaryWithoutSecondContact sourceFiniteBoundaryColumn
    sourceFiniteOrbit sourcePrimitive secondOrbitWithoutContact secondPrimitiveSource
  simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]
  module

variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬∃ n:Nat,observation.coordinate=-2*(n+1))
variable (half : OriginalKCombCalculation.Half observation) (depth ordinal : Nat)
local notation "c" => OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half
local notation "h" => Real.log stageZeroSonineQ
local notation "receipt" => installedOriginalKReceiptAt observation nontrivial half.down

include depth ordinal in
/-- The same installed residual pays the actual omitted source contact, with no nonzero premise. -/
theorem actual_delete_second_contact_price :
    (receipt).fixedResidual + inner ℂ (receipt).kernel (boundaryWithoutSecondContact c h) =
      (sourceCoefficients c 1 * sourceRate c) * inner ℂ (receipt).kernel
        (nativeIntegral (sourceRate c) (fourierL2 ConstantDual.seed) h +
          nativeIntegral (sourceRate c) (fourierL2 ConstantDual.seed) (-h)) := by
  have actual := actual_finite_source_on_original_whole_next observation nontrivial half depth ordinal
  have price := actual.2.2.2.1
  have tested := congrArg (inner ℂ (receipt).kernel) (boundary_delete_second_contact c h)
  rw [inner_sub_right, inner_smul_right] at tested
  rw [price]
  linear_combination -tested

/-- At zero shift the complete orbit retains its source columns while the boundary and its physical fee vanish. -/
theorem zero_shift_source_override (coordinate : BurnolCompletedMellinCoordinate) :
    (∀ i : Fin 2, sourceFiniteOrbit coordinate 0 i = sourceColumns coordinate i) ∧
    sourceFiniteBoundary coordinate 0 = 0 ∧ sourceProjectionLoss coordinate 0 = 0 := by
  have character : pairedMellinTranslationCharacter coordinate.value 0 = 1 := by
    norm_num [pairedMellinTranslationCharacter, fullMellinTranslationCharacter, reciprocalMellinTranslationCharacter]
  have boundary : sourceFiniteBoundary coordinate 0 = 0 := by
    rw [←generatedK_boundary_action]
    unfold finiteBoundaryAction
    rw [character,one_smul,neg_zero,burnolMultiplicativeDilation_zero]
    module
  have normal : sourceNormal coordinate 0 = 0 :=
    (sourceNormal_generated coordinate 0).trans ((generatedK_boundary_action coordinate 0).trans boundary)
  refine ⟨?_,boundary,?_⟩
  · intro i
    rw [←source_columns_finite_action,burnolMultiplicativeDilation_zero]
  · rw [sourceProjectionLoss_actual,normal]
    simp only [map_zero,Submodule.coe_zero,sub_self]

end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKSourceFiniteUpdate
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
