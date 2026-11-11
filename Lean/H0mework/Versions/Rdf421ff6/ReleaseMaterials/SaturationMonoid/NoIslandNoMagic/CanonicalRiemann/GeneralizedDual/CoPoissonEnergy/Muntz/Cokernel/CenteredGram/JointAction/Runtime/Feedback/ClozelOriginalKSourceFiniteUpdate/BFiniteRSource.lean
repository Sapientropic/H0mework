import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKSourceFiniteUpdate.BFiniteSource
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKSourceFiniteUpdate.ReciprocalSource

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalKSourceFiniteUpdate.OriginalBFiniteRAction

open Complex MeasureTheory BurnolPhysicalState
open OriginalRieszSource OriginalRieszFiniteSource
open OriginalKSourceResolventReconstruction OriginalKSourceGramAction OriginalKFixedBoundarySourceFibre
open OriginalRieszFinitePairing.CoPoisson.Ward
open OriginalBFiniteAction
open scoped InnerProductSpace
noncomputable section

/-- Both signs are generated from the actual B drive and its full window loss. -/
def forcingPlus (c : BurnolCompletedMellinCoordinate) (h : ℝ) : Fin 2 → BurnolL2 :=
  ![f0PlusSource c h, fourierL2 (f0MinusSource c h) +
    (2 * sourceRate c) • burnolMultiplicativeDilation h (fourierL2 ConstantDual.seed)]

def forcingMinus (c : BurnolCompletedMellinCoordinate) (h : ℝ) : Fin 2 → BurnolL2 :=
  ![f0MinusSource c h, fourierL2 (f0PlusSource c h) +
    (2 * sourceRate c) • burnolMultiplicativeDilation (-h) (fourierL2 ConstantDual.seed)]

private theorem second_forcing_source (c : BurnolCompletedMellinCoordinate) :
    fourierL2 (regularForcing c 0) + (2 * sourceRate c) • fourierL2 ConstantDual.seed =
      regularForcing c 1 := by
  have actual := OriginalKForcingGapAction.fourier_forcing0_source c
  linear_combination (norm := module) actual

theorem forcingPlus_actual (c : BurnolCompletedMellinCoordinate) (h : ℝ)
    (nonnegative : 0 ≤ h) (i : Fin 2) :
    forcingPlus c h i = burnolMultiplicativeDilation h (regularForcing c i) := by
  fin_cases i
  · exact (forcing0_forward_source c h nonnegative).symm
  · change fourierL2 (f0MinusSource c h) +
      (2 * sourceRate c) • burnolMultiplicativeDilation h (fourierL2 ConstantDual.seed) =
        burnolMultiplicativeDilation h (regularForcing c 1)
    rw [←forcing0_backward_source c h nonnegative, fourierL2_burnolMultiplicativeDilation, neg_neg]
    rw [←second_forcing_source c, map_add, map_smul]

theorem forcingMinus_actual (c : BurnolCompletedMellinCoordinate) (h : ℝ)
    (nonnegative : 0 ≤ h) (i : Fin 2) :
    forcingMinus c h i = burnolMultiplicativeDilation (-h) (regularForcing c i) := by
  fin_cases i
  · exact (forcing0_backward_source c h nonnegative).symm
  · change fourierL2 (f0PlusSource c h) +
      (2 * sourceRate c) • burnolMultiplicativeDilation (-h) (fourierL2 ConstantDual.seed) =
        burnolMultiplicativeDilation (-h) (regularForcing c 1)
    rw [←forcing0_forward_source c h nonnegative, fourierL2_burnolMultiplicativeDilation]
    rw [←second_forcing_source c, map_add, map_smul]

/-- The paid original-R preimage formula acts on the new source forcing. -/
def sourceInput (c : BurnolCompletedMellinCoordinate) (forcing : BurnolL2) : BurnolL2 :=
  -(1/2 : ℂ) • forcing + ((1/4 : ℂ) * (c.value - star c.value)) •
    sourceResolvent c forcing

theorem source_input_updates (c : BurnolCompletedMellinCoordinate) (h : ℝ)
    (nonnegative : 0 ≤ h) (i : Fin 2) :
    sourceInput c (forcingPlus c h i) = burnolMultiplicativeDilation h (regularInput c i) ∧
    sourceInput c (forcingMinus c h i) = burnolMultiplicativeDilation (-h) (regularInput c i) := by
  rw [forcingPlus_actual c h nonnegative, forcingMinus_actual c h nonnegative]
  constructor <;>
    simp only [sourceInput, regularInput, sourceResolvent,
      burnolDirectRightResolvent_dilation, map_add, map_smul]

def calculatedInputColumn (c : BurnolCompletedMellinCoordinate) (h : ℝ) (i : Fin 2) : BurnolL2 :=
  pairedMellinTranslationCharacter c.value h • regularInput c i - (1/2 : ℂ) •
    (sourceInput c (forcingPlus c h i) + sourceInput c (forcingMinus c h i))

theorem calculated_input_column_actual (c : BurnolCompletedMellinCoordinate) (h : ℝ)
    (nonnegative : 0 ≤ h) (i : Fin 2) :
    calculatedInputColumn c h i = finiteBoundaryAction c h (regularInput c i) := by
  rw [calculatedInputColumn, (source_input_updates c h nonnegative i).1,
    (source_input_updates c h nonnegative i).2]
  rfl

def calculatedBoundaryInput (c : BurnolCompletedMellinCoordinate) (h : ℝ) : BurnolL2 :=
  ∑ i : Fin 2, sourceCoefficients c i • calculatedInputColumn c h i

def calculatedBoundaryColumn (c : BurnolCompletedMellinCoordinate) (h : ℝ) (i : Fin 2) : BurnolL2 :=
  burnolDirectRightResolvent (c.value/2) (calculatedInputColumn c h i) +
    finiteBoundaryAction c h (jumpColumns i)

theorem calculated_boundary_column_actual (c : BurnolCompletedMellinCoordinate) (h : ℝ)
    (nonnegative : 0 ≤ h) (i : Fin 2) :
    calculatedBoundaryColumn c h i = finiteBoundaryAction c h (sourceColumns c i) := by
  rw [calculatedBoundaryColumn, calculated_input_column_actual c h nonnegative,
    finiteBoundaryAction_R, regularInput_action, sourceColumns_from_regular_resolvent]
  simp only [finiteBoundaryAction, map_add]
  module

theorem calculated_columns_reciprocal (c : BurnolCompletedMellinCoordinate) (h : ℝ)
    (nonnegative : 0 ≤ h) :
    calculatedBoundaryColumn c h 1 = sourceReciprocity c (calculatedBoundaryColumn c h 0) := by
  rw [calculated_boundary_column_actual c h nonnegative,
    calculated_boundary_column_actual c h nonnegative]
  change finiteBoundaryAction c h (sourceY1 c) =
    sourceReciprocity c (finiteBoundaryAction c h (sourceY0 c))
  rw [sourceY1_reciprocal_source, sourceReciprocity_boundary]

theorem calculated_boundary_input_actual (c : BurnolCompletedMellinCoordinate) (h : ℝ)
    (nonnegative : 0 ≤ h) : calculatedBoundaryInput c h = boundaryInput c h := by
  unfold calculatedBoundaryInput
  simp only [calculated_input_column_actual c h nonnegative]
  unfold boundaryInput regularSource
  simp only [Fin.sum_univ_two, finiteBoundaryAction, map_add, map_smul]
  module

/-- This original R action has no shifted f0/Y/K, finite primitive, or boundary input. -/
def calculatedSourceNormal (c : BurnolCompletedMellinCoordinate) (h : ℝ) : BurnolL2 :=
  burnolDirectRightResolvent (c.value/2) (calculatedBoundaryInput c h) + rawBoundaryJump c h

theorem calculated_source_normal_actual (c : BurnolCompletedMellinCoordinate) (h : ℝ)
    (nonnegative : 0 ≤ h) : calculatedSourceNormal c h = contactSourceBoundary c h := by
  rw [calculatedSourceNormal, calculated_boundary_input_actual c h nonnegative]
  change sourceNormal c h = contactSourceBoundary c h
  rw [sourceNormal_generated, generatedK_boundary_action, ←contact_source_word_actual]

theorem calculated_source_reciprocal_word (c : BurnolCompletedMellinCoordinate) (h : ℝ)
    (nonnegative : 0 ≤ h) :
    calculatedSourceNormal c h = Kernel.A c • calculatedBoundaryColumn c h 0 +
      Kernel.beta c • sourceReciprocity c (calculatedBoundaryColumn c h 0) := by
  rw [calculated_source_normal_actual c h nonnegative, ←reciprocal_source_word_actual]
  unfold reciprocalSourceBoundary
  rw [calculated_boundary_column_actual c h nonnegative, source_columns_boundary_action]
  simp only [contact_source_column_actual]

def calculatedSourceGram (c : BurnolCompletedMellinCoordinate) (h : ℝ) (i j : Fin 2) : ℂ :=
  -inner ℂ (regularColumns c i + jumpColumns i) (calculatedBoundaryColumn c h j)

theorem calculated_source_Gram_actual (c : BurnolCompletedMellinCoordinate) (h : ℝ)
    (nonnegative : 0 ≤ h) (i j : Fin 2) :
    sourceFiniteGram c h i j = calculatedSourceGram c h i j := by
  rw [source_finite_Gram_action]
  unfold sourceOrbitGram calculatedSourceGram
  rw [calculated_boundary_column_actual c h nonnegative, source_columns_boundary_action]

theorem original_fixedResidual_calculated_source (c : BurnolCompletedMellinCoordinate)
    (zero : riemannZeta c.value = 0) (h : ℝ)
    (nonnegative : 0 ≤ h) (fixed : h = Real.log stageZeroSonineQ) :
    burnolPaFixedShiftResidual c zero = -inner ℂ (generatedK c) (calculatedSourceNormal c h) := by
  rw [calculated_source_normal_actual c h nonnegative, fixed]
  exact original_fixedResidual_contact_source c zero

theorem original_boundary_calculated_source (c : BurnolCompletedMellinCoordinate)
    (zero : riemannZeta c.value = 0) (h : ℝ) (nonnegative : 0 ≤ h) :
    (burnolZeroPairedFixedAnnulusBoundary c zero h : BurnolL2) =
      (burnolEvenAmbientProjection (calculatedSourceNormal c h) : BurnolL2) := by
  rw [calculated_source_normal_actual c h nonnegative]
  exact original_boundary_contact_source c zero h

end
end OriginalKSourceFiniteUpdate.OriginalBFiniteRAction
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
