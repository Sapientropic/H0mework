import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKSourceFiniteUpdate.BFiniteRSource
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKSourceFiniteUpdate.BFiniteControls
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFullAdjointSource.Source

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1500000

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalKSourceFiniteUpdate.OriginalBFiniteRAction

open Complex MeasureTheory BurnolPhysicalState OriginalRieszSource
open OriginalRieszFinitePairing.CoPoisson.Ward
open OriginalBFiniteAction OriginalKSourceResolventReconstruction OriginalKSourceGramAction
open OriginalKFixedBoundarySourceFibre OriginalKFullAdjointSource
open scoped InnerProductSpace
noncomputable section

def forcingPlusNoLoss (c : BurnolCompletedMellinCoordinate) (h : ℝ) : Fin 2 → BurnolL2 :=
  ![f0PlusWithoutWindowLoss c h, fourierL2 (f0MinusWithoutWindowLoss c h) +
    (2 * sourceRate c) • burnolMultiplicativeDilation h (fourierL2 ConstantDual.seed)]

def forcingMinusNoLoss (c : BurnolCompletedMellinCoordinate) (h : ℝ) : Fin 2 → BurnolL2 :=
  ![f0MinusWithoutWindowLoss c h, fourierL2 (f0PlusWithoutWindowLoss c h) +
    (2 * sourceRate c) • burnolMultiplicativeDilation (-h) (fourierL2 ConstantDual.seed)]

/-- The two-column deletion is generated from whole source losses, with F² retained. -/
def forcingPlusLossDefect (h : ℝ) : Fin 2 → BurnolL2 :=
  ![-fourierL2 (fullWindowLoss h Response.u), fourierL2 (fullWindowLoss h Response.v)]

def forcingMinusLossDefect (h : ℝ) : Fin 2 → BurnolL2 :=
  ![fullWindowLoss h Response.v, -fourierL2 (fourierL2 (fullWindowLoss h Response.u))]

theorem forcingPlusNoLoss_actual (c : BurnolCompletedMellinCoordinate)
    (h : ℝ) (nonnegative : 0 ≤ h) (i : Fin 2) :
    forcingPlusNoLoss c h i - forcingPlus c h i = forcingPlusLossDefect h i := by
  fin_cases i
  · have actual := delete_plus_loss_actual c h nonnegative
    rw [forcing0_forward_source c h nonnegative] at actual
    exact actual
  · change fourierL2 (f0MinusWithoutWindowLoss c h) + _ -
      (fourierL2 (f0MinusSource c h) + _) = fourierL2 (fullWindowLoss h Response.v)
    have actual := delete_minus_loss_actual c h nonnegative
    rw [forcing0_backward_source c h nonnegative] at actual
    have mapped := congrArg fourierL2 actual
    rw [map_sub] at mapped
    linear_combination (norm := module) mapped

theorem forcingMinusNoLoss_actual (c : BurnolCompletedMellinCoordinate)
    (h : ℝ) (nonnegative : 0 ≤ h) (i : Fin 2) :
    forcingMinusNoLoss c h i - forcingMinus c h i = forcingMinusLossDefect h i := by
  fin_cases i
  · have actual := delete_minus_loss_actual c h nonnegative
    rw [forcing0_backward_source c h nonnegative] at actual
    exact actual
  · change fourierL2 (f0PlusWithoutWindowLoss c h) + _ -
      (fourierL2 (f0PlusSource c h) + _) = -fourierL2 (fourierL2 (fullWindowLoss h Response.u))
    have actual := delete_plus_loss_actual c h nonnegative
    rw [forcing0_forward_source c h nonnegative] at actual
    have mapped := congrArg fourierL2 actual
    rw [map_sub, map_neg] at mapped
    linear_combination (norm := module) mapped

private theorem sourceInput_sub (c : BurnolCompletedMellinCoordinate) (left right : BurnolL2) :
    sourceInput c left - sourceInput c right = sourceInput c (left - right) := by
  unfold sourceInput sourceResolvent
  change -(1/2 : ℂ) • left + ((1/4 : ℂ) * (c.value - star c.value)) •
    (burnolDirectRightResolventCLM (OriginalPrimitiveRankBalance.conjugateCoordinate c)) left -
    (-(1/2 : ℂ) • right + ((1/4 : ℂ) * (c.value - star c.value)) •
      (burnolDirectRightResolventCLM (OriginalPrimitiveRankBalance.conjugateCoordinate c)) right) =
    -(1/2 : ℂ) • (left - right) + ((1/4 : ℂ) * (c.value - star c.value)) •
      (burnolDirectRightResolventCLM (OriginalPrimitiveRankBalance.conjugateCoordinate c)) (left - right)
  rw [map_sub]
  module

def boundaryInputNoLoss (c : BurnolCompletedMellinCoordinate) (h : ℝ) : BurnolL2 :=
  ∑ i : Fin 2, sourceCoefficients c i •
    (pairedMellinTranslationCharacter c.value h • regularInput c i - (1/2 : ℂ) •
      (sourceInput c (forcingPlusNoLoss c h i) + sourceInput c (forcingMinusNoLoss c h i)))

def sourceLossInput (c : BurnolCompletedMellinCoordinate) (h : ℝ) : BurnolL2 :=
  ∑ i : Fin 2, sourceCoefficients c i • (-(1/2 : ℂ) •
    (sourceInput c (forcingPlusLossDefect h i) + sourceInput c (forcingMinusLossDefect h i)))

theorem source_loss_input_actual (c : BurnolCompletedMellinCoordinate)
    (h : ℝ) (nonnegative : 0 ≤ h) :
    boundaryInputNoLoss c h - calculatedBoundaryInput c h = sourceLossInput c h := by
  unfold boundaryInputNoLoss calculatedBoundaryInput calculatedInputColumn sourceLossInput
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  rw [← smul_sub]
  congr 1
  have plus := sourceInput_sub c (forcingPlusNoLoss c h i) (forcingPlus c h i)
  rw [forcingPlusNoLoss_actual c h nonnegative i] at plus
  have minus := sourceInput_sub c (forcingMinusNoLoss c h i) (forcingMinus c h i)
  rw [forcingMinusNoLoss_actual c h nonnegative i] at minus
  linear_combination (norm := module) -(1/2 : ℂ) • plus - (1/2 : ℂ) • minus

def normalNoLoss (c : BurnolCompletedMellinCoordinate) (h : ℝ) : BurnolL2 :=
  burnolDirectRightResolvent (c.value/2) (boundaryInputNoLoss c h) + rawBoundaryJump c h

theorem deleted_loss_full_R_effect (c : BurnolCompletedMellinCoordinate)
    (h : ℝ) (nonnegative : 0 ≤ h) :
    normalNoLoss c h - calculatedSourceNormal c h =
      burnolDirectRightResolvent (c.value/2) (sourceLossInput c h) := by
  change (burnolDirectRightResolventCLM c) (boundaryInputNoLoss c h) + rawBoundaryJump c h -
    ((burnolDirectRightResolventCLM c) (calculatedBoundaryInput c h) + rawBoundaryJump c h) =
      (burnolDirectRightResolventCLM c) (sourceLossInput c h)
  rw [show (burnolDirectRightResolventCLM c) (boundaryInputNoLoss c h) + rawBoundaryJump c h -
      ((burnolDirectRightResolventCLM c) (calculatedBoundaryInput c h) + rawBoundaryJump c h) =
        (burnolDirectRightResolventCLM c) (boundaryInputNoLoss c h) -
          (burnolDirectRightResolventCLM c) (calculatedBoundaryInput c h) by module,
    ← map_sub, source_loss_input_actual c h nonnegative]

def deletedSourceResidual (c : BurnolCompletedMellinCoordinate) (h : ℝ) : ℂ :=
  -inner ℂ (generatedK c) (normalNoLoss c h)

/-- The actual adjoint source prices this change on the original diagonal. -/
theorem original_residual_deleted_loss_effect (c : BurnolCompletedMellinCoordinate)
    (zero : riemannZeta c.value = 0) (h : ℝ) (nonnegative : 0 ≤ h)
    (fixed : h = Real.log stageZeroSonineQ) :
    burnolPaFixedShiftResidual c zero - deletedSourceResidual c h =
      inner ℂ (sourceAdjointField c) (sourceLossInput c h) := by
  rw [original_fixedResidual_calculated_source c zero h nonnegative fixed, deletedSourceResidual]
  have read := congrArg (inner ℂ (generatedK c)) (deleted_loss_full_R_effect c h nonnegative)
  rw [inner_sub_right, generatedK_eq_original, original_R_full_input] at read
  rw [generatedK_eq_original]
  linear_combination read

private theorem boundary_action_zero (c : BurnolCompletedMellinCoordinate) (value : BurnolL2) :
    finiteBoundaryAction c 0 value = 0 := by
  have character : pairedMellinTranslationCharacter c.value 0 = 1 := by
    norm_num [pairedMellinTranslationCharacter, fullMellinTranslationCharacter,
      reciprocalMellinTranslationCharacter]
  rw [finiteBoundaryAction, character]
  simp only [one_smul, neg_zero, burnolMultiplicativeDilation_zero]
  module

private theorem sourceInput_zero (c : BurnolCompletedMellinCoordinate) : sourceInput c 0 = 0 := by
  have read := sourceInput_sub c 0 0
  simpa only [sub_self] using read.symm

theorem source_loss_input_zero (c : BurnolCompletedMellinCoordinate) : sourceLossInput c 0 = 0 := by
  unfold sourceLossInput forcingPlusLossDefect forcingMinusLossDefect
  simp only [Fin.sum_univ_two, fullWindowLoss_zero, map_zero, neg_zero, Matrix.cons_val_zero, Matrix.cons_val_one,
    sourceInput_zero, add_zero, smul_zero]

theorem full_R_source_zero_override (c : BurnolCompletedMellinCoordinate) :
    (sourceDrive 0 = Response.eta ∧ sourceDriveV 0 = burnolMeanZeroTruncatedFourier Response.eta ∧
      sourceFirst 0 = Response.u ∧ sourceSecond 0 = Response.v ∧
      sourceVFirst 0 = Response.v ∧ sourceVSecond 0 = Response.u - Response.eta ∧
      fullWindowLoss 0 Response.u = 0 ∧ fullWindowLoss 0 Response.v = 0) ∧
    calculatedBoundaryInput c 0 = 0 ∧ boundaryInputNoLoss c 0 = 0 ∧
    calculatedSourceNormal c 0 = 0 ∧ normalNoLoss c 0 = 0 ∧ sourceLossInput c 0 = 0 := by
  have inputZero : calculatedBoundaryInput c 0 = 0 := by
    unfold calculatedBoundaryInput
    simp only [calculated_input_column_actual c 0 le_rfl, boundary_action_zero, smul_zero,
      Finset.sum_const_zero]
  have lossZero := source_loss_input_zero c
  have noLossInputZero := source_loss_input_actual c 0 le_rfl
  rw [inputZero, lossZero, sub_zero] at noLossInputZero
  have jumpZero : rawBoundaryJump c 0 = 0 := boundary_action_zero c _
  have rzero : burnolDirectRightResolvent (c.value/2) 0 = 0 := (burnolDirectRightResolventCLM c).map_zero
  have normalZero : calculatedSourceNormal c 0 = 0 := by
    rw [calculatedSourceNormal, inputZero, rzero, jumpZero, add_zero]
  have noLossNormalZero : normalNoLoss c 0 = 0 := by
    rw [normalNoLoss, noLossInputZero, rzero, jumpZero, add_zero]
  exact ⟨actual_B_source_zero, inputZero, noLossInputZero, normalZero, noLossNormalZero, lossZero⟩

end
end OriginalKSourceFiniteUpdate.OriginalBFiniteRAction
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
