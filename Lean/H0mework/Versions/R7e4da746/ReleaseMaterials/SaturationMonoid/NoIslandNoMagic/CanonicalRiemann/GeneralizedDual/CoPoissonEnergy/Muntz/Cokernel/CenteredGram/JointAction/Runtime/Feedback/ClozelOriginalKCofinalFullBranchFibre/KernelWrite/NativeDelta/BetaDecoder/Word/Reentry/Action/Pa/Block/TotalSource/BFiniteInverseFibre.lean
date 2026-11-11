import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKCofinalFullBranchFibre.KernelWrite.NativeDelta.BetaDecoder.Word.Reentry.Action.Pa.Block.TotalSource.BFiniteStep

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 600000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalKCofinalFullBranchFibre.KernelWrite.NativeDelta.BetaDecoder.OriginalTotalSourceBFiniteInverseFibre
open Complex BurnolPhysicalState SourceOperationEffects SourceOperationExecution
open OriginalRieszSource OriginalKSourceResolventReconstruction OriginalKFixedBoundarySourceFibre
open OriginalRieszFinitePairing.CoPoisson.Ward
namespace BF
export OriginalKBFiniteCalculation (Value Var Base reader result code coordinate sourceEnvironment fixedShift)
end BF
namespace Stage
export OriginalKCofinalFullBranchFibre.KernelWrite.NativeDelta.BetaDecoder.OriginalTotalSourceBFiniteStep (read)
end Stage
namespace Action
export OriginalKSourceFiniteUpdate.OriginalBFiniteRAction
  (calculatedSourceNormal calculated_boundary_input_actual)
end Action

private theorem unitary_difference_injective (unitary : BurnolL2 ≃ₗᵢ[ℂ] BurnolL2)
    (coefficient : ℂ) (offUnit : ‖coefficient‖ ≠ 1) :
    Function.Injective (fun value : BurnolL2 => unitary value - coefficient • value) := by
  intro left right same
  have eigen : unitary (left-right) = coefficient • (left-right) := by
    rw [map_sub, smul_sub]
    linear_combination (norm := module) same
  have normEq := congrArg norm eigen
  rw [unitary.norm_map, norm_smul] at normEq
  have product : (‖coefficient‖ - 1)*‖left-right‖ = 0 := by nlinarith
  have zero := (mul_eq_zero.mp product).resolve_left (sub_ne_zero.mpr offUnit)
  exact sub_eq_zero.mp (norm_eq_zero.mp zero)

private theorem characters_inverse (c : BurnolCompletedMellinCoordinate) (h : ℝ) :
    fullMellinTranslationCharacter c.value h * reciprocalMellinTranslationCharacter c.value h = 1 := by
  unfold fullMellinTranslationCharacter reciprocalMellinTranslationCharacter
  rw [← Complex.exp_add]
  have exponent : ((1/2 : ℂ)-c.value)*(h : ℂ)+(c.value-(1/2 : ℂ))*(h : ℂ) = 0 := by ring
  rw [exponent, Complex.exp_zero]

theorem actual_factorization (c : BurnolCompletedMellinCoordinate) (h : ℝ) (value : BurnolL2) :
    burnolMultiplicativeDilation h
        (burnolMultiplicativeDilation h value-fullMellinTranslationCharacter c.value h • value) -
      reciprocalMellinTranslationCharacter c.value h •
        (burnolMultiplicativeDilation h value-fullMellinTranslationCharacter c.value h • value) =
      (-2 : ℂ) • burnolMultiplicativeDilation h (finiteBoundaryAction c h value) := by
  have returned : reciprocalMellinTranslationCharacter c.value h •
      (fullMellinTranslationCharacter c.value h • value) = value := by
    rw [smul_smul, mul_comm, characters_inverse, one_smul]
  rw [map_sub, map_smul, smul_sub, returned]
  unfold finiteBoundaryAction
  rw [map_sub, map_smul, map_smul, map_add,
    burnolMultiplicativeDilation_neg_eq_symm, LinearIsometryEquiv.apply_symm_apply]
  unfold pairedMellinTranslationCharacter
  module

private theorem full_character_off_unit (c : BurnolCompletedMellinCoordinate) (h : ℝ) (positive : 0 < h) :
    ‖fullMellinTranslationCharacter c.value h‖ ≠ 1 := by
  rw [fullMellinTranslationCharacter, Complex.norm_exp]
  apply ne_of_lt
  apply Real.exp_lt_one_iff.mpr
  simp only [Complex.mul_re, Complex.sub_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
  norm_num
  exact mul_neg_of_neg_of_pos (by linarith [c.rightHalf]) positive

private theorem reciprocal_character_off_unit (c : BurnolCompletedMellinCoordinate) (h : ℝ) (positive : 0 < h) :
    ‖reciprocalMellinTranslationCharacter c.value h‖ ≠ 1 := by
  rw [reciprocalMellinTranslationCharacter, Complex.norm_exp]
  apply ne_of_gt
  apply Real.one_lt_exp_iff.mpr
  simp only [Complex.mul_re, Complex.sub_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
  norm_num
  exact mul_pos (by linarith [c.rightHalf]) positive

theorem actual_action_injective (c : BurnolCompletedMellinCoordinate) (h : ℝ) (positive : 0 < h) :
    Function.Injective (finiteBoundaryAction c h) := by
  let first := fun value : BurnolL2 =>
    burnolMultiplicativeDilation h value-fullMellinTranslationCharacter c.value h • value
  let second := fun value : BurnolL2 =>
    burnolMultiplicativeDilation h value-reciprocalMellinTranslationCharacter c.value h • value
  have firstInjective : Function.Injective first := unitary_difference_injective _ _ (full_character_off_unit c h positive)
  have secondInjective : Function.Injective second := unitary_difference_injective _ _ (reciprocal_character_off_unit c h positive)
  intro left right same
  apply firstInjective
  apply secondInjective
  exact (actual_factorization c h left).trans
    ((congrArg (fun value : BurnolL2 => (-2 : ℂ) • burnolMultiplicativeDilation h value) same).trans
      (actual_factorization c h right).symm)

private theorem full_source_fibre (c : BurnolCompletedMellinCoordinate) (h : ℝ) (positive : 0 < h)
    {value : BurnolL2} (actual : Trace BF.sourceEnvironment (BF.code c h) (.const value)) :
    (∃! source : BurnolL2, finiteBoundaryAction c h source = value) ∧
    (value = finiteBoundaryAction c h (generatedK c)) ∧
    (value-(burnolEvenAmbientProjection value : BurnolL2) = sourceProjectionLoss c h) := by
  have paid : value = Action.calculatedSourceNormal c h :=
    actual.sound.symm.trans (OriginalKBFiniteCalculation.Semantics.code_eval c h positive.le)
  have normal : Action.calculatedSourceNormal c h = sourceNormal c h := by
    unfold Action.calculatedSourceNormal
    rw [Action.calculated_boundary_input_actual c h positive.le]
    rfl
  have image : value = finiteBoundaryAction c h (generatedK c) :=
    paid.trans (normal.trans (sourceNormal_generated c h))
  have fee : value-(burnolEvenAmbientProjection value : BurnolL2) = sourceProjectionLoss c h := by
    rw [paid, normal]
    exact (sourceProjectionLoss_actual c h).symm
  refine ⟨⟨generatedK c, image.symm, ?_⟩, image, fee⟩
  intro source sourceImage
  exact actual_action_injective c h positive (sourceImage.trans image)

private theorem fixed_positive : 0 < BF.fixedShift := by
  apply Real.log_pos
  change 1 < Real.sqrt 3
  exact (Real.lt_sqrt (by norm_num : (0 : ℝ) ≤ 1)).mpr (by norm_num)

variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
variable (half : OriginalKCombCalculation.Half observation)
variable {current : CanonicalUnitArithmeticRoot.V.Current}
variable (occurrence : BF.Base.toLedgerRoot.source.source.toRootSource.actual.OccurrenceAt current)

def actualRead :=
  let material := BF.result observation nontrivial half occurrence
  let actual := OriginalKCofinalFullBranchFibre.KernelWrite.NativeDelta.BetaDecoder.OriginalTotalSourceBFiniteAction.Source.actualTrace
    observation nontrivial half occurrence
  let inverse := full_source_fibre (BF.coordinate observation nontrivial half occurrence) BF.fixedShift fixed_positive actual
  PProd.mk (material, Stage.read observation nontrivial half occurrence) inverse

end OriginalKCofinalFullBranchFibre.KernelWrite.NativeDelta.BetaDecoder.OriginalTotalSourceBFiniteInverseFibre
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
