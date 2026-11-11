import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Material.Calculation.ClozelOriginalKCoefficientBSelfCalculation
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKCoefficientBFiniteAction.Source

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000

noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalKCoefficientBSelfCalculation.Semantics

open Complex BurnolPhysicalState SourceOperationEffects SourceOperationExecution
open OriginalRieszFinitePairing.CoPoisson.Ward OriginalKFixedBoundarySourceFibre
open OriginalKCoefficientBFiniteAction
open OriginalKSourceFiniteUpdate OriginalKSourceFiniteUpdate.OriginalBFiniteAction
open scoped InnerProductSpace
local notation "M" => BurnolQuarterMeanZeroCarrier
local notation "Hq" => BurnolQuarterIntervalL2
local notation "ι" => burnolQuarterZeroExtension
local notation "S" => burnolMeanZeroTruncatedFourier

theorem coefficient_b_code_eval (c : BurnolCompletedMellinCoordinate) :
    (OriginalKBFiniteCalculation.coefficientSourceCode c).eval sourceEnvironment =
      ι (sourceB c : Hq) := coefficient_source_calculation c

theorem coefficient_sb_code_eval (c : BurnolCompletedMellinCoordinate) :
    (coefficientSCode c).eval sourceEnvironment = ι (sourceSB c : Hq) := by
  rw [coefficient_S_code_eval, coefficient_b_code_eval]
  rfl

theorem kernel_code_eval (c : BurnolCompletedMellinCoordinate) :
    (sourceKernelCode c).eval sourceEnvironment = sourceKernel c := by
  rw [source_kernel_code_eval, elementary_even_code_eval, coefficient_sb_code_eval,
    coefficient_b_code_eval]
  rfl

private theorem loss_code_actual (h : ℝ) (input : E) (value : M)
    (read : input.eval sourceEnvironment = ι (value : Hq)) :
    (OriginalKBFiniteCalculation.lossCode h input).eval sourceEnvironment = fullWindowLoss h value := by
  rw [OriginalKBFiniteCalculation.loss_code_eval, read]
  have H_whole : OriginalKBFiniteCalculation.wholeZeroMean
      (burnolMultiplicativeDilation (-h) (ι (value : Hq))) =
        ι (meanZeroDilation (-h) value : Hq) := rfl
  rw [H_whole]
  have inventory := outward_full_source_inventory h value
  linear_combination (norm := module) inventory

private theorem boundary_code_actual (c : BurnolCompletedMellinCoordinate) (h : ℝ) (input : E) :
    (OriginalKBFiniteCalculation.boundaryActionCode c h input).eval sourceEnvironment =
      finiteBoundaryAction c h (input.eval sourceEnvironment) := by
  change pairedMellinTranslationCharacter c.value h • input.eval sourceEnvironment +
    (-1 : ℂ) • ((1/2 : ℂ) •
      (burnolMultiplicativeDilation h (input.eval sourceEnvironment) +
        burnolMultiplicativeDilation (-h) (input.eval sourceEnvironment))) = _
  rw [neg_one_smul]
  simp only [finiteBoundaryAction, sub_eq_add_neg]

theorem core_code_eval (c : BurnolCompletedMellinCoordinate) (h : ℝ) :
    (sourceCoreCode c h).eval sourceEnvironment = sourceCore c h := by
  rw [source_core_code_eval, boundary_code_actual, elementary_even_code_eval,
    loss_code_actual h (coefficientSCode c) (sourceSB c) (coefficient_sb_code_eval c),
    loss_code_actual h (OriginalKBFiniteCalculation.coefficientSourceCode c) (sourceB c)
      (coefficient_b_code_eval c)]
  rfl

/-- The calculated price is encoded in the original unit; the complete two source subtrees are evaluated. -/
theorem cotest_code_eval (c : BurnolCompletedMellinCoordinate) (h : ℝ) :
    (cotestCode c h).eval sourceEnvironment =
      inner ℂ (sourceKernel c) (sourceCore c h) • ConstantDual.seed := by
  rw [OriginalKCoefficientBSelfCalculation.cotest_code_eval, kernel_code_eval, core_code_eval]
  rfl

theorem source_zero_override (c : BurnolCompletedMellinCoordinate) :
    (OriginalKBFiniteCalculation.coefficientSourceCode c).eval sourceEnvironment = ι (sourceB c : Hq) ∧
    (coefficientSCode c).eval sourceEnvironment = ι (sourceSB c : Hq) ∧
    (sourceKernelCode c).eval sourceEnvironment = sourceKernel c ∧
    (sourceCoreCode c 0).eval sourceEnvironment = 0 ∧
    (cotestCode c 0).eval sourceEnvironment = 0 := by
  have coreZero := (OriginalKCoefficientBFiniteAction.source_zero_override c).2.2.2.2.2.2.2.2.1
  refine ⟨coefficient_b_code_eval c, coefficient_sb_code_eval c, kernel_code_eval c, ?_, ?_⟩
  · rw [core_code_eval, coreZero]
  · rw [cotest_code_eval, coreZero, inner_zero_right, zero_smul]

end OriginalKCoefficientBSelfCalculation.Semantics
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
