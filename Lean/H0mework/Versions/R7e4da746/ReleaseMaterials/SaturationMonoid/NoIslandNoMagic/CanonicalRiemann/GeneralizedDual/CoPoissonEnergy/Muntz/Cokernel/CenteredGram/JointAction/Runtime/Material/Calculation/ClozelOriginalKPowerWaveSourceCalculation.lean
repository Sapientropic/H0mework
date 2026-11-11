import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Material.Calculation.ClozelOriginalKPowerWaveSourceProgram
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.WholeDebtRPowerWaveDilationSource
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKConstantSeedWholeRAction.Source

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000

noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalKPowerWaveSourceCalculation
open Complex MeasureTheory BurnolPhysicalState SourceOperationEffects SourceOperationExecution
open OriginalRieszSource OriginalRieszFiniteSource OriginalRieszFinitePairing

open private sub fourier sub_eval from
  H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Material.Calculation.ClozelOriginalKPowerWaveSourceProgram

theorem edge_code_eval (c : BurnolCompletedMellinCoordinate) (environment : Env Value Var) :
    (edgeCode c).eval environment = edgePrimitive c := by
  have twice : OriginalKQuarterTailPhysicalSource.actualStarSource (starCoordinate c) = c := by
    cases c
    simp only [starCoordinate, OriginalKQuarterTailPhysicalSource.actualStarSource,
      OriginalKBFiniteCalculation.conjugateCoordinate, star_star]
  have qualified : (starCoordinate c).value - 1 ≠ 0 := by
    intro zero
    have real := congrArg Complex.re zero
    norm_num at real
    linarith [(starCoordinate c).belowOne]
  have unit : (-((starCoordinate c).value - 1)/2 : ℂ)*
      (-2/((starCoordinate c).value - 1)) = 1 := by
    field_simp [qualified]
  rw [edgeCode, sub_eval]
  change (-((starCoordinate c).value - 1)/2 : ℂ) •
    burnolDirectRightResolvent ((starCoordinate c).value/2) OriginalRieszFinitePairing.CoPoisson.Ward.ConstantDual.seed - OriginalRieszFinitePairing.CoPoisson.Ward.ConstantDual.seed = _
  rw [OriginalKConstantSeedWholeRAction.actual_original_R_seed_whole_field]
  unfold OriginalKConstantSeedWholeRAction.actualWholeSeedRField
  rw [twice, smul_smul, unit, one_smul]
  exact add_sub_cancel_right _ _

theorem edge_integral_code_eval (c : BurnolCompletedMellinCoordinate) (h : ℝ)
    (environment : Env Value Var) : (edgeIntegralCode c h).eval environment = edgeIntegral c h := by
  rw [edgeIntegralCode, sub_eval]
  change burnolMultiplicativeDilation h ((edgeCode c).eval environment) -
    fullMellinTranslationCharacter (star c.value) h • (edgeCode c).eval environment = _
  rw [edge_code_eval]
  rfl

theorem fourier_edge_integral_code_eval (c : BurnolCompletedMellinCoordinate) (h : ℝ)
    (environment : Env Value Var) :
    (fourierEdgeIntegralCode c h).eval environment = fourierEdgeIntegral c h := by
  rw [fourierEdgeIntegralCode, sub_eval, sub_eval]
  change (2*(star c.value - 1/2)) •
      nativeIntegral (star c.value - 1/2) (fourierL2 ((edgeCode c).eval environment)) h -
    (burnolMultiplicativeDilation h (fourierL2 ((edgeCode c).eval environment)) -
      fullMellinTranslationCharacter (star c.value) h • fourierL2 ((edgeCode c).eval environment)) = _
  rw [edge_code_eval]
  rfl

theorem profile_code_eval (c : BurnolCompletedMellinCoordinate) (h : ℝ)
    (environment : Env Value Var) : (profileCode c h).eval environment = profileIntegral c h := by
  rw [profileCode, sub_eval, edge_integral_code_eval]
  change nativeAction (star c.value - 1/2) h ((sub (fourier wholeUCode) wholeVCode).eval environment) -
    edgeIntegral c h = profileIntegral c h
  rw [sub_eval]
  rfl

theorem fourier_profile_code_eval (c : BurnolCompletedMellinCoordinate) (h : ℝ)
    (environment : Env Value Var) :
    (fourierProfileCode c h).eval environment = fourierProfileIntegral c h := by
  rw [fourierProfileCode, sub_eval, fourier_edge_integral_code_eval]
  change nativeAction (star c.value - 1/2) h ((sub wholeUCode (fourier wholeVCode)).eval environment) -
    fourierEdgeIntegral c h = fourierProfileIntegral c h
  rw [sub_eval]
  rfl

theorem single_code_eval (c : BurnolCompletedMellinCoordinate) (h : ℝ)
    (environment : Env Value Var) :
    (singleCode c h).eval environment = OriginalWholeDebtRPowerWaveDilationSource.singleSource c h := by
  change fourierL2
    (OriginalWholeDebtRPowerWaveDilationSource.coupling1 c •
        (profileCode (OriginalPrimitiveRankBalance.conjugateCoordinate c) (-h)).eval environment +
      OriginalWholeDebtRPowerWaveDilationSource.coupling0 c •
        (fourierProfileCode (OriginalPrimitiveRankBalance.conjugateCoordinate c) (-h)).eval environment) = _
  rw [profile_code_eval, fourier_profile_code_eval]
  rfl

theorem code_eval (c : BurnolCompletedMellinCoordinate) (h : ℝ) (environment : Env Value Var) :
    (code c h).eval environment = OriginalWholeDebtRPowerWaveDilationSource.pairedSource c h := by
  change (1/2 : ℂ) • ((singleCode c h).eval environment + (singleCode c (-h)).eval environment) = _
  rw [single_code_eval, single_code_eval]
  rfl

end OriginalKPowerWaveSourceCalculation
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
