import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Gamma.Source.KGammaSource
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Gamma.Source.RelativeConductorGapReadback
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Unit.QuarterClock

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 2800000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Gamma.CutPower
open Complex MeasureTheory Set Filter BurnolPhysicalState
open OriginalRieszFinitePairing.CoPoisson.Ward
open OriginalGamma.Source.KGamma OriginalGamma.Source.RelativeConductorGapReadback OriginalGamma.Source.JointLogConductor
open OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Unit.SameN OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Unit.QuarterClock
open scoped InnerProductSpace Topology
open private gamma_pair_dilation from H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Gamma.Source.RelativeConductorGapReadback
open private gamma_pair_fourier from H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Gamma.Source.KGammaSource
local notation "q" => (1/4 : ℝ)
local notation "R" => burnolDirectRightResolventCLM
local notation "D" => burnolMultiplicativeDilation
local notation "seed" => ConstantDual.seed

/-- The original integrable resolvent acts on both members of the complete conductor source. -/
theorem actual_Gamma_R (coordinate : BurnolCompletedMellinCoordinate) (value gamma : BurnolL2)
    (source : GammaPair value gamma) : GammaPair (R coordinate value) (R coordinate gamma) := by
  intro test
  have right : 1/4<(coordinate.value/2).re := by
    rw [Complex.div_re]
    norm_num
    linarith [coordinate.rightHalf]
  have left := (innerSL ℂ (wholeConductorTest test)).integral_comp_comm
    (burnolDirectRightResolventIntegrand_integrableOn (coordinate.value/2) right value)
  have other := (innerSL ℂ (test.toLp 2 volume)).integral_comp_comm
    (burnolDirectRightResolventIntegrand_integrableOn (coordinate.value/2) right gamma)
  simp only [innerSL_apply_apply] at left other
  change inner ℂ (wholeConductorTest test) (burnolDirectRightResolvent (coordinate.value/2) value)=
    inner ℂ (test.toLp 2 volume) (burnolDirectRightResolvent (coordinate.value/2) gamma)
  unfold burnolDirectRightResolvent
  rw [inner_neg_right,inner_neg_right,←left,←other]
  congr 1
  apply integral_congr_ae
  filter_upwards with time
  unfold burnolDirectRightResolventIntegrand
  rw [inner_smul_right,inner_smul_right]
  exact congrArg (positiveMellinQuarterRightResolventWeight (coordinate.value/2) time*·)
    (gamma_pair_dilation (-time/2) value gamma source test)

def quarterTailGamma (coordinate : BurnolCompletedMellinCoordinate) : BurnolL2 :=
  (q : ℂ)^(-coordinate.value) • (actualGammaSeed+(coordinate.value/2) • R coordinate actualGammaSeed)

theorem actual_quarter_tail_Gamma (coordinate : BurnolCompletedMellinCoordinate) :
    GammaPair (burnolRadiusNormalizedUnitTail coordinate q (by norm_num)) (quarterTailGamma coordinate) := by
  intro test
  have resolved := actual_Gamma_R coordinate seed actualGammaSeed actual_gamma_seed_source
  rw [actual_seed_quarter_tail,quarterTailGamma,inner_smul_right,inner_smul_right,
    inner_add_right,inner_add_right,inner_smul_right,inner_smul_right,
    actual_gamma_seed_source test,resolved test]

private def scaleFactor (coordinate : BurnolCompletedMellinCoordinate) : ℂ :=
  (fullMellinTranslationCharacter coordinate.value (-Real.log 16))⁻¹

private theorem actual_four_tail_source (coordinate : BurnolCompletedMellinCoordinate) :
    burnolRadiusNormalizedUnitTail coordinate 4 (by norm_num)=
      scaleFactor coordinate • D (-Real.log 16) (burnolRadiusNormalizedUnitTail coordinate q (by norm_num)) := by
  have radius : q*Real.exp (-(-Real.log 16))=4 := by
    rw [neg_neg,Real.exp_log (by norm_num : (0 : ℝ)<16)]
    norm_num
  have moved := burnolRadiusNormalizedUnitTail_dilation coordinate q (by norm_num) (-Real.log 16)
  have paid : D (-Real.log 16) (burnolRadiusNormalizedUnitTail coordinate q (by norm_num))=
      fullMellinTranslationCharacter coordinate.value (-Real.log 16) •
        burnolRadiusNormalizedUnitTail coordinate 4 (by norm_num) := by
    simpa only [radius] using moved
  have nonzero : fullMellinTranslationCharacter coordinate.value (-Real.log 16)≠0 := Complex.exp_ne_zero _
  rw [paid,scaleFactor,smul_smul,inv_mul_cancel₀ nonzero,one_smul]

def fourTailGamma (coordinate : BurnolCompletedMellinCoordinate) : BurnolL2 :=
  scaleFactor coordinate • D (-Real.log 16) (quarterTailGamma coordinate)

theorem actual_four_tail_Gamma (coordinate : BurnolCompletedMellinCoordinate) :
    GammaPair (burnolRadiusNormalizedUnitTail coordinate 4 (by norm_num)) (fourTailGamma coordinate) := by
  intro test
  rw [actual_four_tail_source,fourTailGamma,inner_smul_right,inner_smul_right,
    gamma_pair_dilation (-Real.log 16) _ _ (actual_quarter_tail_Gamma coordinate) test]

/-- This is the positive power cut in the source variable, rather than an uncut homogeneous actor. -/
def rankValue (coordinate : BurnolCompletedMellinCoordinate) : BurnolL2 := -quarterShellSource coordinate

def rankGamma (coordinate : BurnolCompletedMellinCoordinate) : BurnolL2 :=
  fourTailGamma coordinate-quarterTailGamma coordinate

theorem actual_rank_raw (coordinate : BurnolCompletedMellinCoordinate) :
    (rankValue coordinate : ℝ → ℂ)=ᵐ[volume] fun u =>
      if q < |u| ∧ |u|≤4 then ((|u| : ℝ) : ℂ)^(-coordinate.value) else 0 := by
  filter_upwards [Lp.coeFn_neg (quarterShellSource coordinate),actual_quarter_shell_raw coordinate] with u negated source
  change (-quarterShellSource coordinate : BurnolL2) u=_
  rw [negated,Pi.neg_apply,source]
  by_cases inside : q < |u| ∧ |u|≤4
  · rw [quarterShellRaw,if_pos inside,if_pos inside,neg_neg]
  · rw [quarterShellRaw,if_neg inside,if_neg inside,neg_zero]

theorem actual_rank_original_inverse (coordinate : BurnolCompletedMellinCoordinate) :
    rankValue coordinate= -burnolMobiusSourceL2 (OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Unit.QuarterShell.quarterShellPa coordinate) := by
  rw [actual_quarter_shell_inverse]
  rfl

/-- Both original source endpoints generate one whole L2 conductor field for the rank leg. -/
theorem actual_rank_Gamma (coordinate : BurnolCompletedMellinCoordinate) :
    GammaPair (rankValue coordinate) (rankGamma coordinate) := by
  intro test
  change inner ℂ (wholeConductorTest test)
      (-(burnolRadiusNormalizedUnitTail coordinate q (by norm_num)-burnolNormalizedFirstSourceUnitTail coordinate))=_
  rw [neg_sub,rankGamma,inner_sub_right,inner_sub_right]
  change inner ℂ (wholeConductorTest test) (burnolRadiusNormalizedUnitTail coordinate 4 (by norm_num))-
    inner ℂ (wholeConductorTest test) (burnolRadiusNormalizedUnitTail coordinate q (by norm_num))=_
  rw [actual_four_tail_Gamma coordinate test,actual_quarter_tail_Gamma coordinate test]

theorem actual_rank_even (coordinate : BurnolCompletedMellinCoordinate) :
    reflectL2 (rankValue coordinate)=rankValue coordinate :=
  burnolReflectL2_eq_of_even_raw _ _ (actual_rank_raw coordinate) (fun u => by simp only [abs_neg])

private theorem Gamma_unique (value first second : BurnolL2)
    (left : GammaPair value first) (right : GammaPair value second) : first=second := by
  apply ext_inner_left ℂ
  intro cotest
  have dense : DenseRange (SchwartzMap.toLpCLM ℝ ℂ 2 (volume : Measure ℝ)) :=
    SchwartzMap.denseRange_toLpCLM (by norm_num)
  refine dense.induction_on (p := fun test : BurnolL2 => inner ℂ test first=inner ℂ test second) cotest ?_ ?_
  · exact isClosed_eq (continuous_id.inner continuous_const) (continuous_id.inner continuous_const)
  intro test
  exact (left test).symm.trans (right test)

theorem actual_rank_Gamma_even (coordinate : BurnolCompletedMellinCoordinate) :
    reflectL2 (rankGamma coordinate)=rankGamma coordinate := by
  have doubled := gamma_pair_fourier _ _ (gamma_pair_fourier _ _ (actual_rank_Gamma coordinate))
  rw [fourierL2_fourierL2,fourierL2_fourierL2,actual_rank_even] at doubled
  exact Gamma_unique _ _ _ doubled (actual_rank_Gamma coordinate)

def rankJointGammaRaw (coordinate : BurnolCompletedMellinCoordinate) (u : ℝ) : BurnolL2 :=
  (-rankGamma coordinate u) • burnolUnitTailResponse coordinate 4

/-- The negative tensor rank field has its genuine whole source-variable L2 domain. -/
theorem actual_rank_joint_Gamma_domain (coordinate : BurnolCompletedMellinCoordinate) :
    MemLp (rankJointGammaRaw coordinate) 2 volume := by
  let tensor : ℂ →L[ℂ] BurnolL2 :=
    (ContinuousLinearMap.id ℂ ℂ).smulRight (burnolUnitTailResponse coordinate 4)
  change MemLp (tensor ∘ (fun u : ℝ => -rankGamma coordinate u)) 2 volume
  exact tensor.comp_memLp' (Lp.memLp (rankGamma coordinate)).neg

end OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Gamma.CutPower
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
