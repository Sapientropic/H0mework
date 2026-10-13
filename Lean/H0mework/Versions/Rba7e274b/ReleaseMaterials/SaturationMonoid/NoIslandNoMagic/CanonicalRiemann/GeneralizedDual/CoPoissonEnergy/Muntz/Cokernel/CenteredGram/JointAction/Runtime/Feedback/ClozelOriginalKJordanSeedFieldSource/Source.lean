import Lean
import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFourierKernelDependentRAction.Consumer
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKJordanSeedFieldSource
open Complex MeasureTheory Set Filter SourceGeneratedHilbertCokernel
open scoped InnerProductSpace Topology
open NoIslandNoMagic.CanonicalRiemann NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual
open BurnolPhysicalState OriginalPaPhysicalGreen
namespace Paid
export _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState.FiniteMobiusResolventFlux (actualMean Rplus RplusIntegrand Rplus_integrable)
export _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState.OriginalJointFluxSource (actual_mean_source_integral actual_mean_dilation_source source_weight_mean_phase)
end Paid
local notation "q" => (1/4:ℝ)

variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬∃ n:Nat,observation.coordinate=-2*(n+1))
variable (half : OriginalKCombCalculation.Half observation)





namespace J
export OriginalKFourierKernelDependentRAction (actualResonantIntegrand actualResonantField actual_resonant_integrable actual_resonant_source_boundary actual_resonant_source_strong actual_resonant_repeated_R)
export OriginalKFourierKernelDependentRAction.Whole (seed)
end J

/-- Original seed and its native gap-Riesz source have the same quarter unit, before dilation. -/
theorem actual_seed_gap_source : J.seed=(2*q:ℂ) • burnolAmbientGapRieszVector q :=by
 unfold burnolAmbientGapRieszVector
 rw [burnolIntervalConstant_norm_sq (by norm_num : (0:ℝ)<q),smul_smul]
 norm_num
 rfl

/-- The paid original source dilation generates the entire moving-radius field, keeping its exterior. -/
theorem actual_seed_dilation_source (shift : ℝ) :
 burnolMultiplicativeDilation shift J.seed=
 (((2*q:ℝ):ℂ)*(Real.exp (-shift/2):ℂ)) • burnolAmbientGapRieszVector (q*Real.exp (-shift)) :=by
 rw [actual_seed_gap_source,map_smul,burnolAmbientGapRiesz_dilation (by norm_num),smul_smul]
 norm_num

private theorem actual_gap_quarter_restriction (radius : ℝ) (positive : 0<radius) (contains : q≤radius) :
 burnolRadiusRestriction q (burnolAmbientGapRieszVector radius)=
 (((2*radius:ℝ):ℂ)⁻¹) • intervalConstant q :=by
 apply Lp.ext
 filter_upwards [LpToLpRestrictCLM_coeFn ℂ (symmetricInterval q) (burnolAmbientGapRieszVector radius),
   ae_restrict_of_ae (burnolGapRiesz_ae_raw radius),ae_restrict_mem (measurableSet_symmetricInterval q),
   Lp.coeFn_smul (((2*radius:ℝ):ℂ)⁻¹) (intervalConstant q),intervalConstant_coeFn q]
    with x restricted raw inside scalar unit
 change burnolRadiusRestriction q (burnolAmbientGapRieszVector radius) x=_ at restricted
 rw [restricted,raw,scalar]
 have contained : x∈symmetricInterval radius :=⟨by linarith [inside.1],by linarith [inside.2]⟩
 unfold burnolGapRieszRaw
 rw [burnolIntervalConstant_norm_sq positive,indicator_of_mem contained]
 simp only [star_inv₀,Pi.smul_apply,smul_eq_mul,unit,mul_one]
 rw [←starRingEnd_apply,Complex.conj_ofReal]

/-- Quarter is a dependent restriction of the actual moving-radius whole field. -/
theorem actual_seed_negative_quarter_source (shift : ℝ) (nonpositive : shift≤0) :
 burnolRadiusRestriction q (burnolMultiplicativeDilation shift J.seed)=
 (Real.exp (shift/2):ℂ) • intervalConstant q :=by
 rw [actual_seed_dilation_source,map_smul,actual_gap_quarter_restriction _ (mul_pos (by norm_num) (Real.exp_pos _))
   (by have expanded:=Real.one_le_exp_iff.mpr (neg_nonneg.mpr nonpositive);nlinarith),smul_smul]
 have phase : Real.exp (-shift/2)*Real.exp shift=Real.exp (shift/2) :=by
  rw [←Real.exp_add]
  congr 1
  ring
 congr 1
 have price : (2*q)*Real.exp (-shift/2)*(2*(q*Real.exp (-shift)))⁻¹=Real.exp (shift/2) :=by
  rw [Real.exp_neg]
  field_simp [Real.exp_ne_zero]
  simpa only [neg_div] using phase
 exact_mod_cast price

end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKJordanSeedFieldSource
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
