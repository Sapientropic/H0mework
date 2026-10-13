import Lean
import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKJordanSeedFieldSource.Quarter
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
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







private theorem actual_seed_scalar_integrable (z : ℂ) (right : 1/4<z.re) :
 IntegrableOn (fun time:ℝ=>(time:ℂ)*Complex.exp (-z*(time:ℂ))) (Ioi 0) :=by
 let unit:=intervalConstant q
 let read:=(innerSL ℂ unit).comp (burnolRadiusRestriction q)
 have generated:=read.integrable_comp (J.actual_resonant_integrable z right J.seed)
 have qualified : inner ℂ unit unit≠0 :=inner_self_ne_zero.mpr (intervalConstant_ne_zero (by norm_num : (0:ℝ)<q))
 have paid:=generated.mul_const (inner ℂ unit unit)⁻¹
 apply paid.congr
 filter_upwards [ae_restrict_mem measurableSet_Ioi] with time positive
 change inner ℂ unit (burnolRadiusRestriction q (J.actualResonantIntegrand z J.seed time))*(inner ℂ unit unit)⁻¹=_
 rw [actual_jordan_seed_integrand_quarter z time positive.le,inner_smul_right,mul_assoc,
   mul_inv_cancel₀ qualified,mul_one]

private def actual_exponential_primitive (z : ℂ) (time : ℝ) : ℂ :=
 -(time/z+1/z^2)*Complex.exp (-z*(time:ℂ))

private theorem actual_exponential_primitive_derivative (z : ℂ) (nonzero : z≠0) (time : ℝ) :
 HasDerivAt (actual_exponential_primitive z) ((time:ℂ)*Complex.exp (-z*(time:ℂ))) time :=by
 have chart : HasDerivAt (fun time:ℝ=>(time:ℂ)) 1 time :=by
  convert! (Complex.ofRealCLM.hasFDerivAt (x:=time)).hasDerivAt using 1
 have generated:=((chart.div_const z).add_const (1/z^2)).neg.mul ((chart.const_mul (-z)).cexp)
 unfold actual_exponential_primitive
 convert! generated using 1
 simp only [Pi.neg_apply] 
 field_simp [nonzero]
 ring

private theorem actual_exponential_linear_decay (z : ℂ) (right : 1/4<z.re) :
 Tendsto (fun time:ℝ=>(time:ℂ)*Complex.exp (-z*(time:ℂ))) atTop (𝓝 0) :=by
 rw [tendsto_zero_iff_norm_tendsto_zero]
 have generated:=tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 1 z.re (by linarith)
 apply generated.congr'
 filter_upwards [Ioi_mem_atTop (0:ℝ)] with time positive
 rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos positive,Complex.norm_exp]
 simp only [Complex.mul_re,Complex.neg_re,Complex.ofReal_re,Complex.ofReal_im,mul_zero,sub_zero,Real.rpow_one,neg_mul]

/-- Actual source exponential current integrates to its generated coefficient, after source-admitted z qualification. -/
theorem actual_jordan_seed_exponential_coefficient (z : ℂ) (right : 1/4<z.re) :
 (∫ time:ℝ in Ioi 0,(time:ℂ)*Complex.exp (-z*(time:ℂ)))=1/z^2 :=by
 have qualified : z≠0:=by
  intro zero
  rw [zero] at right
  norm_num at right
 have exponential : Tendsto (fun time:ℝ=>Complex.exp (-z*(time:ℂ))) atTop (𝓝 0) :=by
  apply Complex.tendsto_exp_nhds_zero_iff.mpr
  have realLimit : Tendsto (fun time:ℝ=> -z.re*time) atTop atBot :=by
   exact (tendsto_const_mul_atBot_of_neg (by linarith : -z.re<0)).mpr tendsto_id
  simpa only [Complex.mul_re,Complex.neg_re,Complex.ofReal_re,Complex.ofReal_im,mul_zero,sub_zero,neg_mul] using realLimit
 have linear:=actual_exponential_linear_decay z right
 have decay : Tendsto (actual_exponential_primitive z) atTop (𝓝 0) :=by
  have generated:=(linear.div_const z).add (exponential.const_mul (1/z^2)) |>.neg
  convert! generated using 1
  · funext time
    unfold actual_exponential_primitive
    ring
  · simp
 have source:=integral_Ioi_of_hasDerivAt_of_tendsto'
   (a:=(0:ℝ)) (f:=actual_exponential_primitive z)
   (fun time _=>actual_exponential_primitive_derivative z qualified time)
   (actual_seed_scalar_integrable z right) decay
 simpa [actual_exponential_primitive] using source

/-- The complete quarter field is generated before any scalar physical readout. -/
theorem actual_jordan_seed_exact_quarter_field (z : ℂ) (right : 1/4<z.re) :
 burnolRadiusRestriction q (J.actualResonantField z J.seed)=(1/z^2:ℂ) • intervalConstant q :=by
 rw [actual_jordan_seed_quarter_field z right,actual_jordan_seed_exponential_coefficient z right]

theorem actual_jordan_seed_exact_complete_inventory (z : ℂ) (right : 1/4<z.re) :
 J.actualResonantField z J.seed=(1/z^2:ℂ) • J.seed+actualJordanSeedExterior z :=by
 rw [actual_jordan_seed_complete_inventory z right,actual_jordan_seed_exponential_coefficient z right]

end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKJordanSeedFieldSource
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
