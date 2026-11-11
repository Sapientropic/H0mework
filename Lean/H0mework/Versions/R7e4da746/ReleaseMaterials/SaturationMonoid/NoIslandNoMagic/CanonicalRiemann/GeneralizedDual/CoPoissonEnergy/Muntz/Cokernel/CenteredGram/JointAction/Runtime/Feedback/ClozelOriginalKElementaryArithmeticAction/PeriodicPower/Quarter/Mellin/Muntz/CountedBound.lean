import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Mellin.Muntz.CountedLimit
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Mellin.ReciprocalTail
set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2600000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Mellin.Muntz.CountedBound
open Complex Filter MeasureTheory Set BurnolPhysicalState
open OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Mellin.Muntz.CountedLimit OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Mellin.ReciprocalProfile
open OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Mellin.ReciprocalQuadrature
open scoped Topology
open private derivative_outside from H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Mellin.ReciprocalProfile

def unitMajor (C:ℝ):ℝ→ℝ:=(Ioc (0:ℝ) 1).indicator (fun _=>C)

private theorem major_integrable (C:ℝ):Integrable (unitMajor C):=
  (integrableOn_const (C:=C) (s:=Ioc (0:ℝ) 1)
    (by exact measure_Ioc_lt_top.ne)).integrable_indicator measurableSet_Ioc

private theorem major_integral (C:ℝ):(∫u:ℝ in Ioi 0,unitMajor C u)=C:=by
  rw [unitMajor,setIntegral_indicator measurableSet_Ioc,
    inter_eq_right.mpr (Ioc_subset_Ioi_self),setIntegral_const]
  norm_num

private theorem norm_bound_integral (g:ℝ→ℂ) (integrable:Integrable g) (C:ℝ)
    (bound:∀u,0<u→‖g u‖≤unitMajor C u):
    (∫u:ℝ in Ioi 0,‖g u‖)≤C:=by
  rw [←major_integral C]
  apply integral_mono_ae integrable.integrableOn.norm (major_integrable C).integrableOn
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
  exact bound u hu

private theorem slope_integral (f:SchwartzMap ℝ ℂ) (C:NNReal)
    (lip:LipschitzWith C (f:ℝ→ℂ))
    (outside:∀u:ℝ,(1/2:ℝ)≤|u|→f u=0):
    (∫u:ℝ in Ioi 0,‖deriv f u‖)≤(C:ℝ):=by
  apply norm_bound_integral (fun u:ℝ=>deriv f u) (SchwartzMap.derivCLM ℂ ℂ f).integrable C
  intro u positive
  unfold unitMajor
  by_cases inside:u≤1
  · rw [indicator_of_mem (show u∈Ioc (0:ℝ) 1 from ⟨positive,inside⟩)]
    exact norm_deriv_le_of_lipschitz lip
  · rw [indicator_of_notMem (show u∉Ioc (0:ℝ) 1 from fun member=>inside member.2),
      derivative_outside f outside u (by rw [abs_of_pos positive];linarith [lt_of_not_ge inside]),norm_zero]

private theorem mass_bound (f:SchwartzMap ℝ ℂ) (C:NNReal)
    (lip:LipschitzWith C (f:ℝ→ℂ)) (origin:f 0=0)
    (outside:∀u:ℝ,(1/2:ℝ)≤|u|→f u=0):
    ‖∫u:ℝ in Ioi 0,f u‖≤(C:ℝ):=by
  apply (norm_integral_le_integral_norm _).trans
  apply norm_bound_integral f f.integrable C
  intro u positive
  unfold unitMajor
  by_cases inside:u≤1
  · rw [indicator_of_mem (show u∈Ioc (0:ℝ) 1 from ⟨positive,inside⟩)]
    exact (actual_origin_growth f C lip origin u).trans (by rw [abs_of_pos positive];nlinarith [C.coe_nonneg])
  · rw [indicator_of_notMem (show u∉Ioc (0:ℝ) 1 from fun member=>inside member.2),
      outside u (by rw [abs_of_pos positive];linarith [lt_of_not_ge inside]),norm_zero]

theorem actual_counted_tail (f:SchwartzMap ℝ ℂ) (C:NNReal)
    (lip:LipschitzWith C (f:ℝ→ℂ))
    (outside:∀u:ℝ,(1/2:ℝ)≤|u|→f u=0) (x:ℝ) (positive:0<x):
    ‖countedImage f x‖≤(C:ℝ)/x:=by
  have summable:Summable (fun n:ℕ=>f (((n+1:ℕ):ℝ)*x⁻¹)):=by
    obtain ⟨M,bound⟩:=exists_nat_gt x
    apply summable_of_ne_finset_zero (s:=Finset.range M)
    intro n notin
    have order:M≤n:=Nat.le_of_not_gt (by simpa only [Finset.mem_range] using notin)
    have cast:(M:ℝ)≤n:=by exact_mod_cast order
    apply outside
    rw [abs_of_nonneg (by positivity)]
    apply (le_mul_inv_iff₀ positive).mpr
    push_cast
    linarith
  have derivativeContinuous:Continuous (fun u:ℝ=>deriv f u):=(SchwartzMap.derivCLM ℂ ℂ f).continuous
  have paid:=actual_infinite_grid_variation f (fun u:ℝ=>deriv f u) derivativeContinuous
    (fun u _=>f.hasDerivAt u) f.integrable.integrableOn
    (SchwartzMap.derivCLM ℂ ℂ f).integrable.integrableOn
    x⁻¹ (inv_pos.mpr positive) summable
  simpa only [countedImage,div_eq_mul_inv,Complex.ofReal_inv] using
    paid.trans ((mul_le_mul_of_nonneg_left (slope_integral f C lip outside)
      (inv_nonneg.mpr positive.le)).trans_eq (by ring))

theorem actual_counted_head (f:SchwartzMap ℝ ℂ) (C:NNReal)
    (lip:LipschitzWith C (f:ℝ→ℂ)) (origin:f 0=0)
    (outside:∀u:ℝ,(1/2:ℝ)≤|u|→f u=0) (x:ℝ) (positive:0<x) (small:x≤1):
    ‖countedImage f x‖≤(C:ℝ):=by
  have vanish (n:ℕ):f ((n+1:ℕ)/x)=0:=by
    apply outside
    rw [abs_of_nonneg (by positivity)]
    apply (le_div_iff₀ positive).mpr
    push_cast
    have natnonnegative:(0:ℝ)≤n:=by positivity
    linarith
  rw [countedImage,tsum_congr (fun n=>vanish n),tsum_zero,mul_zero,zero_sub,norm_neg]
  exact mass_bound f C lip origin outside

end OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Mellin.Muntz.CountedBound
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
