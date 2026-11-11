import Mathlib.Analysis.MellinTransform
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Gamma.Source.GammaRadialRawSource
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Gamma.Source.GammaRadialTailSource
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Gamma.Source.GammaSeedExteriorSource
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Gamma.Source.KGammaSource
import H0mework.Arithmetic.BurnolCarrier.ConstantGapFace
import H0mework.Arithmetic.MellinProjection.TailKernel

set_option autoImplicit false
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
namespace OriginalGamma.Source.GammaSeedMellinDomain
open Complex Filter MeasureTheory Set
open scoped InnerProductSpace Topology
open OriginalGamma.Source.KGamma OriginalGamma.Source.GammaSeedExterior
open OriginalGamma.Source.GammaRadialRaw OriginalGamma.Source.GammaRadialTail
noncomputable section
local notation "q" => (1/4:ℝ)

theorem actual_gamma_seed_exterior_inverse_bound (x : ℝ) (large : (1/2:ℝ)≤x) :
    ‖actualGammaSeedExteriorRaw x‖≤(1/2:ℝ)/x := by
  have xpos : 0<x := lt_of_lt_of_le (by norm_num) large
  have minusPos : 0<x-q := by linarith
  have plusPos : 0<x+q := by linarith
  have ratioPos : 0<(x+q)/(x-q) := div_pos plusPos minusPos
  have oneRatio : 1≤(x+q)/(x-q) := by
    apply (le_div_iff₀ minusPos).mpr
    linarith
  have logPos : 0≤Real.log ((x+q)/(x-q)) := Real.log_nonneg oneRatio
  have logBound := Real.log_le_sub_one_of_pos ratioPos
  have ratioPrice : (x+q)/(x-q)-1=2*q/(x-q) := by
    rw [div_sub_one minusPos.ne']
    congr 1
    ring
  have fraction : q/(x-q)≤2*q/x := by
    apply (div_le_div_iff₀ minusPos xpos).mpr
    nlinarith
  unfold actualGammaSeedExteriorRaw
  rw [abs_of_pos xpos,norm_neg,Complex.norm_real,Real.norm_eq_abs,
    ←Real.log_div plusPos.ne' minusPos.ne',abs_of_nonneg (div_nonneg logPos (by norm_num))]
  have bound : Real.log ((x+q)/(x-q))/2≤q/(x-q) := by
    rw [ratioPrice] at logBound
    rw [mul_div_assoc] at logBound
    linarith
  exact bound.trans (by norm_num only [show 2*q=(1/2:ℝ) by norm_num] at fraction ⊢;exact fraction)

theorem actual_gamma_seed_mellin_tail_integrable (c : BurnolCompletedMellinCoordinate) :
    IntegrableOn (fun x : ℝ=>(x:ℂ)^(star c.value-1)*gammaSeedRaw x) (Ioi (1/2:ℝ)) := by
  have powerMeasured : Measurable (fun x : ℝ=>(x:ℂ)^(star c.value-1)) := by
    apply measurable_of_continuousOn_compl_singleton 0
    intro x nonzero
    exact (Complex.continuousAt_ofReal_cpow_const x _ (Or.inr nonzero)).continuousWithinAt
  have bound := (integrableOn_Ioi_rpow_of_lt (by linarith [c.belowOne] : c.value.re-2 < -1)
    (by norm_num : (0:ℝ)<1/2)).const_mul (1/2:ℝ)
  apply bound.mono' (powerMeasured.mul gammaSeedRaw_measurable).aestronglyMeasurable
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with x inside
  have lower : (1/2:ℝ)<x := inside
  have xpos : 0<x := lt_trans (by norm_num) inside
  have exterior : gammaSeedRaw x=actualGammaSeedExteriorRaw x := by
    rw [gammaSeedRaw,if_pos (by rw [abs_of_pos xpos];linarith : q < |x|)]
  change ‖(x:ℂ)^(star c.value-1)*gammaSeedRaw x‖≤(1/2:ℝ)*x^(c.value.re-2)
  rw [norm_mul,Complex.norm_cpow_eq_rpow_re_of_pos xpos,exterior]
  simp only [sub_re,star_def,conj_re,one_re]
  calc
    x^(c.value.re-1)*‖actualGammaSeedExteriorRaw x‖≤x^(c.value.re-1)*((1/2:ℝ)/x) :=
      mul_le_mul_of_nonneg_left (actual_gamma_seed_exterior_inverse_bound x inside.le) (Real.rpow_nonneg xpos.le _)
    _=(1/2:ℝ)*x^(c.value.re-2) := by
      rw [div_eq_mul_inv,←Real.rpow_neg_one,←mul_assoc,mul_comm _ (1/2:ℝ),mul_assoc,
        ←Real.rpow_add xpos]
      congr 2
      ring

theorem actual_gamma_seed_mellin_domain (c : BurnolCompletedMellinCoordinate) :
    MellinConvergent gammaSeedRaw (star c.value) := by
  have near := actual_original_gamma_mellin_primitive_integrable c (1/2) (by norm_num)
  have nearClosed : IntegrableOn (fun x : ℝ=>(x:ℂ)^(star c.value-1)*gammaSeedRaw x) (Ioc 0 (1/2:ℝ)) := by
    change Integrable _ (volume.restrict (Ioc (0:ℝ) (1/2)))
    rw [←Measure.restrict_congr_set (Ioo_ae_eq_Ioc (μ:=volume) (a:=(0:ℝ)) (b:=1/2))]
    exact near
  have total := nearClosed.union (actual_gamma_seed_mellin_tail_integrable c)
  have domains : Ioc (0:ℝ) (1/2)∪Ioi (1/2)=Ioi 0 := by
    ext x
    simp only [mem_union,mem_Ioc,mem_Ioi]
    constructor
    · rintro (⟨lower,_⟩|upper)
      · exact lower
      · linarith
    · intro positive
      by_cases upper : x≤1/2
      · exact Or.inl ⟨positive,upper⟩
      · exact Or.inr (lt_of_not_ge upper)
  rw [domains] at total
  exact total

theorem actual_gamma_seed_original_mellin_domain (c : BurnolCompletedMellinCoordinate) :
    MellinConvergent (actualGammaSeed:ℝ→ℂ) (star c.value) := by
  apply (actual_gamma_seed_mellin_domain c).congr
  filter_upwards [ae_restrict_of_ae (s:=Ioi (0:ℝ)) actual_gamma_seed_whole_raw] with x source
  rw [source]

end
end OriginalGamma.Source.GammaSeedMellinDomain
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
