import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Dirichlet
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Mellin
import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.Analysis.Complex.Convex

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 3000000

noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Continuation
open Complex Filter MeasureTheory Set BurnolPhysicalState
open OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Mellin.Source OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.Inverse.ReturnMellin
open OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Source OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Floor
open OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Mellin OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Dirichlet
open scoped Topology InnerProductSpace
open private log_top_bound logSource_zero from H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Mellin.Source
open private compact_memLp compact_origin from H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.Inverse.ReturnMellin
local notation "q" => (1/4:ℝ)

private theorem smooth_mellin_differentiable (w:ℂ) (below:w.re<1) (z:ℂ) (positive:0<z.re):
    DifferentiableAt ℂ (mellin (compactRaw (smoothRaw w below))) z:=by
  have regular:Continuous (smoothRaw w below):=(actual_smooth_contDiff w below).continuous
  have outside:∀x:ℝ,q < |x| → compactRaw (smoothRaw w below) x=0:=by
    intro x beyond
    exact indicator_of_notMem (s:=symmetricInterval q)
      (fun inside=>not_le_of_gt beyond (abs_le.mpr inside)) _
  have tail:compactRaw (smoothRaw w below)=O[atTop](fun x:ℝ=>x^(-(z.re+1))):=by
    simpa only [logSource_zero] using log_top_bound _ q outside 0 (z.re+1)
  exact mellin_differentiableAt_of_isBigO_rpow
    (((compact_memLp _ regular).locallyIntegrable (by norm_num)).locallyIntegrableOn _)
    tail (by linarith : z.re<z.re+1) (compact_origin _ regular) positive

def poleFreeSource (c:BurnolCompletedMellinCoordinate) (z:ℂ):ℂ:=
  (1/2:ℂ)*(q:ℂ)^(z-star c.value)+(z-star c.value)*
    mellin (compactRaw (smoothRaw c.value c.belowOne)) z

theorem actual_polefree_differentiable (c:BurnolCompletedMellinCoordinate)
    (z:ℂ) (positive:0<z.re):DifferentiableAt ℂ (poleFreeSource c) z:=by
  have idD:DifferentiableAt ℂ (fun z:ℂ=>z) z:=differentiableAt_id
  have power:DifferentiableAt ℂ (fun z:ℂ=>(q:ℂ)^(z-star c.value)) z:=
    (idD.sub_const _).const_cpow (Or.inl (by norm_num : (q:ℂ)≠0))
  exact (power.const_mul (1/2:ℂ)).add
    ((idD.sub_const _).mul (smooth_mellin_differentiable c.value c.belowOne z positive))

theorem actual_polefree_at_source (c:BurnolCompletedMellinCoordinate):
    poleFreeSource c (star c.value)=1/2:=by
  simp only [poleFreeSource,sub_self,Complex.cpow_zero,mul_one,zero_mul,add_zero]

private theorem oneSub_read (z:ℂ) (notOne:z≠1):riemannZeta₁ z=(z-1)*riemannZeta z:=by
  rw [riemannZeta_eq_inv_sub_mul notOne,←mul_assoc,mul_inv_cancel₀ (sub_ne_zero.mpr notOne),one_mul]

/-- The same entire one-sub zeta source transports the real integer-grid calculation to its whole Mellin domain. -/
theorem actual_counting_one_sub_source (c:BurnolCompletedMellinCoordinate)
    (zero:riemannZeta c.value=0) (z:ℂ) (positive:0<z.re):
    (z-1)*(z-star c.value)*mellin (fullFloorRaw c) z=riemannZeta₁ z*poleFreeSource c z:=by
  let U:Set ℂ:={z:ℂ|0<z.re}
  let left:ℂ→ℂ:=fun z=>(z-1)*(z-star c.value)*mellin (fullFloorRaw c) z
  let right:ℂ→ℂ:=fun z=>riemannZeta₁ z*poleFreeSource c z
  have openU:IsOpen U:=isOpen_lt continuous_const Complex.continuous_re
  have analyticLeft:AnalyticOnNhd ℂ left U:=by
    apply DifferentiableOn.analyticOnNhd _ openU
    intro u inside
    have value:DifferentiableAt ℂ (mellin (fullFloorRaw c)) u:=by
      simpa only [logSource_zero] using
        (actual_floor_log_derivative c zero 0 u inside).differentiableAt
    have idD:DifferentiableAt ℂ (fun u:ℂ=>u) u:=differentiableAt_id
    exact (((idD.sub_const 1).mul (idD.sub_const (star c.value))).mul value).differentiableWithinAt
  have analyticRight:AnalyticOnNhd ℂ right U:=by
    apply DifferentiableOn.analyticOnNhd _ openU
    intro u inside
    exact (differentiable_riemannZeta₁.differentiableAt.mul
      (actual_polefree_differentiable c u inside)).differentiableWithinAt
  have agreement (u:ℂ) (large:1<u.re):left u=right u:=by
    have source:=(actual_counting_source_factorization c.value c.belowOne u large).2
    change mellin (fullFloorRaw c) u=riemannZeta u*
      ((1/2:ℂ)*(q:ℂ)^(u-star c.value)/(u-star c.value)+
        mellin (compactRaw (smoothRaw c.value c.belowOne)) u) at source
    have notOne:u≠1:=by intro eq;simp only [eq,one_re,lt_self_iff_false] at large
    have notSource:u-star c.value≠0:=by
      intro eq
      have real:=congrArg Complex.re eq
      simp only [sub_re,star_def,conj_re,zero_re] at real
      linarith [c.belowOne]
    dsimp only [left,right,poleFreeSource]
    rw [source,oneSub_read u notOne]
    field_simp
  have same:=analyticLeft.eqOn_of_preconnected_of_eventuallyEq analyticRight
    (convex_halfSpace_re_gt (0:ℝ)).isPreconnected
    (show (2:ℂ)∈U by norm_num [U])
    (eventuallyEq_of_mem ((isOpen_lt continuous_const Complex.continuous_re).mem_nhds
      (by norm_num : (1:ℝ)<(2:ℂ).re)) agreement)
  exact same positive

theorem actual_counting_pole_cleared_source (c:BurnolCompletedMellinCoordinate)
    (zero:riemannZeta c.value=0) (z:ℂ) (positive:0<z.re) (notOne:z≠1):
    (z-star c.value)*mellin (fullFloorRaw c) z=riemannZeta z*poleFreeSource c z:=by
  have source:=actual_counting_one_sub_source c zero z positive
  rw [oneSub_read z notOne] at source
  apply mul_left_cancel₀ (sub_ne_zero.mpr notOne)
  simpa only [mul_assoc] using source

end OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Continuation
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
