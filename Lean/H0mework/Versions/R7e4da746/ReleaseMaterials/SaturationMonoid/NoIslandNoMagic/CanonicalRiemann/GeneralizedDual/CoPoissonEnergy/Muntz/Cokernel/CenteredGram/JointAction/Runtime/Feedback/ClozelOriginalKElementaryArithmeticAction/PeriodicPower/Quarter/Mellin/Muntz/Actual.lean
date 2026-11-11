import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Mellin.Muntz.ImageRead
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Mellin.Muntz.CountedBound
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Mellin.Muntz.ImageLimit
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Mellin.SchwartzMellin
set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2800000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Mellin.Muntz.Actual
open Complex Filter MeasureTheory Set BurnolPhysicalState
open OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.CoPoisson.DirectBound OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.CoPoisson.Forward
open OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Mellin.Schwartz OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Mellin.SchwartzMellin
open OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Mellin.Muntz.ImageRead OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Mellin.Muntz.CountedLimit
open OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Mellin.Muntz.CountedBound OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Mellin.Muntz.ImageLimit
open OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Mellin.Muntz.CoSumLimit OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Mellin.ReciprocalTail
open scoped Topology
open private pweight channel forward_reindex forward_measurable from H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.CoPoisson.Forward

private theorem source_outside (c:BurnolCompletedMellinCoordinate) (zero:riemannZeta c.value=0)
    (h:ℝ) (nonnegative:0≤h) (N:ℕ) (x:ℝ) (outside:(1/2:ℝ)≤|x|):
    schwartzApprox c zero h nonnegative N x=0:=
  actual_schwartz_outer_zero c zero h nonnegative N x (by linarith [radius_bound N])

private theorem source_origin (c:BurnolCompletedMellinCoordinate) (zero:riemannZeta c.value=0)
    (h:ℝ) (nonnegative:0≤h) (N:ℕ):schwartzApprox c zero h nonnegative N 0=0:=
  actual_schwartz_inner_zero c zero h nonnegative N 0 (by simpa using (radius_positive N).le)

private theorem counted_measurable (test:SchwartzMap ℝ ℂ):Measurable (countedImage test):=by
  unfold countedImage
  exact ((Complex.measurable_ofReal.comp measurable_id).inv.mul
    (Measurable.tsum (fun n=>test.continuous.measurable.comp (measurable_const.div measurable_id)))).sub_const _

/-- Both means and the whole arithmetic co-sum survive the actual Schwartz limit. -/
theorem actual_counted_mellin (c:BurnolCompletedMellinCoordinate) (zero:riemannZeta c.value=0)
    (h:ℝ) (nonnegative:0≤h) (w:ℂ) (positive:0<w.re) (below:w.re<1):
    mellin (countedImage (directRaw c h)) w=riemannZeta (1-w)*mellin (directRaw c h) (1-w):=by
  let C:NNReal:=4*sourceLipschitz c zero h nonnegative
  have left:=actual_image_mellin_limit
    (fun N=>countedImage (schwartzApprox c zero h nonnegative N)) (countedImage (directRaw c h)) C
    (fun N=>counted_measurable _)
    (fun N x hx small=>actual_counted_head _ C
      (actual_schwartz_global_lipschitz c zero h nonnegative N)
      (source_origin c zero h nonnegative N) (source_outside c zero h nonnegative N) x hx small)
    (fun N x hx=>actual_counted_tail _ C (actual_schwartz_global_lipschitz c zero h nonnegative N)
      (source_outside c zero h nonnegative N) x (by linarith))
    (fun x hx=>actual_counted_pointwise_limit
      (fun N=>schwartzApprox c zero h nonnegative N) (directRaw c h) C C.coe_nonneg
      (fun N=>(schwartzApprox c zero h nonnegative N).continuous.measurable)
      (actual_schwartz_linear_bound c zero h nonnegative)
      (fun N x outside=>source_outside c zero h nonnegative N x outside.le)
      (actual_schwartz_tendsto c zero h nonnegative) x hx) w positive below
  have right: Tendsto
      (fun N:ℕ=>mellin (countedImage (schwartzApprox c zero h nonnegative N)) w) atTop
      (𝓝 (riemannZeta (1-w)*mellin (directRaw c h) (1-w))):=by
    have source:= (actual_schwartz_mellin_limit c zero h nonnegative (1-w)
      (by simp only [sub_re,one_re];linarith)).const_mul (riemannZeta (1-w))
    exact source.congr' (Eventually.of_forall (fun N=>(actual_cutoff_counted_mellin c zero h nonnegative N w positive below).symm))
  exact tendsto_nhds_unique left right

/-- The other actual source image retains its reciprocal Unit in the same limit. -/
theorem actual_forward_mellin (c:BurnolCompletedMellinCoordinate) (zero:riemannZeta c.value=0)
    (h:ℝ) (nonnegative:0≤h) (w:ℂ) (positive:0<w.re) (below:w.re<1):
    mellin (directField c h) w=riemannZeta (1-w)*mellin (directRaw c h) w:=by
  let C:NNReal:=4*sourceLipschitz c zero h nonnegative
  let mass:ℝ:=∑'n:ℕ,pweight n
  let B:ℝ:=(C:ℝ)*(mass+3)
  have massNonnegative:0≤mass:=tsum_nonneg (fun n=>by unfold pweight;positivity)
  have field_eq:directField c h=forwardImage (directRaw c h):=rfl
  rw [field_eq]
  have left:=actual_image_mellin_limit
    (fun N=>forwardImage (schwartzApprox c zero h nonnegative N)) (forwardImage (directRaw c h)) B
    (fun N=>(forward_measurable _ (schwartzApprox c zero h nonnegative N).continuous.measurable).sub_const _)
    (fun N x hx small=>by
      have paid:=actual_complete_direct_head _ C (actual_schwartz_global_lipschitz c zero h nonnegative N)
        (source_origin c zero h nonnegative N) (source_outside c zero h nonnegative N) x hx small
      change ‖forwardImage (schwartzApprox c zero h nonnegative N) x‖≤B
      apply (show ‖forwardImage (schwartzApprox c zero h nonnegative N) x‖≤(C:ℝ)*(mass+1) from
        by simpa only [forwardImage,forward_reindex,channel] using paid).trans
      dsimp only [B]
      nlinarith [C.coe_nonneg])
    (fun N x large=>by
      have hx:0<x:=by linarith
      have paid:=actual_complete_direct_tail _ C (actual_schwartz_global_lipschitz c zero h nonnegative N)
        (source_origin c zero h nonnegative N) (source_outside c zero h nonnegative N) x hx
      apply (show ‖forwardImage (schwartzApprox c zero h nonnegative N) x‖≤2*(C:ℝ)/x from
        by simpa only [forwardImage,forward_reindex,channel] using paid).trans
      apply div_le_div_of_nonneg_right _ hx.le
      dsimp only [B]
      nlinarith [C.coe_nonneg,mul_nonneg C.coe_nonneg massNonnegative])
    (fun x _=>actual_forward_image_pointwise_limit
      (fun N=>schwartzApprox c zero h nonnegative N) (directRaw c h) C
      (fun N=>(schwartzApprox c zero h nonnegative N).continuous.measurable)
      (actual_schwartz_linear_bound c zero h nonnegative)
      (fun N x outside=>source_outside c zero h nonnegative N x outside.le)
      (actual_schwartz_tendsto c zero h nonnegative) x) w positive below
  have right: Tendsto
      (fun N:ℕ=>mellin (forwardImage (schwartzApprox c zero h nonnegative N)) w) atTop
      (𝓝 (riemannZeta (1-w)*mellin (directRaw c h) w)):=by
    have source:=(actual_schwartz_mellin_limit c zero h nonnegative w (by linarith)).const_mul (riemannZeta (1-w))
    exact source.congr' (Eventually.of_forall (fun N=>(actual_cutoff_forward_mellin c zero h nonnegative N w positive below).symm))
  exact tendsto_nhds_unique left right

theorem actual_original_forward_zero (c:BurnolCompletedMellinCoordinate) (zero:riemannZeta c.value=0)
    (h:ℝ) (nonnegative:0≤h):mellin (directField c h) (1-c.value)=0:=by
  rw [actual_forward_mellin c zero h nonnegative (1-c.value)
    (by simp only [sub_re,one_re];linarith[c.belowOne])
    (by simp only [sub_re,one_re];linarith[c.rightHalf]),
    show 1-(1-c.value)=c.value by ring,zero,zero_mul]

theorem actual_original_counted_zero (c:BurnolCompletedMellinCoordinate) (zero:riemannZeta c.value=0)
    (h:ℝ) (nonnegative:0≤h):mellin (countedImage (directRaw c h)) (1-c.value)=0:=by
  rw [actual_counted_mellin c zero h nonnegative (1-c.value)
    (by simp only [sub_re,one_re];linarith[c.belowOne])
    (by simp only [sub_re,one_re];linarith[c.rightHalf]),
    show 1-(1-c.value)=c.value by ring,zero,zero_mul]

end OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Mellin.Muntz.Actual
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
