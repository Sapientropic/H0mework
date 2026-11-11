import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Mellin.Schwartz
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Mellin.Muntz.ExactOrder
import Mathlib.Analysis.Calculus.Deriv.Abs
set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2600000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Mellin.Muntz.TateApprox
open Complex Filter MeasureTheory Set BurnolPhysicalState
open OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Mellin.Schwartz
open scoped Topology ContDiff
local notation "q" => (1/4:ℝ)

def tateRaw (c:BurnolCompletedMellinCoordinate) (zero:riemannZeta c.value=0)
    (h:ℝ) (nonnegative:0≤h) (N:ℕ) (x:ℝ):ℂ :=
  if x=0 then 0 else ((|x|:ℝ):ℂ)⁻¹*schwartzApprox c zero h nonnegative N x⁻¹

private theorem tate_inner_zero (c:BurnolCompletedMellinCoordinate) (zero:riemannZeta c.value=0)
    (h:ℝ) (nonnegative:0≤h) (N:ℕ) (x:ℝ) (inside:|x|<1/2):
    tateRaw c zero h nonnegative N x=0:=by
  by_cases origin:x=0
  · simp only [tateRaw,if_pos origin]
  · rw [tateRaw,if_neg origin,actual_schwartz_outer_zero c zero h nonnegative N x⁻¹, mul_zero]
    rw [abs_inv]
    have positive:0 < |x|:=abs_pos.mpr origin
    calc
      _≤1:=by nlinarith [radius_bound N]
      _≤|x|⁻¹:=one_le_inv_iff₀.mpr ⟨positive,by linarith⟩

private theorem tate_smooth (c:BurnolCompletedMellinCoordinate) (zero:riemannZeta c.value=0)
    (h:ℝ) (nonnegative:0≤h) (N:ℕ):ContDiff ℝ ∞ (tateRaw c zero h nonnegative N):=by
  rw [contDiff_iff_contDiffAt]
  intro x
  by_cases origin:x=0
  · subst x
    have near:∀ᶠy:ℝ in 𝓝 0,|y|<1/2:=
      (isOpen_lt continuous_abs continuous_const).mem_nhds (by norm_num)
    refine (contDiffAt_const:ContDiffAt ℝ ∞ (fun _:ℝ=>(0:ℂ)) 0).congr_of_eventuallyEq ?_
    filter_upwards [near] with y hy
    exact tate_inner_zero c zero h nonnegative N y hy
  · have near:∀ᶠy:ℝ in 𝓝 x,y≠0:=eventually_ne_nhds origin
    have absSmooth:ContDiffAt ℝ ∞ (fun y:ℝ=>|y|) x:=
      contDiffAt_abs (n:=(⊤:ℕ∞)) origin
    have absComplex:ContDiffAt ℝ ∞ (fun y:ℝ=>((|y|:ℝ):ℂ)) x:=
      Complex.ofRealCLM.contDiff.contDiffAt.comp x absSmooth
    have invSmooth:ContDiffAt ℝ ∞ (fun y:ℝ=>y⁻¹) x:=contDiffAt_inv ℝ origin
    have source:ContDiffAt ℝ ∞ (fun y:ℝ=>schwartzApprox c zero h nonnegative N y⁻¹) x:=
      ((schwartzApprox c zero h nonnegative N).contDiffAt (⊤:ℕ∞)).comp x invSmooth
    refine ((absComplex.inv (Complex.ofReal_ne_zero.mpr (abs_ne_zero.mpr origin))).mul source).congr_of_eventuallyEq ?_
    filter_upwards [near] with y hy
    simp only [tateRaw,if_neg hy,Pi.inv_apply]

private theorem tate_outer_zero (c:BurnolCompletedMellinCoordinate) (zero:riemannZeta c.value=0)
    (h:ℝ) (nonnegative:0≤h) (N:ℕ) (x:ℝ) (outside:(radius N)⁻¹ < |x|):
    tateRaw c zero h nonnegative N x=0:=by
  have positive:0 < |x|:=(inv_pos.mpr (radius_positive N)).trans outside
  rw [tateRaw,if_neg (abs_pos.mp positive),actual_schwartz_inner_zero c zero h nonnegative N x⁻¹,mul_zero]
  rw [abs_inv]
  exact (inv_le_comm₀ positive (radius_positive N)).mpr outside.le

private theorem tate_compact (c:BurnolCompletedMellinCoordinate) (zero:riemannZeta c.value=0)
    (h:ℝ) (nonnegative:0≤h) (N:ℕ):HasCompactSupport (tateRaw c zero h nonnegative N):=by
  apply HasCompactSupport.of_support_subset_isCompact
    (isCompact_Icc (a:= -(radius N)⁻¹) (b:=(radius N)⁻¹))
  intro x nonzero
  apply abs_le.mp
  by_contra outside
  exact nonzero (tate_outer_zero c zero h nonnegative N x (lt_of_not_ge outside))

/-- The Tate member is constructed from the actual shrinking annulus, with no fixed-q admission. -/
def tateApprox (c:BurnolCompletedMellinCoordinate) (zero:riemannZeta c.value=0)
    (h:ℝ) (nonnegative:0≤h) (N:ℕ):SchwartzMap ℝ ℂ:=
  (tate_compact c zero h nonnegative N).toSchwartzMap (tate_smooth c zero h nonnegative N)

theorem actual_tate_even (c:BurnolCompletedMellinCoordinate) (zero:riemannZeta c.value=0)
    (h:ℝ) (nonnegative:0≤h) (N:ℕ) (x:ℝ):
    tateApprox c zero h nonnegative N (-x)=tateApprox c zero h nonnegative N x:=by
  change tateRaw c zero h nonnegative N (-x)=tateRaw c zero h nonnegative N x
  by_cases origin:x=0
  · subst x; rw [neg_zero]
  · simp only [tateRaw,if_neg origin,if_neg (neg_ne_zero.mpr origin),abs_neg,inv_neg,
      actual_schwartz_even]

theorem actual_tate_mellin (c:BurnolCompletedMellinCoordinate) (zero:riemannZeta c.value=0)
    (h:ℝ) (nonnegative:0≤h) (N:ℕ) (w:ℂ):
    mellin (tateApprox c zero h nonnegative N) w=
      mellin (schwartzApprox c zero h nonnegative N) (1-w):=by
  calc
    _=mellin (fun x:ℝ=>(x:ℂ)^(-1:ℂ) • schwartzApprox c zero h nonnegative N x⁻¹) w:=by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro x hx
      change (x:ℂ)^(w-1) • tateRaw c zero h nonnegative N x=
        (x:ℂ)^(w-1) • ((x:ℂ)^(-1:ℂ) • schwartzApprox c zero h nonnegative N x⁻¹)
      congr 1
      rw [tateRaw,if_neg (ne_of_gt hx),abs_of_pos hx,Complex.cpow_neg_one,smul_eq_mul]
    _=mellin (fun x:ℝ=>schwartzApprox c zero h nonnegative N x⁻¹) (w+(-1)):=
      mellin_cpow_smul _ w (-1)
    _=mellin (schwartzApprox c zero h nonnegative N) (1-w):=by
      rw [mellin_comp_inv]
      congr 1
      ring

theorem actual_schwartz_muntz (c:BurnolCompletedMellinCoordinate) (zero:riemannZeta c.value=0)
    (h:ℝ) (nonnegative:0≤h) (N:ℕ) (w:ℂ) (positive:0<w.re) (below:w.re<1):
    mellin (coPoissonMuntzScaleRemainder (schwartzApprox c zero h nonnegative N)) w=
      riemannZeta w*coPoissonMuntzEvenSourceMellin (schwartzApprox c zero h nonnegative N) w:=
  coPoissonMuntzScaleRemainder_mellin_factorization _ positive below

theorem actual_tate_muntz (c:BurnolCompletedMellinCoordinate) (zero:riemannZeta c.value=0)
    (h:ℝ) (nonnegative:0≤h) (N:ℕ) (w:ℂ) (positive:0<w.re) (below:w.re<1):
    mellin (coPoissonMuntzScaleRemainder (tateApprox c zero h nonnegative N)) w=
      riemannZeta w*coPoissonMuntzEvenSourceMellin (tateApprox c zero h nonnegative N) w:=
  coPoissonMuntzScaleRemainder_mellin_factorization _ positive below

theorem actual_original_order_schwartz (c:BurnolCompletedMellinCoordinate) (zero:riemannZeta c.value=0)
    (h:ℝ) (nonnegative:0≤h) (N:ℕ):
    mellin (coPoissonMuntzScaleRemainder (schwartzApprox c zero h nonnegative N)) c.value=0:=
  OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Mellin.Muntz.ExactOrder.actual_cutoff_zero_read c zero _

theorem actual_original_order_tate (c:BurnolCompletedMellinCoordinate) (zero:riemannZeta c.value=0)
    (h:ℝ) (nonnegative:0≤h) (N:ℕ):
    mellin (coPoissonMuntzScaleRemainder (tateApprox c zero h nonnegative N)) c.value=0:=
  OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Mellin.Muntz.ExactOrder.actual_cutoff_zero_read c zero _

end OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Mellin.Muntz.TateApprox
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
