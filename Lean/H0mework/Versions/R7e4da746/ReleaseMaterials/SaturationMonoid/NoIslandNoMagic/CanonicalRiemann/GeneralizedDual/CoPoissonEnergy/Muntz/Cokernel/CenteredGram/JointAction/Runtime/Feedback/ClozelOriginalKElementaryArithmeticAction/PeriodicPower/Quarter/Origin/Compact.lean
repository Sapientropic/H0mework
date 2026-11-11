import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Alias.Continuous
import H0mework.Versions.R7e4da746.Arithmetic.MellinProjection.FiniteWindow
import Mathlib.Analysis.Fourier.PoissonSummation
import Mathlib.Analysis.Fourier.FourierTransformDeriv
set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Origin.Compact
open Complex Filter MeasureTheory Set BurnolPhysicalState FourierTransform
open OriginalRieszSource OriginalRieszSourceGreen
open OriginalKElementaryArithmeticAction.PeriodicPower.Resolved OriginalKElementaryArithmeticAction.PeriodicPower.Alias.Continuous
open scoped Topology InnerProductSpace FourierTransform
local notation "q"=>(1/4:ℝ)
local notation "F"=>fourierL2

def waveCharacter (c:BurnolCompletedMellinCoordinate) (h:ℝ):ℂ :=
  fullMellinTranslationCharacter (star c.value) (-h)
def waveRadius (h:ℝ):ℝ:=q*Real.exp h
def compactWave (c:BurnolCompletedMellinCoordinate) (h:ℝ):BurnolL2:=
  burnolMultiplicativeDilation (-h) (resolvedSource c)-waveCharacter c h • resolvedSource c

def compactRaw (c:BurnolCompletedMellinCoordinate) (h x:ℝ):ℂ :=
  (Real.exp (-h/2):ℂ)*resolvedRaw c (Real.exp (-h)*x)-waveCharacter c h*resolvedRaw c x

theorem actual_compact_raw_continuous (c:BurnolCompletedMellinCoordinate) (h:ℝ):
    Continuous (compactRaw c h):=
  (continuous_const.mul ((actual_resolved_continuous c).comp (continuous_const.mul continuous_id))).sub
    (continuous_const.mul (actual_resolved_continuous c))

theorem actual_compact_raw (c:BurnolCompletedMellinCoordinate) (h:ℝ):
    (compactWave c h:ℝ→ℂ)=ᵐ[volume]compactRaw c h := by
  have scale:Measure.QuasiMeasurePreserving (fun x:ℝ=>Real.exp (-h)*x) volume volume:=by
    simpa only [smul_eq_mul] using
      (Measure.quasiMeasurePreserving_smul (μ:=(volume:Measure ℝ))
        (r:=Real.exp (-h)) (Real.exp_ne_zero (-h)))
  filter_upwards [Lp.coeFn_sub (burnolMultiplicativeDilation (-h) (resolvedSource c))
      (waveCharacter c h • resolvedSource c),
    burnolMultiplicativeDilation_coeFn (-h) (resolvedSource c),
    Lp.coeFn_smul (waveCharacter c h) (resolvedSource c),actual_resolved_raw c,
    scale.ae (actual_resolved_raw c)] with x difference dilation scalar direct moved
  change (burnolMultiplicativeDilation (-h) (resolvedSource c)-waveCharacter c h • resolvedSource c:BurnolL2) x=_
  rw [difference,Pi.sub_apply,dilation,scalar,Pi.smul_apply,smul_eq_mul,direct]
  change (Real.exp (-h/2):ℂ)*resolvedSource c (Real.exp (-h)*x)-waveCharacter c h*resolvedRaw c x=_
  rw [moved]
  rfl

private theorem power_scale (c:BurnolCompletedMellinCoordinate) (h x:ℝ) (positive:0<x):
    (Real.exp (-h/2):ℂ)*(Real.exp (-h)*x:ℂ)^(-star c.value)=
      waveCharacter c h*(x:ℂ)^(-star c.value) := by
  have ne:(Real.exp (-h):ℂ)≠0:=Complex.ofReal_ne_zero.mpr (Real.exp_ne_zero (-h))
  rw [show (Real.exp (-h)*x:ℂ)=(Real.exp (-h):ℂ)*(x:ℂ) by push_cast;rfl,
    Complex.mul_cpow_ofReal_nonneg (Real.exp_pos (-h)).le positive.le,
    Complex.cpow_def_of_ne_zero ne,←Complex.ofReal_log (Real.exp_pos (-h)).le,Real.log_exp]
  rw [←mul_assoc,Complex.ofReal_exp,←Complex.exp_add]
  unfold waveCharacter fullMellinTranslationCharacter
  congr 1
  congr 1
  push_cast
  ring

theorem actual_compact_outside (c:BurnolCompletedMellinCoordinate) (h:ℝ)
    (nonnegative:0≤h) (x:ℝ) (outside:waveRadius h < |x|):compactRaw c h x=0 := by
  have expOne:1≤Real.exp h:=Real.one_le_exp_iff.mpr nonnegative
  have lower:q < |x|:=by unfold waveRadius at outside;nlinarith
  have moved:q<Real.exp (-h)*|x|:=by
    rw [Real.exp_neg]
    simpa only [div_eq_mul_inv,mul_comm] using
      (lt_div_iff₀ (Real.exp_pos h)).mpr outside
  have absolute:|Real.exp (-h)*x|=Real.exp (-h)*|x|:=by
    rw [abs_mul,abs_of_pos (Real.exp_pos (-h))]
  unfold compactRaw resolvedRaw
  rw [absolute,max_eq_right moved.le,max_eq_right lower.le]
  have power:=power_scale c h |x| (by linarith)
  push_cast at power ⊢
  linear_combination (1/2:ℂ)*power

theorem actual_compact_support (c:BurnolCompletedMellinCoordinate) (h:ℝ) (nonnegative:0≤h):
    HasCompactSupport (compactRaw c h) := by
  apply HasCompactSupport.intro isCompact_Icc
  intro x outside
  apply actual_compact_outside c h nonnegative x
  exact lt_of_not_ge (fun bound=>outside (abs_le.mp bound))

theorem actual_compact_integrable (c:BurnolCompletedMellinCoordinate) (h:ℝ) (nonnegative:0≤h):
    Integrable (compactRaw c h):=
  (actual_compact_raw_continuous c h).integrable_of_hasCompactSupport (actual_compact_support c h nonnegative)

theorem actual_compact_decay (c:BurnolCompletedMellinCoordinate) (h:ℝ) (nonnegative:0≤h):
    Asymptotics.IsBigO (cocompact ℝ) (compactRaw c h) (fun x:ℝ=>|x|^(-2:ℝ)) := by
  apply Asymptotics.IsBigO.of_bound 0
  have vanishes:compactRaw c h=ᶠ[cocompact ℝ]0:=by
    simpa only [coclosedCompact_eq_cocompact] using
      hasCompactSupport_iff_eventuallyEq.mp (actual_compact_support c h nonnegative)
  filter_upwards [vanishes] with x hx
  simp only [hx,Pi.zero_apply,norm_zero,zero_mul,le_refl]

/-- The actual compact source pays every ordinary Fourier derivative at zero as well as away from zero. -/
theorem actual_compact_fourier_smooth (c:BurnolCompletedMellinCoordinate) (h:ℝ) (nonnegative:0≤h)
    (N:ℕ∞):ContDiff ℝ N (𝓕 (compactRaw c h)) := by
  apply Real.contDiff_fourier
  intro n _
  have continuous:Continuous (fun x:ℝ=>‖x‖^n*‖compactRaw c h x‖):=
    (continuous_norm.pow n).mul (actual_compact_raw_continuous c h).norm
  apply continuous.integrable_of_hasCompactSupport
  apply HasCompactSupport.intro isCompact_Icc
  intro x outside
  have vanishes:=actual_compact_outside c h nonnegative x
    (lt_of_not_ge (fun bound=>outside (abs_le.mp bound)))
  simp only [vanishes,norm_zero,mul_zero]


end OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Origin.Compact
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
