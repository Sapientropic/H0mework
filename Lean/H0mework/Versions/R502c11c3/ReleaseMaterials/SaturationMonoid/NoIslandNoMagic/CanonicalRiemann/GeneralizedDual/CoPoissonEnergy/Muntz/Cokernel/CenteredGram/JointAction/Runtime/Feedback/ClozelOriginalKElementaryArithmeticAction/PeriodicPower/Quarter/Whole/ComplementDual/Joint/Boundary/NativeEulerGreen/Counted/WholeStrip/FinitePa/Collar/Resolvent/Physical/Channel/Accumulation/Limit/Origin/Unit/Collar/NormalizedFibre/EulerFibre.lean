import H0mework.Versions.R502c11c3.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Boundary.NativeEulerGreen.Counted.WholeStrip.FinitePa.Collar.Resolvent.Physical.Channel.Accumulation.Limit.Origin.Unit.Collar.NormalizedFibre.WeakLimit
import H0mework.Versions.R502c11c3.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.Projection.ExtendedSonine.Source.Action.Euler.Dilation.L1

set_option autoImplicit false
set_option Elab.async false

noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalCanonicalNativeEulerGreen.Counted.WholeStrip.FinitePa.Collar.Resolvent

open Complex Filter MeasureTheory Set BurnolPhysicalState OriginalRieszSource
open OriginalRieszFinitePairing.CoPoisson.Ward OriginalKCoefficientBFiniteAction
open OriginalKSourceResolventReconstruction
open OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Source
open scoped Topology ENNReal
attribute [local instance 1100] NormedSpace.complexToReal

open private centreLimit centre_integrable counted_full_weak homogeneous_tail_read homogeneous_test_read from
  H0mework.Versions.R502c11c3.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Boundary.NativeEulerGreen.Counted.WholeStrip.FinitePa.Collar.Resolvent.Physical.Channel.Accumulation.Limit.Origin.Unit.Collar.NormalizedFibre.WeakLimit
open private singular_limit_not_memLp from
  H0mework.Versions.R502c11c3.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Boundary.NativeEulerGreen.Counted.WholeStrip.FinitePa.Collar.Resolvent.Physical.Channel.Accumulation.Limit.Origin.Unit.Collar.NormalizedFibre
open private translation_apply from
  H0mework.Versions.R502c11c3.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.Projection.ExtendedSonine.Source.Action.Euler.Dilation.L1
open private halfPower_dilation from
  H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Ward.UnitDual

local notation "q₀" => (1/4 : ℝ)
local notation "r₀" => (q₀/2)
local notation "S'" => TemperedDistribution ℝ ℂ
local notation "H" => countedHomogeneousDistribution
local notation "Y" => countedNormalizedField
local notation "K" => burnolCompletedMellinRieszVector
local notation "P" => burnolEvenAmbientProjection
local notation "T" => coPoissonSchwartzEnergyTranslation
local notation "barC" => OriginalPrimitiveRankBalance.conjugateCoordinate
local notation "s₀" => fun c => star (BurnolCompletedMellinCoordinate.value c)
local notation "rawPower" => fun c (x : ℝ) => ((|x| : ℝ) : ℂ)^(-s₀ c)*(1/2 : ℂ)
local notation "tail" => fun c => (-(1/2 : ℂ)) • burnolRadiusNormalizedUnitTail (barC c) r₀ (by norm_num)
local notation "scale" => fun c (n : Nat) =>
  (Real.log ((n+2 : Nat) : ℝ) : ℂ)*((n+2 : Nat) : ℂ)^(-s₀ c)
local notation "whole" => fun c => floorFromResponses c+riemannZeta (s₀ c) • elementarySource c
local notation "delta" => fun c (n : Nat) => whole c-compensated c (n+2)

/-- The same generated weak field carries the original homogeneous dilation
character under the literal inverse cotest action. -/
theorem counted_homogeneous_translation (c : BurnolCompletedMellinCoordinate) (h : ℝ)
    (test : SchwartzMap ℝ ℂ) :
    H c (T (-h) test) = Complex.exp (((1/2 : ℂ)-s₀ c)*(h : ℂ))*H c test := by
  let s := s₀ c
  let f := fun x : ℝ => test x*rawPower c x
  have raw (x : ℝ) : rawPower c (Real.exp (-h)*x) =
      Complex.exp (-s*((-h : ℝ) : ℂ))*rawPower c x := by
    simpa only [OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Ward.halfPower,
      powerRaw, mul_comm (1/2 : ℂ), s] using halfPower_dilation c (-h) x
  have hom (x : ℝ) : Complex.exp (-s*(h : ℂ))*rawPower c (Real.exp (-h)*x) = rawPower c x := by
    rw [raw, ← mul_assoc, ← Complex.exp_add]
    rw [show -s*(h : ℂ)+-s*((-h : ℝ) : ℂ)=0 by push_cast; ring, Complex.exp_zero, one_mul]
  rw [(homogeneous_test_read c (T (-h) test)).2, (homogeneous_test_read c test).2]
  calc
    _ = (Real.exp (-h/2) : ℂ)*Complex.exp (-s*(h : ℂ)) *
          (∫ x : ℝ, f (Real.exp (-h)*x)) := by
      rw [← integral_const_mul]
      apply integral_congr_ae
      filter_upwards with x
      rw [translation_apply]
      dsimp only [f]
      linear_combination (Real.exp (-h/2) : ℂ)*test (Real.exp (-h)*x)*(hom x).symm
    _ = _ := by
      rw [Measure.integral_comp_mul_left f (Real.exp (-h)),
        abs_of_pos (inv_pos.mpr (Real.exp_pos _)), Real.exp_neg h, inv_inv, Complex.real_smul]
      simp only [Complex.ofReal_exp]
      rw [← mul_assoc, ← Complex.exp_add, ← Complex.exp_add]
      dsimp only [f, s]
      congr 2
      push_cast
      ring

/-- The original Euler operator consumes the same weak field as a homogeneous
source, with the original right-resolvent coefficient. -/
theorem counted_homogeneous_euler (c : BurnolCompletedMellinCoordinate) :
    GapEuler.euler (H c)+(s₀ c-1/2) • H c = 0 := by
  ext test
  let coefficient := (1/2 : ℂ)-s₀ c
  let outside : BurnolL2 := tail c
  have centre := Dilation.integrable_weak_at_zero (centreLimit c) test
  have exterior : HasDerivAt (fun h : ℝ => (outside : S') (T (-h) test))
      (GapEuler.euler (outside : S') test) 0 := by
    simpa only [OriginalRieszFiniteResponse.original_read] using
      Dilation.original_weak_at_zero outside test
  have actual : HasDerivAt (fun h : ℝ => H c (T (-h) test)) (GapEuler.euler (H c) test) 0 := by
    simpa only [countedHomogeneousDistribution, map_add, add_apply, outside] using! centre.add exterior
  have parameter : HasDerivAt (fun h : ℝ => coefficient*(h : ℂ)) coefficient 0 := by
    simpa only [Function.comp_def, Complex.ofRealCLM_apply, Complex.ofReal_one, mul_one] using!
      (Complex.ofRealCLM.hasFDerivAt.comp_hasDerivAt (0 : ℝ) (hasDerivAt_id 0)).const_mul coefficient
  have exactRead : HasDerivAt (fun h : ℝ => H c (T (-h) test)) (coefficient*H c test) 0 := by
    have read := ((Complex.hasDerivAt_exp (coefficient*(0 : ℂ))).scomp (0 : ℝ) parameter).mul_const (H c test)
    rw [show (fun h : ℝ => H c (T (-h) test)) =
      fun h : ℝ => Complex.exp (coefficient*(h : ℂ))*H c test from
        funext (fun h => counted_homogeneous_translation c h test)]
    simpa only [Complex.ofReal_zero, mul_zero, Complex.exp_zero, smul_eq_mul, mul_one, one_mul,
      Function.comp_def] using! read
  have equation := actual.unique exactRead
  simp only [add_apply, smul_apply, smul_eq_mul, zero_apply]
  dsimp only [coefficient] at equation
  linear_combination equation

theorem counted_homogeneous_ne_zero (c : BurnolCompletedMellinCoordinate) : H c ≠ 0 := by
  let centre := centreLimit c
  let outside : BurnolL2 := tail c
  have locally : LocallyIntegrable (rawPower c) (volume : Measure ℝ) := by
    have inner := (Lp.memLp centre).locallyIntegrable (by norm_num : (1 : ℝ≥0∞) ≤ 1)
    have outer := (Lp.memLp outside).locallyIntegrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)
    apply (inner.add outer).congr
    have compact := (centre_integrable c).coeFn_toL1
    filter_upwards [compact, homogeneous_tail_read c] with x left right
    change centre x = _ at left
    change outside x = _ at right
    change centre x+outside x = _
    rw [left, right]
    by_cases inside : |x| ≤ r₀
    · rw [indicator_of_mem (show x ∈ symmetricInterval r₀ from abs_le.mp inside),
        if_neg (not_lt_of_ge inside), add_zero]
    · rw [indicator_of_notMem (show x ∉ symmetricInterval r₀ from fun h => inside (abs_le.mpr h)),
        if_pos (lt_of_not_ge inside), zero_add]
  intro erased
  have zero : rawPower c =ᵐ[volume] 0 := by
    apply ae_eq_zero_of_integral_contDiff_smul_eq_zero locally
    intro test smooth compact
    have complexCompact : HasCompactSupport (Complex.ofRealCLM ∘ test) := compact.comp_left rfl
    have complexSmooth := Complex.ofRealCLM.contDiff.comp smooth
    have read := (homogeneous_test_read c (complexCompact.toSchwartzMap complexSmooth)).2
    rw [erased, zero_apply] at read
    change (0 : ℂ) = ∫ x, ((test x : ℝ) : ℂ)*rawPower c x at read
    simpa only [Complex.real_smul] using read.symm
  apply singular_limit_not_memLp c
  have vanish : (0 : ℝ → ℂ) =ᵐ[volume.restrict (Ioc 0 q₀)]
      fun x => (x : ℂ)^(-s₀ c)*(1/2 : ℂ) := by
    filter_upwards [ae_restrict_of_ae zero.symm, ae_restrict_mem measurableSet_Ioc] with x read member
    change (0 : ℂ) = _ at read ⊢
    rw [read]
    change ((|x| : ℝ) : ℂ)^(-s₀ c)*(1/2 : ℂ) = _
    rw [abs_of_pos member.1]
  exact (MemLp.zero : MemLp (0 : ℝ → ℂ) 2 (volume.restrict (Ioc 0 q₀))).ae_eq vanish

/-- The original weak source graph has an actual zero-input limit with a
nonzero homogeneous output. Its original physical K read belongs to the same
scaled count sequence. -/
theorem actual_counted_weak_euler_fibre (c : BurnolCompletedMellinCoordinate) :
    Tendsto (fun n : Nat =>
      (((((scale c n)⁻¹ • delta c n : BurnolL2)) : S'), (Y c n : S'), P (Y c n)))
      atTop (𝓝 (0, H c, K c)) := by
  let input := fun n : Nat => (scale c n)⁻¹ • delta c n
  let euler := GapEuler.euler+(s₀ c-1/2) • ContinuousLinearMap.id ℂ S'
  have law (n : Nat) : euler (Y c n : S') = -(2 : ℂ) • (input n : S') := by
    have acted : sourceResolvent c (input n) = Y c n := by
      change burnolDirectRightResolventCLM (barC c) ((scale c n)⁻¹ • delta c n) =
        (scale c n)⁻¹ • burnolDirectRightResolventCLM (barC c) (delta c n)
      exact map_smul _ _ _
    have full := sourceResolvent_euler c (input n)
    rw [acted] at full
    exact full
  have kernel : euler (H c) = 0 := counted_homogeneous_euler c
  have zero := (euler.continuous.tendsto (H c)).comp (counted_full_weak c)
  rw [kernel] at zero
  have scalarZero : (-(1/2 : ℂ)) • (0 : S') = 0 := by
    ext test
    simp [smul_apply]
  have scaled : Tendsto (fun n => (-(1/2 : ℂ)) • euler (Y c n : S')) atTop (𝓝 0) := by
    have actual : Tendsto (fun n => (-(1/2 : ℂ)) • euler (Y c n : S')) atTop
        (𝓝 ((-(1/2 : ℂ)) • (0 : S'))) := zero.const_smul _
    exact scalarZero ▸ actual
  have recover (v : S') : (-(1/2 : ℂ)) • (-(2 : ℂ) • v) = v := by
    ext test
    simp only [smul_apply, smul_eq_mul]
    ring
  have origin : Tendsto (fun n => (input n : S')) atTop (𝓝 0) := by
    apply scaled.congr'
    filter_upwards with n
    exact (congrArg ((-(1/2 : ℂ)) • ·) (law n)).trans (recover _)
  have physical : Tendsto (fun n => P (Y c n)) atTop (𝓝 (K c)) := by
    simpa only [countedNormalizedField, map_smul] using actual_scaled_counted_physical_limit c
  exact origin.prodMk_nhds ((counted_full_weak c).prodMk_nhds physical)

end OriginalCanonicalNativeEulerGreen.Counted.WholeStrip.FinitePa.Collar.Resolvent
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
