import H0mework.Versions.R502c11c3.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Boundary.NativeEulerGreen.Counted.WholeStrip.FinitePa.Collar.Resolvent.Physical.Channel.Accumulation.Limit.Origin.Unit.Collar.NormalizedFibre.CountedPhaseFourierOriginalB
import Mathlib.Analysis.Calculus.BumpFunction.Basic

set_option autoImplicit false
set_option Elab.async false

noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalCanonicalNativeEulerGreen.Counted.WholeStrip.FinitePa.Collar.Resolvent

open Complex Filter MeasureTheory Set BurnolPhysicalState OriginalRieszSource
open scoped Topology ContDiff

open private compact_join_read quarter_cut_identity from H0mework.Versions.R502c11c3.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Boundary.NativeEulerGreen.Counted.WholeStrip.FinitePa.Collar.Resolvent.Physical.Channel.Accumulation.Limit.Origin.Unit.Collar.NormalizedFibre.CountedCompactPhaseWave
open private cutoff_split_read from H0mework.Versions.R502c11c3.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Boundary.NativeEulerGreen.Counted.WholeStrip.FinitePa.Collar.Resolvent.Physical.Channel.Accumulation.Limit.Origin.Unit.Collar.NormalizedFibre.HomogeneousFibre
open private centre_seed_integrable from H0mework.Versions.R502c11c3.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Boundary.NativeEulerGreen.Counted.WholeStrip.FinitePa.Collar.Resolvent.Physical.Channel.Accumulation.Limit.Origin.Unit.Collar.NormalizedFibre.CountedPhaseInput
open private seed_quarter_supported from H0mework.Versions.R502c11c3.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Boundary.NativeEulerGreen.Counted.WholeStrip.FinitePa.Collar.Resolvent.Physical.Channel.Accumulation.Limit.Origin.Unit.Collar.NormalizedFibre.CountedPhaseHomogeneousWave
open private phase_input_wave_supported from H0mework.Versions.R502c11c3.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Boundary.NativeEulerGreen.Counted.WholeStrip.FinitePa.Collar.Resolvent.Physical.Channel.Accumulation.Limit.Origin.Unit.Collar.NormalizedFibre.CountedPhaseFourierOriginalB


local notation "L¹" => Lp ℂ 1 (volume : Measure ℝ)
local notation "S'" => TemperedDistribution ℝ ℂ
local notation "q" => (1/4 : ℝ)
local notation "r₀" => (q/2)
local notation "R" => fun c => burnolDirectRightResolventCLM (OriginalPrimitiveRankBalance.conjugateCoordinate c)

private def quarterEulerBump : ContDiffBump (0 : ℝ) where
  rIn := 1
  rOut := 2
  rIn_pos := by norm_num
  rIn_lt_rOut := by norm_num

private theorem compact_join_supported (z : L¹ × BurnolL2)
    (support : ∀ᵐ x : ℝ ∂volume, q < |x| → z.1 x = 0 ∧ z.2 x = 0) :
    ∀ᵐ x : ℝ ∂volume, q < |x| → compactPhaseJoin z x = 0 := by
  have outside := support.mono fun _ read h => (read h).2
  filter_upwards [compact_join_read z (quarter_cut_identity _ outside), support] with x joined atX beyond
  change compactPhaseJoin z x = _ at joined
  rw [joined, (atX beyond).1, (atX beyond).2, add_zero]

private theorem compact_probe_read (z : L¹ × BurnolL2)
    (support : ∀ᵐ x : ℝ ∂volume, q < |x| → z.1 x = 0 ∧ z.2 x = 0)
    (test : SchwartzMap ℝ ℂ) (φ : ℝ → ℂ) (same : ∀ x, |x| ≤ q → test x = φ x) :
    distributionOfSplit z test = ∫ x, φ x * compactPhaseJoin z x := by
  have outside := support.mono fun _ read h => (read h).2
  rw [distributionOfSplit_apply]
  apply integral_congr_ae
  filter_upwards [compact_join_read z (quarter_cut_identity _ outside), support] with x joined atX
  change compactPhaseJoin z x = _ at joined
  rw [joined]
  by_cases inside : |x| ≤ q
  · rw [same x inside]
  · have zeros := atX (lt_of_not_ge inside)
    rw [zeros.1, zeros.2, add_zero, mul_zero, mul_zero]

/-- The exact compact Euler equation tests against every smooth coefficient
on its actual support. -/
theorem compact_euler_smooth_read (c : BurnolCompletedMellinCoordinate)
    (output input : L¹ × BurnolL2) (scale : ℂ)
    (outputSupport : ∀ᵐ x : ℝ ∂volume, q < |x| → output.1 x = 0 ∧ output.2 x = 0)
    (inputSupport : ∀ᵐ x : ℝ ∂volume, q < |x| → input.1 x = 0 ∧ input.2 x = 0)
    (equation : eulerOfPhysicalSplit c output = scale • distributionOfSplit input)
    (φ : ℝ → ℂ) (smooth : ContDiff ℝ ∞ φ) :
    (star c.value-1)*(∫ x, φ x*compactPhaseJoin output x) -
      (∫ x : ℝ, (x : ℂ)*deriv φ x*compactPhaseJoin output x) =
      scale*(∫ x, φ x*compactPhaseJoin input x) := by
  let cut := fun x : ℝ => (quarterEulerBump x : ℂ)
  have cutCompact : HasCompactSupport cut :=
    quarterEulerBump.hasCompactSupport.comp_left (show ((0 : ℝ) : ℂ) = 0 by norm_num)
  have cutSmooth : ContDiff ℝ ∞ cut :=
    Complex.ofRealCLM.contDiff.comp quarterEulerBump.contDiff
  have support : HasCompactSupport (cut * φ) := cutCompact.mul_right
  let test := support.toSchwartzMap (cutSmooth.mul smooth)
  have agreement (x : ℝ) (inside : |x| ≤ q) :
      (test : ℝ → ℂ) =ᶠ[𝓝 x] φ := by
    have near : x ∈ Metric.ball (0 : ℝ) quarterEulerBump.rIn := by
      rw [Metric.mem_ball, Real.dist_eq, sub_zero]
      exact inside.trans_lt (by norm_num [quarterEulerBump])
    filter_upwards [quarterEulerBump.eventuallyEq_one_of_mem_ball near] with y read
    change (quarterEulerBump y : ℂ)*φ y = _
    change quarterEulerBump y = 1 at read
    rw [read, Complex.ofReal_one, one_mul]
  have plain (x : ℝ) (inside : |x| ≤ q) : test x = φ x := (agreement x inside).eq_of_nhds
  let weighted := SchwartzMap.smulLeftCLM ℂ (fun x : ℝ => (x : ℂ)) (SchwartzMap.derivCLM ℂ ℂ test)
  have weightedRead (x : ℝ) (inside : |x| ≤ q) : weighted x = (x : ℂ)*deriv φ x := by
    have growth : (fun x : ℝ => (x : ℂ)).HasTemperateGrowth := by fun_prop
    dsimp only [weighted]
    rw [SchwartzMap.smulLeftCLM_apply growth]
    change (x : ℂ) • (SchwartzMap.derivCLM ℂ ℂ test) x = _
    rw [SchwartzMap.derivCLM_apply, smul_eq_mul, (agreement x inside).deriv_eq]
  have read := congrArg (fun d : S' => d test) equation
  change (GapEuler.euler (distributionOfSplit output) +
    (star c.value-1/2) • distributionOfSplit output) test =
    (scale • distributionOfSplit input) test at read
  simp only [add_apply, smul_apply, smul_eq_mul, Dilation.euler_test] at read
  change -(1/2 : ℂ)*distributionOfSplit output test-distributionOfSplit output weighted+
    (star c.value-1/2)*distributionOfSplit output test = scale*distributionOfSplit input test at read
  rw [compact_probe_read output outputSupport test φ plain,
    compact_probe_read output outputSupport weighted _ weightedRead,
    compact_probe_read input inputSupport test φ plain] at read
  linear_combination read

private theorem counted_phase_input_support (c : BurnolCompletedMellinCoordinate) (n : Nat) :
    let source := splitAtPhysicalCutoff r₀ (countedPhaseSource c n)
    ∀ᵐ x : ℝ ∂volume, q < |x| → source.1 x = 0 ∧ source.2 x = 0 := by
  filter_upwards [cutoff_split_read r₀ (countedPhaseSource c n), phase_input_wave_supported c n]
    with x read outside beyond
  have missing : x ∉ symmetricInterval r₀ := fun h =>
    beyond.not_ge ((abs_le.mpr h).trans (by norm_num))
  exact ⟨read.1.trans (indicator_of_notMem missing _), outside beyond⟩

private theorem counted_seed_support (c : BurnolCompletedMellinCoordinate) :
    ∀ᵐ x : ℝ ∂volume, q < |x| → (countedSeedSplit c).1 x = 0 ∧ (countedSeedSplit c).2 x = 0 := by
  filter_upwards [(centre_seed_integrable c).coeFn_toL1, seed_quarter_supported c] with x read outside beyond
  have missing : x ∉ symmetricInterval r₀ := fun h =>
    beyond.not_ge ((abs_le.mpr h).trans (by norm_num))
  exact ⟨read.trans (indicator_of_notMem missing _), outside beyond⟩

/-- Every literal phase field reads the same compact source in the original Euler equation. -/
theorem actual_counted_compact_phase_euler (c : BurnolCompletedMellinCoordinate) (n : Nat) :
    eulerOfPhysicalSplit c (countedCompactPhaseField c n) =
      -(2 : ℂ) • distributionOfSplit (splitAtPhysicalCutoff r₀ (countedPhaseSource c n)) := by
  have source : eulerOfPhysicalSplit c (splitAtPhysicalCutoff r₀ (R c (countedPhaseSource c n))) =
      -(2 : ℂ) • (countedPhaseSource c n : S') :=
    actual_split_R_equation c (countedPhaseSource c n)
  have homogeneous : eulerOfPhysicalSplit c (countedHomogeneousSplit c) = 0 := counted_homogeneous_euler c
  unfold countedCompactPhaseField
  rw [map_add, map_smul, source, homogeneous, distributionOfSplit_from_cutoff]
  have zero (scalar : ℂ) : scalar • (0 : S') = 0 := by
    ext test
    simp [smul_apply]
  rw [zero, add_zero]

end OriginalCanonicalNativeEulerGreen.Counted.WholeStrip.FinitePa.Collar.Resolvent
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
