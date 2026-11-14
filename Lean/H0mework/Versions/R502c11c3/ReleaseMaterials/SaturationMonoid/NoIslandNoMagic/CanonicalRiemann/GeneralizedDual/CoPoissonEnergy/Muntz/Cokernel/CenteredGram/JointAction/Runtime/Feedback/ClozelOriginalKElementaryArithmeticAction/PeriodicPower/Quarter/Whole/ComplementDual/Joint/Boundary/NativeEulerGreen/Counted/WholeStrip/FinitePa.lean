import H0mework.Versions.R502c11c3.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Boundary.NativeEulerGreen.Counted.WholeStrip.OriginalK

set_option autoImplicit false
set_option Elab.async false

noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalCanonicalNativeEulerGreen.Counted.WholeStrip.FinitePa

open Complex Filter MeasureTheory Set BurnolPhysicalState
open OriginalRieszSource OriginalRieszSourceGreen OriginalRieszFinitePairing.CoPoisson.Ward
open OriginalKCoefficientBFiniteAction OriginalKElementaryArithmeticAction
open OriginalKFiniteOrderRelease.UnitPowerJordanSource OriginalKFiniteOrderRelease.UnitPowerJordanAction
open OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Source
open OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Ward
open OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Boundary.NativeSmooth
open scoped Topology InnerProductSpace

open private compact_finite_event from
  H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Ward.CompactFloor
open private fourier_raw_even_of_fixed from
  H0mework.Versions.R7e4da746.Arithmetic.RieszFinitePairing.ExteriorRaw
open private mean_power from
  H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.SeedFourier

local notation "q" => (1/4 : ℝ)
local notation "μq" => volume.restrict (symmetricInterval q)
local notation "Hq" => BurnolQuarterIntervalL2
local notation "E" => burnolQuarterZeroExtension
local notation "Q" => burnolQuarterRestriction
local notation "S" => burnolMeanZeroTruncatedFourier
local notation "D" => DualSource.source
local notation "lead" => ForcingPrimitive.leadingCoefficient
local notation "Z" => fun c : BurnolCompletedMellinCoordinate => FiniteForcing.coefficient (star (BurnolCompletedMellinCoordinate.value c))

def logCount (c : BurnolCompletedMellinCoordinate) (N : ℕ) : BurnolL2 :=
  D N (E (S (logBFirst c 0) : Hq))

/-- The finite correction uses the original coefficient from that same integer and continuous count. -/
def compensated (c : BurnolCompletedMellinCoordinate) (N : ℕ) : BurnolL2 :=
  D N (input c) + Z c N • elementarySource c

private theorem finite_base (c : BurnolCompletedMellinCoordinate) (N : ℕ) :
    D N (input c) = lead c • logCount c N - KCountingSource.finite c N := by
  have source : input c = lead c • E (S (logBFirst c 0) : Hq) -
      E (S (burnolRieszSingleFourierSource c) : Hq) - elementarySource c := by
    simp only [input, nativeSmooth, map_sub, map_smul, Submodule.coe_sub, Submodule.coe_smul]
  have linear : D N (input c) =
      lead c • logCount c N - ReturnCounting.finite c N - D N (elementarySource c) := by
    simp only [source, logCount, ReturnCounting.finite, Constructor.returnState,
      CountingDual.dual_eq_adjoint, map_sub, map_smul]
  rw [linear, elementary_reverse_finite]
  module

private theorem log_return_even (c : BurnolCompletedMellinCoordinate) (x : ℝ)
    (_inside : x ∈ symmetricInterval q) :
    burnolMeanZeroFourierRaw (logBFirst c 0) |x| = burnolMeanZeroFourierRaw (logBFirst c 0) x := by
  have fixed : reflectRestricted q (logBFirst c 0 : Hq) = (logBFirst c 0 : Hq) :=
    congrArg (fun state : BurnolQuarterMeanZeroCarrier => (state : Hq)) (log_B_even c 0)
  by_cases positive : 0 ≤ x
  · rw [abs_of_nonneg positive]
  · rw [abs_of_neg (lt_of_not_ge positive)]
    simp only [burnolMeanZeroFourierRaw, fourier_raw_even_of_fixed _ fixed x]

private theorem log_count_exterior (c : BurnolCompletedMellinCoordinate) (N : ℕ)
    (positiveN : 0 < N) : ∀ᵐ x ∂volume, q < |x| → logCount c N x = 0 := by
  let raw := burnolMeanZeroFourierRaw (logBFirst c 0)
  have read := burnolMeanZeroFourier_ae_raw (logBFirst c 0)
  have measured := (OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.Inverse.Derivative.actual_return_contDiff
    (logBFirst c 0)).continuous.measurable
  filter_upwards [actual_compact_reverse_finite_raw (S (logBFirst c 0) : Hq)
    raw read (log_return_even c) measured N] with x finite outside
  have positive : 0 < |x| := (by norm_num : 0 < q).trans outside
  have small : q/|x| < 1 := (div_lt_one positive).mpr outside
  have included : q/|x| < (N : ℝ) := small.trans_le (by exact_mod_cast positiveN)
  have index : ⌊q/|x|⌋₊ = 0 := Nat.floor_eq_zero.mpr small
  rw [show logCount c N x = _ from finite,
    compact_finite_event (S (logBFirst c 0)) raw read (log_return_even c) N x
      (abs_pos.mp positive) included,
    compactReverseFloorRaw, DualSourceRaw.channels, index]
  simp

private theorem elementary_outside (c : BurnolCompletedMellinCoordinate) (x : ℝ)
    (outside : q < |x|) :
    burnolEvenRaw (burnolAmbientMellinKernelRaw c) x =
      (1/2 : ℂ)*((|x| : ℝ) : ℂ)^(-star c.value) := by
  have even : burnolEvenRaw (burnolAmbientMellinKernelRaw c) x =
      burnolEvenRaw (burnolAmbientMellinKernelRaw c) |x| := by
    rcases le_total 0 x with positive | negative
    · rw [abs_of_nonneg positive]
    · rw [abs_of_nonpos negative]
      unfold burnolEvenRaw
      simp only [neg_neg]
      ring
  exact even.trans (gapState_raw_tail c outside)

/-- The complete finite field retains the entire centered power and both actual compact contributions. -/
theorem actual_compensated_raw (c : BurnolCompletedMellinCoordinate) (N : ℕ) :
    (compensated c N : ℝ → ℂ) =ᵐ[volume] fun x =>
      lead c*logCount c N x + PositionCounting.raw c N x -
        Z c N * (symmetricInterval q).indicator (seedRaw c.value) x := by
  unfold compensated
  rw [finite_base]
  filter_upwards [Lp.coeFn_add (lead c • logCount c N - KCountingSource.finite c N)
      (Z c N • elementarySource c),
    Lp.coeFn_sub (lead c • logCount c N) (KCountingSource.finite c N),
    Lp.coeFn_smul (lead c) (logCount c N), Lp.coeFn_smul (Z c N) (elementarySource c),
    KCountingSource.finite_coeFn c N, gapState_read c, volume.ae_ne (0 : ℝ)] with
    x add sub leadRead coeffRead base elem nonzero
  rw [add, Pi.add_apply, sub, Pi.sub_apply, leadRead, coeffRead]
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [base, KCountingSource.raw_synthesis c N x nonzero]
  change _ + Z c N * gapState c x = _
  rw [elem]
  by_cases inside : x ∈ symmetricInterval q
  · rw [indicator_of_mem inside, gapState_raw_gap c inside, seedRaw, powerRaw]
    linear_combination -Z c N * mean_power c
  · have outside : q < |x| := lt_of_not_ge (fun bounded => inside (abs_le.mp bounded))
    rw [indicator_of_notMem inside, elementary_outside c x outside]
    ring

theorem actual_compact (c : BurnolCompletedMellinCoordinate) (N : ℕ) (positive : 0 < N) :
    E (Q (compensated c N)) = compensated c N := by
  have exterior : ∀ᵐ x ∂volume, x ∉ symmetricInterval q → compensated c N x = 0 := by
    filter_upwards [actual_compensated_raw c N, log_count_exterior c N positive] with x raw logRead outside
    have large : q < |x| := lt_of_not_ge (fun bounded => outside (abs_le.mp bounded))
    rw [raw, logRead large, PositionCountedEuler.raw_outside c N x large, indicator_of_notMem outside]
    ring
  apply Lp.ext
  filter_upwards [OriginalPaPhysicalGreen.originalPhysicalCutoff_coeFn q (compensated c N), exterior]
    with x cut support
  change OriginalPaPhysicalGreen.originalPhysicalCutoff q (compensated c N) x = _
  rw [cut]
  by_cases inside : x ∈ symmetricInterval q
  · rw [indicator_of_mem inside]
  · rw [indicator_of_notMem inside, support inside]

end OriginalCanonicalNativeEulerGreen.Counted.WholeStrip.FinitePa
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
