import H0mework.Versions.X.NavierStokes.SourceAction.Spacetime

set_option autoImplicit false
open scoped BigOperators ENNReal Topology

namespace SaturationMonoid.NavierStokes.NativePolynomialTimeJets

open Set Filter
open ThreeDimensionalPeriodicCoarseFilterCore
open ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion.GeneratedWholeRestartCurrent
open RationalVorticityEvaluator RationalVorticityEvaluator.ButterflyStackedSourceCurrent
open NativeStressSource NativeTimeJetCarrier NativeTimeJetRecursion NativeMixedTimeSpace
open NativeHigherTimeJets NativeHigherTimeJetsSource

noncomputable section

variable {index : ℕ}

def jet (base : Profile index) (linear nonlinear : ℝ) : ℕ → Profile index
  | 0 => base
  | order + 1 =>
      add (scale linear (viscous (jet base linear nonlinear order)))
        (scale nonlinear (NativeTimeJetCarrier.sum (List.ofFn fun rank : Fin (order + 1) =>
          scale (order.choose rank : ℝ)
            (bilinear (jet base linear nonlinear rank) (jet base linear nonlinear (order - rank))))))
termination_by order => order
decreasing_by all_goals omega

@[simp] theorem jet_zero (base : Profile index) (linear nonlinear : ℝ) : jet base linear nonlinear 0 = base := by rw [jet]

def read (base : Profile index) (linear nonlinear : ℝ) (order : ℕ) (actual : ℝ) : ComplexVorticityHilbertState :=
  readProfile (jet base linear nonlinear order) actual

@[simp] theorem read_zero (base : Profile index) (linear nonlinear : ℝ) : read base linear nonlinear 0 = readProfile base := by
  funext actual
  simp only [read, jet_zero]

theorem read_continuous (base : Profile index) (linear nonlinear : ℝ) (order : ℕ) :
    Continuous (read base linear nonlinear order) :=
  (jet base linear nonlinear order).continuous.comp continuous_projIcc

theorem jet_succ_row (base : Profile index) (linear nonlinear : ℝ) (order : ℕ)
    (time : Time index) (wave : IntegerWavevector) :
    (jet base linear nonlinear (order + 1)).value time wave =
      linear • (-(butterflyGainViscosity.coeff * integerWaveViscousMultiplier wave) •
        (jet base linear nonlinear order).value time wave) +
      nonlinear • (∑ rank : Fin (order + 1), (order.choose rank : ℝ) • projectedDivergenceCLM wave
        (mixedFlux ((jet base linear nonlinear rank).value time)
          ((jet base linear nonlinear (order - rank)).value time) wave)) := by
  rw [jet]
  change linear • ((viscous (jet base linear nonlinear order)).value time wave) +
    nonlinear • ((NativeTimeJetCarrier.sum (List.ofFn fun rank : Fin (order + 1) =>
      scale (order.choose rank : ℝ)
        (bilinear (jet base linear nonlinear rank) (jet base linear nonlinear (order - rank))))).value time wave) = _
  rw [viscous_row, sum_ofFn_value]
  simp only [lp.coeFn_sum, Finset.sum_apply, scale, lp.coeFn_smul, Pi.smul_apply, bilinear_row]

theorem read_succ_row (base : Profile index) (linear nonlinear : ℝ) (order : ℕ)
    (actual : ℝ) (wave : IntegerWavevector) :
    read base linear nonlinear (order + 1) actual wave =
      linear • (-(butterflyGainViscosity.coeff * integerWaveViscousMultiplier wave) •
        read base linear nonlinear order actual wave) +
      nonlinear • projectedDivergenceCLM wave
        (mixedTimeSum (read base linear nonlinear) (read base linear nonlinear) order actual wave) := by
  let time := projIcc (0 : ℝ) (run stackedShortCurrent index).duration
    (run stackedShortCurrent index).receipt.requestedTimePos.le actual
  change (jet base linear nonlinear (order + 1)).value time wave = _
  rw [jet_succ_row]
  congr 2
  unfold mixedTimeSum
  have rowSum : (fun output input => ∑ rank ∈ Finset.range (order + 1),
      (order.choose rank : ℂ) * mixedFlux (read base linear nonlinear rank actual)
        (read base linear nonlinear (order - rank) actual) wave output input) =
      ∑ rank : Fin (order + 1), (order.choose rank : ℝ) •
        mixedFlux ((jet base linear nonlinear rank).value time)
          ((jet base linear nonlinear (order - rank)).value time) wave := by
    funext output input
    simp only [Finset.sum_apply, Pi.smul_apply, Complex.real_smul, Complex.ofReal_natCast]
    rw [Fin.sum_univ_eq_sum_range (fun rank => (order.choose rank : ℂ) *
      mixedFlux ((jet base linear nonlinear rank).value time)
        ((jet base linear nonlinear (order - rank)).value time) wave output input) (order + 1)]
    apply Finset.sum_congr rfl
    intro rank inside
    rfl
  rw [rowSum, map_sum]
  apply Finset.sum_congr rfl
  intro rank _
  exact (projectedDivergenceCLM wave).map_smul (order.choose rank : ℝ) _ |>.symm

theorem read_one_row (base : Profile index) (linear nonlinear : ℝ) (actual : ℝ) (wave : IntegerWavevector) :
    read base linear nonlinear 1 actual wave =
      linear • (-(butterflyGainViscosity.coeff * integerWaveViscousMultiplier wave) • readProfile base actual wave) +
      nonlinear • projectedDivergenceCLM wave (quadraticFlux (readProfile base actual) wave) := by
  rw [show 1 = 0 + 1 from rfl, read_succ_row, read_zero]
  have stress : mixedTimeSum (read base linear nonlinear) (read base linear nonlinear) 0 actual wave =
      quadraticFlux (readProfile base actual) wave := by
    funext output input
    simp only [mixedTimeSum, Nat.zero_add, Finset.sum_range_one, Nat.choose_zero_right,
      Nat.cast_one, tsub_zero, one_mul, read_zero, mixedFlux_diagonal]
  rw [stress]

theorem evolves (base : Profile index) (linear nonlinear : ℝ)
    (baseDerivative : ∀ time : Time index, HasDerivWithinAt (readProfile base)
      (read base linear nonlinear 1 time.1) (Icc (0 : ℝ) (run stackedShortCurrent index).duration) time.1)
    (order : ℕ) (time : Time index) :
    HasDerivWithinAt (read base linear nonlinear order) (read base linear nonlinear (order + 1) time.1)
      (Icc (0 : ℝ) (run stackedShortCurrent index).duration) time.1 := by
  induction order using Nat.strong_induction_on generalizing time with
  | h order previous =>
    cases order with
    | zero => simpa only [read_zero] using baseDerivative time
    | succ order =>
      apply hilbert_hasDerivWithinAt_of_rows _ _ _ (read_continuous base linear nonlinear (order + 1))
        (read_continuous base linear nonlinear (order + 1 + 1)) _ time
      intro wave sample inside
      have lower (rank : ℕ) (bounded : rank ≤ order) :
          HasDerivWithinAt (read base linear nonlinear rank) (read base linear nonlinear (rank + 1) sample)
            (Icc (0 : ℝ) (run stackedShortCurrent index).duration) sample :=
        previous rank (by omega) ⟨sample, inside⟩
      have tensor : HasDerivWithinAt
          (fun actual => mixedTimeSum (read base linear nonlinear) (read base linear nonlinear) order actual wave)
          (mixedTimeSum (read base linear nonlinear) (read base linear nonlinear) (order + 1) sample wave)
          (Icc (0 : ℝ) (run stackedShortCurrent index).duration) sample := by
        apply hasDerivWithinAt_pi.mpr
        intro output
        apply hasDerivWithinAt_pi.mpr
        intro input
        exact mixedTimeSum_hasDerivWithinAt _ _ order _ sample lower lower wave output input
      have linearPart := (((lp.evalCLM ℝ (fun _ : IntegerWavevector => ComplexCoordinateVector) 2 wave).hasFDerivAt.comp_hasDerivWithinAt
        sample (lower order le_rfl)).const_smul
          (-(butterflyGainViscosity.coeff * integerWaveViscousMultiplier wave))).const_smul linear
      have nonlinearPart := ((projectedDivergenceCLM wave).hasFDerivAt.comp_hasDerivWithinAt sample tensor).const_smul nonlinear
      convert! linearPart.add nonlinearPart using 1
      · funext actual
        exact read_succ_row base linear nonlinear order actual wave
      · exact read_succ_row base linear nonlinear (order + 1) sample wave

end
end SaturationMonoid.NavierStokes.NativePolynomialTimeJets
