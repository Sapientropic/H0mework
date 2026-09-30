import H0mework.NavierStokes.RecoveryAction.RecoveryCurrentAction

set_option autoImplicit false
open scoped BigOperators Topology ContDiff

namespace SaturationMonoid.NavierStokes.NativeRecoveryCurrentJets

open Set Filter
open ThreeDimensionalPeriodicCoarseFilterCore ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open ThreeDimensionalVorticityCoefficientNativeFluidMedium
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open NativeRecoveryUnifiedCurrent NativeRecoveryCurrentAction NativeRecoveryAEWindows
open NativeRecoveryStrongWindow NativeHigherTimeJets NativePairedCurrentFourier
open NativeCofinalPairedCurrent (source)

noncomputable section

variable {nu : Viscosity}

def velocityJet (initial : GeneratedWholeRestartCurrent nu) (order : ℕ) : ℝ → ComplexVorticityHilbertState :=
  iteratedDeriv order (velocity initial)

theorem velocityJet_read (initial : GeneratedWholeRestartCurrent nu) {lower : ℝ}
    (window : ControlledWindow (receipt initial) lower (terminal initial)) (order : ℕ) (actual : ℝ)
    (inside : actual ∈ Ioo window.first window.last) :
    velocityJet initial order actual = NativeRecoveryTimeJets.timeJet window order actual := by
  have smooth := (NativeRecoveryTimeJets.velocity_time_contDiffOn window).contDiffAt (Icc_mem_nhds inside.1 inside.2)
  unfold velocityJet NativeRecoveryUnifiedCurrent.velocity
  rw [← iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_Icc window.ordered)
    (smooth.of_le (WithTop.coe_le_coe.mpr le_top)) ⟨inside.1.le, inside.2.le⟩]
  exact NativeRecoveryTimeJets.velocity_iteratedDerivWithin window order actual ⟨inside.1.le, inside.2.le⟩

theorem velocityJet_evolves (initial : GeneratedWholeRestartCurrent nu) (order : ℕ) (actual : ℝ)
    (member : actual ∈ regularSet (receipt initial) (terminal initial)) :
    HasDerivAt (velocityJet initial order) (velocityJet initial (order + 1) actual) actual := by
  obtain ⟨lower, window, inside⟩ := regular_window initial actual member
  have original := (NativeRecoveryTimeJets.timeJet_evolves window order actual ⟨inside.1.le, inside.2.le⟩).hasDerivAt
    (Icc_mem_nhds inside.1 inside.2)
  rw [velocityJet_read initial window (order + 1) actual inside]
  apply original.congr_of_eventuallyEq
  filter_upwards [Ioo_mem_nhds inside.1 inside.2] with sample nearby
  exact velocityJet_read initial window order sample nearby

def fluxJet (initial : GeneratedWholeRestartCurrent nu) (order : ℕ) (actual : ℝ) : NativeFluidStressFourierState :=
  mixedTimeSum (velocityJet initial) (velocityJet initial) order actual

theorem fluxJet_evolves (initial : GeneratedWholeRestartCurrent nu) (order : ℕ) (actual : ℝ)
    (member : actual ∈ regularSet (receipt initial) (terminal initial)) (wave : IntegerWavevector) (output input : Coordinate) :
    HasDerivAt (fun sample => fluxJet initial order sample wave output input)
      (fluxJet initial (order + 1) actual wave output input) actual :=
  (mixedTimeSum_hasDerivWithinAt _ _ order univ actual
    (fun rank _ => (velocityJet_evolves initial rank actual member).hasDerivWithinAt)
    (fun rank _ => (velocityJet_evolves initial rank actual member).hasDerivWithinAt) wave output input).hasDerivAt univ_mem

def responseJet (initial : GeneratedWholeRestartCurrent nu) (order : ℕ) (actual : ℝ)
    (direction : Fin 4) (wave : IntegerWavevector) : ℂ :=
  Fin.cases
    ((if order = 0 then baseline wave - source initial 0 wave else 0) - trace (fluxJet initial order actual) wave / 8)
    (fun coordinate => velocityJet initial order actual wave coordinate - if order = 0 then source initial coordinate.succ wave else 0) direction

theorem responseJet_zero (initial : GeneratedWholeRestartCurrent nu) (actual : ℝ) (direction : Fin 4) (wave : IntegerWavevector) :
    responseJet initial 0 actual direction wave = physicalCoefficient initial actual direction wave - source initial direction wave := by
  have diagonal : fluxJet initial 0 actual = NativeStressSource.quadraticFlux (velocity initial actual) := by
    funext frequency output input
    simp only [fluxJet, mixedTimeSum, Nat.zero_add, Finset.sum_range_one, Nat.choose_zero_right,
      Nat.cast_one, one_mul, tsub_zero, mixedFlux_diagonal, velocityJet, iteratedDeriv_zero]
  rw [physicalCoefficient_eq]
  refine Fin.cases ?_ (fun coordinate => ?_) direction
  · change (baseline wave - source initial 0 wave) - trace (fluxJet initial 0 actual) wave / 8 =
      (baseline wave - trace (NativeStressSource.quadraticFlux (velocity initial actual)) wave / 8) - source initial 0 wave
    rw [diagonal]
    ring
  · change iteratedDeriv 0 (velocity initial) actual wave coordinate - source initial coordinate.succ wave = _
    rw [iteratedDeriv_zero]
    rfl

theorem responseJet_evolves (initial : GeneratedWholeRestartCurrent nu) (order : ℕ) (actual : ℝ)
    (member : actual ∈ regularSet (receipt initial) (terminal initial)) (direction : Fin 4) (wave : IntegerWavevector) :
    HasDerivAt (fun sample => responseJet initial order sample direction wave)
      (responseJet initial (order + 1) actual direction wave) actual := by
  refine Fin.cases ?_ (fun coordinate => ?_) direction
  · have differential := (HasDerivAt.fun_sum
      (fun coordinate (_ : coordinate ∈ Finset.univ) => fluxJet_evolves initial order actual member wave coordinate coordinate)).div_const 8
    simpa only [responseJet, Fin.cases_zero, trace, Nat.add_eq_zero_iff, one_ne_zero,
      and_false, if_false, zero_sub] using differential.const_sub
        (if order = 0 then baseline wave - source initial 0 wave else 0)
  · have row := (lp.evalCLM ℝ (fun _ : IntegerWavevector => ComplexCoordinateVector) 2 wave).hasFDerivAt.comp_hasDerivAt
      actual (velocityJet_evolves initial order actual member)
    have coordinateRate := (ContinuousLinearMap.proj coordinate : ComplexCoordinateVector →L[ℝ] ℂ).hasFDerivAt.comp_hasDerivAt actual row
    change HasDerivAt (fun sample => velocityJet initial order sample wave coordinate)
      (velocityJet initial (order + 1) actual wave coordinate) actual at coordinateRate
    simpa only [responseJet, Fin.cases_succ, Nat.add_eq_zero_iff, one_ne_zero,
      and_false, if_false, sub_zero] using coordinateRate.sub_const
        (if order = 0 then source initial coordinate.succ wave else 0)

theorem response_iteratedDeriv (initial : GeneratedWholeRestartCurrent nu) (order : ℕ) (actual : ℝ)
    (member : actual ∈ regularSet (receipt initial) (terminal initial)) (direction : Fin 4) (wave : IntegerWavevector) :
    iteratedDeriv order (fun sample => physicalCoefficient initial sample direction wave - source initial direction wave) actual =
      responseJet initial order actual direction wave := by
  induction order generalizing actual with
  | zero => rw [iteratedDeriv_zero]; exact (responseJet_zero initial actual direction wave).symm
  | succ order previous =>
      rw [iteratedDeriv_succ]
      have same : (fun sample => iteratedDeriv order
          (fun time => physicalCoefficient initial time direction wave - source initial direction wave) sample) =ᶠ[𝓝 actual]
            (fun sample => responseJet initial order sample direction wave) := by
        filter_upwards [(regularSet_open (receipt initial) (terminal initial)).mem_nhds member] with sample nearby
        exact previous sample nearby
      rw [same.deriv_eq]
      exact (responseJet_evolves initial order actual member direction wave).deriv

theorem velocityJet_one (initial : GeneratedWholeRestartCurrent nu) (actual : ℝ)
    (member : actual ∈ regularSet (receipt initial) (terminal initial)) : velocityJet initial 1 actual = momentum initial actual := by
  rw [velocityJet, iteratedDeriv_succ, iteratedDeriv_zero]
  exact (velocity_hasDerivAt initial actual member).deriv

end
end SaturationMonoid.NavierStokes.NativeRecoveryCurrentJets
