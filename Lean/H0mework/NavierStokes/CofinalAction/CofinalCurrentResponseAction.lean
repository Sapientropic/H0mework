import H0mework.NavierStokes.CofinalAction.CofinalCurrentResponse

set_option autoImplicit false
open scoped BigOperators Topology

namespace SaturationMonoid.NavierStokes.NativeCofinalCurrentResponseAction

open Set
open ThreeDimensionalPeriodicCoarseFilterCore ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open ThreeDimensionalVorticityCoefficientNativeFluidMedium
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartCanonicalReplay
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open NativeHigherTimeJets NativePairedCurrentFourier NativeCofinalPairedCurrent NativeCofinalCurrentResponse
open NativeCofinalUnifiedField (target window)
open NativeCofinalUnifiedAction (momentum)
open NativeReceiptSpacetime (timeJet timeJet_zero timeJet_evolves)

noncomputable section

variable {nu : Viscosity}

def fluxJet (initial : GeneratedWholeRestartCurrent nu) (order : ℕ) (actual : ℝ) : NativeFluidStressFourierState :=
  mixedTimeSum (timeJet (window initial)) (timeJet (window initial)) order actual

theorem fluxJet_zero (initial : GeneratedWholeRestartCurrent nu) (actual : ℝ)
    (inside : actual ∈ Icc (0 : ℝ) (wholeRestartDuration (target initial).contact)) :
    fluxJet initial 0 actual = NativeStressSource.quadraticFlux (regeneratedVelocity initial actual) := by
  funext wave output input
  simp only [fluxJet, mixedTimeSum, Nat.zero_add, Finset.sum_range_one, Nat.choose_zero_right,
    Nat.cast_one, one_mul, tsub_zero, mixedFlux_diagonal, timeJet_zero (window initial) actual inside]
  rfl

theorem fluxJet_evolves (initial : GeneratedWholeRestartCurrent nu) (order : ℕ) (actual : ℝ)
    (inside : actual ∈ Icc (0 : ℝ) (wholeRestartDuration (target initial).contact))
    (wave : IntegerWavevector) (output input : Coordinate) :
    HasDerivWithinAt (fun sample => fluxJet initial order sample wave output input)
      (fluxJet initial (order + 1) actual wave output input)
      (Icc (0 : ℝ) (wholeRestartDuration (target initial).contact)) actual :=
  mixedTimeSum_hasDerivWithinAt _ _ order _ actual
    (fun rank _ => timeJet_evolves (window initial) rank actual inside)
    (fun rank _ => timeJet_evolves (window initial) rank actual inside) wave output input

def responseJet (initial : GeneratedWholeRestartCurrent nu) (order : ℕ) (actual : ℝ)
    (direction : Fin 4) (wave : IntegerWavevector) : ℂ :=
  Fin.cases
    ((if order = 0 then baseline wave - source initial 0 wave else 0) - trace (fluxJet initial order actual) wave / 8)
    (fun coordinate => timeJet (window initial) order actual wave coordinate -
      if order = 0 then source initial coordinate.succ wave else 0) direction

theorem responseJet_zero (initial : GeneratedWholeRestartCurrent nu) (actual : ℝ)
    (inside : actual ∈ Icc (0 : ℝ) (wholeRestartDuration (target initial).contact))
    (direction : Fin 4) (wave : IntegerWavevector) :
    responseJet initial 0 actual direction wave =
      regenerated initial actual direction wave - source initial direction wave := by
  rw [regenerated, current_fourier _ (regenerated_reality initial actual)]
  refine Fin.cases ?_ (fun coordinate => ?_) direction
  · change (baseline wave - source initial 0 wave) - trace (fluxJet initial 0 actual) wave / 8 =
      (baseline wave - trace (NativeStressSource.quadraticFlux (regeneratedVelocity initial actual)) wave / 8) - source initial 0 wave
    rw [fluxJet_zero initial actual inside]
    ring
  · change timeJet (window initial) 0 actual wave coordinate - source initial coordinate.succ wave = _
    rw [timeJet_zero (window initial) actual inside]
    rfl

theorem responseJet_evolves (initial : GeneratedWholeRestartCurrent nu) (order : ℕ) (actual : ℝ)
    (inside : actual ∈ Icc (0 : ℝ) (wholeRestartDuration (target initial).contact))
    (direction : Fin 4) (wave : IntegerWavevector) :
    HasDerivWithinAt (fun sample => responseJet initial order sample direction wave)
      (responseJet initial (order + 1) actual direction wave)
      (Icc (0 : ℝ) (wholeRestartDuration (target initial).contact)) actual := by
  refine Fin.cases ?_ (fun coordinate => ?_) direction
  · have differential := (HasDerivWithinAt.fun_sum
      (fun coordinate (_ : coordinate ∈ Finset.univ) => fluxJet_evolves initial order actual inside wave coordinate coordinate)).div_const 8
    simpa only [responseJet, Fin.cases_zero, trace, Nat.add_eq_zero_iff, one_ne_zero,
      and_false, if_false, zero_sub] using differential.const_sub
        (if order = 0 then baseline wave - source initial 0 wave else 0)
  · have row := (lp.evalCLM ℝ (fun _ : IntegerWavevector => ComplexCoordinateVector) 2 wave).hasFDerivAt.comp_hasDerivWithinAt
      actual (timeJet_evolves (window initial) order actual inside)
    have coordinateRate := (ContinuousLinearMap.proj coordinate : ComplexCoordinateVector →L[ℝ] ℂ).hasFDerivAt.comp_hasDerivWithinAt actual row
    change HasDerivWithinAt (fun sample => timeJet (window initial) order sample wave coordinate)
      (timeJet (window initial) (order + 1) actual wave coordinate)
      (Icc (0 : ℝ) (wholeRestartDuration (target initial).contact)) actual at coordinateRate
    simpa only [responseJet, Fin.cases_succ, Nat.add_eq_zero_iff, one_ne_zero,
      and_false, if_false, sub_zero, Function.comp_def] using coordinateRate.sub_const
        (if order = 0 then source initial coordinate.succ wave else 0)

theorem response_iteratedDerivWithin (initial : GeneratedWholeRestartCurrent nu) (order : ℕ) (actual : ℝ)
    (inside : actual ∈ Icc (0 : ℝ) (wholeRestartDuration (target initial).contact))
    (direction : Fin 4) (wave : IntegerWavevector) :
    iteratedDerivWithin order (fun sample => regenerated initial sample direction wave - source initial direction wave)
      (Icc (0 : ℝ) (wholeRestartDuration (target initial).contact)) actual =
      responseJet initial order actual direction wave := by
  induction order generalizing actual with
  | zero => rw [iteratedDerivWithin_zero]; exact (responseJet_zero initial actual inside direction wave).symm
  | succ order previous =>
      rw [iteratedDerivWithin_succ, derivWithin_congr (f := fun sample => responseJet initial order sample direction wave)
        (fun sample member => previous sample member) (previous actual inside)]
      exact (responseJet_evolves initial order actual inside direction wave).derivWithin
        (uniqueDiffOn_Icc (wholeRestartDuration_pos (target initial).contact) actual inside)

theorem fluxJet_one (initial : GeneratedWholeRestartCurrent nu) (actual : ℝ)
    (inside : actual ∈ Icc (0 : ℝ) (wholeRestartDuration (target initial).contact))
    (wave : IntegerWavevector) (output input : Coordinate) :
    fluxJet initial 1 actual wave output input =
      mixedFlux (momentum initial actual) (regeneratedVelocity initial actual) wave output input +
      mixedFlux (regeneratedVelocity initial actual) (momentum initial actual) wave output input := by
  simp only [fluxJet, mixedTimeSum, Finset.sum_range_succ, Finset.sum_range_zero, zero_add,
    Nat.choose_zero_right, Nat.choose_self, Nat.cast_one, one_mul, tsub_zero, tsub_self,
    timeJet_zero (window initial) actual inside]
  exact add_comm _ _

end
end SaturationMonoid.NavierStokes.NativeCofinalCurrentResponseAction
