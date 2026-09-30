import H0mework.NavierStokes.MacroAction.FiniteMacroGlobal
import H0mework.NavierStokes.TimeJets.TimeCarrier

set_option autoImplicit false
open scoped Topology

namespace SaturationMonoid.NavierStokes.NativeMomentumIntegral

open Set Filter MeasureTheory
open ThreeDimensionalPeriodicCoarseFilterCore
open ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientWholeVelocityPairDiagonalBudget
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open ThreeDimensionalVorticityCoefficientFiniteGalerkinMildDuhamel
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityWeakEndpoint
open ThreeDimensionalVorticityCoefficientFinitePhysicalTrajectoryEndpointSplice
open NativeStressSource NativeEndpointVelocityCarrier NativeTimeJetCarrier

noncomputable section

def row (state : WholeRestartVelocityEndpointState) (wave : IntegerWavevector) : ComplexCoordinateVector :=
  wholeVelocity state wave

def action (nu : Viscosity) (state : WholeRestartVelocityEndpointState)
    (wave : IntegerWavevector) : ComplexCoordinateVector :=
  projectedDivergenceCLM wave (quadraticFlux (wholeVelocity state) wave) -
    (nu.coeff * integerWaveViscousMultiplier wave) • row state wave

def WritesOn (nu : Viscosity) (curve : ℝ → WholeRestartVelocityEndpointState) (horizon : ℝ) : Prop :=
  ∀ wave, IntervalIntegrable (fun time => action nu (curve time) wave) volume 0 horizon ∧
    ∀ time ∈ Icc (0 : ℝ) horizon,
      row (curve time) wave - row (curve 0) wave = ∫ earlier in (0 : ℝ)..time, action nu (curve earlier) wave

variable {nu : Viscosity} {curve prior restart : ℝ → WholeRestartVelocityEndpointState} {horizon joinTime : ℝ}

theorem writes_zero : WritesOn nu curve 0 := by
  intro wave
  refine ⟨IntervalIntegrable.refl, ?_⟩
  intro time inside
  have same : time = 0 := le_antisymm inside.2 inside.1
  simp [same]

theorem WritesOn.mono (source : WritesOn nu curve horizon) {smaller : ℝ}
    (nonnegative : 0 ≤ smaller) (below : smaller ≤ horizon) : WritesOn nu curve smaller := by
  intro wave
  refine ⟨(source wave).1.mono_set ?_, ?_⟩
  · rw [uIcc_of_le nonnegative, uIcc_of_le (nonnegative.trans below)]
    exact Icc_subset_Icc le_rfl below
  · intro time inside
    exact (source wave).2 time ⟨inside.1, inside.2.trans below⟩

theorem WritesOn.between (source : WritesOn nu curve horizon) {a b : ℝ}
    (a_mem : a ∈ Icc (0 : ℝ) horizon) (b_mem : b ∈ Icc (0 : ℝ) horizon) (wave : IntegerWavevector) :
    row (curve b) wave - row (curve a) wave = ∫ time in a..b, action nu (curve time) wave := by
  have paidA := ((source.mono a_mem.1 a_mem.2) wave).1
  have paidB := ((source.mono b_mem.1 b_mem.2) wave).1
  have split := intervalIntegral.integral_add_adjacent_intervals paidA (paidA.symm.trans paidB)
  rw [← (source wave).2 a a_mem, ← (source wave).2 b b_mem] at split
  linear_combination -split

theorem WritesOn.congr (source : WritesOn nu curve horizon) (nonnegative : 0 ≤ horizon)
    {other : ℝ → WholeRestartVelocityEndpointState} (same : ∀ time ∈ Icc (0 : ℝ) horizon, other time = curve time) :
    WritesOn nu other horizon := by
  intro wave
  have equalAction : ∀ time ∈ uIcc (0 : ℝ) horizon, action nu (curve time) wave = action nu (other time) wave := by
    rw [uIcc_of_le nonnegative]
    intro time inside
    rw [same time inside]
  refine ⟨(source wave).1.congr (fun time inside => equalAction time (uIoc_subset_uIcc inside)), ?_⟩
  intro time inside
  rw [same time inside, same 0 ⟨le_rfl, nonnegative⟩, (source wave).2 time inside]
  apply intervalIntegral.integral_congr
  intro earlier within
  rw [uIcc_of_le inside.1] at within
  exact equalAction earlier (by rw [uIcc_of_le nonnegative]; exact ⟨within.1, within.2.trans inside.2⟩)

theorem splice_chart (same : restart 0 = prior joinTime) (time : ℝ) (nonnegative : 0 ≤ time) :
    endpointSplice joinTime prior restart (joinTime + time) = restart time := by
  by_cases zero : time = 0
  · simp [zero, endpointSplice_of_le, same]
  · rw [endpointSplice_of_lt _ _ _ _ (by linarith [lt_of_le_of_ne nonnegative (Ne.symm zero)]), add_sub_cancel_left]

theorem WritesOn.splice (first : WritesOn nu prior joinTime) (second : WritesOn nu restart horizon)
    (join_nonnegative : 0 ≤ joinTime) (horizon_nonnegative : 0 ≤ horizon)
    (same : restart 0 = prior joinTime) :
    WritesOn nu (endpointSplice joinTime prior restart) (joinTime + horizon) := by
  let joined := endpointSplice joinTime prior restart
  have before : WritesOn nu joined joinTime := first.congr join_nonnegative
    (fun time inside => endpointSplice_of_le _ _ _ _ inside.2)
  have after (wave : IntegerWavevector) (time : ℝ) (inside : time ∈ Icc joinTime (joinTime + horizon)) :
      IntervalIntegrable (fun sample => action nu (joined sample) wave) volume joinTime time ∧
        row (joined time) wave - row (joined joinTime) wave =
          ∫ sample in joinTime..time, action nu (joined sample) wave := by
    have elapsed : time - joinTime ∈ Icc (0 : ℝ) horizon := ⟨sub_nonneg.mpr inside.1, by linarith [inside.2]⟩
    have sameTime (sample : ℝ) (later : joinTime ≤ sample) : joined sample = restart (sample - joinTime) := by
      simpa only [add_sub_cancel] using splice_chart same (sample - joinTime) (sub_nonneg.mpr later)
    have paid : IntervalIntegrable (fun sample => action nu (restart (sample - joinTime)) wave) volume joinTime time := by
      simpa only [zero_add, sub_add_cancel] using (((second.mono elapsed.1 elapsed.2) wave).1.comp_sub_right joinTime)
    have paidJoined : IntervalIntegrable (fun sample => action nu (joined sample) wave) volume joinTime time :=
      paid.congr (fun sample member => by
      rw [uIoc_of_le inside.1] at member
      rw [sameTime sample member.1.le])
    refine ⟨paidJoined, ?_⟩
    rw [sameTime time inside.1, sameTime joinTime le_rfl, sub_self, (second wave).2 _ elapsed]
    calc
      _ = ∫ sample in joinTime..time, action nu (restart (sample - joinTime)) wave := by
        simpa only [sub_self] using (intervalIntegral.integral_comp_sub_right
          (fun sample => action nu (restart sample) wave) (a := joinTime) (b := time) joinTime).symm
      _ = _ := intervalIntegral.integral_congr (fun sample member => by
        rw [uIcc_of_le inside.1] at member
        rw [sameTime sample member.1])
  intro wave
  refine ⟨(before wave).1.trans (after wave _ ⟨by linarith, le_rfl⟩).1, ?_⟩
  intro time inside
  by_cases earlier : time ≤ joinTime
  · exact (before wave).2 time ⟨inside.1, earlier⟩
  · have later : time ∈ Icc joinTime (joinTime + horizon) := ⟨(lt_of_not_ge earlier).le, inside.2⟩
    have split := intervalIntegral.integral_add_adjacent_intervals (before wave).1 (after wave time later).1
    rw [← (before wave).2 joinTime ⟨join_nonnegative, le_rfl⟩, ← (after wave time later).2] at split
    linear_combination split

end
end SaturationMonoid.NavierStokes.NativeMomentumIntegral
