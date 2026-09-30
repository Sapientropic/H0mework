import H0mework.Versions.X.NavierStokes.WindowEnergyApproximation.Window
import H0mework.Versions.X.NavierStokes.WindowSourceSobolev.UniformTail

set_option autoImplicit false
open scoped BigOperators Topology ENNReal Pointwise
namespace SaturationMonoid.NavierStokes.NativeWindowFiniteStressTail
open Set Filter MeasureTheory
open ThreeDimensionalPeriodicCoarseFilterCore ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientInfiniteFixedOutputNonlinearRow
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open NativeCompleteStressCarrier NativeForwardWindowJets NativeWindowFiniteStressConvergence NativeWindowFiniteStressUniform
open NativeWindowSobolevUniformTail (high)
noncomputable section

theorem high_bound (F : Finset IntegerWavevector) (value : Space) : ‖high F value‖ ≤ ‖value‖ := by
  apply lp.norm_mono (by norm_num : (2 : ℝ≥0∞) ≠ 0)
  intro wave
  change ‖if wave ∈ F then (0 : Tensor) else value wave‖ ≤ _
  split_ifs <;> simp

theorem high_mono (first last : Finset IntegerWavevector) (inside : first ⊆ last) (value : Space) :
    ‖high last value‖ ≤ ‖high first value‖ := by
  apply lp.norm_mono (by norm_num : (2 : ℝ≥0∞) ≠ 0)
  intro wave
  change ‖if wave ∈ last then (0 : Tensor) else value wave‖ ≤ ‖if wave ∈ first then (0 : Tensor) else value wave‖
  by_cases member : wave ∈ first
  · simp only [if_pos member,if_pos (inside member)]
    exact le_rfl
  · split_ifs <;> simp

theorem high_difference (F : Finset IntegerWavevector) (first last : Space) :
    ‖high F first‖ ≤ ‖first-last‖+‖high F last‖ := by
  have same : high F first = high F (first-last)+high F last := by
    apply lp.ext
    funext wave
    change (if wave ∈ F then 0 else first wave) =
      (if wave ∈ F then 0 else first wave-last wave)+(if wave ∈ F then 0 else last wave)
    split_ifs <;> simp
  rw [same]
  exact (norm_add_le (high F (first-last)) (high F last)).trans
    (add_le_add (high_bound F (first-last)) (le_rfl : ‖high F last‖ ≤ ‖high F last‖))

variable {nu : Viscosity}

theorem window_supported (seed : GeneratedWholeRestartCurrent nu) (radius order : ℕ) (time : ℝ)
    (nonnegative : 0 ≤ time) (wave : IntegerWavevector)
    (outside : wave ∉ integerWaveFrequencyCube radius+integerWaveFrequencyCube radius) :
    window seed radius order time wave = 0 := by
  let observed := lp.evalCLM ℝ (fun _ : IntegerWavevector => Tensor) 2 wave
  have paid : Integrable (finiteAt seed (integerWaveFrequencyCube radius)) (volume.restrict (Icc 0 (time+2))) :=
    (finiteAt_continuous seed (integerWaveFrequencyCube radius)).integrableOn_Icc
  change observed (window seed radius order time) = 0
  rw [window_original seed radius order time time ⟨nonnegative,le_rfl⟩,NativeWindowFiniteStressUniform.average,
    ← observed.integral_comp_comm (average_integrable order time time paid)]
  have zero (sample : ℝ) : observed (kernelJet order (time-sample) • finiteAt seed (integerWaveFrequencyCube radius) sample) = 0 := by
    rw [map_smul]
    change kernelJet order (time-sample) • finite _ _ wave = 0
    rw [finite_supported _ _ wave outside,smul_zero]
  simp only [zero,integral_zero]

theorem window_high_zero (seed : GeneratedWholeRestartCurrent nu) (radius order : ℕ) (time : ℝ)
    (nonnegative : 0 ≤ time) (F : Finset IntegerWavevector)
    (covers : integerWaveFrequencyCube radius+integerWaveFrequencyCube radius ⊆ F) :
    high F (window seed radius order time) = 0 := by
  apply lp.ext
  funext wave
  change (if wave ∈ F then 0 else window seed radius order time wave) = 0
  by_cases inside : wave ∈ F
  · rw [if_pos inside]
  · rw [if_neg inside]
    exact window_supported seed radius order time nonnegative wave (fun member => inside (covers member))

def prefixSupport (length : ℕ) : Finset IntegerWavevector :=
  (Finset.range length).biUnion fun radius => integerWaveFrequencyCube radius+integerWaveFrequencyCube radius

theorem prefix_covers (length radius : ℕ) (before : radius < length) :
    integerWaveFrequencyCube radius+integerWaveFrequencyCube radius ⊆ prefixSupport length := by
  intro wave member
  exact Finset.mem_biUnion.mpr ⟨radius,Finset.mem_range.mpr before,member⟩

theorem exists_uniform_high (seed : GeneratedWholeRestartCurrent nu) (order : ℕ) (horizon delta : ℝ)
    (nonnegative : 0 ≤ horizon) (positive : 0 < delta) :
    ∃ F : Finset IntegerWavevector, ∀ radius : ℕ, ∀ time : Icc (0 : ℝ) horizon,
      ‖high F (window seed radius order time)‖ < delta := by
  obtain ⟨whole,wholeSmall⟩ := NativeWindowSobolevUniformTail.exists_uniform_high seed order horizon (delta/3) (by positivity)
  have approximation := (Metric.tendstoUniformly_iff.mp (uniform_tendsto seed order horizon nonnegative))
    (delta/3) (by positivity)
  obtain ⟨length,all⟩ := eventually_atTop.mp approximation
  refine ⟨whole∪prefixSupport length,fun radius time => ?_⟩
  by_cases after : length ≤ radius
  · let target := NativeWindowSobolevContinuity.curve seed order horizon time
    have close : ‖window seed radius order time-target‖ < delta/3 := by
      have paid := all radius after time
      rwa [dist_comm,dist_eq_norm] at paid
    have small : ‖high (whole∪prefixSupport length) target‖ < delta/3 :=
      (high_mono whole _ Finset.subset_union_left target).trans_lt (wholeSmall time)
    exact (high_difference _ (window seed radius order time) target).trans_lt (by linarith)
  · rw [window_high_zero seed radius order time time.property.1 _
      ((prefix_covers length radius (Nat.lt_of_not_ge after)).trans Finset.subset_union_right),norm_zero]
    exact positive

end
end SaturationMonoid.NavierStokes.NativeWindowFiniteStressTail
