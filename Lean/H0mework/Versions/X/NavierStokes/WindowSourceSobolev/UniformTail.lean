import H0mework.Versions.X.NavierStokes.WindowSourceSobolev.Continuity
import Mathlib.Topology.UniformSpace.Dini

set_option autoImplicit false
open scoped BigOperators Topology ENNReal
namespace SaturationMonoid.NavierStokes.NativeWindowSobolevUniformTail
open Set Filter MeasureTheory
open ThreeDimensionalPeriodicCoarseFilterCore ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open NativeCompleteStressCarrier NativeWindowSobolevContinuity
noncomputable section
variable {nu : Viscosity}

theorem square_sum (value : Space) : HasSum (fun wave => ‖value wave‖^2) (‖value‖^2) := by
  simpa only [ENNReal.toReal_ofNat,Real.rpow_two] using
    lp.hasSum_norm (p := (2 : ℝ≥0∞)) (by norm_num) value

def tail (F : Finset IntegerWavevector) (value : Space) : ℝ := ‖value‖^2-∑ wave ∈ F, ‖value wave‖^2

theorem tail_nonnegative (F : Finset IntegerWavevector) (value : Space) : 0 ≤ tail F value := by
  unfold tail
  have paid := (square_sum value).summable.sum_le_tsum F (fun _ _ => sq_nonneg _)
  rw [(square_sum value).tsum_eq] at paid
  exact sub_nonneg.mpr paid

theorem tail_continuous (F : Finset IntegerWavevector) : Continuous (tail F) := by
  apply (continuous_norm.pow 2).sub
  exact continuous_finsetSum _ fun wave _ => (lp.evalCLM ℝ (fun _ : IntegerWavevector => Tensor) 2 wave).continuous.norm.pow 2

theorem tail_antitone (value : Space) : Antitone (fun F : Finset IntegerWavevector => tail F value) := by
  intro first last inside
  apply sub_le_sub_left
  exact Finset.sum_le_sum_of_subset_of_nonneg inside (fun _ _ _ => sq_nonneg _)

theorem tail_tendsto (value : Space) : Tendsto (fun F : Finset IntegerWavevector => tail F value) atTop (nhds 0) := by
  have constant : Tendsto (fun _ : Finset IntegerWavevector => ‖value‖^2) atTop (nhds (‖value‖^2)) := tendsto_const_nhds
  simpa only [tail,sub_self] using constant.sub (square_sum value)

theorem source_uniform_tail (seed : GeneratedWholeRestartCurrent nu) (order : ℕ) (horizon : ℝ) :
    TendstoUniformly (fun F : Finset IntegerWavevector => fun time : Icc (0 : ℝ) horizon =>
      tail F (curve seed order horizon time)) (fun _ => 0) atTop := by
  exact Antitone.tendstoUniformly_of_forall_tendsto
    (fun F => (tail_continuous F).comp (curve_continuous seed order horizon))
    (fun first last included time => tail_antitone (curve seed order horizon time) included)
    continuous_const (fun time => tail_tendsto (curve seed order horizon time))

def high (F : Finset IntegerWavevector) (value : Space) : Space :=
  ⟨fun wave => if wave ∈ F then 0 else value wave,
    (lp.memℓp value).mono' fun wave => by split_ifs <;> simp⟩

theorem high_square (F : Finset IntegerWavevector) (value : Space) : ‖high F value‖^2 = tail F value := by
  have finite : Summable (fun wave => if wave ∈ F then ‖value wave‖^2 else 0) := by
    apply summable_of_ne_finset_zero (s := F)
    intro wave outside
    simp only [if_neg outside]
  have actual (wave : IntegerWavevector) : ‖high F value wave‖^2 =
      ‖value wave‖^2-(if wave ∈ F then ‖value wave‖^2 else 0) := by
    change ‖if wave ∈ F then (0 : Tensor) else value wave‖^2 = _
    split_ifs <;> simp
  rw [← (square_sum (high F value)).tsum_eq]
  simp_rw [actual]
  rw [Summable.tsum_sub (square_sum value).summable finite,(square_sum value).tsum_eq,
    tsum_eq_sum (s := F) (fun wave outside => by simp only [if_neg outside])]
  simp only [tail,Finset.sum_ite_mem,Finset.inter_self]

theorem exists_uniform_high (seed : GeneratedWholeRestartCurrent nu) (order : ℕ) (horizon epsilon : ℝ)
    (positive : 0 < epsilon) : ∃ F : Finset IntegerWavevector, ∀ time : Icc (0 : ℝ) horizon,
      ‖high F (curve seed order horizon time)‖ < epsilon := by
  have uniform := (Metric.tendstoUniformly_iff.mp (source_uniform_tail seed order horizon))
    (epsilon^2) (sq_pos_of_pos positive)
  obtain ⟨F, all⟩ := uniform.exists
  refine ⟨F,fun time => ?_⟩
  have paid := all time
  rw [Real.dist_eq,zero_sub,abs_neg,abs_of_nonneg (tail_nonnegative _ _),← high_square] at paid
  exact (sq_lt_sq₀ (norm_nonneg _) positive.le).mp paid

open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointRecursiveMacroRuntime
open SourceGeneratedNativeResponseDisposition

theorem high_next (seed : GeneratedWholeRestartCurrent nu) (order : ℕ)
    (response : Response (GeneratedWholeRestartEndpointMacroStep nu) seed)
    (generated : generatedWholeRestartEndpointMacroRespond seed = some response)
    (time : ℝ) (nonnegative : 0 ≤ time) (F : Finset IntegerWavevector) :
    high F (NativeWindowSobolevStress.state seed order (response.2.clockAdvance+time)
      (by linarith [response.2.clockAdvance_pos])) =
      high F (NativeWindowSobolevStress.state response.1 order time (by linarith)) := by
  rw [NativeWindowSobolevStress.state_next seed order response generated time nonnegative]

end
end SaturationMonoid.NavierStokes.NativeWindowSobolevUniformTail
