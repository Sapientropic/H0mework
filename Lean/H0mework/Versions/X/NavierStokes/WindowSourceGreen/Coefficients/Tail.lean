import H0mework.Versions.X.NavierStokes.WindowSourceGreen.Coefficients.Curve

set_option autoImplicit false
open scoped BigOperators Topology ENNReal
namespace SaturationMonoid.NavierStokes.NativeWindowMotherCoefficientForm
open Set Filter MeasureTheory
open ThreeDimensionalPeriodicCoarseFilterCore ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientGeneratedIntegerShellStrongContinuationEnergyLedger
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartCrossingTangentCoercivity
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityWeakEndpoint
open NativeForwardWindowEvolution (velocityJet)
open NativeWindowSobolevVelocity (multiplier state state_row)
noncomputable section
variable {nu : Viscosity}

theorem square_sum (value : WholeRestartVelocityEndpointState) : HasSum (fun wave => ‖value wave‖^2) (‖value‖^2) := by
  simpa only [ENNReal.toReal_ofNat,Real.rpow_two] using
    lp.hasSum_norm (p := (2 : ℝ≥0∞)) (by norm_num) value

def tail (F : Finset NonzeroIntegerWavevector) (value : WholeRestartVelocityEndpointState) : ℝ := ‖value‖^2-∑ wave ∈ F, ‖value wave‖^2

theorem tail_nonnegative (F : Finset NonzeroIntegerWavevector) (value : WholeRestartVelocityEndpointState) : 0 ≤ tail F value := by
  unfold tail
  have paid := (square_sum value).summable.sum_le_tsum F (fun _ _ => sq_nonneg _)
  rw [(square_sum value).tsum_eq] at paid
  exact sub_nonneg.mpr paid

theorem tail_continuous (F : Finset NonzeroIntegerWavevector) : Continuous (tail F) := by
  apply (continuous_norm.pow 2).sub
  exact continuous_finsetSum _ fun wave _ => (lp.evalCLM ℝ (fun _ : NonzeroIntegerWavevector => ComplexCoordinateEuclidean) 2 wave).continuous.norm.pow 2

theorem tail_antitone (value : WholeRestartVelocityEndpointState) : Antitone (fun F : Finset NonzeroIntegerWavevector => tail F value) := by
  intro first last inside
  apply sub_le_sub_left
  exact Finset.sum_le_sum_of_subset_of_nonneg inside (fun _ _ _ => sq_nonneg _)

theorem tail_tendsto (value : WholeRestartVelocityEndpointState) : Tendsto (fun F : Finset NonzeroIntegerWavevector => tail F value) atTop (nhds 0) := by
  have constant : Tendsto (fun _ : Finset NonzeroIntegerWavevector => ‖value‖^2) atTop (nhds (‖value‖^2)) := tendsto_const_nhds
  simpa only [tail,sub_self] using constant.sub (square_sum value)

theorem source_uniform_tail (seed : GeneratedWholeRestartCurrent nu) (order : ℕ) (horizon : ℝ) :
    TendstoUniformly (fun F : Finset NonzeroIntegerWavevector => fun time : Icc (0 : ℝ) horizon =>
      tail F (curve seed order horizon time)) (fun _ => 0) atTop := by
  exact Antitone.tendstoUniformly_of_forall_tendsto
    (fun F => (tail_continuous F).comp (curve_continuous seed order horizon))
    (fun first last included time => tail_antitone (curve seed order horizon time) included)
    continuous_const (fun time => tail_tendsto (curve seed order horizon time))

def high (F : Finset NonzeroIntegerWavevector) (value : WholeRestartVelocityEndpointState) : WholeRestartVelocityEndpointState :=
  ⟨fun wave => if wave ∈ F then 0 else value wave,
    (lp.memℓp value).mono' fun wave => by split_ifs <;> simp⟩

theorem high_square (F : Finset NonzeroIntegerWavevector) (value : WholeRestartVelocityEndpointState) : ‖high F value‖^2 = tail F value := by
  have finite : Summable (fun wave => if wave ∈ F then ‖value wave‖^2 else 0) := by
    apply summable_of_ne_finset_zero (s := F)
    intro wave outside
    simp only [if_neg outside]
  have actual (wave : NonzeroIntegerWavevector) : ‖high F value wave‖^2 =
      ‖value wave‖^2-(if wave ∈ F then ‖value wave‖^2 else 0) := by
    change ‖if wave ∈ F then (0 : ComplexCoordinateEuclidean) else value wave‖^2 = _
    split_ifs <;> simp
  rw [← (square_sum (high F value)).tsum_eq]
  simp_rw [actual]
  rw [Summable.tsum_sub (square_sum value).summable finite,(square_sum value).tsum_eq,
    tsum_eq_sum (s := F) (fun wave outside => by simp only [if_neg outside])]
  simp only [tail,Finset.sum_ite_mem,Finset.inter_self]

theorem exists_uniform_high (seed : GeneratedWholeRestartCurrent nu) (order : ℕ) (horizon epsilon : ℝ)
    (positive : 0 < epsilon) : ∃ F : Finset NonzeroIntegerWavevector, ∀ time : Icc (0 : ℝ) horizon,
      ‖high F (curve seed order horizon time)‖ < epsilon := by
  have uniform := (Metric.tendstoUniformly_iff.mp (source_uniform_tail seed order horizon))
    (epsilon^2) (sq_pos_of_pos positive)
  obtain ⟨F, all⟩ := uniform.exists
  refine ⟨F,fun time => ?_⟩
  have paid := all time
  rw [Real.dist_eq,zero_sub,abs_neg,abs_of_nonneg (tail_nonnegative _ _),← high_square] at paid
  exact (sq_lt_sq₀ (norm_nonneg _) positive.le).mp paid

open NativePhysicalFourier (ScalarSequence)
open NativeWindowSobolevVelocity (wholeDensity)
open ThreeDimensionalVorticityCoefficientGeneratedShellSerrinGeometry

private def wholeHigh (F : Finset NonzeroIntegerWavevector) (seed : GeneratedWholeRestartCurrent nu)
    (order : ℕ) (time : ℝ) (k : IntegerWavevector) : ℝ :=
  if k∈F.image Subtype.val then 0 else wholeDensity seed order time k

private theorem wholeHigh_sum (F : Finset NonzeroIntegerWavevector)
    (seed : GeneratedWholeRestartCurrent nu) (order : ℕ) (time : ℝ) (valid : -1<time) :
    HasSum (wholeHigh F seed order time) (‖high F (state seed order time valid)‖^2) := by
  have support : Function.support (wholeHigh F seed order time)⊆{k | k≠0} := by
    intro k included
    have source : k∈Function.support (wholeDensity seed order time) := by
      intro vanish
      exact included (by simp only [wholeHigh,vanish]; split_ifs <;> rfl)
    exact NativeWindowSobolevVelocity.wholeDensity_support seed order time source
  apply (hasSum_subtype_iff_of_support_subset support).mp
  convert square_sum (high F (state seed order time valid)) using 1
  ext k
  change wholeHigh F seed order time k.1=‖if k∈F then 0 else state seed order time valid k‖^2
  have member : k.1∈F.image Subtype.val↔k∈F := Finset.mem_image.trans (by
    constructor
    · rintro ⟨j,inside,equal⟩
      exact (Subtype.ext equal : j=k) ▸ inside
    · intro inside
      exact ⟨k,inside,rfl⟩)
  simp only [wholeHigh,member]
  split_ifs
  · simp
  · rw [state_row,norm_smul,mul_pow,Real.norm_eq_abs,sq_abs,NativeWindowSobolevVelocity.multiplier_sq]
    simp only [wholeDensity,NativeUnheatedWindowGradient.whole_row_mass]

def scalarHigh (F : Finset IntegerWavevector) (c : ScalarSequence) : ScalarSequence :=
  ⟨fun k => if k∈F then 0 else c k,(lp.memℓp c).mono' fun k => by split_ifs <;> simp⟩

theorem coefficient_high (seed : GeneratedWholeRestartCurrent nu) (order : ℕ)
    (time : ℝ) (valid : -1<time) (K : ℝ) (c : ScalarSequence)
    (source : ∀ k,‖c k‖^2≤K*wholeDensity seed order time k)
    (F : Finset NonzeroIntegerWavevector) :
    ‖scalarHigh (F.image Subtype.val) c‖^2≤K*‖high F (state seed order time valid)‖^2 := by
  have scalar : HasSum (fun k => ‖scalarHigh (F.image Subtype.val) c k‖^2)
      (‖scalarHigh (F.image Subtype.val) c‖^2) := by
    simpa only [ENNReal.toReal_ofNat,Real.rpow_two] using
      lp.hasSum_norm (p := (2:ℝ≥0∞)) (by norm_num) (scalarHigh (F.image Subtype.val) c)
  have bound : ∀ k,‖scalarHigh (F.image Subtype.val) c k‖^2≤K*wholeHigh F seed order time k := by
    intro k
    change ‖if k∈F.image Subtype.val then 0 else c k‖^2≤_
    dsimp only [wholeHigh]
    split_ifs
    · simp
    · exact source k
  exact hasSum_le bound scalar ((wholeHigh_sum F seed order time valid).mul_left K)

theorem spatial_high (seed : GeneratedWholeRestartCurrent nu) (time : ℝ) (valid : -1<time)
    (j i : Coordinate) (F : Finset NonzeroIntegerWavevector) :
    ‖scalarHigh (F.image Subtype.val) (NativeWindowMotherCoefficientSpectrum.spatial seed time valid j i)‖^2≤
      (2*Real.pi)^2*‖high F (state seed 0 time valid)‖^2 :=
  coefficient_high seed 0 time valid ((2*Real.pi)^2) _
    (NativeWindowMotherCoefficientSpectrum.spatial_square seed time j i) F

theorem temporal_high (seed : GeneratedWholeRestartCurrent nu) (order : ℕ) (time : ℝ) (valid : -1<time)
    (i : Coordinate) (F : Finset NonzeroIntegerWavevector) :
    ‖scalarHigh (F.image Subtype.val) (NativeWindowMotherCoefficientSpectrum.temporal seed order time valid i)‖^2≤
      ‖high F (state seed order time valid)‖^2 := by
  simpa only [one_mul] using coefficient_high seed order time valid 1
    (NativeWindowMotherCoefficientSpectrum.temporal seed order time valid i)
    (fun k => by simpa only [one_mul,NativeWindowMotherCoefficientSpectrum.temporal] using NativeWindowMotherCoefficientSpectrum.temporal_square seed order time i k) F

theorem hOne_high (seed : GeneratedWholeRestartCurrent nu) (order : ℕ) (time : ℝ) (valid : -1<time)
    (i : Coordinate) (F : Finset NonzeroIntegerWavevector) :
    ‖scalarHigh (F.image Subtype.val) (NativeWindowMotherCoefficientSpectrum.hOne seed order time valid i)‖^2≤
      ‖high F (state seed order time valid)‖^2 := by
  simpa only [one_mul] using coefficient_high seed order time valid 1
    (NativeWindowMotherCoefficientSpectrum.hOne seed order time valid i)
    (fun k => by simpa only [one_mul,NativeWindowMotherCoefficientSpectrum.hOne] using NativeWindowMotherCoefficientSpectrum.hOne_square seed order time i k) F


end
end SaturationMonoid.NavierStokes.NativeWindowMotherCoefficientForm
