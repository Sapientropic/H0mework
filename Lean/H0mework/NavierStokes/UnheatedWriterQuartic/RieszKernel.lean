import H0mework.NavierStokes.ClockMoment.Kernel
import H0mework.NavierStokes.StressAction.CompleteStressCarrier

set_option autoImplicit false
open scoped BigOperators Topology
namespace SaturationMonoid.NavierStokes.NativeUnheatedRieszKernel
open Set Filter
open ThreeDimensionalPeriodicCoarseFilterCore ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalVorticityCoefficientRawSourceCore ThreeDimensionalVorticityCoefficientInfiniteFixedOutputNonlinearRow
open ThreeDimensionalIntegerLatticeCriticalKernel ThreeDimensionalIntegerLatticeCriticalKernelExplicitTail
open NativeCompleteStressCarrier
noncomputable section

theorem radius_square (wave : IntegerWavevector) : (integerWaveCoordinateRadius wave : ℝ)^2 ≤ integerWaveNormSq wave := by
  obtain ⟨i, _, same⟩ := Finset.exists_mem_eq_sup Finset.univ Finset.univ_nonempty (fun i : Coordinate => Int.natAbs (wave i))
  change ((Finset.univ.sup (fun i : Coordinate => Int.natAbs (wave i)) : ℕ) : ℝ)^2 ≤ _
  rw [same]
  have cast : (Int.natAbs (wave i) : ℝ) = |(wave i : ℝ)| := by
    rw [← Int.cast_natCast, Int.natCast_natAbs]
    norm_cast
  rw [cast, sq_abs]
  exact Finset.single_le_sum (fun j _ => sq_nonneg (wave j : ℝ)) (Finset.mem_univ i)

theorem outside_square (radius : ℕ) (wave : IntegerWavevector) (outside : wave ∉ integerWaveFrequencyCube radius) :
    (radius : ℝ)^2 ≤ integerWaveNormSq wave := by
  have larger : radius ≤ integerWaveCoordinateRadius wave := by
    by_contra contrary
    exact outside (integerWave_mem_frequencyCube_of_radius_le wave radius (Nat.le_of_lt (Nat.lt_of_not_ge contrary)))
  exact (pow_le_pow_left₀ (Nat.cast_nonneg radius) (Nat.cast_le.mpr larger) 2).trans (radius_square wave)

theorem cube_sub {r s : ℕ} {k p : IntegerWavevector}
    (first : k ∈ integerWaveFrequencyCube r) (last : p ∈ integerWaveFrequencyCube s) :
    k-p ∈ integerWaveFrequencyCube (r+s) := by
  rw [integerWaveFrequencyCube, Fintype.mem_piFinset] at first last ⊢
  intro i
  have a := first i
  have b := last i
  simp only [Finset.mem_Icc, Pi.sub_apply, Nat.cast_add] at a b ⊢
  omega

theorem norm_square_add (a b : IntegerWavevector) :
    integerWaveNormSq (a+b) ≤ 2*(integerWaveNormSq a+integerWaveNormSq b) := by
  have row (i : Coordinate) : ((a i : ℝ)+(b i : ℝ))^2 ≤ 2*((a i : ℝ)^2+(b i : ℝ)^2) := by
    nlinarith [sq_nonneg ((a i : ℝ)-(b i : ℝ))]
  have paid := Finset.sum_le_sum (s := Finset.univ) (fun i _ => row i)
  simp only [← Finset.mul_sum, Finset.sum_add_distrib] at paid
  simpa only [integerWaveNormSq, Pi.add_apply, Int.cast_add] using paid

theorem weight_split (wave : IntegerWavevector) :
    weight wave = (if wave = 0 then 1 else 0)+(integerWaveNormSq wave)⁻¹ := by
  by_cases zero : wave = 0 <;> simp [weight, zero]

theorem inverse_weight_lower (wave : IntegerWavevector) : integerWaveNormSq wave ≤ (weight wave)⁻¹ := by
  by_cases zero : wave = 0 <;> simp [weight, zero]

theorem cube_weight_sum (radius : ℕ) :
    (∑ wave ∈ integerWaveFrequencyCube radius, weight wave) ≤ 1+26*(radius : ℝ) := by
  have zero : (0 : IntegerWavevector) ∈ integerWaveFrequencyCube radius := by
    simp [integerWaveFrequencyCube, Fintype.mem_piFinset]
  simp_rw [weight_split]
  rw [Finset.sum_add_distrib]
  simpa only [Finset.sum_ite_eq', zero, if_true] using
    add_le_add (le_rfl : (1 : ℝ) ≤ 1) (NativeUnheatedClockMomentKernel.cube_inverse_sum radius)

theorem low_point (k p : IntegerWavevector) (radius : ℕ) (positive : 0 < radius)
    (lower : (radius : ℝ)^2 ≤ integerWaveNormSq k) :
    weight p*weight (k-p) ≤ (2/(radius : ℝ)^2)*(weight p+weight (k-p)) := by
  have original := norm_square_add p (k-p)
  rw [add_sub_cancel] at original
  have denom : (radius : ℝ)^2 ≤ 2*((weight p)⁻¹+(weight (k-p))⁻¹) := by
    linarith [inverse_weight_lower p, inverse_weight_lower (k-p)]
  have paid : (radius : ℝ)^2*(weight p*weight (k-p)) ≤ 2*(weight p+weight (k-p)) := by
    apply (mul_le_mul_of_nonneg_right denom (mul_nonneg (weight_pos p).le (weight_pos (k-p)).le)).trans_eq
    field_simp [(weight_pos p).ne', (weight_pos (k-p)).ne']
    ring
  calc
    _ ≤ (2*(weight p+weight (k-p)))/(radius : ℝ)^2 :=
      (le_div_iff₀ (sq_pos_of_pos (Nat.cast_pos.mpr positive))).mpr (by simpa only [mul_comm] using paid)
    _ = _ := by ring

theorem low_sum (k : IntegerWavevector) (radius : ℕ) (positive : 0 < radius)
    (member : k ∈ integerWaveFrequencyCube radius) (lower : (radius : ℝ)^2 ≤ integerWaveNormSq k)
    (F : Finset IntegerWavevector) :
    (∑ p ∈ F ∩ integerWaveFrequencyCube (4*radius), weight p*weight (k-p)) ≤ 472/(radius : ℝ) := by
  let low := F ∩ integerWaveFrequencyCube (4*radius)
  have first : (∑ p ∈ low, weight p) ≤ 1+26*((4*radius : ℕ) : ℝ) :=
    (Finset.sum_le_sum_of_subset_of_nonneg Finset.inter_subset_right (fun p _ _ => (weight_pos p).le)).trans (cube_weight_sum _)
  have images : low.image (fun p => k-p) ⊆ integerWaveFrequencyCube (5*radius) := by
    intro q inside
    obtain ⟨p, selected, rfl⟩ := Finset.mem_image.mp inside
    simpa only [show radius+4*radius = 5*radius by omega] using cube_sub member (Finset.mem_inter.mp selected).2
  have second : (∑ p ∈ low, weight (k-p)) ≤ 1+26*((5*radius : ℕ) : ℝ) := by
    rw [← Finset.sum_image (fun _ _ _ _ same => sub_right_injective same)]
    exact (Finset.sum_le_sum_of_subset_of_nonneg images (fun p _ _ => (weight_pos p).le)).trans (cube_weight_sum _)
  have paid := Finset.sum_le_sum (s := low) (fun p _ => low_point k p radius positive lower)
  rw [← Finset.mul_sum, Finset.sum_add_distrib] at paid
  apply paid.trans
  have bounded := mul_le_mul_of_nonneg_left (add_le_add first second) (by positivity : (0 : ℝ) ≤ 2/(radius : ℝ)^2)
  apply bounded.trans
  have atLeast : (1 : ℝ) ≤ radius := by exact_mod_cast positive
  push_cast
  calc
    _ = (4+468*(radius : ℝ))/(radius : ℝ)^2 := by ring
    _ ≤ (472*(radius : ℝ))/(radius : ℝ)^2 := div_le_div_of_nonneg_right (by linarith) (sq_nonneg _)
    _ = _ := by field_simp

theorem high_point (k p : IntegerWavevector) (radius : ℕ) (positive : 0 < radius)
    (member : k ∈ integerWaveFrequencyCube radius) (outside : p ∉ integerWaveFrequencyCube (4*radius)) :
    weight p*weight (k-p) ≤ 4*integerWaveCriticalKernel p := by
  have kp := integerWaveNormSq_le_three_mul_radius_sq_of_mem radius k member
  have pp := outside_square (4*radius) p outside
  have triangle := norm_square_add k (p-k)
  rw [add_sub_cancel] at triangle
  have reversal : integerWaveNormSq (p-k) = integerWaveNormSq (k-p) := by
    unfold integerWaveNormSq
    simp only [Pi.sub_apply, Int.cast_sub]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [reversal] at triangle
  have rpos : (0 : ℝ) < radius := Nat.cast_pos.mpr positive
  have ppos : 0 < integerWaveNormSq p := by push_cast at pp; nlinarith
  have lower : integerWaveNormSq p/4 ≤ integerWaveNormSq (k-p) := by push_cast at pp; nlinarith
  have qpos : 0 < integerWaveNormSq (k-p) := (div_pos ppos (by norm_num)).trans_le lower
  have pnz : p ≠ 0 := by intro zero; simp [zero] at ppos
  have qnz : k-p ≠ 0 := by intro zero; simp [zero] at qpos
  have compared : (integerWaveNormSq (k-p))⁻¹ ≤ 4*(integerWaveNormSq p)⁻¹ :=
    (inv_anti₀ (div_pos ppos (by norm_num)) lower).trans_eq (by field_simp)
  simp only [weight, if_neg pnz, if_neg qnz, integerWaveCriticalKernel]
  exact (mul_le_mul_of_nonneg_left compared (inv_nonneg.mpr ppos.le)).trans_eq (by ring)

theorem radial_sum (k : IntegerWavevector) (radius : ℕ) (positive : 0 < radius)
    (member : k ∈ integerWaveFrequencyCube radius) (lower : (radius : ℝ)^2 ≤ integerWaveNormSq k)
    (F : Finset IntegerWavevector) :
    (∑ p ∈ F, weight p*weight (k-p)) ≤ 498/(radius : ℝ) := by
  have high : (∑ p ∈ F \ integerWaveFrequencyCube (4*radius), weight p*weight (k-p)) ≤ 26/(radius : ℝ) := by
    have rows := Finset.sum_le_sum (s := F \ integerWaveFrequencyCube (4*radius))
      (fun p inside => high_point k p radius positive member (Finset.mem_sdiff.mp inside).2)
    rw [← Finset.mul_sum] at rows
    exact rows.trans ((mul_le_mul_of_nonneg_left (finiteModes_integerWaveCriticalKernel_tail_le
      (4*radius) (by omega) F) (by norm_num : (0 : ℝ) ≤ 4)).trans_eq (by push_cast; field_simp))
  rw [← Finset.sum_inter_add_sum_sdiff F (integerWaveFrequencyCube (4*radius))]
  exact (add_le_add (low_sum k radius positive member lower F) high).trans_eq (by ring)

def constant : ℝ := 1000+∑' wave, weight wave^2

theorem constant_nonnegative : 0 ≤ constant := add_nonneg (by norm_num) (tsum_nonneg fun _ => sq_nonneg _)

theorem finite_bound (k : IntegerWavevector) (F : Finset IntegerWavevector) :
    Real.sqrt (1+integerWaveNormSq k)*(∑ p ∈ F, weight p*weight (k-p)) ≤ constant := by
  by_cases zero : k = 0
  · have neg (p : IntegerWavevector) : weight (-p) = weight p := by
      simp [weight, integerWaveNormSq]
    simp only [zero, integerWaveNormSq_zero, add_zero, Real.sqrt_one, one_mul, zero_sub, neg, ← pow_two]
    exact (weight_summable.sum_le_tsum F (fun _ _ => sq_nonneg _)).trans (le_add_of_nonneg_left (by norm_num))
  · let radius := integerWaveCoordinateRadius k
    have member : k ∈ integerWaveFrequencyCube radius := integerWave_mem_frequencyCube_of_radius_le k radius le_rfl
    have positive : 0 < radius := by
      by_contra nonpositive
      have rzero : radius = 0 := Nat.eq_zero_of_not_pos nonpositive
      have paid := integerWaveNormSq_le_three_mul_radius_sq_of_mem radius k member
      rw [rzero, Nat.cast_zero, zero_pow (by decide : (2 : ℕ) ≠ 0), mul_zero] at paid
      exact zero ((integerWaveNormSq_eq_zero_iff k).mp (le_antisymm paid (integerWaveNormSq_nonneg k)))
    have rpos : (0 : ℝ) < radius := Nat.cast_pos.mpr positive
    have atLeast : (1 : ℝ) ≤ radius := by exact_mod_cast positive
    have upper : Real.sqrt (1+integerWaveNormSq k) ≤ 2*(radius : ℝ) := by
      apply (Real.sqrt_le_left (by positivity)).mpr
      nlinarith [integerWaveNormSq_le_three_mul_radius_sq_of_mem radius k member]
    have paid := mul_le_mul upper (radial_sum k radius positive member (radius_square k) F)
      (Finset.sum_nonneg fun p _ => mul_nonneg (weight_pos p).le (weight_pos (k-p)).le) (by positivity)
    have scalar : 2*(radius : ℝ)*(498/(radius : ℝ)) = 996 := by field_simp; norm_num
    rw [scalar] at paid
    exact paid.trans ((by norm_num : (996 : ℝ) ≤ 1000).trans
      (le_add_of_nonneg_right (tsum_nonneg (fun wave => sq_nonneg (weight wave)))))

theorem kernel_summable (k : IntegerWavevector) : Summable (fun p => weight p*weight (k-p)) := by
  apply summable_of_sum_le (c := constant/Real.sqrt (1+integerWaveNormSq k))
    (fun p => mul_nonneg (weight_pos p).le (weight_pos (k-p)).le)
  intro F
  exact (le_div_iff₀ (Real.sqrt_pos.mpr (by linarith [integerWaveNormSq_nonneg k]))).mpr
    (by simpa only [mul_comm] using finite_bound k F)

theorem kernel_bound (k : IntegerWavevector) :
    Real.sqrt (1+integerWaveNormSq k)*(∑' p, weight p*weight (k-p)) ≤ constant := by
  rw [← tsum_mul_left]
  apply ((kernel_summable k).mul_left _).tsum_le_of_sum_le
  intro F
  simpa only [Finset.mul_sum] using finite_bound k F

end
end SaturationMonoid.NavierStokes.NativeUnheatedRieszKernel
