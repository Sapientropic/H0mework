import H0mework.Versions.X.NavierStokes.HigherTreeSextic.LatticePrefix
import H0mework.Versions.X.NavierStokes.HigherTreeSextic.LatticeTail

set_option autoImplicit false
open scoped BigOperators Topology
namespace SaturationMonoid.NavierStokes.NativeUnheatedSexticShiftRiesz
open ThreeDimensionalPeriodicCoarseFilterCore ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalVorticityCoefficientRawSourceCore ThreeDimensionalVorticityCoefficientInfiniteFixedOutputNonlinearRow
open ThreeDimensionalIntegerLatticeCriticalKernel ThreeDimensionalIntegerLatticeCriticalKernelExplicitTail
open NativeUnheatedSexticLatticePower NativeUnheatedSexticLatticePrefix NativeUnheatedRieszKernel
noncomputable section

theorem mass_triangle (a b : IntegerWavevector) : mass (a+b) ≤ 2*(mass a+mass b) := by
  have paid := norm_square_add a b
  unfold mass
  linarith

theorem radical_separation (wave first : IntegerWavevector) (radius : ℕ)
    (lower : (radius : ℝ)^2 ≤ mass wave) :
    Real.sqrt radius ≤ 2*radical first ∨ Real.sqrt radius ≤ 2*radical (wave-first) := by
  by_contra neither
  push Not at neither
  have a := pow_le_pow_left₀ (mul_nonneg (by norm_num) (radical_positive first).le) neither.1.le 4
  have b := pow_le_pow_left₀ (mul_nonneg (by norm_num) (radical_positive (wave-first)).le) neither.2.le 4
  have triangle := mass_triangle first (wave-first)
  rw [add_sub_cancel] at triangle
  have root : (Real.sqrt radius)^4 = (radius : ℝ)^2 := by
    rw [show (Real.sqrt radius)^4 = ((Real.sqrt radius)^2)^2 by ring, Real.sq_sqrt (Nat.cast_nonneg radius)]
  rw [mul_pow, radical_fourth, root] at a b
  nlinarith only [a,b,triangle,lower, mass_positive wave]

theorem density_large (power radius : ℕ) (positive : 0 < radius) (wave : IntegerWavevector)
    (lower : Real.sqrt radius ≤ 2*radical wave) :
    density power wave ≤ (2 : ℝ)^power*((Real.sqrt radius)^power)⁻¹ := by
  have root : 0 < Real.sqrt radius := Real.sqrt_pos.mpr (Nat.cast_pos.mpr positive)
  have paid := inv_anti₀ (pow_pos (div_pos root (by norm_num : (0 : ℝ) < 2)) power)
    (pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ Real.sqrt radius/2) (show Real.sqrt radius/2 ≤ radical wave by linarith) power)
  exact paid.trans_eq (by rw [div_pow, inv_div, div_eq_mul_inv])

theorem low_point (wave first : IntegerWavevector) (radius : ℕ) (positive : 0 < radius)
    (lower : (radius : ℝ)^2 ≤ mass wave) :
    density 5 first*density 2 (wave-first) ≤
      32*((Real.sqrt radius)^5)⁻¹*density 2 (wave-first)+4*((Real.sqrt radius)^2)⁻¹*density 5 first := by
  rcases radical_separation wave first radius lower with firstLarge | lastLarge
  · have paid := mul_le_mul_of_nonneg_right (density_large 5 radius positive first firstLarge) (density_positive 2 (wave-first)).le
    norm_num only at paid
    exact paid.trans (le_add_of_nonneg_right (by positivity [(density_positive 5 first).le]))
  · have paid := mul_le_mul_of_nonneg_left (density_large 2 radius positive (wave-first) lastLarge) (density_positive 5 first).le
    norm_num only at paid
    calc
      _ ≤ density 5 first*(4*((Real.sqrt radius)^2)⁻¹) := paid
      _ = 4*((Real.sqrt radius)^2)⁻¹*density 5 first := by ring
      _ ≤ _ := le_add_of_nonneg_left (by positivity [(density_positive 2 (wave-first)).le])

theorem low_sum (wave : IntegerWavevector) (radius : ℕ) (positive : 0 < radius)
    (member : wave ∈ integerWaveFrequencyCube radius) (lower : (radius : ℝ)^2 ≤ mass wave)
    (observed : Finset IntegerWavevector) :
    (∑ first ∈ observed ∩ integerWaveFrequencyCube (4*radius), density 5 first*density 2 (wave-first)) ≤
      90000*(Real.sqrt radius)⁻¹ := by
  let low := observed ∩ integerWaveFrequencyCube (4*radius)
  have first : (∑ p ∈ low, density 5 p) ≤ 106*Real.sqrt radius := by
    have paid := (Finset.sum_le_sum_of_subset_of_nonneg (s := low) Finset.inter_subset_right
      (fun p _ _ => (density_positive 5 p).le)).trans (prefix_five (4*radius) (by omega))
    apply paid.trans_eq
    rw [Nat.cast_mul, Nat.cast_ofNat, Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 4)]
    norm_num
    ring
  have images : low.image (fun p => wave-p) ⊆ integerWaveFrequencyCube (5*radius) := by
    intro q inside
    obtain ⟨p, selected, rfl⟩ := Finset.mem_image.mp inside
    simpa only [show radius+4*radius=5*radius by omega] using cube_sub member (Finset.mem_inter.mp selected).2
  have second : (∑ p ∈ low, density 2 (wave-p)) ≤ 2700*(radius : ℝ)^2 := by
    rw [← Finset.sum_image (fun _ _ _ _ same => sub_right_injective same)]
    have paid := (Finset.sum_le_sum_of_subset_of_nonneg images (fun p _ _ => (density_positive 2 p).le)).trans
      (prefix_two (5*radius) (by omega))
    exact paid.trans_eq (by push_cast; ring)
  have rows := Finset.sum_le_sum (s := low) (fun p _ => low_point wave p radius positive lower)
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum] at rows
  apply rows.trans
  have paid := add_le_add
    (mul_le_mul_of_nonneg_left second (by positivity : (0 : ℝ) ≤ 32*((Real.sqrt radius)^5)⁻¹))
    (mul_le_mul_of_nonneg_left first (by positivity : (0 : ℝ) ≤ 4*((Real.sqrt radius)^2)⁻¹))
  apply paid.trans
  have root : 0 < Real.sqrt radius := Real.sqrt_pos.mpr (Nat.cast_pos.mpr positive)
  have radiusSq : (radius : ℝ)^2 = (Real.sqrt radius)^4 := by
    rw [show (Real.sqrt radius)^4 = ((Real.sqrt radius)^2)^2 by ring, Real.sq_sqrt (Nat.cast_nonneg radius)]
  rw [radiusSq]
  have same : 32*((Real.sqrt radius)^5)⁻¹*(2700*(Real.sqrt radius)^4)+
      4*((Real.sqrt radius)^2)⁻¹*(106*Real.sqrt radius) = 86824*(Real.sqrt radius)⁻¹ := by
    field_simp
    ring
  rw [same]
  exact mul_le_mul_of_nonneg_right (by norm_num) (inv_nonneg.mpr root.le)

theorem high_point (wave first : IntegerWavevector) (radius : ℕ) (_positive : 0 < radius)
    (member : wave ∈ integerWaveFrequencyCube radius) (outside : first ∉ integerWaveFrequencyCube (4*radius)) :
    density 5 first*density 2 (wave-first) ≤ 2*density 7 first := by
  have output := integerWaveNormSq_le_three_mul_radius_sq_of_mem radius wave member
  have lower := outside_square (4*radius) first outside
  have triangle := norm_square_add wave (first-wave)
  rw [add_sub_cancel] at triangle
  have reverse : integerWaveNormSq (first-wave) = integerWaveNormSq (wave-first) := by
    unfold integerWaveNormSq
    simp only [Pi.sub_apply, Int.cast_sub]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [reverse] at triangle
  have separated : mass first ≤ 4*mass (wave-first) := by
    unfold mass
    push_cast at lower
    nlinarith
  have radicalBound : radical first^2 ≤ 2*radical (wave-first)^2 := by
    rw [radical_square, radical_square]
    exact (Real.sqrt_le_left (by positivity)).mpr (by rw [mul_pow, Real.sq_sqrt (mass_positive _).le]; norm_num; exact separated)
  have divided : density 2 (wave-first) ≤ 2*density 2 first := by
    unfold density
    have paid := mul_le_mul_of_nonneg_left (inv_anti₀ (pow_pos (radical_positive first) 2) radicalBound) (by norm_num : (0 : ℝ) ≤ 2)
    convert! paid using 1
    field_simp
  have paid := mul_le_mul_of_nonneg_left divided (density_positive 5 first).le
  rw [show (7 : ℕ)=5+2 by norm_num, density_add]
  exact paid.trans_eq (by ring)

theorem radial_bound (wave : IntegerWavevector) (radius : ℕ) (positive : 0 < radius)
    (member : wave ∈ integerWaveFrequencyCube radius) (lower : (radius : ℝ)^2 ≤ mass wave)
    (observed : Finset IntegerWavevector) :
    (∑ first ∈ observed, density 5 first*density 2 (wave-first)) ≤ 90104*(Real.sqrt radius)⁻¹ := by
  have high : (∑ first ∈ observed \ integerWaveFrequencyCube (4*radius), density 5 first*density 2 (wave-first)) ≤
      104*(Real.sqrt radius)⁻¹ := by
    have compared := Finset.sum_le_sum (s := observed \ integerWaveFrequencyCube (4*radius)) fun first inside =>
      high_point wave first radius positive member (Finset.mem_sdiff.mp inside).2
    rw [← Finset.mul_sum] at compared
    have paid := mul_le_mul_of_nonneg_left (NativeUnheatedSexticLatticeTail.seven_tail (4*radius) (by omega) observed) (by norm_num : (0 : ℝ) ≤ 2)
    apply (compared.trans paid).trans
    have large : Real.sqrt radius ≤ Real.sqrt ((4*radius : ℕ) : ℝ) := Real.sqrt_le_sqrt (by push_cast; nlinarith [Nat.cast_nonneg (α := ℝ) radius])
    have inverses := inv_anti₀ (Real.sqrt_pos.mpr (Nat.cast_pos.mpr positive)) large
    calc
      _ = 104*(Real.sqrt ((4*radius : ℕ) : ℝ))⁻¹ := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left inverses (by norm_num : (0 : ℝ) ≤ 104)
  rw [← Finset.sum_inter_add_sum_sdiff observed (integerWaveFrequencyCube (4*radius))]
  exact (add_le_add (low_sum wave radius positive member lower observed) high).trans_eq (by ring)

theorem finite_bound (wave : IntegerWavevector) (observed : Finset IntegerWavevector) :
    (∑ first ∈ observed, density 5 first*density 2 (wave-first)) ≤ 200000*density 1 wave := by
  have generated := radial_bound wave (radius wave) (radius_positive wave) (radius_member wave) (radius_lower wave) observed
  have positive : 0 < Real.sqrt (radius wave) := Real.sqrt_pos.mpr (Nat.cast_pos.mpr (radius_positive wave))
  have paid := mul_le_mul_of_nonneg_left (inv_anti₀ (radical_positive wave)
    (radical_cube_upper (radius wave) (radius_positive wave) wave (radius_member wave))) (by norm_num : (0 : ℝ) ≤ 2)
  have transfer : (Real.sqrt (radius wave))⁻¹ ≤ 2*density 1 wave := by
    rw [density, pow_one]
    convert! paid using 1
    field_simp
  exact generated.trans ((mul_le_mul_of_nonneg_left transfer (by norm_num : (0 : ℝ) ≤ 90104)).trans
    (by nlinarith [density_positive 1 wave]))

theorem kernel_summable (wave : IntegerWavevector) :
    Summable (fun first => density 5 first*density 2 (wave-first)) :=
  summable_of_sum_le (fun first => mul_nonneg (density_positive 5 first).le (density_positive 2 _).le) (finite_bound wave)

theorem kernel_bound (wave : IntegerWavevector) :
    (∑' first, density 5 first*density 2 (wave-first)) ≤ 200000*density 1 wave :=
  (kernel_summable wave).tsum_le_of_sum_le (finite_bound wave)

end
end SaturationMonoid.NavierStokes.NativeUnheatedSexticShiftRiesz
