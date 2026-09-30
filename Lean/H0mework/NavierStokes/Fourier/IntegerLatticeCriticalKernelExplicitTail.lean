import Mathlib.Algebra.Module.ZLattice.Basic
import H0mework.NavierStokes.Fourier.IntegerLatticeCriticalKernel
import H0mework.NavierStokes.WholeSpace.InfiniteFixedOutputNonlinearRow

/-!
# Explicit cubic tail for the integer critical kernel

The summable reciprocal-fourth-power lattice kernel admits a canonical
frequency-cube tail bound.  This gives source compilers an explicit finite
core radius instead of an uncontrolled finite set selected only by
`Classical.choose`.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace NavierStokes
namespace ThreeDimensionalIntegerLatticeCriticalKernelExplicitTail

open scoped BigOperators

open ThreeDimensionalPeriodicCoarseFilterCore
open ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalIntegerLatticeCriticalKernel
open ThreeDimensionalVorticityCoefficientInfiniteFixedOutputNonlinearRow

/-- Exact cardinality of the canonical integer-frequency cube. -/
theorem integerWaveFrequencyCube_card
    (radius : ℕ) :
    (integerWaveFrequencyCube radius).card =
      (2 * radius + 1) ^ 3 := by
  simp [integerWaveFrequencyCube, Fintype.card_piFinset,
    Int.card_Icc]
  omega

/-- Every wave in the radius-`r` cube has squared frequency at most
`3 r²`. -/
theorem integerWaveNormSq_le_three_mul_radius_sq_of_mem
    (radius : ℕ)
    (wave : IntegerWavevector)
    (waveMem : wave ∈ integerWaveFrequencyCube radius) :
    integerWaveNormSq wave ≤ 3 * (radius : ℝ) ^ 2 := by
  rw [integerWaveFrequencyCube, Fintype.mem_piFinset] at waveMem
  unfold integerWaveNormSq
  calc
    (∑ coordinate : Coordinate, (wave coordinate : ℝ) ^ 2) ≤
        ∑ _coordinate : Coordinate, (radius : ℝ) ^ 2 := by
      apply Finset.sum_le_sum
      intro coordinate _coordinateMem
      have coordinateMem := waveMem coordinate
      rw [Finset.mem_Icc] at coordinateMem
      have lower : -(radius : ℝ) ≤ (wave coordinate : ℝ) := by
        exact_mod_cast coordinateMem.1
      have upper : (wave coordinate : ℝ) ≤ radius := by
        exact_mod_cast coordinateMem.2
      nlinarith [sq_nonneg ((wave coordinate : ℝ) + radius),
        sq_nonneg ((wave coordinate : ℝ) - radius)]
    _ = 3 * (radius : ℝ) ^ 2 := by
      simp [Fintype.card_fin]

/-- Positive half-block inside the canonical cube.  It exposes a cubic
number of waves whose individual squared frequency is quadratic in the
radius. -/
noncomputable def integerWavePositiveHalfFrequencyBlock
    (radius : ℕ) : Finset IntegerWavevector :=
  let half := radius / 2
  Fintype.piFinset fun _ : Coordinate =>
    Finset.Icc (half : Int) (2 * half : Int)

theorem integerWavePositiveHalfFrequencyBlock_subset_cube
    (radius : ℕ) :
    integerWavePositiveHalfFrequencyBlock radius ⊆
      integerWaveFrequencyCube radius := by
  intro wave waveMem
  rw [integerWavePositiveHalfFrequencyBlock,
    Fintype.mem_piFinset] at waveMem
  rw [integerWaveFrequencyCube, Fintype.mem_piFinset]
  intro coordinate
  have coordinateMem := waveMem coordinate
  rw [Finset.mem_Icc] at coordinateMem ⊢
  have twoHalfLe : 2 * (radius / 2) ≤ radius := by omega
  constructor
  · have negLeHalf : -(radius : Int) ≤ (radius / 2 : ℕ) := by omega
    exact negLeHalf.trans coordinateMem.1
  · exact coordinateMem.2.trans (by exact_mod_cast twoHalfLe)

theorem integerWavePositiveHalfFrequencyBlock_card
    (radius : ℕ) :
    (integerWavePositiveHalfFrequencyBlock radius).card =
      (radius / 2 + 1) ^ 3 := by
  have intervalCard :
      (Finset.Icc ((radius / 2 : ℕ) : Int)
        (2 * (radius / 2 : ℕ) : Int)).card = radius / 2 + 1 := by
    rw [Int.card_Icc]
    have nonneg : 0 ≤
        (2 * ((radius / 2 : ℕ) : Int) + 1 -
          ((radius / 2 : ℕ) : Int)) := by omega
    omega
  unfold integerWavePositiveHalfFrequencyBlock
  rw [Fintype.card_piFinset]
  simp_rw [intervalCard]
  simp [Fintype.card_fin]

theorem three_halfRadius_sq_le_integerWaveNormSq_of_mem
    (radius : ℕ)
    (wave : IntegerWavevector)
    (waveMem : wave ∈ integerWavePositiveHalfFrequencyBlock radius) :
    3 * ((radius / 2 : ℕ) : ℝ) ^ 2 ≤ integerWaveNormSq wave := by
  rw [integerWavePositiveHalfFrequencyBlock,
    Fintype.mem_piFinset] at waveMem
  unfold integerWaveNormSq
  calc
    3 * ((radius / 2 : ℕ) : ℝ) ^ 2 =
        ∑ _coordinate : Coordinate,
          ((radius / 2 : ℕ) : ℝ) ^ 2 := by
      simp [Fintype.card_fin]
    _ ≤ ∑ coordinate : Coordinate, (wave coordinate : ℝ) ^ 2 := by
      apply Finset.sum_le_sum
      intro coordinate _coordinateMem
      have coordinateMem := waveMem coordinate
      rw [Finset.mem_Icc] at coordinateMem
      have lower : ((radius / 2 : ℕ) : ℝ) ≤
          (wave coordinate : ℝ) := by
        have intLower : ((radius / 2 : ℕ) : Int) ≤ wave coordinate := by
          rw [Int.natCast_div]
          exact coordinateMem.1
        change
          ((((radius / 2 : ℕ) : Int)) : ℝ) ≤
            ((wave coordinate : Int) : ℝ)
        exact Int.cast_le.mpr intLower
      nlinarith [sq_nonneg
        ((wave coordinate : ℝ) - (radius / 2 : ℕ))]

/-- Fifth-order lower bound for the exact squared-frequency mass of the
canonical cube. -/
theorem integerWaveFrequencyCube_frequencyMass_ge_halfBlock
    (radius : ℕ) :
    3 * ((radius / 2 : ℕ) : ℝ) ^ 2 *
          (((radius / 2 + 1) ^ 3 : ℕ) : ℝ) ≤
      ∑ wave ∈ integerWaveFrequencyCube radius,
        integerWaveNormSq wave := by
  let block := integerWavePositiveHalfFrequencyBlock radius
  have blockSubset : block ⊆ integerWaveFrequencyCube radius :=
    integerWavePositiveHalfFrequencyBlock_subset_cube radius
  calc
    3 * ((radius / 2 : ℕ) : ℝ) ^ 2 *
          (((radius / 2 + 1) ^ 3 : ℕ) : ℝ) =
        ∑ _wave ∈ block,
          3 * ((radius / 2 : ℕ) : ℝ) ^ 2 := by
      rw [Finset.sum_const, Finset.card_eq_sum_ones]
      simp [block, integerWavePositiveHalfFrequencyBlock_card]
      ring
    _ ≤ ∑ wave ∈ block, integerWaveNormSq wave := by
      exact Finset.sum_le_sum fun wave waveMem =>
        three_halfRadius_sq_le_integerWaveNormSq_of_mem
          radius wave waveMem
    _ ≤ ∑ wave ∈ integerWaveFrequencyCube radius,
          integerWaveNormSq wave := by
      exact Finset.sum_le_sum_of_subset_of_nonneg blockSubset
        (fun wave _cubeMem _blockNotMem => integerWaveNormSq_nonneg wave)

private theorem integerWaveFrequencyCube_mono
    {smaller larger : ℕ}
    (radiusLe : smaller ≤ larger) :
    integerWaveFrequencyCube smaller ⊆
      integerWaveFrequencyCube larger := by
  intro wave waveMem
  rw [integerWaveFrequencyCube, Fintype.mem_piFinset] at waveMem ⊢
  intro coordinate
  have coordinateMem := waveMem coordinate
  rw [Finset.mem_Icc] at coordinateMem ⊢
  have radiusCastLe : (smaller : ℤ) ≤ larger := by
    exact_mod_cast radiusLe
  constructor <;> omega

private theorem integerWaveFrequencyCube_shell_card
    (radius : ℕ) :
    (integerWaveFrequencyCube (radius + 1) \
      integerWaveFrequencyCube radius).card =
        24 * (radius + 1) ^ 2 + 2 := by
  have cubeCard (later : ℕ) :
      (integerWaveFrequencyCube later).card =
        (2 * later + 1) ^ 3 :=
    integerWaveFrequencyCube_card later
  rw [Finset.card_sdiff_of_subset
    (integerWaveFrequencyCube_mono radius.le_succ)]
  rw [cubeCard, cubeCard]
  have polynomial :
      (2 * (radius + 1) + 1) ^ 3 =
        (24 * (radius + 1) ^ 2 + 2) +
          (2 * radius + 1) ^ 3 := by
    ring
  rw [polynomial]
  omega

private theorem integerWaveCoordinateRadius_succ_sq_le_normSq
    (radius : ℕ)
    (wave : IntegerWavevector)
    (radiusLarge : radius < integerWaveCoordinateRadius wave) :
    ((radius + 1 : ℕ) : ℝ) ^ 2 ≤ integerWaveNormSq wave := by
  unfold integerWaveCoordinateRadius at radiusLarge
  obtain ⟨coordinate, _coordinateMem, coordinateLarge⟩ :=
    Finset.lt_sup_iff.mp radiusLarge
  have radiusSuccLe :
      radius + 1 ≤ Int.natAbs (wave coordinate) :=
    Nat.succ_le_iff.mpr coordinateLarge
  have radiusSuccCastLe :
      ((radius + 1 : ℕ) : ℝ) ≤
        ((Int.natAbs (wave coordinate) : ℕ) : ℝ) := by
    exact_mod_cast radiusSuccLe
  have natAbsCast :
      ((Int.natAbs (wave coordinate) : ℕ) : ℝ) =
        |(wave coordinate : ℝ)| := by
    rw [← Int.cast_natCast]
    rw [Int.natCast_natAbs]
    norm_cast
  rw [natAbsCast] at radiusSuccCastLe
  have coordinateSqLe :
      ((radius + 1 : ℕ) : ℝ) ^ 2 ≤
        (wave coordinate : ℝ) ^ 2 := by
    calc
      ((radius + 1 : ℕ) : ℝ) ^ 2 ≤
          |(wave coordinate : ℝ)| ^ 2 :=
        (sq_le_sq₀ (by positivity) (abs_nonneg _)).2 radiusSuccCastLe
      _ = (wave coordinate : ℝ) ^ 2 := sq_abs _
  exact coordinateSqLe.trans (by
    unfold integerWaveNormSq
    exact Finset.single_le_sum
      (fun other _otherMem => sq_nonneg (wave other : ℝ))
      (Finset.mem_univ coordinate))

private theorem integerWaveFrequencyCube_shell_normSq
    (radius : ℕ)
    (wave : IntegerWavevector)
    (waveMem :
      wave ∈ integerWaveFrequencyCube (radius + 1) \
        integerWaveFrequencyCube radius) :
    ((radius + 1 : ℕ) : ℝ) ^ 2 ≤ integerWaveNormSq wave := by
  have notMem : wave ∉ integerWaveFrequencyCube radius :=
    (Finset.mem_sdiff.mp waveMem).2
  have radiusLarge : radius < integerWaveCoordinateRadius wave := by
    by_contra notLarge
    exact notMem
      (integerWave_mem_frequencyCube_of_radius_le
        wave radius (Nat.le_of_not_gt notLarge))
  exact integerWaveCoordinateRadius_succ_sq_le_normSq
    radius wave radiusLarge

private theorem integerWaveCriticalKernel_shell_sum_le
    (radius : ℕ) :
    ∑ wave ∈
        integerWaveFrequencyCube (radius + 1) \
          integerWaveFrequencyCube radius,
      integerWaveCriticalKernel wave ≤
        26 * ((((radius + 1 : ℕ) : ℝ) ^ 2)⁻¹) := by
  let shell :=
    integerWaveFrequencyCube (radius + 1) \
      integerWaveFrequencyCube radius
  have radiusPos : 0 < ((radius + 1 : ℕ) : ℝ) := by
    positivity
  have pointwise :
      ∀ wave ∈ shell,
        integerWaveCriticalKernel wave ≤
          (((((radius + 1 : ℕ) : ℝ) ^ 2)⁻¹) ^ 2) := by
    intro wave waveMem
    have inverseBound :
        (integerWaveNormSq wave)⁻¹ ≤
          (((radius + 1 : ℕ) : ℝ) ^ 2)⁻¹ :=
      inv_anti₀ (sq_pos_of_pos radiusPos)
        (integerWaveFrequencyCube_shell_normSq radius wave waveMem)
    unfold integerWaveCriticalKernel
    exact
      (sq_le_sq₀
        (inv_nonneg.mpr (integerWaveNormSq_nonneg wave))
        (inv_nonneg.mpr (sq_nonneg _))).2 inverseBound
  have sumBound :=
    Finset.sum_le_card_nsmul shell
      integerWaveCriticalKernel
      (((((radius + 1 : ℕ) : ℝ) ^ 2)⁻¹) ^ 2)
      pointwise
  change
    (∑ wave ∈ shell, integerWaveCriticalKernel wave) ≤ _
  calc
    (∑ wave ∈ shell, integerWaveCriticalKernel wave) ≤
        shell.card •
          (((((radius + 1 : ℕ) : ℝ) ^ 2)⁻¹) ^ 2) := sumBound
    _ = ((shell.card : ℕ) : ℝ) *
          (((((radius + 1 : ℕ) : ℝ) ^ 2)⁻¹) ^ 2) := by
      rw [nsmul_eq_mul]
    _ = ((24 * (radius + 1) ^ 2 + 2 : ℕ) : ℝ) *
          (((((radius + 1 : ℕ) : ℝ) ^ 2)⁻¹) ^ 2) := by
      rw [show shell.card = 24 * (radius + 1) ^ 2 + 2 by
        exact integerWaveFrequencyCube_shell_card radius]
    _ ≤ 26 * ((((radius + 1 : ℕ) : ℝ) ^ 2)⁻¹) := by
      push_cast
      have radiusNonneg : 0 ≤ (radius : ℝ) := Nat.cast_nonneg radius
      have xPos : 0 < ((radius : ℝ) + 1) ^ 2 := by positivity
      have xOne : 1 ≤ ((radius : ℝ) + 1) ^ 2 := by nlinarith
      field_simp
      nlinarith

private theorem inverseSquare_Ico_sum_le
    (lower upper : ℕ)
    (lowerPos : 0 < lower)
    (lowerLe : lower ≤ upper) :
    ∑ index ∈ Finset.Ico lower upper,
        ((((index + 1 : ℕ) : ℝ) ^ 2)⁻¹) ≤
      (lower : ℝ)⁻¹ := by
  calc
    (∑ index ∈ Finset.Ico lower upper,
        ((((index + 1 : ℕ) : ℝ) ^ 2)⁻¹)) ≤
        ∑ index ∈ Finset.Ico lower upper,
          ((index : ℝ)⁻¹ - (((index + 1 : ℕ) : ℝ)⁻¹)) := by
      apply Finset.sum_le_sum
      intro index indexMem
      have oneLeIndex : 1 ≤ index :=
        lowerPos.trans_le (Finset.mem_Ico.mp indexMem).1
      have indexPos : 0 < (index : ℝ) := by
        exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one oneLeIndex)
      have successorPos : 0 < ((index + 1 : ℕ) : ℝ) := by positivity
      push_cast
      field_simp
      ring_nf
      norm_num
    _ = ((0 : ℝ)⁻¹ - (upper : ℝ)⁻¹) -
          ((0 : ℝ)⁻¹ - (lower : ℝ)⁻¹) := by
      rw [Finset.sum_Ico_eq_sub
        (fun index : ℕ =>
          ((index : ℝ)⁻¹ - (((index + 1 : ℕ) : ℝ)⁻¹)))
        lowerLe]
      rw [Finset.sum_range_sub', Finset.sum_range_sub']
      norm_num
    _ ≤ (lower : ℝ)⁻¹ := by
      have upperInvNonneg : 0 ≤ (upper : ℝ)⁻¹ :=
        inv_nonneg.mpr (Nat.cast_nonneg upper)
      simp only [_root_.inv_zero, zero_sub, sub_neg_eq_add]
      linarith

private theorem integerWaveCriticalKernel_frequencyCube_tail_le
    (lower upper : ℕ)
    (lowerPos : 0 < lower)
    (lowerLe : lower ≤ upper) :
    ∑ wave ∈
        integerWaveFrequencyCube upper \
          integerWaveFrequencyCube lower,
      integerWaveCriticalKernel wave ≤
        26 * (lower : ℝ)⁻¹ := by
  let shellSum : ℕ → ℝ := fun index =>
    ∑ wave ∈
        integerWaveFrequencyCube (index + 1) \
          integerWaveFrequencyCube index,
      integerWaveCriticalKernel wave
  have cubeZero :
      ∑ wave ∈ integerWaveFrequencyCube 0,
        integerWaveCriticalKernel wave = 0 := by
    simp [integerWaveFrequencyCube, integerWaveCriticalKernel,
      integerWaveNormSq]
  have upperExpansion :
      ∑ wave ∈ integerWaveFrequencyCube upper,
          integerWaveCriticalKernel wave =
        ∑ index ∈ Finset.range upper, shellSum index := by
    rw [Finset.sum_eq_sum_range_sdiff
      integerWaveFrequencyCube
        (fun _ _ radiusLe => integerWaveFrequencyCube_mono radiusLe)
        integerWaveCriticalKernel upper]
    rw [cubeZero, zero_add]
  have lowerExpansion :
      ∑ wave ∈ integerWaveFrequencyCube lower,
          integerWaveCriticalKernel wave =
        ∑ index ∈ Finset.range lower, shellSum index := by
    rw [Finset.sum_eq_sum_range_sdiff
      integerWaveFrequencyCube
        (fun _ _ radiusLe => integerWaveFrequencyCube_mono radiusLe)
        integerWaveCriticalKernel lower]
    rw [cubeZero, zero_add]
  have cubeSplit :=
    Finset.sum_sdiff (integerWaveFrequencyCube_mono lowerLe)
      (f := integerWaveCriticalKernel)
  have tailExpansion :
      ∑ wave ∈
          integerWaveFrequencyCube upper \
            integerWaveFrequencyCube lower,
        integerWaveCriticalKernel wave =
      ∑ index ∈ Finset.range upper \ Finset.range lower,
        shellSum index := by
    rw [upperExpansion] at cubeSplit
    rw [lowerExpansion] at cubeSplit
    have rangeSplit :=
      Finset.sum_sdiff (Finset.range_mono lowerLe) (f := shellSum)
    linarith
  rw [tailExpansion]
  have rangeDiffEq :
      Finset.range upper \ Finset.range lower =
        Finset.Ico lower upper := by
    ext index
    simp only [Finset.mem_sdiff, Finset.mem_range, Finset.mem_Ico]
    omega
  rw [rangeDiffEq]
  calc
    (∑ index ∈ Finset.Ico lower upper, shellSum index) ≤
        ∑ index ∈ Finset.Ico lower upper,
          26 * ((((index + 1 : ℕ) : ℝ) ^ 2)⁻¹) := by
      apply Finset.sum_le_sum
      intro index indexMem
      exact integerWaveCriticalKernel_shell_sum_le index
    _ = 26 * ∑ index ∈ Finset.Ico lower upper,
          ((((index + 1 : ℕ) : ℝ) ^ 2)⁻¹) := by
      rw [Finset.mul_sum]
    _ ≤ 26 * (lower : ℝ)⁻¹ := by
      exact mul_le_mul_of_nonneg_left
        (inverseSquare_Ico_sum_le lower upper lowerPos lowerLe)
        (by norm_num)

/-- Any finite inventory outside the canonical radius-`r` cube has critical
kernel mass at most `26 / r`. -/
theorem finiteModes_integerWaveCriticalKernel_tail_le
    (radius : ℕ)
    (radiusPos : 0 < radius)
    (modes : Finset IntegerWavevector) :
    ∑ wave ∈ modes \ integerWaveFrequencyCube radius,
      integerWaveCriticalKernel wave ≤
        26 * (radius : ℝ)⁻¹ := by
  let upper := max radius (modes.sup integerWaveCoordinateRadius)
  have highSubset :
      modes \ integerWaveFrequencyCube radius ⊆
        integerWaveFrequencyCube upper \
          integerWaveFrequencyCube radius := by
    intro wave waveMem
    have waveModes : wave ∈ modes := (Finset.mem_sdiff.mp waveMem).1
    have waveNotLow : wave ∉ integerWaveFrequencyCube radius :=
      (Finset.mem_sdiff.mp waveMem).2
    have radiusLeSup :
        integerWaveCoordinateRadius wave ≤
          modes.sup integerWaveCoordinateRadius :=
      Finset.le_sup waveModes
    have radiusLeUpper : integerWaveCoordinateRadius wave ≤ upper :=
      radiusLeSup.trans (Nat.le_max_right _ _)
    exact Finset.mem_sdiff.mpr
      ⟨integerWave_mem_frequencyCube_of_radius_le
          wave upper radiusLeUpper,
        waveNotLow⟩
  calc
    (∑ wave ∈ modes \ integerWaveFrequencyCube radius,
      integerWaveCriticalKernel wave) ≤
        ∑ wave ∈
            integerWaveFrequencyCube upper \
              integerWaveFrequencyCube radius,
          integerWaveCriticalKernel wave :=
      Finset.sum_le_sum_of_subset_of_nonneg highSubset
        (fun wave waveMem waveNotMem =>
          integerWaveCriticalKernel_nonneg wave)
    _ ≤ 26 * (radius : ℝ)⁻¹ :=
      integerWaveCriticalKernel_frequencyCube_tail_le
        radius upper radiusPos (Nat.le_max_left _ _)

end ThreeDimensionalIntegerLatticeCriticalKernelExplicitTail
end NavierStokes
end SaturationMonoid
