import H0mework.Versions.Y.Arithmetic.RiemannAnnulus.CoordinateMatchedAnnulusDilationSource

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual
namespace BurnolPhysicalState

open Complex MeasureTheory Set
open scoped ENNReal SchwartzMap

noncomputable section

theorem coPoissonMuntzEvenSourceMellin_smul
    (coefficient coordinate : ℂ) (source : SchwartzMap ℝ ℂ) :
    coPoissonMuntzEvenSourceMellin (coefficient • source) coordinate =
      coefficient * coPoissonMuntzEvenSourceMellin source coordinate := by
  unfold coPoissonMuntzEvenSourceMellin mellin coPoissonMuntzEvenSource
  simp only [smul_apply, smul_eq_mul]
  rw [← integral_const_mul]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro t _
  ring

def burnolCoordinateMatchedNormalizer (coordinate : ℂ) : ℂ :=
  ((2 : ℂ) * coPoissonMuntzEvenSourceMellin
    (burnolCoordinateMatchedAnnulusSource coordinate).1 coordinate)⁻¹

theorem burnolCoordinateMatchedNormalizer_ne_zero (coordinate : ℂ) :
    burnolCoordinateMatchedNormalizer coordinate ≠ 0 := by
  unfold burnolCoordinateMatchedNormalizer
  exact inv_ne_zero (mul_ne_zero (by norm_num)
    (burnolCoordinateMatchedAnnulusSource_mellin_ne_zero coordinate))

/-- Coordinate-matched compact source in the canonical normalization
`2 * Mellin(source)(coordinate) = 1`. -/
def burnolCoordinateNormalizedAnnulusSource (coordinate : ℂ) :
    burnolCompactAnnulusSource :=
  burnolCoordinateMatchedNormalizer coordinate •
    burnolCoordinateMatchedAnnulusSource coordinate

theorem burnolCoordinateNormalizedAnnulusSource_mellin_normalization
    (coordinate : ℂ) :
    (2 : ℂ) * coPoissonMuntzEvenSourceMellin
      (burnolCoordinateNormalizedAnnulusSource coordinate).1 coordinate = 1 := by
  rw [show (burnolCoordinateNormalizedAnnulusSource coordinate).1 =
      burnolCoordinateMatchedNormalizer coordinate •
        (burnolCoordinateMatchedAnnulusSource coordinate).1 by rfl]
  rw [coPoissonMuntzEvenSourceMellin_smul]
  unfold burnolCoordinateMatchedNormalizer
  field_simp [burnolCoordinateMatchedAnnulusSource_mellin_ne_zero coordinate]

theorem burnolCoordinateNormalizedAnnulusSource_mellin_ne_zero
    (coordinate : ℂ) :
    coPoissonMuntzEvenSourceMellin
      (burnolCoordinateNormalizedAnnulusSource coordinate).1 coordinate ≠ 0 := by
  intro zeroRead
  have normalization :=
    burnolCoordinateNormalizedAnnulusSource_mellin_normalization coordinate
  rw [zeroRead, mul_zero] at normalization
  exact zero_ne_one normalization

theorem burnolCoordinateNormalizedAnnulusSource_integral_ne_zero
    (coordinate : ℂ) :
    (∫ x : ℝ, (burnolCoordinateNormalizedAnnulusSource coordinate).1 x) ≠ 0 := by
  have integralRead :
      (∫ x : ℝ, (burnolCoordinateNormalizedAnnulusSource coordinate).1 x) =
        burnolCoordinateMatchedNormalizer coordinate *
          ∫ x : ℝ, burnolCoordinateMatchedAnnulusSchwartz coordinate x := by
    change (∫ x : ℝ, burnolCoordinateMatchedNormalizer coordinate *
        burnolCoordinateMatchedAnnulusSchwartz coordinate x) = _
    rw [integral_const_mul]
  rw [integralRead]
  exact mul_ne_zero (burnolCoordinateMatchedNormalizer_ne_zero coordinate)
    (burnolCoordinateMatchedAnnulusSchwartz_integral_ne_zero coordinate)

theorem burnolCoordinateNormalized_scaled_nonzero_lattice_zero
    (coordinate : ℂ) {x : ℝ} (lower : Real.log 3 ≤ x)
    (n : {n : ℤ // n ≠ 0}) :
    (burnolCoordinateNormalizedAnnulusSource coordinate).1
        (Real.exp x * (n.1 : ℝ)) = 0 := by
  change burnolCoordinateMatchedNormalizer coordinate *
      burnolCoordinateMatchedAnnulusSchwartz coordinate
        (Real.exp x * (n.1 : ℝ)) = 0
  rw [burnolCoordinateMatchedAnnulusSchwartz_zero_of_three_le_abs]
  · simp
  · rw [abs_mul, abs_of_pos (Real.exp_pos x)]
    have oneLe : (1 : ℝ) ≤ |(n.1 : ℝ)| := by
      exact_mod_cast Int.one_le_abs n.2
    have expLower : 3 ≤ Real.exp x := by
      calc
        (3 : ℝ) = Real.exp (Real.log 3) :=
          (Real.exp_log (by norm_num)).symm
        _ ≤ Real.exp x := Real.exp_le_exp.mpr lower
    nlinarith

theorem coPoissonLogOrbitMap_coordinateNormalized_ne_zero
    (coordinate : ℂ) {x : ℝ} (lower : Real.log 3 ≤ x) :
    coPoissonLogOrbitMap
        (burnolCoordinateNormalizedAnnulusSource coordinate).1 x ≠ 0 := by
  rw [coPoissonLogOrbitMap_nonzero_formula]
  have sumZero : (∑' n : {n : ℤ // n ≠ 0},
      (burnolCoordinateNormalizedAnnulusSource coordinate).1
        (Real.exp x * (n.1 : ℝ))) = 0 := by
    rw [show (fun n : {n : ℤ // n ≠ 0} =>
        (burnolCoordinateNormalizedAnnulusSource coordinate).1
          (Real.exp x * (n.1 : ℝ))) = 0 by
      funext n
      exact burnolCoordinateNormalized_scaled_nonzero_lattice_zero
        coordinate lower n]
    exact tsum_zero
  rw [sumZero, zero_sub]
  exact mul_ne_zero
    (Complex.cpow_ne_zero_iff.mpr
      (Or.inl (Complex.ofReal_ne_zero.mpr (Real.exp_ne_zero x))))
    (neg_ne_zero.mpr (smul_ne_zero (Real.exp_ne_zero (-x))
      (burnolCoordinateNormalizedAnnulusSource_integral_ne_zero coordinate)))

/-- The normalized coordinate source generates a nonzero quarter-energy
state.  Nonvanishing is witnessed by its actual large-scale co-Poisson tail,
not by feeding a Mellin value or spectral vector into the theorem. -/
theorem burnolCoordinateNormalizedRelation_sourceEnergy_ne_zero
    (coordinate z : ℂ) (positive : 0 < z.re)
    (belowHalf : z.re < (1 / 2 : ℝ)) :
    quarterMellinL2Feature z
        (coPoissonQuarterMellinConvergentMap z positive belowHalf
          (burnolCoordinateNormalizedAnnulusSource coordinate).1) ≠ 0 := by
  let source := burnolCoordinateNormalizedAnnulusSource coordinate
  let relation := coPoissonQuarterMellinConvergentMap
    z positive belowHalf source.1
  intro energyZero
  have energyAeZero :
      (quarterMellinL2Feature z relation : ℝ → ℂ) =ᵐ[volume] 0 :=
    Lp.eq_zero_iff_ae_eq_zero.mp energyZero
  have featureRead :
      (quarterMellinL2Feature z relation : ℝ → ℂ) =ᵐ[volume]
        positiveMellinLogQuarterTransform relation.1 :=
    MemLp.coeFn_toLp relation.2.1
  have orbitAeZero :
      (fun x : ℝ => coPoissonLogOrbitMap source.1 (x / 2)) =ᵐ[volume] 0 := by
    filter_upwards [featureRead, energyAeZero] with x featureAt zeroAt
    rw [← positiveMellinLogQuarterTransform_coPoissonQuarterMellinMap
      source.1 x]
    exact featureAt.symm.trans zeroAt
  have intervalMeasure :
      (volume : Measure ℝ) (Ioo (2 * Real.log 3) (2 * Real.log 3 + 1)) ≠ 0 := by
    rw [Real.volume_Ioo]
    norm_num
  obtain ⟨x, location, zeroAt⟩ :=
    Measure.exists_mem_of_measure_ne_zero_of_ae
      intervalMeasure (ae_restrict_of_ae orbitAeZero)
  exact coPoissonLogOrbitMap_coordinateNormalized_ne_zero coordinate
    (by linarith [location.1]) zeroAt

def burnolCoordinateNormalizedAnnulusDilationSource
    (coordinate : ℂ) (shift : ℝ) (nonnegative : 0 ≤ shift)
    (bounded : shift ≤ Real.log 16) : burnolCompactAnnulusSource :=
  burnolCoordinateMatchedNormalizer coordinate •
    burnolCoordinateMatchedAnnulusDilationSource
      coordinate shift nonnegative bounded

theorem burnolCoordinateNormalizedAnnulusDilationSource_coe
    (coordinate : ℂ) (shift : ℝ) (nonnegative : 0 ≤ shift)
    (bounded : shift ≤ Real.log 16) :
    (burnolCoordinateNormalizedAnnulusDilationSource
      coordinate shift nonnegative bounded).1 =
      quarterMuntzSchwartzDilationAction
        (Real.exp shift) (Real.exp_pos shift)
        (burnolCoordinateNormalizedAnnulusSource coordinate).1 := by
  change burnolCoordinateMatchedNormalizer coordinate •
      (burnolCoordinateMatchedAnnulusDilationSource
        coordinate shift nonnegative bounded).1 = _
  rw [burnolCoordinateMatchedAnnulusDilationSource_coe,
    show (burnolCoordinateNormalizedAnnulusSource coordinate).1 =
      burnolCoordinateMatchedNormalizer coordinate •
        (burnolCoordinateMatchedAnnulusSource coordinate).1 by rfl,
    map_smul]

end
end BurnolPhysicalState
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
