import H0mework.NavierStokes.Fourier.IntegerCharacterUnitCellMean

/-!
# Integer-character orthogonality on the physical unit cell

The unit-cell mean of a single integer character is combined with the
elementary product-to-sum identities.  The resulting formulas are stated on
the full integer-wavevector carrier: the zero mode, equal frequencies, and
opposite frequencies are all handled by the displayed Kronecker terms rather
than by side hypotheses.

The normalization of the constant character is proved here from the actual
coordinate equivalence and the volume of the coordinate unit cube.  Thus this
module depends only on the low-level unit-cell geometry and the already proved
single-character means.
-/

open MeasureTheory Set

namespace SaturationMonoid
namespace NavierStokes
namespace ThreeDimensionalPeriodicIntegerCharacterOrthogonality

open ThreeDimensionalPeriodicCoarseFilterCore
open ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicIntegerCharacterUnitCellMean
open ThreeDimensionalPeriodicUnitCellDivergence

noncomputable section

/-- The physical unit cell has volume one. -/
theorem physicalUnitCell_integral_one :
    (∫ _x in physicalUnitCell, (1 : ℝ)) = 1 := by
  have hembedding : MeasurableEmbedding coordinateEquiv :=
    coordinateEquiv.toHomeomorph.measurableEmbedding
  calc
    (∫ _x in physicalUnitCell, (1 : ℝ)) =
        ∫ _y in coordinateUnitCube, (1 : ℝ) := by
      rw [← coordinateEquiv_measurePreserving.setIntegral_preimage_emb
        hembedding]
      rfl
    _ = 1 := by
      rw [setIntegral_const]
      simp only [smul_eq_mul, mul_one, measureReal_def]
      unfold coordinateUnitCube
      have cubeVolume :=
        Real.volume_Icc_pi_toReal
          (a := (0 : CoordinateSpace)) (b := fun _ => 1)
          (fun _ => zero_le_one)
      simpa using cubeVolume

theorem integerWavePhase_wavevector_add
    (k l : IntegerWavevector) (x : PhysicalSpace) :
    integerWavePhase (k + l) x =
      integerWavePhase k x + integerWavePhase l x := by
  simp only [integerWavePhase, Pi.add_apply, Int.cast_add,
    add_mul, Finset.sum_add_distrib]
  ring

theorem integerWavePhase_wavevector_sub
    (k l : IntegerWavevector) (x : PhysicalSpace) :
    integerWavePhase (k - l) x =
      integerWavePhase k x - integerWavePhase l x := by
  simp only [integerWavePhase, Pi.sub_apply, Int.cast_sub,
    sub_mul, Finset.sum_sub_distrib]
  ring

theorem integerCosine_mul_integerCosine
    (k l : IntegerWavevector) (x : PhysicalSpace) :
    integerCosine k x * integerCosine l x =
      (integerCosine (k + l) x +
        integerCosine (k - l) x) / 2 := by
  unfold integerCosine
  rw [integerWavePhase_wavevector_add,
    integerWavePhase_wavevector_sub,
    Real.cos_add, Real.cos_sub]
  ring

theorem integerSine_mul_integerSine
    (k l : IntegerWavevector) (x : PhysicalSpace) :
    integerSine k x * integerSine l x =
      (integerCosine (k - l) x -
        integerCosine (k + l) x) / 2 := by
  unfold integerSine integerCosine
  rw [integerWavePhase_wavevector_sub,
    integerWavePhase_wavevector_add,
    Real.cos_sub, Real.cos_add]
  ring

theorem integerSine_mul_integerCosine
    (k l : IntegerWavevector) (x : PhysicalSpace) :
    integerSine k x * integerCosine l x =
      (integerSine (k + l) x +
        integerSine (k - l) x) / 2 := by
  unfold integerSine integerCosine
  rw [integerWavePhase_wavevector_add,
    integerWavePhase_wavevector_sub,
    Real.sin_add, Real.sin_sub]
  ring

private theorem integerCosine_integrableOn_physicalUnitCell
    (k : IntegerWavevector) :
    IntegrableOn (integerCosine k) physicalUnitCell :=
  (integerCosine_continuous k).continuousOn.integrableOn_compact
    physicalUnitCell_isCompact

private theorem integerSine_integrableOn_physicalUnitCell
    (k : IntegerWavevector) :
    IntegrableOn (integerSine k) physicalUnitCell :=
  (integerSine_continuous k).continuousOn.integrableOn_compact
    physicalUnitCell_isCompact

/-- The zero mode is included in the single-cosine unit-cell mean. -/
theorem physicalUnitCell_integerCosine_integral
    (k : IntegerWavevector) :
    (∫ x in physicalUnitCell, integerCosine k x) =
      if k = 0 then 1 else 0 := by
  by_cases hk : k = 0
  · subst k
    rw [if_pos rfl]
    simpa [integerCosine, integerWavePhase] using
      physicalUnitCell_integral_one
  · rw [if_neg hk]
    exact physicalUnitCell_integerCosine_integral_eq_zero k hk

/-- Every integer sine character, including the zero mode, has zero mean. -/
theorem physicalUnitCell_integerSine_integral
    (k : IntegerWavevector) :
    (∫ x in physicalUnitCell, integerSine k x) = 0 := by
  by_cases hk : k = 0
  · subst k
    simp [integerSine, integerWavePhase]
  · exact physicalUnitCell_integerSine_integral_eq_zero k hk

/-- Full cosine-character orthogonality, including zero and opposite modes. -/
theorem physicalUnitCell_integerCosine_mul_integerCosine_integral
    (k l : IntegerWavevector) :
    (∫ x in physicalUnitCell,
      integerCosine k x * integerCosine l x) =
      ((if k = l then 1 else 0) +
        (if k = -l then 1 else 0)) / 2 := by
  calc
    (∫ x in physicalUnitCell,
        integerCosine k x * integerCosine l x) =
        ∫ x in physicalUnitCell,
          (integerCosine (k + l) x +
            integerCosine (k - l) x) / 2 := by
      apply integral_congr_ae
      filter_upwards with x
      exact integerCosine_mul_integerCosine k l x
    _ = ((∫ x in physicalUnitCell, integerCosine (k + l) x) +
          (∫ x in physicalUnitCell, integerCosine (k - l) x)) / 2 := by
      rw [integral_div]
      rw [integral_add
        (integerCosine_integrableOn_physicalUnitCell (k + l))
        (integerCosine_integrableOn_physicalUnitCell (k - l))]
    _ = ((if k = l then 1 else 0) +
          (if k = -l then 1 else 0)) / 2 := by
      rw [physicalUnitCell_integerCosine_integral,
        physicalUnitCell_integerCosine_integral]
      simp only [sub_eq_zero, add_eq_zero_iff_eq_neg]
      ring

/-- Full sine-character orthogonality, including zero and opposite modes. -/
theorem physicalUnitCell_integerSine_mul_integerSine_integral
    (k l : IntegerWavevector) :
    (∫ x in physicalUnitCell,
      integerSine k x * integerSine l x) =
      ((if k = l then 1 else 0) -
        (if k = -l then 1 else 0)) / 2 := by
  calc
    (∫ x in physicalUnitCell,
        integerSine k x * integerSine l x) =
        ∫ x in physicalUnitCell,
          (integerCosine (k - l) x -
            integerCosine (k + l) x) / 2 := by
      apply integral_congr_ae
      filter_upwards with x
      exact integerSine_mul_integerSine k l x
    _ = ((∫ x in physicalUnitCell, integerCosine (k - l) x) -
          (∫ x in physicalUnitCell, integerCosine (k + l) x)) / 2 := by
      rw [integral_div]
      rw [integral_sub
        (integerCosine_integrableOn_physicalUnitCell (k - l))
        (integerCosine_integrableOn_physicalUnitCell (k + l))]
    _ = ((if k = l then 1 else 0) -
          (if k = -l then 1 else 0)) / 2 := by
      rw [physicalUnitCell_integerCosine_integral,
        physicalUnitCell_integerCosine_integral]
      simp only [sub_eq_zero, add_eq_zero_iff_eq_neg]

/-- Sine and cosine integer characters are orthogonal on the unit cell. -/
theorem physicalUnitCell_integerSine_mul_integerCosine_integral_eq_zero
    (k l : IntegerWavevector) :
    (∫ x in physicalUnitCell,
      integerSine k x * integerCosine l x) = 0 := by
  calc
    (∫ x in physicalUnitCell,
        integerSine k x * integerCosine l x) =
        ∫ x in physicalUnitCell,
          (integerSine (k + l) x +
            integerSine (k - l) x) / 2 := by
      apply integral_congr_ae
      filter_upwards with x
      exact integerSine_mul_integerCosine k l x
    _ = ((∫ x in physicalUnitCell, integerSine (k + l) x) +
          (∫ x in physicalUnitCell, integerSine (k - l) x)) / 2 := by
      rw [integral_div]
      rw [integral_add
        (integerSine_integrableOn_physicalUnitCell (k + l))
        (integerSine_integrableOn_physicalUnitCell (k - l))]
    _ = 0 := by
      rw [physicalUnitCell_integerSine_integral,
        physicalUnitCell_integerSine_integral]
      norm_num

/-- Symmetric cosine-sine orthogonality on the unit cell. -/
theorem physicalUnitCell_integerCosine_mul_integerSine_integral_eq_zero
    (k l : IntegerWavevector) :
    (∫ x in physicalUnitCell,
      integerCosine k x * integerSine l x) = 0 := by
  simpa [mul_comm] using
    physicalUnitCell_integerSine_mul_integerCosine_integral_eq_zero l k

end

end ThreeDimensionalPeriodicIntegerCharacterOrthogonality
end NavierStokes
end SaturationMonoid
