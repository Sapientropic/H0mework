import H0mework.NavierStokes.Galerkin.CriticalEnstrophyBarrier

/-!
# Viscous derivative loss at the finite Galerkin restart gate

The critical enstrophy barrier controls coefficient enstrophy uniformly in
the Galerkin inventory.  A direct Picard restart estimate for the complete
vector field, however, must also estimate its viscous tangent.  On the
actual `lp 2` coefficient carrier that tangent has the exact norm ledger

```text
‖ν Δω‖² = ν² (2π)⁴ ∑ₖ |k|⁴ ‖ωₖ‖².
```

Thus its field norm reads a genuine two-derivative mass, not only the
coefficient enstrophy controlled by the critical barrier.

The final theorem makes this loss cutoff-independent and physical.  It
constructs an explicit family of sharply supported, transverse,
Fourier-real states with coefficient enstrophy exactly `2`, while the
viscous tangent exceeds every proposed multiple of that enstrophy.  No
maximum frequency, mode count, target cutoff, derivative bound, or
trajectory certificate occurs in the theorem mouth.

This rules out the direct strategy of obtaining a cutoff-independent
uniform Picard radius from the critical enstrophy barrier alone.  It does
not obstruct fixed-cutoff continuation from a bounded-solution theorem:
there the finite inventory may supply local ODE constants without becoming
part of the PDE barrier.
-/

namespace SaturationMonoid
namespace NavierStokes
namespace ThreeDimensionalVorticityCoefficientFiniteGalerkinViscousRestartDerivativeLoss

open scoped BigOperators Matrix Topology ENNReal

open Matrix
open Set
open ThreeDimensionalPeriodicCoarseFilterCore
open ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientStretchingPairTable
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open ThreeDimensionalVorticityCoefficientGeneratedShellSerrinGeometry
open ThreeDimensionalVorticityCoefficientFiniteSupportRealityTrajectory
open ThreeDimensionalVorticityCoefficientFiniteGalerkinEnstrophyBalance

noncomputable section

/-! ## Exact whole-carrier viscous norm -/

/-- The positive viscous part of the finite Galerkin tangent.  The complete
generator subtracts this state from its nonlinear tangent. -/
def finiteStateVorticityViscousTangent
    (modes : Finset IntegerWavevector)
    (ν : ℝ)
    (state : ComplexVorticityHilbertState) :
    ComplexVorticityHilbertState :=
  finiteComplexVorticityState modes fun wave =>
    (ν * integerWaveViscousMultiplier wave) • state wave

/-- The exact two-derivative mass read by the viscous tangent on the
`lp 2` carrier.  The inner three-coordinate norm is the carrier's finite
product norm; no comparison constant is hidden in this definition. -/
def finiteStateVorticitySecondDerivativeMass
    (modes : Finset IntegerWavevector)
    (state : ComplexVorticityHilbertState) : ℝ :=
  ∑ wave ∈ modes,
    integerWaveNormSq wave ^ 2 * ‖state wave‖ ^ 2

/-- The viscous tangent has exactly the physical `ν² (2π)⁴ |k|⁴` norm
ledger on the whole coefficient carrier. -/
theorem finiteStateVorticityViscousTangent_norm_sq
    (modes : Finset IntegerWavevector)
    (ν : ℝ)
    (state : ComplexVorticityHilbertState) :
    ‖finiteStateVorticityViscousTangent modes ν state‖ ^ 2 =
      ν ^ 2 * (2 * Real.pi) ^ 4 *
        finiteStateVorticitySecondDerivativeMass modes state := by
  have normIdentity :=
    lp.norm_rpow_eq_tsum
      (p := (2 : ℝ≥0∞)) (by norm_num)
      (finiteStateVorticityViscousTangent modes ν state)
  norm_num at normIdentity
  rw [normIdentity, tsum_eq_sum]
  · unfold finiteStateVorticitySecondDerivativeMass
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro wave waveMem
    simp only [finiteStateVorticityViscousTangent,
      finiteComplexVorticityState_apply, if_pos waveMem,
      norm_smul, Real.norm_eq_abs, integerWaveViscousMultiplier]
    rw [mul_pow, sq_abs]
    ring
  · intro wave waveNotMem
    simp [finiteStateVorticityViscousTangent, waveNotMem]

/-! ## A physical fixed-enstrophy high-frequency family -/

/-- Positive axial frequency used by the parameterized obstruction family. -/
def viscousRestartAxialWave
    (frequency : ℕ) : IntegerWavevector :=
  fun coordinate =>
    if coordinate = 0 then (frequency : ℤ) else 0

/-- The negation-closed two-mode inventory at one axial frequency. -/
def viscousRestartPhysicalModes
    (frequency : ℕ) : Finset IntegerWavevector :=
  {viscousRestartAxialWave frequency,
    waveNeg (viscousRestartAxialWave frequency)}

/-- A real unit coefficient in the second coordinate, transverse to the
axial frequency. -/
def viscousRestartTransverseUnit : ComplexCoordinateVector :=
  fun coordinate =>
    if coordinate = 1 then 1 else 0

/-- The same real transverse coefficient on the positive and negative
axial modes. -/
def viscousRestartPhysicalState
    (frequency : ℕ) : ComplexVorticityHilbertState :=
  finiteComplexVorticityState
    (viscousRestartPhysicalModes frequency)
    fun _ => viscousRestartTransverseUnit

theorem viscousRestartAxialWave_ne_zero
    (frequency : ℕ)
    (frequencyPos : 0 < frequency) :
    viscousRestartAxialWave frequency ≠ 0 := by
  intro equality
  have coordinateEquality := congrFun equality 0
  simp [viscousRestartAxialWave] at coordinateEquality
  omega

theorem viscousRestartAxialWave_neg_ne
    (frequency : ℕ)
    (frequencyPos : 0 < frequency) :
    waveNeg (viscousRestartAxialWave frequency) ≠
      viscousRestartAxialWave frequency := by
  intro equality
  have coordinateEquality := congrFun equality 0
  simp [waveNeg, viscousRestartAxialWave] at coordinateEquality
  omega

theorem zero_not_mem_viscousRestartPhysicalModes
    (frequency : ℕ)
    (frequencyPos : 0 < frequency) :
    0 ∉ viscousRestartPhysicalModes frequency := by
  simp only [viscousRestartPhysicalModes, Finset.mem_insert,
    Finset.mem_singleton, not_or]
  refine
    ⟨(viscousRestartAxialWave_ne_zero
        frequency frequencyPos).symm, ?_⟩
  intro equality
  exact
    viscousRestartAxialWave_ne_zero frequency frequencyPos
      ((waveNeg_eq_zero_iff _).mp equality.symm)

theorem viscousRestartPhysicalModes_neg_closed
    (frequency : ℕ)
    {wave : IntegerWavevector}
    (waveMem : wave ∈ viscousRestartPhysicalModes frequency) :
    waveNeg wave ∈ viscousRestartPhysicalModes frequency := by
  simp only [viscousRestartPhysicalModes, Finset.mem_insert,
    Finset.mem_singleton] at waveMem ⊢
  rcases waveMem with rfl | rfl
  · exact Or.inr rfl
  · exact Or.inl (waveNeg_involutive _)

theorem viscousRestartPhysicalState_supported
    (frequency : ℕ)
    {wave : IntegerWavevector}
    (waveNotMem :
      wave ∉ viscousRestartPhysicalModes frequency) :
    viscousRestartPhysicalState frequency wave = 0 := by
  simp [viscousRestartPhysicalState, waveNotMem]

theorem viscousRestartPhysicalState_transverse
    (frequency : ℕ)
    {wave : IntegerWavevector}
    (waveMem : wave ∈ viscousRestartPhysicalModes frequency) :
    complexWavevector wave ⬝ᵥ
        viscousRestartPhysicalState frequency wave = 0 := by
  rw [viscousRestartPhysicalState,
    finiteComplexVorticityState_apply, if_pos waveMem]
  simp only [viscousRestartPhysicalModes, Finset.mem_insert,
    Finset.mem_singleton] at waveMem
  rcases waveMem with rfl | rfl <;>
    simp [dotProduct, complexWavevector,
      viscousRestartAxialWave, waveNeg,
      viscousRestartTransverseUnit]

theorem viscousRestartPhysicalState_reality
    (frequency : ℕ) :
    FiniteStateFourierReality
      (viscousRestartPhysicalState frequency) := by
  intro wave
  rw [viscousRestartPhysicalState,
    finiteComplexVorticityState_apply,
    finiteComplexVorticityState_apply]
  have memIff :
      waveNeg wave ∈ viscousRestartPhysicalModes frequency ↔
        wave ∈ viscousRestartPhysicalModes frequency := by
    constructor
    · intro negMem
      simpa using
        viscousRestartPhysicalModes_neg_closed frequency negMem
    · exact viscousRestartPhysicalModes_neg_closed frequency
  by_cases waveMem :
      wave ∈ viscousRestartPhysicalModes frequency
  · rw [if_pos waveMem, if_pos (memIff.mpr waveMem)]
    funext coordinate
    simp [vectorConj, viscousRestartTransverseUnit]
  · rw [if_neg waveMem, if_neg (memIff.not.mpr waveMem)]
    simp

private theorem viscousRestartTransverseUnit_norm :
    ‖viscousRestartTransverseUnit‖ = 1 := by
  apply le_antisymm
  · rw [pi_norm_le_iff_of_nonneg (by norm_num)]
    intro coordinate
    fin_cases coordinate <;>
      simp [viscousRestartTransverseUnit]
  · calc
      1 = ‖viscousRestartTransverseUnit 1‖ := by
        simp [viscousRestartTransverseUnit]
      _ ≤ ‖viscousRestartTransverseUnit‖ :=
        norm_le_pi_norm _ _

private theorem viscousRestartPhysicalState_row_norm
    (frequency : ℕ)
    {wave : IntegerWavevector}
    (waveMem :
      wave ∈ viscousRestartPhysicalModes frequency) :
    ‖viscousRestartPhysicalState frequency wave‖ = 1 := by
  rw [viscousRestartPhysicalState,
    finiteComplexVorticityState_apply, if_pos waveMem,
    viscousRestartTransverseUnit_norm]

@[simp] theorem integerWaveNormSq_viscousRestartAxialWave
    (frequency : ℕ) :
    integerWaveNormSq (viscousRestartAxialWave frequency) =
      (frequency : ℝ) ^ 2 := by
  simp [integerWaveNormSq, viscousRestartAxialWave]

private theorem integerWaveNormSq_eq_on_viscousRestartPhysicalModes
    (frequency : ℕ)
    {wave : IntegerWavevector}
    (waveMem :
      wave ∈ viscousRestartPhysicalModes frequency) :
    integerWaveNormSq wave = (frequency : ℝ) ^ 2 := by
  simp only [viscousRestartPhysicalModes, Finset.mem_insert,
    Finset.mem_singleton] at waveMem
  rcases waveMem with rfl | rfl
  · exact integerWaveNormSq_viscousRestartAxialWave frequency
  · rw [integerWaveNormSq_waveNeg,
      integerWaveNormSq_viscousRestartAxialWave]

theorem viscousRestartPhysicalState_secondDerivativeMass
    (frequency : ℕ)
    (frequencyPos : 0 < frequency) :
    finiteStateVorticitySecondDerivativeMass
        (viscousRestartPhysicalModes frequency)
        (viscousRestartPhysicalState frequency) =
      2 * (frequency : ℝ) ^ 4 := by
  unfold finiteStateVorticitySecondDerivativeMass
  calc
    (∑ wave ∈ viscousRestartPhysicalModes frequency,
      integerWaveNormSq wave ^ 2 *
        ‖viscousRestartPhysicalState frequency wave‖ ^ 2) =
        ∑ _wave ∈ viscousRestartPhysicalModes frequency,
          (frequency : ℝ) ^ 4 := by
      apply Finset.sum_congr rfl
      intro wave waveMem
      rw [integerWaveNormSq_eq_on_viscousRestartPhysicalModes
          frequency waveMem,
        viscousRestartPhysicalState_row_norm frequency waveMem]
      ring
    _ = 2 * (frequency : ℝ) ^ 4 := by
      have distinct :
          viscousRestartAxialWave frequency ≠
            waveNeg (viscousRestartAxialWave frequency) :=
        (viscousRestartAxialWave_neg_ne
          frequency frequencyPos).symm
      simp [viscousRestartPhysicalModes, distinct]

theorem viscousRestartPhysicalState_coefficientEnstrophy
    (frequency : ℕ)
    (frequencyPos : 0 < frequency) :
    finiteStateVorticityCoefficientEnstrophy
        (viscousRestartPhysicalModes frequency)
        (viscousRestartPhysicalState frequency) = 2 := by
  unfold finiteStateVorticityCoefficientEnstrophy
  calc
    (∑ wave ∈ viscousRestartPhysicalModes frequency,
      complexCoordinateAmplitudeSq
        (viscousRestartPhysicalState frequency wave)) =
        ∑ _wave ∈ viscousRestartPhysicalModes frequency,
          (1 : ℝ) := by
      apply Finset.sum_congr rfl
      intro wave waveMem
      rw [viscousRestartPhysicalState,
        finiteComplexVorticityState_apply, if_pos waveMem]
      norm_num [complexCoordinateAmplitudeSq,
        viscousRestartTransverseUnit,
        Complex.normSq, Fin.sum_univ_succ]
    _ = 2 := by
      have distinct :
          viscousRestartAxialWave frequency ≠
            waveNeg (viscousRestartAxialWave frequency) :=
        (viscousRestartAxialWave_neg_ne
          frequency frequencyPos).symm
      simp [viscousRestartPhysicalModes, distinct]

/-- Even inside sharply supported, transverse, Fourier-real finite states,
the viscous tangent cannot be bounded by a cutoff-independent multiple of
coefficient enstrophy.  The family and all physical laws are generated
explicitly above; only the proposed multiplier and nonzero viscosity are
inputs. -/
theorem exists_physicalViscousTangent_exceeding_enstrophyMultiplier
    (ν proposedMultiplier : ℝ)
    (νNeZero : ν ≠ 0) :
    ∃ frequency : ℕ,
      0 < frequency ∧
        proposedMultiplier *
            finiteStateVorticityCoefficientEnstrophy
              (viscousRestartPhysicalModes frequency)
              (viscousRestartPhysicalState frequency) <
          ‖finiteStateVorticityViscousTangent
              (viscousRestartPhysicalModes frequency)
              ν
              (viscousRestartPhysicalState frequency)‖ ^ 2 := by
  have scalePos :
      0 < ν ^ 2 * (2 * Real.pi) ^ 4 := by
    positivity
  obtain ⟨frequency, frequencyLarge⟩ :=
    exists_nat_gt
      (max
        ((2 * proposedMultiplier) /
          (ν ^ 2 * (2 * Real.pi) ^ 4))
        1)
  have frequencyPos : 0 < frequency := by
    have frequencyGreaterThanOne :
        (1 : ℝ) < frequency :=
      lt_of_le_of_lt (le_max_right _ _) frequencyLarge
    exact_mod_cast
      (lt_trans (by norm_num : (0 : ℝ) < 1)
        frequencyGreaterThanOne)
  refine ⟨frequency, frequencyPos, ?_⟩
  rw [viscousRestartPhysicalState_coefficientEnstrophy
      frequency frequencyPos,
    finiteStateVorticityViscousTangent_norm_sq,
    viscousRestartPhysicalState_secondDerivativeMass
      frequency frequencyPos]
  have ratioLtFrequency :
      (2 * proposedMultiplier) /
          (ν ^ 2 * (2 * Real.pi) ^ 4) <
        (frequency : ℝ) :=
    lt_of_le_of_lt (le_max_left _ _) frequencyLarge
  have frequencyLeFourth :
      (frequency : ℝ) ≤ 2 * (frequency : ℝ) ^ 4 := by
    have oneLeFrequency : 1 ≤ (frequency : ℝ) := by
      exact_mod_cast frequencyPos
    nlinarith
      [sq_nonneg
        ((frequency : ℝ) ^ 2 - (frequency : ℝ))]
  have ratioLtMass :
      (2 * proposedMultiplier) /
          (ν ^ 2 * (2 * Real.pi) ^ 4) <
        2 * (frequency : ℝ) ^ 4 :=
    ratioLtFrequency.trans_le frequencyLeFourth
  have scaled :=
    (div_lt_iff₀ scalePos).mp ratioLtMass
  nlinarith

end

end ThreeDimensionalVorticityCoefficientFiniteGalerkinViscousRestartDerivativeLoss
end NavierStokes
end SaturationMonoid
