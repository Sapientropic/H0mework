import H0mework.NavierStokes.Galerkin.CriticalEnstrophyRate
import H0mework.NavierStokes.Fourier.IntegerLatticeCriticalKernelExplicitTail

/-!
# Source-owned local kernel absorption above the global critical ball

The global small-data compiler absorbs the complete `Z^3` critical kernel at
once.  A supercritical source contact instead needs a local whole-flow
lifespan.  The first cutoff-independent step is to let the actual viscosity
and current coefficient-enstrophy ceiling choose a finite lattice core.

Outside that internally generated core the summable reciprocal-fourth-power
kernel is small enough for viscosity to absorb the high-frequency velocity
majorant.  The caller supplies no frequency cutoff or tail certificate.
-/

namespace SaturationMonoid
namespace NavierStokes
namespace
    ThreeDimensionalVorticityCoefficientSourceOwnedLocalKernelAbsorption

open scoped BigOperators

open Set
open ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalIntegerLatticeCriticalKernel
open ThreeDimensionalIntegerLatticeCriticalKernelExplicitTail
open ThreeDimensionalVorticityCoefficientInfiniteFixedOutputNonlinearRow
open ThreeDimensionalVorticityCoefficientGeneratedShellSerrinGeometry
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open ThreeDimensionalVorticityCoefficientFiniteSupportCriticalSobolev
open ThreeDimensionalVorticityCoefficientFiniteSupportRealityTrajectory
open ThreeDimensionalVorticityCoefficientFiniteGalerkinEnstrophyBalance
open ThreeDimensionalVorticityCoefficientFiniteGalerkinCriticalEnstrophyRate

noncomputable section

/-- Positive tail tolerance selected from the actual viscosity and an
enstrophy ceiling.  `max 0 ceiling + 1` keeps the producer total. -/
def sourceOwnedKernelTailTolerance
    (ν : Viscosity)
    (ceiling : ℝ) : ℝ :=
  ν.coeff ^ 2 * (2 * Real.pi) ^ 2 /
    (8 * biotSavartSerrinConstant * (max 0 ceiling + 1))

theorem sourceOwnedKernelTailTolerance_pos
    (ν : Viscosity)
    (ceiling : ℝ) :
    0 < sourceOwnedKernelTailTolerance ν ceiling := by
  unfold sourceOwnedKernelTailTolerance
  have coeffSqPos : 0 < ν.coeff ^ 2 := sq_pos_of_pos ν.coeff_pos
  have frequencySqPos : 0 < (2 * Real.pi) ^ 2 := by positivity
  have ceilingPos : 0 < max 0 ceiling + 1 := by
    linarith [le_max_left 0 ceiling]
  exact div_pos (mul_pos coeffSqPos frequencySqPos)
    (mul_pos
      (mul_pos (by norm_num) biotSavartSerrinConstant_pos)
      ceilingPos)

/-- Canonical cube radius whose explicit reciprocal tail is strictly below
the source-selected tolerance. -/
noncomputable def sourceOwnedLocalKernelRadius
    (ν : Viscosity)
    (ceiling : ℝ) : ℕ :=
  Nat.ceil (26 / sourceOwnedKernelTailTolerance ν ceiling) + 1

/-- Linear scale hidden inside the exact canonical radius formula. -/
def sourceOwnedLocalKernelRadiusSlope (ν : Viscosity) : ℝ :=
  (208 * biotSavartSerrinConstant) /
    (ν.coeff ^ 2 * (2 * Real.pi) ^ 2)

theorem sourceOwnedLocalKernelRadiusSlope_pos (ν : Viscosity) :
    0 < sourceOwnedLocalKernelRadiusSlope ν := by
  unfold sourceOwnedLocalKernelRadiusSlope
  exact div_pos
    (mul_pos (by norm_num) biotSavartSerrinConstant_pos)
    (mul_pos (sq_pos_of_pos ν.coeff_pos) (by positivity))

theorem twentySix_div_sourceOwnedKernelTailTolerance
    (ν : Viscosity)
    (ceiling : ℝ) :
    26 / sourceOwnedKernelTailTolerance ν ceiling =
      sourceOwnedLocalKernelRadiusSlope ν * (max 0 ceiling + 1) := by
  unfold sourceOwnedKernelTailTolerance sourceOwnedLocalKernelRadiusSlope
  have coeffNe : ν.coeff ≠ 0 := ν.coeff_pos.ne'
  have piNe : Real.pi ≠ 0 := Real.pi_ne_zero
  have constantNe : biotSavartSerrinConstant ≠ 0 :=
    biotSavartSerrinConstant_pos.ne'
  have ceilingPos : 0 < max 0 ceiling + 1 := by
    linarith [le_max_left 0 ceiling]
  field_simp
  ring

/-- The canonical cube radius grows at least linearly with the actual
coefficient ceiling. -/
theorem sourceOwnedLocalKernelRadiusSlope_mul_le
    (ν : Viscosity)
    (ceiling : ℝ) :
    sourceOwnedLocalKernelRadiusSlope ν * (max 0 ceiling + 1) ≤
      (sourceOwnedLocalKernelRadius ν ceiling : ℝ) := by
  rw [← twentySix_div_sourceOwnedKernelTailTolerance]
  unfold sourceOwnedLocalKernelRadius
  have ceilLe :
      26 / sourceOwnedKernelTailTolerance ν ceiling ≤
        (Nat.ceil
          (26 / sourceOwnedKernelTailTolerance ν ceiling) : ℝ) :=
    Nat.le_ceil _
  norm_num [Nat.cast_add]
  linarith

theorem sourceOwnedLocalKernelRadius_lt_linear
    (ν : Viscosity)
    (ceiling : ℝ)
    (ceilingNonneg : 0 ≤ ceiling) :
    (sourceOwnedLocalKernelRadius ν ceiling : ℝ) <
      (sourceOwnedLocalKernelRadiusSlope ν + 2) * (ceiling + 1) := by
  let ratio := 26 / sourceOwnedKernelTailTolerance ν ceiling
  have ratioPos : 0 < ratio := by
    exact div_pos (by norm_num) (sourceOwnedKernelTailTolerance_pos ν ceiling)
  have ceilLt : (Nat.ceil ratio : ℝ) < ratio + 1 :=
    Nat.ceil_lt_add_one ratioPos.le
  have ratioEq : ratio =
      sourceOwnedLocalKernelRadiusSlope ν * (ceiling + 1) := by
    dsimp only [ratio]
    rw [twentySix_div_sourceOwnedKernelTailTolerance,
      max_eq_right ceilingNonneg]
  unfold sourceOwnedLocalKernelRadius
  have ceilingOne : 1 ≤ ceiling + 1 := by linarith
  change ((Nat.ceil ratio + 1 : ℕ) : ℝ) < _
  calc
    ((Nat.ceil ratio + 1 : ℕ) : ℝ) < ratio + 2 := by
      norm_num [Nat.cast_add]
      linarith
    _ = sourceOwnedLocalKernelRadiusSlope ν * (ceiling + 1) + 2 := by
      rw [ratioEq]
    _ ≤ (sourceOwnedLocalKernelRadiusSlope ν + 2) *
          (ceiling + 1) := by
      nlinarith [sourceOwnedLocalKernelRadiusSlope_pos ν]

theorem sourceOwnedLocalKernelRadius_pos
    (ν : Viscosity)
    (ceiling : ℝ) :
    0 < sourceOwnedLocalKernelRadius ν ceiling := by
  unfold sourceOwnedLocalKernelRadius
  omega

theorem sourceOwnedLocalKernelRadius_two_le
    (ν : Viscosity)
    (ceiling : ℝ) :
    2 ≤ sourceOwnedLocalKernelRadius ν ceiling := by
  unfold sourceOwnedLocalKernelRadius
  have ratioPos :
      0 < 26 / sourceOwnedKernelTailTolerance ν ceiling :=
    div_pos (by norm_num) (sourceOwnedKernelTailTolerance_pos ν ceiling)
  have ceilPos :
      0 < Nat.ceil (26 / sourceOwnedKernelTailTolerance ν ceiling) :=
    Nat.ceil_pos.mpr ratioPos
  omega

/-- The finite core is now the exact canonical integer-frequency cube at the
generated radius.  Its size and frequency mass can therefore be bounded from
the source data. -/
noncomputable def sourceOwnedLocalKernelCore
    (ν : Viscosity)
    (ceiling : ℝ) : Finset IntegerWavevector :=
  integerWaveFrequencyCube (sourceOwnedLocalKernelRadius ν ceiling)

attribute [irreducible] sourceOwnedLocalKernelCore

theorem sourceOwnedLocalKernelCore_eq_frequencyCube
    (ν : Viscosity)
    (ceiling : ℝ) :
    sourceOwnedLocalKernelCore ν ceiling =
      integerWaveFrequencyCube
        (sourceOwnedLocalKernelRadius ν ceiling) := by
  unfold sourceOwnedLocalKernelCore
  rfl

/-- Every finite inventory disjoint from the generated core has kernel mass
strictly below the source-selected tolerance. -/
theorem sourceOwnedLocalKernelCore_tail_lt
    (ν : Viscosity)
    (ceiling : ℝ)
    (waves : Finset IntegerWavevector)
    (disjoint :
      Disjoint waves (sourceOwnedLocalKernelCore ν ceiling)) :
    ∑ wave ∈ waves, integerWaveCriticalKernel wave <
      sourceOwnedKernelTailTolerance ν ceiling := by
  let tolerance := sourceOwnedKernelTailTolerance ν ceiling
  let radius := sourceOwnedLocalKernelRadius ν ceiling
  have tolerancePos : 0 < tolerance := by
    exact sourceOwnedKernelTailTolerance_pos ν ceiling
  have radiusPos : 0 < radius := by
    exact sourceOwnedLocalKernelRadius_pos ν ceiling
  have ratioLeCeil :
      26 / tolerance ≤ (Nat.ceil (26 / tolerance) : ℝ) :=
    Nat.le_ceil (26 / tolerance)
  have ratioLtRadius : 26 / tolerance < (radius : ℝ) := by
    dsimp only [radius, sourceOwnedLocalKernelRadius]
    push_cast
    linarith
  have modelLt : 26 * (radius : ℝ)⁻¹ < tolerance := by
    rw [← div_eq_mul_inv]
    apply (div_lt_iff₀ (by exact_mod_cast radiusPos)).2
    have scaled := (div_lt_iff₀ tolerancePos).mp ratioLtRadius
    nlinarith
  have outsideLe :
      ∑ wave ∈ waves \
          integerWaveFrequencyCube radius,
        integerWaveCriticalKernel wave ≤
          26 * (radius : ℝ)⁻¹ :=
    finiteModes_integerWaveCriticalKernel_tail_le radius radiusPos waves
  have sdiffEq :
      waves \ integerWaveFrequencyCube radius = waves := by
    ext wave
    simp only [Finset.mem_sdiff]
    constructor
    · exact fun waveMem => waveMem.1
    · intro waveMem
      exact ⟨waveMem,
        fun coreMem =>
          (Finset.disjoint_left.mp disjoint) waveMem (by
            simpa only [sourceOwnedLocalKernelCore, radius] using coreMem)⟩
  rw [sdiffEq] at outsideLe
  exact outsideLe.trans_lt modelLt

/-! ## Exact low/high split forced by the generated core -/

def sourceOwnedLocalLowModes
    (ν : Viscosity)
    (ceiling : ℝ)
    (modes : Finset IntegerWavevector) :
    Finset IntegerWavevector :=
  modes ∩ sourceOwnedLocalKernelCore ν ceiling

def sourceOwnedLocalHighModes
    (ν : Viscosity)
    (ceiling : ℝ)
    (modes : Finset IntegerWavevector) :
    Finset IntegerWavevector :=
  modes \ sourceOwnedLocalKernelCore ν ceiling

theorem sourceOwnedLocalVelocityMajorant_split
    (ν : Viscosity)
    (ceiling : ℝ)
    (modes : Finset IntegerWavevector)
    (state : ComplexVorticityHilbertState) :
    finiteStateVelocityMajorant
          (sourceOwnedLocalLowModes ν ceiling modes) state +
        finiteStateVelocityMajorant
          (sourceOwnedLocalHighModes ν ceiling modes) state =
      finiteStateVelocityMajorant modes state := by
  unfold sourceOwnedLocalLowModes sourceOwnedLocalHighModes
    finiteStateVelocityMajorant finiteVelocityFourierMajorant
  exact Finset.sum_inter_add_sum_sdiff
    modes (sourceOwnedLocalKernelCore ν ceiling) _

theorem finiteStateVorticityEnstrophyMass_mono
    {smaller larger : Finset IntegerWavevector}
    (subset : smaller ⊆ larger)
    (state : ComplexVorticityHilbertState) :
    finiteStateVorticityEnstrophyMass smaller state ≤
      finiteStateVorticityEnstrophyMass larger state := by
  unfold finiteStateVorticityEnstrophyMass
  exact Finset.sum_le_sum_of_subset_of_nonneg subset
    (fun wave waveMem waveNotMem =>
      mul_nonneg (integerWaveNormSq_nonneg wave)
        (complexCoordinateAmplitudeSq_nonneg (state wave)))

theorem finiteStateVorticityCoefficientEnstrophy_mono
    {smaller larger : Finset IntegerWavevector}
    (subset : smaller ⊆ larger)
    (state : ComplexVorticityHilbertState) :
    finiteStateVorticityCoefficientEnstrophy smaller state ≤
      finiteStateVorticityCoefficientEnstrophy larger state := by
  unfold finiteStateVorticityCoefficientEnstrophy
  exact Finset.sum_le_sum_of_subset_of_nonneg subset
    (fun wave waveMem waveNotMem =>
      complexCoordinateAmplitudeSq_nonneg (state wave))

/-- The generated finite core carries its own squared-frequency mass. -/
def sourceOwnedLocalCoreFrequencyMass
    (ν : Viscosity)
    (ceiling : ℝ) : ℝ :=
  ∑ wave ∈ sourceOwnedLocalKernelCore ν ceiling,
    integerWaveNormSq wave

theorem sourceOwnedLocalCoreFrequencyMass_nonneg
    (ν : Viscosity)
    (ceiling : ℝ) :
    0 ≤ sourceOwnedLocalCoreFrequencyMass ν ceiling := by
  unfold sourceOwnedLocalCoreFrequencyMass
  exact Finset.sum_nonneg fun wave waveMem =>
    integerWaveNormSq_nonneg wave

/-- Explicit frequency-mass majorant of the canonical cube core. -/
noncomputable def sourceOwnedLocalCoreFrequencyMassUpper
    (ν : Viscosity)
    (ceiling : ℝ) : ℝ :=
  let radius := sourceOwnedLocalKernelRadius ν ceiling
  (((2 * radius + 1) ^ 3 : Nat) : ℝ) *
    (3 * (radius : ℝ) ^ 2)

theorem sourceOwnedLocalCoreFrequencyMass_le_upper
    (ν : Viscosity)
    (ceiling : ℝ) :
    sourceOwnedLocalCoreFrequencyMass ν ceiling ≤
      sourceOwnedLocalCoreFrequencyMassUpper ν ceiling := by
  let radius := sourceOwnedLocalKernelRadius ν ceiling
  let core := integerWaveFrequencyCube radius
  have pointwise : ∀ wave ∈ core,
      integerWaveNormSq wave ≤ 3 * (radius : ℝ) ^ 2 := by
    intro wave waveMem
    exact integerWaveNormSq_le_three_mul_radius_sq_of_mem
      radius wave waveMem
  have sumBound := Finset.sum_le_card_nsmul core
    integerWaveNormSq (3 * (radius : ℝ) ^ 2) pointwise
  unfold sourceOwnedLocalCoreFrequencyMass
    sourceOwnedLocalCoreFrequencyMassUpper sourceOwnedLocalKernelCore
  change
    (∑ wave ∈ core, integerWaveNormSq wave) ≤
      (((2 * radius + 1) ^ 3 : Nat) : ℝ) *
        (3 * (radius : ℝ) ^ 2)
  calc
    (∑ wave ∈ core, integerWaveNormSq wave) ≤
        core.card • (3 * (radius : ℝ) ^ 2) := sumBound
    _ = (core.card : ℝ) * (3 * (radius : ℝ) ^ 2) := by
      rw [nsmul_eq_mul]
    _ = (((2 * radius + 1) ^ 3 : Nat) : ℝ) *
          (3 * (radius : ℝ) ^ 2) := by
      rw [show core.card = (2 * radius + 1) ^ 3 by
        exact integerWaveFrequencyCube_card radius]

/-- The explicit canonical frequency-mass upper bound has the same fifth
order as the exact lower block. -/
theorem sourceOwnedLocalCoreFrequencyMassUpper_le_fifth
    (ν : Viscosity)
    (ceiling : ℝ)
    (ceilingNonneg : 0 ≤ ceiling) :
    sourceOwnedLocalCoreFrequencyMassUpper ν ceiling ≤
      81 * (sourceOwnedLocalKernelRadiusSlope ν + 2) ^ 5 *
        (ceiling + 1) ^ 5 := by
  let radius := sourceOwnedLocalKernelRadius ν ceiling
  let radiusBound :=
    (sourceOwnedLocalKernelRadiusSlope ν + 2) * (ceiling + 1)
  have radiusPos : 0 < radius := sourceOwnedLocalKernelRadius_pos ν ceiling
  have radiusOne : (1 : ℝ) ≤ (radius : ℝ) := by
    exact_mod_cast radiusPos
  have radiusLeBound : (radius : ℝ) ≤ radiusBound :=
    (sourceOwnedLocalKernelRadius_lt_linear ν ceiling ceilingNonneg).le
  have boundNonneg : 0 ≤ radiusBound := by
    dsimp only [radiusBound]
    have slopeNonneg := (sourceOwnedLocalKernelRadiusSlope_pos ν).le
    exact mul_nonneg (by linarith) (by linarith)
  have radiusFifthLe : (radius : ℝ) ^ 5 ≤ radiusBound ^ 5 :=
    pow_le_pow_left₀ (by positivity) radiusLeBound 5
  have threeRadius : (2 * radius + 1 : ℕ) ≤ 3 * radius := by
    omega
  have cubeCastLe : (((2 * radius + 1) ^ 3 : ℕ) : ℝ) ≤
      (3 * (radius : ℝ)) ^ 3 := by
    have castLe : ((2 * radius + 1 : ℕ) : ℝ) ≤
        ((3 * radius : ℕ) : ℝ) := by exact_mod_cast threeRadius
    simpa only [Nat.cast_pow, Nat.cast_mul, Nat.cast_ofNat] using
      (pow_le_pow_left₀ (by positivity) castLe 3)
  unfold sourceOwnedLocalCoreFrequencyMassUpper
  dsimp only [radius]
  calc
    (((2 * radius + 1) ^ 3 : ℕ) : ℝ) *
          (3 * (radius : ℝ) ^ 2) ≤
        (3 * (radius : ℝ)) ^ 3 *
          (3 * (radius : ℝ) ^ 2) :=
      mul_le_mul_of_nonneg_right cubeCastLe (by positivity)
    _ = 81 * (radius : ℝ) ^ 5 := by ring
    _ ≤ 81 * radiusBound ^ 5 := by nlinarith
    _ = 81 * (sourceOwnedLocalKernelRadiusSlope ν + 2) ^ 5 *
          (ceiling + 1) ^ 5 := by
      dsimp only [radiusBound]
      ring

/-- Matching fifth-order lower bound for the exact canonical core frequency
mass. -/
theorem sourceOwnedLocalCoreFrequencyMass_ge_halfBlock
    (ν : Viscosity)
    (ceiling : ℝ) :
    3 * ((sourceOwnedLocalKernelRadius ν ceiling / 2 : ℕ) : ℝ) ^ 2 *
          ((((sourceOwnedLocalKernelRadius ν ceiling / 2 + 1) ^ 3 : ℕ)) : ℝ) ≤
      sourceOwnedLocalCoreFrequencyMass ν ceiling := by
  unfold sourceOwnedLocalCoreFrequencyMass
  rw [sourceOwnedLocalKernelCore_eq_frequencyCube]
  exact integerWaveFrequencyCube_frequencyMass_ge_halfBlock
    (sourceOwnedLocalKernelRadius ν ceiling)

/-- Polynomial lower form extracted from the half block. -/
theorem sourceOwnedLocalKernelRadius_fifth_le_frequencyMass
    (ν : Viscosity)
    (ceiling : ℝ) :
    (sourceOwnedLocalKernelRadius ν ceiling : ℝ) ^ 5 / 81 ≤
      sourceOwnedLocalCoreFrequencyMass ν ceiling := by
  let radius := sourceOwnedLocalKernelRadius ν ceiling
  let half := radius / 2
  have radiusTwo : 2 ≤ radius :=
    sourceOwnedLocalKernelRadius_two_le ν ceiling
  have radiusLeThreeHalf : radius ≤ 3 * half := by
    dsimp only [half]
    omega
  have radiusThirdLeHalf : (radius : ℝ) / 3 ≤ (half : ℝ) := by
    have castBound : (radius : ℝ) ≤ 3 * (half : ℝ) := by
      exact_mod_cast radiusLeThreeHalf
    nlinarith
  have fifthLe : ((radius : ℝ) / 3) ^ 5 ≤ (half : ℝ) ^ 5 := by
    exact pow_le_pow_left₀ (by positivity) radiusThirdLeHalf 5
  have halfNonneg : 0 ≤ (half : ℝ) := by positivity
  have halfCubeLe : (half : ℝ) ^ 3 ≤ ((half + 1 : ℕ) : ℝ) ^ 3 := by
    have halfLe : (half : ℝ) ≤ ((half + 1 : ℕ) : ℝ) := by
      norm_num
    exact pow_le_pow_left₀ halfNonneg halfLe 3
  have blockLower := sourceOwnedLocalCoreFrequencyMass_ge_halfBlock ν ceiling
  change
    (radius : ℝ) ^ 5 / 81 ≤ sourceOwnedLocalCoreFrequencyMass ν ceiling
  calc
    (radius : ℝ) ^ 5 / 81 = 3 * ((radius : ℝ) / 3) ^ 5 := by ring
    _ ≤ 3 * (half : ℝ) ^ 5 := by nlinarith
    _ = 3 * (half : ℝ) ^ 2 * (half : ℝ) ^ 3 := by ring
    _ ≤ 3 * (half : ℝ) ^ 2 * (((half + 1 : ℕ) : ℝ) ^ 3) := by
      exact mul_le_mul_of_nonneg_left halfCubeLe
        (mul_nonneg (by norm_num) (sq_nonneg _))
    _ ≤ sourceOwnedLocalCoreFrequencyMass ν ceiling := by
      simpa only [radius, half, Nat.cast_pow] using blockLower

/-- The low-frequency gradient mass is bounded by the generated finite-core
frequency mass times ordinary coefficient enstrophy. -/
theorem sourceOwnedLocalLow_enstrophyMass_le
    (ν : Viscosity)
    (ceiling : ℝ)
    (modes : Finset IntegerWavevector)
    (state : ComplexVorticityHilbertState) :
    finiteStateVorticityEnstrophyMass
        (sourceOwnedLocalLowModes ν ceiling modes) state ≤
      sourceOwnedLocalCoreFrequencyMass ν ceiling *
        finiteStateVorticityCoefficientEnstrophy modes state := by
  have lowSubsetModes :
      sourceOwnedLocalLowModes ν ceiling modes ⊆ modes := by
    exact Finset.inter_subset_left
  have lowSubsetCore :
      sourceOwnedLocalLowModes ν ceiling modes ⊆
        sourceOwnedLocalKernelCore ν ceiling := by
    exact Finset.inter_subset_right
  have pointwise :
      ∀ wave ∈ sourceOwnedLocalLowModes ν ceiling modes,
        integerWaveNormSq wave *
            complexCoordinateAmplitudeSq (state wave) ≤
          sourceOwnedLocalCoreFrequencyMass ν ceiling *
            complexCoordinateAmplitudeSq (state wave) := by
    intro wave waveMem
    have waveMemCore :
        wave ∈ sourceOwnedLocalKernelCore ν ceiling :=
      lowSubsetCore waveMem
    have waveNormLe :
        integerWaveNormSq wave ≤
          sourceOwnedLocalCoreFrequencyMass ν ceiling := by
      unfold sourceOwnedLocalCoreFrequencyMass
      exact Finset.single_le_sum
        (fun later laterMem => integerWaveNormSq_nonneg later)
        waveMemCore
    exact mul_le_mul_of_nonneg_right waveNormLe
      (complexCoordinateAmplitudeSq_nonneg (state wave))
  unfold finiteStateVorticityEnstrophyMass
    finiteStateVorticityCoefficientEnstrophy
  calc
    (∑ wave ∈ sourceOwnedLocalLowModes ν ceiling modes,
        integerWaveNormSq wave *
          complexCoordinateAmplitudeSq (state wave)) ≤
        ∑ wave ∈ sourceOwnedLocalLowModes ν ceiling modes,
          sourceOwnedLocalCoreFrequencyMass ν ceiling *
            complexCoordinateAmplitudeSq (state wave) := by
      exact Finset.sum_le_sum pointwise
    _ = sourceOwnedLocalCoreFrequencyMass ν ceiling *
          (∑ wave ∈ sourceOwnedLocalLowModes ν ceiling modes,
            complexCoordinateAmplitudeSq (state wave)) := by
      rw [Finset.mul_sum]
    _ ≤ sourceOwnedLocalCoreFrequencyMass ν ceiling *
          (∑ wave ∈ modes,
            complexCoordinateAmplitudeSq (state wave)) := by
      exact mul_le_mul_of_nonneg_left
        (Finset.sum_le_sum_of_subset_of_nonneg lowSubsetModes
          (fun wave waveMem waveNotMem =>
            complexCoordinateAmplitudeSq_nonneg (state wave)))
        (sourceOwnedLocalCoreFrequencyMass_nonneg ν ceiling)

/-- Finite coefficient multiplying the low-frequency quadratic enstrophy
term.  Every factor is selected from the actual viscosity/ceiling core. -/
def sourceOwnedLocalCoreVelocityCoefficient
    (ν : Viscosity)
    (ceiling : ℝ) : ℝ :=
  biotSavartSerrinConstant *
    (∑ wave ∈ sourceOwnedLocalKernelCore ν ceiling,
      integerWaveCriticalKernel wave) *
    sourceOwnedLocalCoreFrequencyMass ν ceiling

theorem sourceOwnedLocalCoreVelocityCoefficient_nonneg
    (ν : Viscosity)
    (ceiling : ℝ) :
    0 ≤ sourceOwnedLocalCoreVelocityCoefficient ν ceiling := by
  unfold sourceOwnedLocalCoreVelocityCoefficient
  exact mul_nonneg
    (mul_nonneg biotSavartSerrinConstant_nonneg
      (Finset.sum_nonneg fun wave waveMem =>
        integerWaveCriticalKernel_nonneg wave))
    (sourceOwnedLocalCoreFrequencyMass_nonneg ν ceiling)

private def sourceOwnedLocalCoreReferenceWave : IntegerWavevector :=
  ![1, 0, 0]

private theorem sourceOwnedLocalCoreReferenceWave_mem
    (ν : Viscosity)
    (ceiling : ℝ) :
    sourceOwnedLocalCoreReferenceWave ∈
      sourceOwnedLocalKernelCore ν ceiling := by
  rw [sourceOwnedLocalKernelCore_eq_frequencyCube,
    integerWaveFrequencyCube, Fintype.mem_piFinset]
  have radiusTwo : 2 ≤ sourceOwnedLocalKernelRadius ν ceiling :=
    sourceOwnedLocalKernelRadius_two_le ν ceiling
  intro coordinate
  fin_cases coordinate <;>
    simp [sourceOwnedLocalCoreReferenceWave, Finset.mem_Icc] <;> omega

private theorem sourceOwnedLocalCoreReferenceWave_kernel_eq_one :
    integerWaveCriticalKernel sourceOwnedLocalCoreReferenceWave = 1 := by
  unfold integerWaveCriticalKernel integerWaveNormSq
  norm_num [sourceOwnedLocalCoreReferenceWave, Fin.sum_univ_succ]

/-- The reference wave fixes a unit kernel factor, so the complete core
velocity coefficient retains the full fifth-order frequency mass. -/
theorem sourceOwnedLocalCoreVelocityCoefficient_ge_frequencyMass
    (ν : Viscosity)
    (ceiling : ℝ) :
    biotSavartSerrinConstant *
        sourceOwnedLocalCoreFrequencyMass ν ceiling ≤
      sourceOwnedLocalCoreVelocityCoefficient ν ceiling := by
  have kernelOneLe :
      (1 : ℝ) ≤
        ∑ wave ∈ sourceOwnedLocalKernelCore ν ceiling,
          integerWaveCriticalKernel wave := by
    calc
      (1 : ℝ) = integerWaveCriticalKernel
          sourceOwnedLocalCoreReferenceWave :=
        sourceOwnedLocalCoreReferenceWave_kernel_eq_one.symm
      _ ≤ ∑ wave ∈ sourceOwnedLocalKernelCore ν ceiling,
          integerWaveCriticalKernel wave := by
        exact Finset.single_le_sum
          (fun wave _waveMem => integerWaveCriticalKernel_nonneg wave)
          (sourceOwnedLocalCoreReferenceWave_mem ν ceiling)
  unfold sourceOwnedLocalCoreVelocityCoefficient
  have frequencyNonneg := sourceOwnedLocalCoreFrequencyMass_nonneg ν ceiling
  have scaledKernel := mul_le_mul_of_nonneg_left kernelOneLe
    biotSavartSerrinConstant_nonneg
  have paid := mul_le_mul_of_nonneg_right scaledKernel frequencyNonneg
  simpa only [one_mul, mul_assoc] using paid

/-- Explicit source-data majorant for the canonical core velocity
coefficient. -/
noncomputable def sourceOwnedLocalCoreVelocityCoefficientUpper
    (ν : Viscosity)
    (ceiling : ℝ) : ℝ :=
  biotSavartSerrinConstant *
    (∑' wave : IntegerWavevector, integerWaveCriticalKernel wave) *
    sourceOwnedLocalCoreFrequencyMassUpper ν ceiling

theorem sourceOwnedLocalCoreVelocityCoefficient_le_upper
    (ν : Viscosity)
    (ceiling : ℝ) :
    sourceOwnedLocalCoreVelocityCoefficient ν ceiling ≤
      sourceOwnedLocalCoreVelocityCoefficientUpper ν ceiling := by
  have kernelLe := finite_sum_integerWaveCriticalKernel_le_tsum
    (sourceOwnedLocalKernelCore ν ceiling)
  have frequencyLe :=
    sourceOwnedLocalCoreFrequencyMass_le_upper ν ceiling
  have kernelNonneg :
      0 ≤ ∑ wave ∈ sourceOwnedLocalKernelCore ν ceiling,
        integerWaveCriticalKernel wave :=
    Finset.sum_nonneg fun wave _waveMem =>
      integerWaveCriticalKernel_nonneg wave
  have totalKernelNonneg :
      0 ≤ ∑' wave : IntegerWavevector,
        integerWaveCriticalKernel wave :=
    tsum_nonneg fun wave => integerWaveCriticalKernel_nonneg wave
  have frequencyNonneg :=
    sourceOwnedLocalCoreFrequencyMass_nonneg ν ceiling
  unfold sourceOwnedLocalCoreVelocityCoefficient
    sourceOwnedLocalCoreVelocityCoefficientUpper
  exact mul_le_mul
    (mul_le_mul_of_nonneg_left kernelLe biotSavartSerrinConstant_nonneg)
    frequencyLe frequencyNonneg
    (mul_nonneg biotSavartSerrinConstant_nonneg totalKernelNonneg)

/-- The generated finite core contributes a quadratic coefficient-enstrophy
term, with a coefficient independent of the ambient Galerkin inventory. -/
theorem sourceOwnedLocalLow_velocityMajorant_sq_le
    (ν : Viscosity)
    (ceiling : ℝ)
    (modes : Finset IntegerWavevector)
    (state : ComplexVorticityHilbertState) :
    finiteStateVelocityMajorant
        (sourceOwnedLocalLowModes ν ceiling modes) state ^ 2 ≤
      sourceOwnedLocalCoreVelocityCoefficient ν ceiling *
        finiteStateVorticityCoefficientEnstrophy modes state := by
  have kernelSubset :
      sourceOwnedLocalLowModes ν ceiling modes ⊆
        sourceOwnedLocalKernelCore ν ceiling :=
    Finset.inter_subset_right
  have kernelLe :
      (∑ wave ∈ sourceOwnedLocalLowModes ν ceiling modes,
          integerWaveCriticalKernel wave) ≤
        ∑ wave ∈ sourceOwnedLocalKernelCore ν ceiling,
          integerWaveCriticalKernel wave :=
    Finset.sum_le_sum_of_subset_of_nonneg kernelSubset
      (fun wave waveMem waveNotMem =>
        integerWaveCriticalKernel_nonneg wave)
  have lowMassNonneg :
      0 ≤ finiteStateVorticityEnstrophyMass
        (sourceOwnedLocalLowModes ν ceiling modes) state :=
    finiteStateVorticityEnstrophyMass_nonneg _ _
  have coreKernelNonneg :
      0 ≤ ∑ wave ∈ sourceOwnedLocalKernelCore ν ceiling,
        integerWaveCriticalKernel wave :=
    Finset.sum_nonneg fun wave waveMem =>
      integerWaveCriticalKernel_nonneg wave
  calc
    finiteStateVelocityMajorant
          (sourceOwnedLocalLowModes ν ceiling modes) state ^ 2 ≤
        biotSavartSerrinConstant *
          (∑ wave ∈ sourceOwnedLocalLowModes ν ceiling modes,
            integerWaveCriticalKernel wave) *
          finiteStateVorticityEnstrophyMass
            (sourceOwnedLocalLowModes ν ceiling modes) state :=
      finiteStateVelocityMajorant_sq_le_criticalFiniteSum _ _
    _ ≤ biotSavartSerrinConstant *
          (∑ wave ∈ sourceOwnedLocalKernelCore ν ceiling,
            integerWaveCriticalKernel wave) *
          finiteStateVorticityEnstrophyMass
            (sourceOwnedLocalLowModes ν ceiling modes) state := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left kernelLe
          biotSavartSerrinConstant_nonneg)
        lowMassNonneg
    _ ≤ biotSavartSerrinConstant *
          (∑ wave ∈ sourceOwnedLocalKernelCore ν ceiling,
            integerWaveCriticalKernel wave) *
          (sourceOwnedLocalCoreFrequencyMass ν ceiling *
            finiteStateVorticityCoefficientEnstrophy modes state) := by
      exact mul_le_mul_of_nonneg_left
        (sourceOwnedLocalLow_enstrophyMass_le
          ν ceiling modes state)
        (mul_nonneg biotSavartSerrinConstant_nonneg coreKernelNonneg)
    _ = sourceOwnedLocalCoreVelocityCoefficient ν ceiling *
          finiteStateVorticityCoefficientEnstrophy modes state := by
      unfold sourceOwnedLocalCoreVelocityCoefficient
      ring

/-- The complementary majorant is small in the vorticity-gradient mass.
The tail set and its smallness certificate are both generated internally. -/
theorem sourceOwnedLocalHigh_velocityMajorant_sq_le
    (ν : Viscosity)
    (ceiling : ℝ)
    (modes : Finset IntegerWavevector)
    (state : ComplexVorticityHilbertState) :
    finiteStateVelocityMajorant
        (sourceOwnedLocalHighModes ν ceiling modes) state ^ 2 ≤
      biotSavartSerrinConstant *
        sourceOwnedKernelTailTolerance ν ceiling *
        finiteStateVorticityEnstrophyMass modes state := by
  have disjoint :
      Disjoint
        (sourceOwnedLocalHighModes ν ceiling modes)
        (sourceOwnedLocalKernelCore ν ceiling) := by
    exact Finset.sdiff_disjoint
  have tailLe :
      (∑ wave ∈ sourceOwnedLocalHighModes ν ceiling modes,
          integerWaveCriticalKernel wave) ≤
        sourceOwnedKernelTailTolerance ν ceiling :=
    (sourceOwnedLocalKernelCore_tail_lt
      ν ceiling (sourceOwnedLocalHighModes ν ceiling modes) disjoint).le
  have highSubset :
      sourceOwnedLocalHighModes ν ceiling modes ⊆ modes :=
    Finset.sdiff_subset
  have highMassLe :
      finiteStateVorticityEnstrophyMass
          (sourceOwnedLocalHighModes ν ceiling modes) state ≤
        finiteStateVorticityEnstrophyMass modes state :=
    finiteStateVorticityEnstrophyMass_mono highSubset state
  have highMassNonneg :
      0 ≤ finiteStateVorticityEnstrophyMass
        (sourceOwnedLocalHighModes ν ceiling modes) state :=
    finiteStateVorticityEnstrophyMass_nonneg _ _
  have tailCoefficientNonneg :
      0 ≤ biotSavartSerrinConstant *
        sourceOwnedKernelTailTolerance ν ceiling :=
    mul_nonneg biotSavartSerrinConstant_nonneg
      (sourceOwnedKernelTailTolerance_pos ν ceiling).le
  calc
    finiteStateVelocityMajorant
          (sourceOwnedLocalHighModes ν ceiling modes) state ^ 2 ≤
        biotSavartSerrinConstant *
          (∑ wave ∈ sourceOwnedLocalHighModes ν ceiling modes,
            integerWaveCriticalKernel wave) *
          finiteStateVorticityEnstrophyMass
            (sourceOwnedLocalHighModes ν ceiling modes) state :=
      finiteStateVelocityMajorant_sq_le_criticalFiniteSum _ _
    _ ≤ biotSavartSerrinConstant *
          sourceOwnedKernelTailTolerance ν ceiling *
          finiteStateVorticityEnstrophyMass
            (sourceOwnedLocalHighModes ν ceiling modes) state := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left tailLe
          biotSavartSerrinConstant_nonneg)
        highMassNonneg
    _ ≤ biotSavartSerrinConstant *
          sourceOwnedKernelTailTolerance ν ceiling *
          finiteStateVorticityEnstrophyMass modes state := by
      exact mul_le_mul_of_nonneg_left highMassLe tailCoefficientNonneg

/-- Complete cutoff-independent local split.  The finite core produces the
quadratic ordinary-enstrophy term; the complementary tail is tied to the
viscous gradient mass. -/
theorem sourceOwnedLocal_velocityMajorant_sq_le
    (ν : Viscosity)
    (ceiling : ℝ)
    (modes : Finset IntegerWavevector)
    (state : ComplexVorticityHilbertState) :
    finiteStateVelocityMajorant modes state ^ 2 ≤
      2 * sourceOwnedLocalCoreVelocityCoefficient ν ceiling *
          finiteStateVorticityCoefficientEnstrophy modes state +
        2 * biotSavartSerrinConstant *
          sourceOwnedKernelTailTolerance ν ceiling *
          finiteStateVorticityEnstrophyMass modes state := by
  let low := finiteStateVelocityMajorant
    (sourceOwnedLocalLowModes ν ceiling modes) state
  let high := finiteStateVelocityMajorant
    (sourceOwnedLocalHighModes ν ceiling modes) state
  have split : low + high = finiteStateVelocityMajorant modes state := by
    exact sourceOwnedLocalVelocityMajorant_split ν ceiling modes state
  have lowBound :
      low ^ 2 ≤ sourceOwnedLocalCoreVelocityCoefficient ν ceiling *
        finiteStateVorticityCoefficientEnstrophy modes state :=
    sourceOwnedLocalLow_velocityMajorant_sq_le ν ceiling modes state
  have highBound :
      high ^ 2 ≤ biotSavartSerrinConstant *
        sourceOwnedKernelTailTolerance ν ceiling *
        finiteStateVorticityEnstrophyMass modes state :=
    sourceOwnedLocalHigh_velocityMajorant_sq_le ν ceiling modes state
  rw [← split]
  nlinarith [sq_nonneg (low - high)]

/-! ## Source-owned viscous absorption and local rate -/

/-- The internally selected tail tolerance spends exactly one eighth of the
viscous gradient coefficient at the generated enstrophy ceiling. -/
theorem sourceOwnedKernelTailTolerance_absorption_identity
    (ν : Viscosity)
    (ceiling : ℝ) :
    ν.coeff⁻¹ * biotSavartSerrinConstant *
          sourceOwnedKernelTailTolerance ν ceiling *
          (max 0 ceiling + 1) =
      ν.coeff * (2 * Real.pi) ^ 2 / 8 := by
  have coeffNe : ν.coeff ≠ 0 := ne_of_gt ν.coeff_pos
  have serrinNe : biotSavartSerrinConstant ≠ 0 :=
    ne_of_gt biotSavartSerrinConstant_pos
  have ceilingPos : 0 < max 0 ceiling + 1 := by
    linarith [le_max_left 0 ceiling]
  have ceilingNe : max 0 ceiling + 1 ≠ 0 := ne_of_gt ceilingPos
  unfold sourceOwnedKernelTailTolerance
  field_simp

/-- Below the actual ceiling, the complete high-frequency contribution is
absorbed by one eighth of the physical viscous gradient term. -/
theorem sourceOwnedLocalHigh_nonlinearTerm_le_viscousEighth
    (ν : Viscosity)
    (ceiling : ℝ)
    (modes : Finset IntegerWavevector)
    (state : ComplexVorticityHilbertState)
    (belowCeiling :
      finiteStateVorticityCoefficientEnstrophy modes state ≤ ceiling) :
    ν.coeff⁻¹ * biotSavartSerrinConstant *
          sourceOwnedKernelTailTolerance ν ceiling *
          finiteStateVorticityEnstrophyMass modes state *
          finiteStateVorticityCoefficientEnstrophy modes state ≤
      (ν.coeff / 8) *
        ((2 * Real.pi) ^ 2 *
          finiteStateVorticityEnstrophyMass modes state) := by
  let enstrophy :=
    finiteStateVorticityCoefficientEnstrophy modes state
  let gradientMass := finiteStateVorticityEnstrophyMass modes state
  let ceilingMass := max 0 ceiling + 1
  have enstrophyLe : enstrophy ≤ ceilingMass := by
    dsimp [enstrophy, ceilingMass]
    linarith [le_max_right 0 ceiling]
  have multiplierNonneg :
      0 ≤ ν.coeff⁻¹ * biotSavartSerrinConstant *
        sourceOwnedKernelTailTolerance ν ceiling * gradientMass := by
    exact mul_nonneg
      (mul_nonneg
        (mul_nonneg (inv_nonneg.mpr ν.coeff_pos.le)
          biotSavartSerrinConstant_nonneg)
        (sourceOwnedKernelTailTolerance_pos ν ceiling).le)
      (finiteStateVorticityEnstrophyMass_nonneg modes state)
  calc
    ν.coeff⁻¹ * biotSavartSerrinConstant *
          sourceOwnedKernelTailTolerance ν ceiling * gradientMass *
          enstrophy ≤
        (ν.coeff⁻¹ * biotSavartSerrinConstant *
          sourceOwnedKernelTailTolerance ν ceiling * gradientMass) *
          ceilingMass := by
      exact mul_le_mul_of_nonneg_left enstrophyLe multiplierNonneg
    _ = (ν.coeff⁻¹ * biotSavartSerrinConstant *
            sourceOwnedKernelTailTolerance ν ceiling * ceilingMass) *
          gradientMass := by ring
    _ = (ν.coeff * (2 * Real.pi) ^ 2 / 8) * gradientMass := by
      rw [show
        ν.coeff⁻¹ * biotSavartSerrinConstant *
              sourceOwnedKernelTailTolerance ν ceiling * ceilingMass =
            ν.coeff * (2 * Real.pi) ^ 2 / 8 by
          simpa [ceilingMass] using
            sourceOwnedKernelTailTolerance_absorption_identity
              ν ceiling]
    _ = (ν.coeff / 8) * ((2 * Real.pi) ^ 2 * gradientMass) := by
      ring

/-- Local supercritical replacement for the global small-data rate.  The
high tail is absorbed; only a finite-core quadratic enstrophy term remains,
uniformly in the Galerkin inventory. -/
theorem finiteStateVorticityCriticalEnstrophyRate_le_sourceOwnedLocal
    (ν : Viscosity)
    (ceiling : ℝ)
    (modes : Finset IntegerWavevector)
    (state : ComplexVorticityHilbertState)
    (belowCeiling :
      finiteStateVorticityCoefficientEnstrophy modes state ≤ ceiling) :
    finiteStateVorticityCriticalEnstrophyRate
        modes ν.coeff state ≤
      -(3 * ν.coeff / 8) *
          ((2 * Real.pi) ^ 2 *
            finiteStateVorticityEnstrophyMass modes state) +
        ν.coeff⁻¹ *
          sourceOwnedLocalCoreVelocityCoefficient ν ceiling *
          finiteStateVorticityCoefficientEnstrophy modes state ^ 2 := by
  let enstrophy :=
    finiteStateVorticityCoefficientEnstrophy modes state
  let gradientMass := finiteStateVorticityEnstrophyMass modes state
  have enstrophyNonneg : 0 ≤ enstrophy := by
    unfold enstrophy finiteStateVorticityCoefficientEnstrophy
    exact Finset.sum_nonneg fun wave waveMem =>
      complexCoordinateAmplitudeSq_nonneg (state wave)
  have criticalMultiplierNonneg :
      0 ≤ (ν.coeff⁻¹ / 2) * enstrophy := by
    exact mul_nonneg
      (div_nonneg (inv_nonneg.mpr ν.coeff_pos.le) (by norm_num))
      enstrophyNonneg
  have majorantBound :=
    sourceOwnedLocal_velocityMajorant_sq_le
      ν ceiling modes state
  have highAbsorption :
      ν.coeff⁻¹ * biotSavartSerrinConstant *
            sourceOwnedKernelTailTolerance ν ceiling * gradientMass *
            enstrophy ≤
        (ν.coeff / 8) *
          ((2 * Real.pi) ^ 2 * gradientMass) := by
    simpa [enstrophy, gradientMass] using
      sourceOwnedLocalHigh_nonlinearTerm_le_viscousEighth
        ν ceiling modes state belowCeiling
  unfold finiteStateVorticityCriticalEnstrophyRate
  calc
    -(ν.coeff / 2) *
          ((2 * Real.pi) ^ 2 * gradientMass) +
        (ν.coeff⁻¹ / 2) *
          finiteStateVelocityMajorant modes state ^ 2 * enstrophy =
      -(ν.coeff / 2) *
          ((2 * Real.pi) ^ 2 * gradientMass) +
        finiteStateVelocityMajorant modes state ^ 2 *
          ((ν.coeff⁻¹ / 2) * enstrophy) := by ring
    _ ≤
      -(ν.coeff / 2) *
          ((2 * Real.pi) ^ 2 * gradientMass) +
        (2 * sourceOwnedLocalCoreVelocityCoefficient ν ceiling *
              enstrophy +
            2 * biotSavartSerrinConstant *
              sourceOwnedKernelTailTolerance ν ceiling * gradientMass) *
          ((ν.coeff⁻¹ / 2) * enstrophy) := by
      exact add_le_add le_rfl
        (mul_le_mul_of_nonneg_right majorantBound
          criticalMultiplierNonneg)
    _ =
      -(ν.coeff / 2) *
          ((2 * Real.pi) ^ 2 * gradientMass) +
        ν.coeff⁻¹ *
          sourceOwnedLocalCoreVelocityCoefficient ν ceiling *
          enstrophy ^ 2 +
        ν.coeff⁻¹ * biotSavartSerrinConstant *
          sourceOwnedKernelTailTolerance ν ceiling * gradientMass *
          enstrophy := by ring
    _ ≤
      -(ν.coeff / 2) *
          ((2 * Real.pi) ^ 2 * gradientMass) +
        ν.coeff⁻¹ *
          sourceOwnedLocalCoreVelocityCoefficient ν ceiling *
          enstrophy ^ 2 +
        (ν.coeff / 8) *
          ((2 * Real.pi) ^ 2 * gradientMass) := by
      exact add_le_add le_rfl highAbsorption
    _ =
      -(3 * ν.coeff / 8) *
          ((2 * Real.pi) ^ 2 * gradientMass) +
        ν.coeff⁻¹ *
          sourceOwnedLocalCoreVelocityCoefficient ν ceiling *
          enstrophy ^ 2 := by ring

/-- The exact stretching-minus-viscosity rate inherits the source-owned
local estimate. -/
theorem finiteStateVorticity_stretching_sub_viscous_le_sourceOwnedLocal
    (ν : Viscosity)
    (ceiling : ℝ)
    (modes : Finset IntegerWavevector)
    (state : ComplexVorticityHilbertState)
    (transverse :
      ∀ wave ∈ modes,
        complexWavevector wave ⬝ᵥ state wave = 0)
    (belowCeiling :
      finiteStateVorticityCoefficientEnstrophy modes state ≤ ceiling) :
    finiteStateVorticityStretchingWork modes state -
          ν.coeff * (2 * Real.pi) ^ 2 *
            finiteStateVorticityEnstrophyMass modes state ≤
      -(3 * ν.coeff / 8) *
          ((2 * Real.pi) ^ 2 *
            finiteStateVorticityEnstrophyMass modes state) +
        ν.coeff⁻¹ *
          sourceOwnedLocalCoreVelocityCoefficient ν ceiling *
          finiteStateVorticityCoefficientEnstrophy modes state ^ 2 := by
  exact
    (finiteStateVorticity_stretching_sub_viscous_le_criticalRate
      modes state ν.coeff ν.coeff_pos transverse).trans
      (finiteStateVorticityCriticalEnstrophyRate_le_sourceOwnedLocal
        ν ceiling modes state belowCeiling)

/-- Actual initial coefficient enstrophy plus one.  This is the internally
generated local barrier ceiling; no caller-selected radius occurs. -/
def sourceOwnedLocalEnstrophyCeiling
    (modes : Finset IntegerWavevector)
    (initialState : ComplexVorticityHilbertState) : ℝ :=
  finiteStateVorticityCoefficientEnstrophy modes initialState + 1

theorem sourceOwnedLocalEnstrophyCeiling_pos
    (modes : Finset IntegerWavevector)
    (initialState : ComplexVorticityHilbertState) :
    0 < sourceOwnedLocalEnstrophyCeiling modes initialState := by
  unfold sourceOwnedLocalEnstrophyCeiling
  have enstrophyNonneg :
      0 ≤ finiteStateVorticityCoefficientEnstrophy modes initialState := by
    unfold finiteStateVorticityCoefficientEnstrophy
    exact Finset.sum_nonneg fun wave waveMem =>
      complexCoordinateAmplitudeSq_nonneg (initialState wave)
  linarith

/-- Finite-core coefficient in the scalar local enstrophy barrier. -/
def sourceOwnedLocalQuadraticCoefficient
    (ν : Viscosity)
    (ceiling : ℝ) : ℝ :=
  ν.coeff⁻¹ * sourceOwnedLocalCoreVelocityCoefficient ν ceiling

theorem sourceOwnedLocalQuadraticCoefficient_nonneg
    (ν : Viscosity)
    (ceiling : ℝ) :
    0 ≤ sourceOwnedLocalQuadraticCoefficient ν ceiling := by
  exact mul_nonneg (inv_nonneg.mpr ν.coeff_pos.le)
    (sourceOwnedLocalCoreVelocityCoefficient_nonneg ν ceiling)

/-- Viscosity-dependent positive coefficient of the fifth-order canonical
core lower bound. -/
def sourceOwnedLocalQuadraticFifthCoefficient (ν : Viscosity) : ℝ :=
  ν.coeff⁻¹ * biotSavartSerrinConstant *
    sourceOwnedLocalKernelRadiusSlope ν ^ 5 / 81

theorem sourceOwnedLocalQuadraticFifthCoefficient_pos
    (ν : Viscosity) :
    0 < sourceOwnedLocalQuadraticFifthCoefficient ν := by
  unfold sourceOwnedLocalQuadraticFifthCoefficient
  exact div_pos
    (mul_pos
      (mul_pos (inv_pos.mpr ν.coeff_pos) biotSavartSerrinConstant_pos)
      (pow_pos (sourceOwnedLocalKernelRadiusSlope_pos ν) 5))
    (by norm_num)

/-- Matching fifth-order lower bound for the actual quadratic barrier
coefficient. -/
theorem sourceOwnedLocalQuadraticFifthCoefficient_mul_le
    (ν : Viscosity)
    (ceiling : ℝ) :
    sourceOwnedLocalQuadraticFifthCoefficient ν *
          (max 0 ceiling + 1) ^ 5 ≤
      sourceOwnedLocalQuadraticCoefficient ν ceiling := by
  have radiusLower := sourceOwnedLocalKernelRadiusSlope_mul_le ν ceiling
  have radiusSlopeNonneg := (sourceOwnedLocalKernelRadiusSlope_pos ν).le
  have ceilingFactorNonneg : 0 ≤ max 0 ceiling + 1 := by
    linarith [le_max_left 0 ceiling]
  have radiusFifthLower :
      (sourceOwnedLocalKernelRadiusSlope ν *
          (max 0 ceiling + 1)) ^ 5 ≤
        (sourceOwnedLocalKernelRadius ν ceiling : ℝ) ^ 5 :=
    pow_le_pow_left₀
      (mul_nonneg radiusSlopeNonneg ceilingFactorNonneg) radiusLower 5
  have frequencyLower :=
    sourceOwnedLocalKernelRadius_fifth_le_frequencyMass ν ceiling
  have velocityLower :=
    sourceOwnedLocalCoreVelocityCoefficient_ge_frequencyMass ν ceiling
  unfold sourceOwnedLocalQuadraticCoefficient
    sourceOwnedLocalQuadraticFifthCoefficient
  have viscosityInvNonneg : 0 ≤ ν.coeff⁻¹ :=
    inv_nonneg.mpr ν.coeff_pos.le
  have constantNonneg : 0 ≤ biotSavartSerrinConstant :=
    biotSavartSerrinConstant_nonneg
  calc
    ν.coeff⁻¹ * biotSavartSerrinConstant *
          sourceOwnedLocalKernelRadiusSlope ν ^ 5 / 81 *
          (max 0 ceiling + 1) ^ 5 =
        ν.coeff⁻¹ * biotSavartSerrinConstant *
          ((sourceOwnedLocalKernelRadiusSlope ν *
            (max 0 ceiling + 1)) ^ 5 / 81) := by ring
    _ ≤ ν.coeff⁻¹ * biotSavartSerrinConstant *
          ((sourceOwnedLocalKernelRadius ν ceiling : ℝ) ^ 5 / 81) := by
      exact mul_le_mul_of_nonneg_left
        (div_le_div_of_nonneg_right radiusFifthLower (by norm_num))
        (mul_nonneg viscosityInvNonneg constantNonneg)
    _ ≤ ν.coeff⁻¹ * biotSavartSerrinConstant *
          sourceOwnedLocalCoreFrequencyMass ν ceiling := by
      exact mul_le_mul_of_nonneg_left frequencyLower
        (mul_nonneg viscosityInvNonneg constantNonneg)
    _ ≤ ν.coeff⁻¹ *
          sourceOwnedLocalCoreVelocityCoefficient ν ceiling := by
      simpa only [mul_assoc] using
        (mul_le_mul_of_nonneg_left velocityLower viscosityInvNonneg)

/-- Explicit upper coefficient generated by the canonical cube radius. -/
noncomputable def sourceOwnedLocalQuadraticCoefficientUpper
    (ν : Viscosity)
    (ceiling : ℝ) : ℝ :=
  ν.coeff⁻¹ * sourceOwnedLocalCoreVelocityCoefficientUpper ν ceiling

theorem sourceOwnedLocalQuadraticCoefficientUpper_nonneg
    (ν : Viscosity)
    (ceiling : ℝ) :
    0 ≤ sourceOwnedLocalQuadraticCoefficientUpper ν ceiling := by
  unfold sourceOwnedLocalQuadraticCoefficientUpper
  exact mul_nonneg (inv_nonneg.mpr ν.coeff_pos.le)
    (by
      unfold sourceOwnedLocalCoreVelocityCoefficientUpper
      exact mul_nonneg
        (mul_nonneg biotSavartSerrinConstant_nonneg
          (tsum_nonneg fun wave => integerWaveCriticalKernel_nonneg wave))
        (by
          unfold sourceOwnedLocalCoreFrequencyMassUpper
          positivity))

theorem sourceOwnedLocalQuadraticCoefficient_le_upper
    (ν : Viscosity)
    (ceiling : ℝ) :
    sourceOwnedLocalQuadraticCoefficient ν ceiling ≤
      sourceOwnedLocalQuadraticCoefficientUpper ν ceiling := by
  unfold sourceOwnedLocalQuadraticCoefficient
    sourceOwnedLocalQuadraticCoefficientUpper
  exact mul_le_mul_of_nonneg_left
    (sourceOwnedLocalCoreVelocityCoefficient_le_upper ν ceiling)
    (inv_nonneg.mpr ν.coeff_pos.le)

/-- Explicit fifth-order coefficient majorizing the canonical quadratic
barrier coefficient. -/
noncomputable def sourceOwnedLocalQuadraticFifthCoefficientUpper
    (ν : Viscosity) : ℝ :=
  ν.coeff⁻¹ * biotSavartSerrinConstant *
    (∑' wave : IntegerWavevector, integerWaveCriticalKernel wave) *
    81 * (sourceOwnedLocalKernelRadiusSlope ν + 2) ^ 5

theorem sourceOwnedLocalQuadraticFifthCoefficientUpper_nonneg
    (ν : Viscosity) :
    0 ≤ sourceOwnedLocalQuadraticFifthCoefficientUpper ν := by
  have kernelTsumNonneg :
      0 ≤ ∑' wave : IntegerWavevector,
        integerWaveCriticalKernel wave :=
    tsum_nonneg fun wave => integerWaveCriticalKernel_nonneg wave
  have slopePlusNonneg :
      0 ≤ sourceOwnedLocalKernelRadiusSlope ν + 2 := by
    linarith [sourceOwnedLocalKernelRadiusSlope_pos ν]
  unfold sourceOwnedLocalQuadraticFifthCoefficientUpper
  exact mul_nonneg
    (mul_nonneg
      (mul_nonneg
        (mul_nonneg
          (inv_nonneg.mpr ν.coeff_pos.le)
          biotSavartSerrinConstant_nonneg)
        kernelTsumNonneg)
      (by norm_num))
    (pow_nonneg slopePlusNonneg 5)

theorem sourceOwnedLocalQuadraticCoefficientUpper_le_fifth
    (ν : Viscosity)
    (ceiling : ℝ)
    (ceilingNonneg : 0 ≤ ceiling) :
    sourceOwnedLocalQuadraticCoefficientUpper ν ceiling ≤
      sourceOwnedLocalQuadraticFifthCoefficientUpper ν *
        (ceiling + 1) ^ 5 := by
  have frequencyUpper :=
    sourceOwnedLocalCoreFrequencyMassUpper_le_fifth
      ν ceiling ceilingNonneg
  have prefactorNonneg :
      0 ≤ ν.coeff⁻¹ * biotSavartSerrinConstant *
        (∑' wave : IntegerWavevector, integerWaveCriticalKernel wave) := by
    exact mul_nonneg
      (mul_nonneg
        (inv_nonneg.mpr ν.coeff_pos.le)
        biotSavartSerrinConstant_nonneg)
      (tsum_nonneg fun wave => integerWaveCriticalKernel_nonneg wave)
  unfold sourceOwnedLocalQuadraticCoefficientUpper
    sourceOwnedLocalCoreVelocityCoefficientUpper
    sourceOwnedLocalQuadraticFifthCoefficientUpper
  calc
    ν.coeff⁻¹ *
          (biotSavartSerrinConstant *
            (∑' wave : IntegerWavevector, integerWaveCriticalKernel wave) *
            sourceOwnedLocalCoreFrequencyMassUpper ν ceiling) =
        (ν.coeff⁻¹ * biotSavartSerrinConstant *
          (∑' wave : IntegerWavevector, integerWaveCriticalKernel wave)) *
            sourceOwnedLocalCoreFrequencyMassUpper ν ceiling := by ring
    _ ≤ (ν.coeff⁻¹ * biotSavartSerrinConstant *
          (∑' wave : IntegerWavevector, integerWaveCriticalKernel wave)) *
        (81 * (sourceOwnedLocalKernelRadiusSlope ν + 2) ^ 5 *
          (ceiling + 1) ^ 5) :=
      mul_le_mul_of_nonneg_left frequencyUpper prefactorNonneg
    _ = ν.coeff⁻¹ * biotSavartSerrinConstant *
          (∑' wave : IntegerWavevector, integerWaveCriticalKernel wave) *
          81 * (sourceOwnedLocalKernelRadiusSlope ν + 2) ^ 5 *
          (ceiling + 1) ^ 5 := by ring

theorem sourceOwnedLocalQuadraticCoefficient_le_fifthUpper
    (ν : Viscosity)
    (ceiling : ℝ)
    (ceilingNonneg : 0 ≤ ceiling) :
    sourceOwnedLocalQuadraticCoefficient ν ceiling ≤
      sourceOwnedLocalQuadraticFifthCoefficientUpper ν *
        (ceiling + 1) ^ 5 :=
  (sourceOwnedLocalQuadraticCoefficient_le_upper ν ceiling).trans
    (sourceOwnedLocalQuadraticCoefficientUpper_le_fifth
      ν ceiling ceilingNonneg)

/-! ## Fixed-wave positive coefficient floor -/

/-- Once the generated tail tolerance is no larger than one fixed wave's
critical-kernel atom, that wave must occur in the source-owned finite core.
Otherwise its singleton would itself be a disjoint tail whose mass is both
strictly below the tolerance and at least that atom. -/
theorem sourceOwnedLocalKernelCore_fixedWave_mem_of_tolerance_le
    (ν : Viscosity)
    (ceiling : ℝ)
    (wave : IntegerWavevector)
    (toleranceLe : sourceOwnedKernelTailTolerance ν ceiling ≤
      integerWaveCriticalKernel wave) :
    wave ∈ sourceOwnedLocalKernelCore ν ceiling := by
  by_contra waveNotMem
  have disjoint : Disjoint ({wave} : Finset IntegerWavevector)
      (sourceOwnedLocalKernelCore ν ceiling) := by
    simpa only [Finset.disjoint_singleton_left] using waveNotMem
  have tail := sourceOwnedLocalKernelCore_tail_lt
    ν ceiling ({wave} : Finset IntegerWavevector) disjoint
  simp only [Finset.sum_singleton] at tail
  exact (not_lt_of_ge toleranceLe) tail

/-- Explicit strictly positive coefficient contributed by one fixed nonzero
wave once that wave has entered the generated core. -/
def sourceOwnedLocalFixedWaveQuadraticFloor
    (ν : Viscosity)
    (wave : IntegerWavevector) : ℝ :=
  ν.coeff⁻¹ * biotSavartSerrinConstant *
    integerWaveCriticalKernel wave * integerWaveNormSq wave

theorem sourceOwnedLocalFixedWaveQuadraticFloor_pos
    (ν : Viscosity)
    (wave : IntegerWavevector)
    (waveNe : wave ≠ 0) :
    0 < sourceOwnedLocalFixedWaveQuadraticFloor ν wave := by
  have kernelPos : 0 < integerWaveCriticalKernel wave := by
    unfold integerWaveCriticalKernel
    exact sq_pos_of_pos (inv_pos.mpr (integerWaveNormSq_pos waveNe))
  unfold sourceOwnedLocalFixedWaveQuadraticFloor
  exact mul_pos
    (mul_pos
      (mul_pos (inv_pos.mpr ν.coeff_pos)
        biotSavartSerrinConstant_pos)
      kernelPos)
    (integerWaveNormSq_pos waveNe)

theorem sourceOwnedLocalFixedWaveQuadraticFloor_le_of_mem
    (ν : Viscosity)
    (ceiling : ℝ)
    (wave : IntegerWavevector)
    (waveMem : wave ∈ sourceOwnedLocalKernelCore ν ceiling) :
    sourceOwnedLocalFixedWaveQuadraticFloor ν wave ≤
      sourceOwnedLocalQuadraticCoefficient ν ceiling := by
  have kernelLe : integerWaveCriticalKernel wave ≤
      ∑ later ∈ sourceOwnedLocalKernelCore ν ceiling,
        integerWaveCriticalKernel later := by
    exact Finset.single_le_sum
      (fun later _ => integerWaveCriticalKernel_nonneg later) waveMem
  have frequencyLe : integerWaveNormSq wave ≤
      sourceOwnedLocalCoreFrequencyMass ν ceiling := by
    unfold sourceOwnedLocalCoreFrequencyMass
    exact Finset.single_le_sum
      (fun later _ => integerWaveNormSq_nonneg later) waveMem
  unfold sourceOwnedLocalFixedWaveQuadraticFloor
    sourceOwnedLocalQuadraticCoefficient
    sourceOwnedLocalCoreVelocityCoefficient
  have inverseNonneg : 0 ≤ ν.coeff⁻¹ := inv_nonneg.mpr ν.coeff_pos.le
  have constantNonneg : 0 ≤ biotSavartSerrinConstant :=
    biotSavartSerrinConstant_nonneg
  have coreKernelNonneg : 0 ≤
      ∑ later ∈ sourceOwnedLocalKernelCore ν ceiling,
        integerWaveCriticalKernel later :=
    Finset.sum_nonneg fun later _ => integerWaveCriticalKernel_nonneg later
  simpa only [mul_assoc] using
    (mul_le_mul_of_nonneg_left
      (mul_le_mul
        (mul_le_mul_of_nonneg_left kernelLe constantNonneg)
        frequencyLe
        (integerWaveNormSq_nonneg wave)
        (mul_nonneg constantNonneg coreKernelNonneg))
      inverseNonneg)

/-- Every fixed nonzero lattice atom eventually supplies one uniform positive
lower bound for the viscosity-dependent quadratic coefficient.  The scale
threshold is generated internally from the actual viscosity and that atom. -/
theorem eventually_sourceOwnedLocalFixedWaveQuadraticFloor_le
    (ν : Viscosity)
    (wave : IntegerWavevector)
    (waveNe : wave ≠ 0) :
    ∃ scaleFloor : ℝ,
      ∀ ceiling : ℝ, scaleFloor ≤ ceiling →
        sourceOwnedLocalFixedWaveQuadraticFloor ν wave ≤
          sourceOwnedLocalQuadraticCoefficient ν ceiling := by
  let kernel := integerWaveCriticalKernel wave
  let denominatorConstant := 8 * biotSavartSerrinConstant * kernel
  let numerator := ν.coeff ^ 2 * (2 * Real.pi) ^ 2
  let scaleFloor := numerator / denominatorConstant
  have kernelPos : 0 < kernel := by
    dsimp only [kernel]
    unfold integerWaveCriticalKernel
    exact sq_pos_of_pos (inv_pos.mpr (integerWaveNormSq_pos waveNe))
  have denominatorConstantPos : 0 < denominatorConstant := by
    dsimp only [denominatorConstant]
    exact mul_pos
      (mul_pos (by norm_num) biotSavartSerrinConstant_pos) kernelPos
  refine ⟨scaleFloor, ?_⟩
  intro ceiling scaleLe
  apply sourceOwnedLocalFixedWaveQuadraticFloor_le_of_mem
  apply sourceOwnedLocalKernelCore_fixedWave_mem_of_tolerance_le
  have ceilingMassPos : 0 < max 0 ceiling + 1 := by
    linarith [le_max_left 0 ceiling]
  have denominatorPos :
      0 < 8 * biotSavartSerrinConstant * (max 0 ceiling + 1) := by
    exact mul_pos
      (mul_pos (by norm_num) biotSavartSerrinConstant_pos) ceilingMassPos
  apply (div_le_iff₀ denominatorPos).2
  have scaleFloorIdentity :
      denominatorConstant * scaleFloor = numerator := by
    dsimp only [scaleFloor]
    field_simp
  have scaleFloorLeCeilingMass : scaleFloor ≤ max 0 ceiling + 1 := by
    linarith [le_max_right 0 ceiling]
  have weightedLe :
      denominatorConstant * scaleFloor ≤
        denominatorConstant * (max 0 ceiling + 1) :=
    mul_le_mul_of_nonneg_left scaleFloorLeCeilingMass
      denominatorConstantPos.le
  change
    numerator ≤ kernel *
      (8 * biotSavartSerrinConstant * (max 0 ceiling + 1))
  rw [← scaleFloorIdentity]
  nlinarith

/-- Strict barrier slope generated from viscosity and actual initial
enstrophy. -/
def sourceOwnedLocalBarrierSlope
    (ν : Viscosity)
    (modes : Finset IntegerWavevector)
    (initialState : ComplexVorticityHilbertState) : ℝ :=
  let ceiling := sourceOwnedLocalEnstrophyCeiling modes initialState
  sourceOwnedLocalQuadraticCoefficient ν ceiling * ceiling ^ 2 + 1

theorem sourceOwnedLocalBarrierSlope_pos
    (ν : Viscosity)
    (modes : Finset IntegerWavevector)
    (initialState : ComplexVorticityHilbertState) :
    0 < sourceOwnedLocalBarrierSlope ν modes initialState := by
  unfold sourceOwnedLocalBarrierSlope
  have coefficientNonneg :=
    sourceOwnedLocalQuadraticCoefficient_nonneg ν
      (sourceOwnedLocalEnstrophyCeiling modes initialState)
  have squareNonneg :
      0 ≤ sourceOwnedLocalEnstrophyCeiling modes initialState ^ 2 :=
    sq_nonneg _
  nlinarith

/-- Positive common physical time selected from the actual local barrier.
The factor two converts half-enstrophy back to full enstrophy. -/
def sourceOwnedLocalDuration
    (ν : Viscosity)
    (modes : Finset IntegerWavevector)
    (initialState : ComplexVorticityHilbertState) : ℝ :=
  1 / (2 * sourceOwnedLocalBarrierSlope ν modes initialState)

theorem sourceOwnedLocalDuration_pos
    (ν : Viscosity)
    (modes : Finset IntegerWavevector)
    (initialState : ComplexVorticityHilbertState) :
    0 < sourceOwnedLocalDuration ν modes initialState := by
  unfold sourceOwnedLocalDuration
  exact div_pos (by norm_num)
    (mul_pos (by norm_num)
      (sourceOwnedLocalBarrierSlope_pos ν modes initialState))

/-- Pointwise derivative law and local rate for one actual finite Galerkin
state below its generated ceiling. -/
theorem finiteStateVorticityHalfEnstrophy_hasDerivAt_and_le_sourceOwnedLocal
    (modes : Finset IntegerWavevector)
    (negClosed :
      ∀ wave, wave ∈ modes → waveNeg wave ∈ modes)
    (ν : Viscosity)
    (ceiling : ℝ)
    (trajectory : ℝ → ComplexVorticityHilbertState)
    (t : ℝ)
    (evolves :
      HasDerivAt trajectory
        (finiteStateVorticityGenerator
          modes ν.coeff (trajectory t)) t)
    (reality : FiniteStateFourierReality (trajectory t))
    (transverse :
      ∀ wave ∈ modes,
        complexWavevector wave ⬝ᵥ trajectory t wave = 0)
    (belowCeiling :
      finiteStateVorticityCoefficientEnstrophy
        modes (trajectory t) ≤ ceiling) :
    HasDerivAt
        (fun time =>
          finiteStateVorticityHalfEnstrophy modes (trajectory time))
        (finiteStateVorticityStretchingWork modes (trajectory t) -
          ν.coeff * (2 * Real.pi) ^ 2 *
            finiteStateVorticityEnstrophyMass modes (trajectory t)) t ∧
      finiteStateVorticityStretchingWork modes (trajectory t) -
            ν.coeff * (2 * Real.pi) ^ 2 *
              finiteStateVorticityEnstrophyMass modes (trajectory t) ≤
        -(3 * ν.coeff / 8) *
            ((2 * Real.pi) ^ 2 *
              finiteStateVorticityEnstrophyMass modes (trajectory t)) +
          sourceOwnedLocalQuadraticCoefficient ν ceiling *
            finiteStateVorticityCoefficientEnstrophy
              modes (trajectory t) ^ 2 := by
  constructor
  · exact finiteStateVorticityHalfEnstrophy_hasDerivAt_stretchingWork
      modes negClosed ν.coeff trajectory t evolves reality
  · simpa [sourceOwnedLocalQuadraticCoefficient] using
      finiteStateVorticity_stretching_sub_viscous_le_sourceOwnedLocal
        ν ceiling modes (trajectory t) transverse belowCeiling

/-- Every actual finite Galerkin solution stays below the source-generated
linear half-enstrophy barrier on the generated common time.  The proof uses
the strict derivative fencing theorem only at a possible first contact, so
the tail absorption hypothesis is produced at that contact rather than
stored in the theorem mouth. -/
theorem finiteStateVorticity_sourceOwnedLocalBarrier_on_Icc
    (modes : Finset IntegerWavevector)
    (negClosed :
      ∀ wave, wave ∈ modes → waveNeg wave ∈ modes)
    (ν : Viscosity)
    (trajectory : ℝ → ComplexVorticityHilbertState)
    (b : ℝ)
    (bLeDuration :
      b ≤ sourceOwnedLocalDuration ν modes (trajectory 0))
    (evolves :
      ∀ t ∈ Icc (0 : ℝ) b,
        HasDerivAt trajectory
          (finiteStateVorticityGenerator
            modes ν.coeff (trajectory t)) t)
    (reality :
      ∀ t ∈ Icc (0 : ℝ) b,
        FiniteStateFourierReality (trajectory t))
    (transverse :
      ∀ t ∈ Icc (0 : ℝ) b,
        ∀ wave ∈ modes,
          complexWavevector wave ⬝ᵥ trajectory t wave = 0) :
    ∀ t ∈ Icc (0 : ℝ) b,
      finiteStateVorticityHalfEnstrophy modes (trajectory t) ≤
          finiteStateVorticityHalfEnstrophy modes (trajectory 0) +
            sourceOwnedLocalBarrierSlope ν modes (trajectory 0) * t ∧
        finiteStateVorticityCoefficientEnstrophy
            modes (trajectory t) ≤
          sourceOwnedLocalEnstrophyCeiling modes (trajectory 0) := by
  let ceiling :=
    sourceOwnedLocalEnstrophyCeiling modes (trajectory 0)
  let slope := sourceOwnedLocalBarrierSlope ν modes (trajectory 0)
  let duration := sourceOwnedLocalDuration ν modes (trajectory 0)
  let halfEnstrophy : ℝ → ℝ := fun time =>
    finiteStateVorticityHalfEnstrophy modes (trajectory time)
  let exactRate : ℝ → ℝ := fun time =>
    finiteStateVorticityStretchingWork modes (trajectory time) -
      ν.coeff * (2 * Real.pi) ^ 2 *
        finiteStateVorticityEnstrophyMass modes (trajectory time)
  let barrier : ℝ → ℝ := fun time =>
    halfEnstrophy 0 + slope * time
  have slopePos : 0 < slope := by
    exact sourceOwnedLocalBarrierSlope_pos ν modes (trajectory 0)
  have durationEq : duration = 1 / (2 * slope) := by
    rfl
  have durationPos : 0 < duration := by
    exact sourceOwnedLocalDuration_pos ν modes (trajectory 0)
  have halfDerivative :
      ∀ t ∈ Icc (0 : ℝ) b,
        HasDerivAt halfEnstrophy (exactRate t) t := by
    intro t tMem
    exact finiteStateVorticityHalfEnstrophy_hasDerivAt_stretchingWork
      modes negClosed ν.coeff trajectory t
      (evolves t tMem)
      (reality t tMem)
  have halfContinuous :
      ContinuousOn halfEnstrophy (Icc (0 : ℝ) b) :=
    HasDerivAt.continuousOn halfDerivative
  have barrierDerivative :
      ∀ t : ℝ, HasDerivAt barrier slope t := by
    intro t
    change HasDerivAt
      (fun time : ℝ => halfEnstrophy 0 + slope * time) slope t
    simpa only [id_eq, mul_one] using
      ((hasDerivAt_id t).const_mul slope).const_add
        (halfEnstrophy 0)
  have boundaryRate :
      ∀ t ∈ Ico (0 : ℝ) b,
        halfEnstrophy t = barrier t → exactRate t < slope := by
    intro t tMem contact
    have tMemClosed : t ∈ Icc (0 : ℝ) b :=
      ⟨tMem.1, tMem.2.le⟩
    have tLtDuration : t < duration :=
      lt_of_lt_of_le tMem.2 bLeDuration
    have denominatorPos : 0 < 2 * slope :=
      mul_pos (by norm_num) slopePos
    have scaledTimeLt : t * (2 * slope) < 1 := by
      apply (lt_div_iff₀ denominatorPos).mp
      simpa [durationEq] using tLtDuration
    have contactEnstrophy :
        finiteStateVorticityCoefficientEnstrophy
            modes (trajectory t) =
          finiteStateVorticityCoefficientEnstrophy
              modes (trajectory 0) + 2 * slope * t := by
      dsimp [halfEnstrophy, barrier] at contact
      unfold finiteStateVorticityHalfEnstrophy at contact
      linarith
    have belowCeiling :
        finiteStateVorticityCoefficientEnstrophy
            modes (trajectory t) ≤ ceiling := by
      dsimp [ceiling, sourceOwnedLocalEnstrophyCeiling]
      rw [contactEnstrophy]
      nlinarith
    have pointwise :=
      finiteStateVorticityHalfEnstrophy_hasDerivAt_and_le_sourceOwnedLocal
        modes negClosed ν ceiling trajectory t
        (evolves t tMemClosed)
        (reality t tMemClosed)
        (transverse t tMemClosed)
        belowCeiling
    have gradientNonneg :
        0 ≤ (2 * Real.pi) ^ 2 *
          finiteStateVorticityEnstrophyMass modes (trajectory t) :=
      mul_nonneg (sq_nonneg _)
        (finiteStateVorticityEnstrophyMass_nonneg modes (trajectory t))
    have enstrophyNonneg :
        0 ≤ finiteStateVorticityCoefficientEnstrophy
          modes (trajectory t) := by
      unfold finiteStateVorticityCoefficientEnstrophy
      exact Finset.sum_nonneg fun wave waveMem =>
        complexCoordinateAmplitudeSq_nonneg (trajectory t wave)
    have ceilingPos : 0 < ceiling := by
      exact sourceOwnedLocalEnstrophyCeiling_pos modes (trajectory 0)
    have squareLe :
        finiteStateVorticityCoefficientEnstrophy
              modes (trajectory t) ^ 2 ≤ ceiling ^ 2 := by
      nlinarith
    have coefficientNonneg :
        0 ≤ sourceOwnedLocalQuadraticCoefficient ν ceiling :=
      sourceOwnedLocalQuadraticCoefficient_nonneg ν ceiling
    have rateLe :
        exactRate t ≤
          sourceOwnedLocalQuadraticCoefficient ν ceiling * ceiling ^ 2 := by
      calc
        exactRate t ≤
            -(3 * ν.coeff / 8) *
                ((2 * Real.pi) ^ 2 *
                  finiteStateVorticityEnstrophyMass modes (trajectory t)) +
              sourceOwnedLocalQuadraticCoefficient ν ceiling *
                finiteStateVorticityCoefficientEnstrophy
                  modes (trajectory t) ^ 2 := pointwise.2
        _ ≤ sourceOwnedLocalQuadraticCoefficient ν ceiling *
              finiteStateVorticityCoefficientEnstrophy
                modes (trajectory t) ^ 2 := by
          have viscousCoefficientNonneg : 0 ≤ 3 * ν.coeff / 8 := by
            exact div_nonneg
              (mul_nonneg (by norm_num) ν.coeff_pos.le)
              (by norm_num)
          have viscousTermNonpos :
              -(3 * ν.coeff / 8) *
                  ((2 * Real.pi) ^ 2 *
                    finiteStateVorticityEnstrophyMass
                      modes (trajectory t)) ≤ 0 :=
            mul_nonpos_of_nonpos_of_nonneg
              (neg_nonpos.mpr viscousCoefficientNonneg)
              gradientNonneg
          exact add_le_of_nonpos_left
            viscousTermNonpos
        _ ≤ sourceOwnedLocalQuadraticCoefficient ν ceiling *
              ceiling ^ 2 :=
          mul_le_mul_of_nonneg_left squareLe coefficientNonneg
    dsimp [slope, sourceOwnedLocalBarrierSlope]
    dsimp [ceiling] at rateLe ⊢
    linarith
  have halfLeBarrier :
      ∀ t ∈ Icc (0 : ℝ) b,
        halfEnstrophy t ≤ barrier t := by
    have initialBarrier : halfEnstrophy 0 ≤ barrier 0 := by
      simp [barrier]
    intro t tMem
    exact image_le_of_deriv_right_lt_deriv_boundary
      (f' := exactRate) (B := barrier) (B' := fun _ => slope)
      halfContinuous
      (fun time timeMem =>
        (halfDerivative time
          ⟨timeMem.1, timeMem.2.le⟩).hasDerivWithinAt)
      initialBarrier barrierDerivative boundaryRate tMem
  intro t tMem
  have halfLe := halfLeBarrier t tMem
  have tLeDuration : t ≤ duration := tMem.2.trans bLeDuration
  have denominatorPos : 0 < 2 * slope :=
    mul_pos (by norm_num) slopePos
  have scaledTimeLe : t * (2 * slope) ≤ 1 := by
    apply (le_div_iff₀ denominatorPos).mp
    rw [← durationEq]
    exact tLeDuration
  have fullLe :
      finiteStateVorticityCoefficientEnstrophy modes (trajectory t) ≤
        ceiling := by
    dsimp [halfEnstrophy, barrier] at halfLe
    dsimp [ceiling, sourceOwnedLocalEnstrophyCeiling]
    unfold finiteStateVorticityHalfEnstrophy at halfLe
    nlinarith
  exact
    ⟨by simpa [halfEnstrophy, barrier, slope] using halfLe,
      by simpa [ceiling] using fullLe⟩

/-- Full generated-time specialization of the local barrier. -/
theorem finiteStateVorticity_sourceOwnedLocalBarrier
    (modes : Finset IntegerWavevector)
    (negClosed :
      ∀ wave, wave ∈ modes → waveNeg wave ∈ modes)
    (ν : Viscosity)
    (trajectory : ℝ → ComplexVorticityHilbertState)
    (evolves :
      ∀ t ∈ Icc (0 : ℝ)
          (sourceOwnedLocalDuration ν modes (trajectory 0)),
        HasDerivAt trajectory
          (finiteStateVorticityGenerator
            modes ν.coeff (trajectory t)) t)
    (reality :
      ∀ t ∈ Icc (0 : ℝ)
          (sourceOwnedLocalDuration ν modes (trajectory 0)),
        FiniteStateFourierReality (trajectory t))
    (transverse :
      ∀ t ∈ Icc (0 : ℝ)
          (sourceOwnedLocalDuration ν modes (trajectory 0)),
        ∀ wave ∈ modes,
          complexWavevector wave ⬝ᵥ trajectory t wave = 0) :
    ∀ t ∈ Icc (0 : ℝ)
        (sourceOwnedLocalDuration ν modes (trajectory 0)),
      finiteStateVorticityHalfEnstrophy modes (trajectory t) ≤
          finiteStateVorticityHalfEnstrophy modes (trajectory 0) +
            sourceOwnedLocalBarrierSlope ν modes (trajectory 0) * t ∧
        finiteStateVorticityCoefficientEnstrophy
            modes (trajectory t) ≤
          sourceOwnedLocalEnstrophyCeiling modes (trajectory 0) := by
  exact finiteStateVorticity_sourceOwnedLocalBarrier_on_Icc
    modes negClosed ν trajectory
    (sourceOwnedLocalDuration ν modes (trajectory 0)) le_rfl
    evolves reality transverse

end


end
    ThreeDimensionalVorticityCoefficientSourceOwnedLocalKernelAbsorption
end NavierStokes
end SaturationMonoid
