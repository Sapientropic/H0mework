import H0mework.NavierStokes.Energy.ClosedEnstrophyTriad
import Mathlib.MeasureTheory.Integral.MeanInequalities
import H0mework.NavierStokes.Galerkin.EnstrophyBalance
import H0mework.NavierStokes.Galerkin.KineticEnergyLedger
import H0mework.NavierStokes.InitialData.FinitePhysicalStateRestart
import H0mework.NavierStokes.InitialData.StretchingPhysicalBridge

/-!
# Physical realization of the source-generated enstrophy-triad table

The complete signed vorticity support and complete ordered stretching table
generate every occurrence `(r, p, q)` before any scalar projection.  This
module realizes each row as the real scalar character

```text
Re ((omega_r dot B_(p,q)) exp (2 pi i (r + p + q) dot x)).
```

The resulting full table is exactly the physical enstrophy-stretching work.
The character product initially has sum- and difference-frequency halves;
negation of the testing-vorticity slot reindexes the second half on the same
source-owned table, so the final full-signed coefficient is one.

Only afterwards does physical-unit-cell integration project the table to its
zero-frequency rows.  No closure, reality, selected occurrence, nonvanishing,
or target-frequency witness is accepted at the theorem mouth.
-/

open MeasureTheory

namespace SaturationMonoid
namespace NavierStokes
namespace ThreeDimensionalVorticityCoefficientClosedEnstrophyPhysicalBridge

open scoped BigOperators Matrix

open Matrix
open ThreeDimensionalPeriodicCoarseFilterCore
open ThreeDimensionalPeriodicFullVorticityStretching
open ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicIntegerCharacterOrthogonality
open ThreeDimensionalPeriodicIntegerCharacterUnitCellMean
open ThreeDimensionalPeriodicLocalEnergyAlgebra
open ThreeDimensionalPeriodicUnitCellDivergence
open ThreeDimensionalVorticityCoefficientClosedEnstrophyTriad
open ThreeDimensionalVorticityCoefficientFiniteGalerkinEnstrophyBalance
open ThreeDimensionalVorticityCoefficientFiniteGalerkinKineticEnergyLedger
open ThreeDimensionalVorticityCoefficientFinitePhysicalStateRestart
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open ThreeDimensionalVorticityCoefficientFiniteSupportRealityTrajectory
open ThreeDimensionalVorticityCoefficientGeneratedShellViscousParseval
open ThreeDimensionalVorticityCoefficientPhysicalCompiler
open ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientStretchingPairTable
open ThreeDimensionalVorticityCoefficientStretchingPhysicalBridge

noncomputable section

/-! ## Whole occurrence table and its physical field -/

/-- The unfiltered source-owned table of all testing waves and stretching pairs. -/
def generatedEnstrophyTriadInventory
    (source : RawVorticityFourierSource) : Finset EnstrophyTriad :=
  generatedSupport source ×ˢ generatedStretchingPairTable source

@[simp] theorem mem_generatedEnstrophyTriadInventory_iff
    (source : RawVorticityFourierSource)
    (triad : EnstrophyTriad) :
    triad ∈ generatedEnstrophyTriadInventory source ↔
      triad.1 ∈ generatedSupport source ∧
        triad.2 ∈ generatedStretchingPairTable source := by
  simp [generatedEnstrophyTriadInventory]

/-- Occurrence-preserving physical scalar field of the complete triad table. -/
def generatedEnstrophyTriadPhysicalField
    (source : RawVorticityFourierSource) : PhysicalSpace → ℝ :=
  fun x =>
    ∑ triad ∈ generatedEnstrophyTriadInventory source,
      realComplexScalarFourierMode
        (enstrophyTriadFrequency triad)
        (closedEnstrophyTriadContribution source triad) x

/-! ## Exact pointwise realization -/

private theorem integerWavePhase_waveNeg
    (wave : IntegerWavevector) (x : PhysicalSpace) :
    integerWavePhase (waveNeg wave) x = -integerWavePhase wave x := by
  simp [integerWavePhase, waveNeg]

/-- The physical dot product of two real complex modes retains both Fourier
character channels and their exact complex bilinear coefficients. -/
private theorem velocityDot_realComplexFourierMode
    (first second : IntegerWavevector)
    (firstCoefficient secondCoefficient : ComplexCoordinateVector)
    (x : PhysicalSpace) :
    velocityDot
        (realComplexFourierMode first firstCoefficient)
        (realComplexFourierMode second secondCoefficient) x =
      (1 / 2 : ℝ) *
        (realComplexScalarFourierMode (first + second)
            (firstCoefficient ⬝ᵥ secondCoefficient) x +
          realComplexScalarFourierMode (waveNeg first + second)
            (vectorConj firstCoefficient ⬝ᵥ secondCoefficient) x) := by
  simp [velocityDot, realComplexFourierMode,
    realComplexScalarFourierMode, coefficientReal, coefficientImag,
    dotProduct, Fin.sum_univ_three,
    integerCosine, integerSine,
    integerWavePhase_wavevector_add,
    integerWavePhase_waveNeg,
    Real.cos_add, Real.sin_add,
    Real.cos_neg, Real.sin_neg,
    vectorConj]
  ring

/-- Negate only the testing-vorticity slot of an enstrophy occurrence. -/
private def enstrophyTriadTestingNeg
    (triad : EnstrophyTriad) : EnstrophyTriad :=
  (waveNeg triad.1, triad.2)

private theorem enstrophyTriadTestingNeg_involutive
    (triad : EnstrophyTriad) :
    enstrophyTriadTestingNeg (enstrophyTriadTestingNeg triad) = triad := by
  rcases triad with ⟨testing, pair⟩
  simp [enstrophyTriadTestingNeg]

private def enstrophyTriadTestingNegEquiv : EnstrophyTriad ≃ EnstrophyTriad where
  toFun := enstrophyTriadTestingNeg
  invFun := enstrophyTriadTestingNeg
  left_inv := enstrophyTriadTestingNeg_involutive
  right_inv := enstrophyTriadTestingNeg_involutive

private theorem mem_generatedEnstrophyTriadInventory_testingNeg_iff
    (source : RawVorticityFourierSource)
    (triad : EnstrophyTriad) :
    enstrophyTriadTestingNeg triad ∈
        generatedEnstrophyTriadInventory source ↔
      triad ∈ generatedEnstrophyTriadInventory source := by
  simp [enstrophyTriadTestingNeg]

private theorem enstrophyTriadFrequency_testingNeg
    (triad : EnstrophyTriad) :
    enstrophyTriadFrequency (enstrophyTriadTestingNeg triad) =
      waveNeg triad.1 + stretchingPairOutput triad.2 :=
  rfl

private theorem closedEnstrophyTriadContribution_testingNeg
    (source : RawVorticityFourierSource)
    (triad : EnstrophyTriad) :
    closedEnstrophyTriadContribution source
        (enstrophyTriadTestingNeg triad) =
      vectorConj (generatedVorticityCoefficient source triad.1) ⬝ᵥ
        generatedStretchingPairContribution source triad.2 := by
  rw [closedEnstrophyTriadContribution,
    enstrophyTriadTestingNeg,
    generatedVorticityCoefficient_waveNeg]

private theorem generatedEnstrophyTriadPhysicalField_testingNeg
    (source : RawVorticityFourierSource) :
    (fun x =>
      ∑ triad ∈ generatedEnstrophyTriadInventory source,
        realComplexScalarFourierMode
          (enstrophyTriadFrequency (enstrophyTriadTestingNeg triad))
          (closedEnstrophyTriadContribution source
            (enstrophyTriadTestingNeg triad)) x) =
      generatedEnstrophyTriadPhysicalField source := by
  funext x
  unfold generatedEnstrophyTriadPhysicalField
  refine Finset.sum_equiv enstrophyTriadTestingNegEquiv ?_ ?_
  · intro triad
    exact
      (mem_generatedEnstrophyTriadInventory_testingNeg_iff
        source triad).symm
  · intro triad membership
    rfl

private theorem velocityDot_physicalVorticity_generatedPairField_apply
    (source : RawVorticityFourierSource)
    (x : PhysicalSpace) :
    velocityDot (physicalVorticity source)
        (generatedStretchingPairField source) x =
      ∑ triad ∈ generatedEnstrophyTriadInventory source,
        velocityDot
          (realComplexFourierMode triad.1
            (generatedVorticityCoefficient source triad.1))
          (realComplexFourierMode (stretchingPairOutput triad.2)
            (generatedStretchingPairContribution source triad.2)) x := by
  unfold physicalVorticity finiteRealComplexFourierField
    generatedStretchingPairField generatedEnstrophyTriadInventory
    velocityDot
  rw [Finset.sum_product]
  simp only [Finset.sum_apply, WithLp.ofLp_sum]
  simp_rw [Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro testing testingMembership
  rw [Finset.sum_comm]

/-- The complete source-owned triad field is exactly the actual physical
enstrophy-stretching work.  The theorem has no side premise. -/
theorem enstrophyStretchingWork_physicalVelocity_eq_generatedTriadField
    (source : RawVorticityFourierSource) :
    enstrophyStretchingWork (physicalVelocity source) =
      generatedEnstrophyTriadPhysicalField source := by
  funext x
  rw [enstrophyStretchingWork,
    vorticityField_physicalVelocity,
    vortexStretching_physicalVelocity_eq_generatedPairField]
  rw [velocityDot_physicalVorticity_generatedPairField_apply]
  simp_rw [velocityDot_realComplexFourierMode]
  unfold generatedEnstrophyTriadPhysicalField
  rw [← Finset.mul_sum]
  simp only [Finset.sum_add_distrib]
  have testingNegSum :
      (∑ triad ∈ generatedEnstrophyTriadInventory source,
        realComplexScalarFourierMode
          (waveNeg triad.1 + stretchingPairOutput triad.2)
          (vectorConj (generatedVorticityCoefficient source triad.1) ⬝ᵥ
            generatedStretchingPairContribution source triad.2) x) =
        ∑ triad ∈ generatedEnstrophyTriadInventory source,
          realComplexScalarFourierMode
            (enstrophyTriadFrequency triad)
            (closedEnstrophyTriadContribution source triad) x := by
    simpa only [enstrophyTriadFrequency_testingNeg,
      closedEnstrophyTriadContribution_testingNeg,
      generatedEnstrophyTriadPhysicalField] using
      congrFun (generatedEnstrophyTriadPhysicalField_testingNeg source) x
  rw [testingNegSum]
  simp only [enstrophyTriadFrequency,
    closedEnstrophyTriadContribution]
  ring

/-! ## Unit-cell zero-frequency readout -/

private theorem integerCosine_integrableOn_physicalUnitCell
    (wave : IntegerWavevector) :
    IntegrableOn (integerCosine wave) physicalUnitCell :=
  (integerCosine_continuous wave).continuousOn.integrableOn_compact
    physicalUnitCell_isCompact

private theorem integerSine_integrableOn_physicalUnitCell
    (wave : IntegerWavevector) :
    IntegrableOn (integerSine wave) physicalUnitCell :=
  (integerSine_continuous wave).continuousOn.integrableOn_compact
    physicalUnitCell_isCompact

private theorem realComplexScalarFourierMode_integrableOn_physicalUnitCell
    (wave : IntegerWavevector) (coefficient : ℂ) :
    IntegrableOn
      (realComplexScalarFourierMode wave coefficient)
      physicalUnitCell := by
  unfold realComplexScalarFourierMode
  exact
    ((integerCosine_integrableOn_physicalUnitCell wave).mul_const _).sub
      ((integerSine_integrableOn_physicalUnitCell wave).mul_const _)

/-- Unit-cell integration of one real complex character is its real
zero-frequency coefficient and vanishes otherwise. -/
private theorem physicalUnitCell_realComplexScalarFourierMode_integral
    (wave : IntegerWavevector) (coefficient : ℂ) :
    (∫ x in physicalUnitCell,
      realComplexScalarFourierMode wave coefficient x) =
      if wave = 0 then coefficient.re else 0 := by
  have cosineIntegrable :=
    integerCosine_integrableOn_physicalUnitCell wave
  have sineIntegrable :=
    integerSine_integrableOn_physicalUnitCell wave
  rw [show realComplexScalarFourierMode wave coefficient =
      fun x =>
        coefficient.re * integerCosine wave x -
          coefficient.im * integerSine wave x by
        funext x
        simp [realComplexScalarFourierMode]
        ring]
  rw [integral_sub
      (cosineIntegrable.const_mul coefficient.re)
      (sineIntegrable.const_mul coefficient.im),
    integral_const_mul, integral_const_mul,
    physicalUnitCell_integerCosine_integral,
    physicalUnitCell_integerSine_integral]
  by_cases frequencyZero : wave = 0
  · simp [frequencyZero]
  · simp [frequencyZero]

/-- The ordinary unit-cell observer keeps exactly the generated closed
zero-frequency triads, with full-signed normalization one. -/
theorem physicalUnitCell_generatedEnstrophyTriadPhysicalField_integral
    (source : RawVorticityFourierSource) :
    (∫ x in physicalUnitCell,
      generatedEnstrophyTriadPhysicalField source x) =
      (generatedEnstrophyZeroFrequencyCoefficient source).re := by
  unfold generatedEnstrophyTriadPhysicalField
  rw [integral_finsetSum
    (generatedEnstrophyTriadInventory source)
    (fun triad _ =>
      realComplexScalarFourierMode_integrableOn_physicalUnitCell
        (enstrophyTriadFrequency triad)
        (closedEnstrophyTriadContribution source triad))]
  simp_rw [physicalUnitCell_realComplexScalarFourierMode_integral]
  rw [generatedEnstrophyZeroFrequencyCoefficient,
    generatedClosedEnstrophyTriadInventory,
    generatedEnstrophyTriadInventory,
    Finset.sum_filter]
  rw [Complex.re_sum]
  apply Finset.sum_congr rfl
  intro triad triadMembership
  by_cases frequencyZero : enstrophyTriadFrequency triad = 0
  · simp [frequencyZero]
  · simp [frequencyZero]

/-- Physical enstrophy-stretching work has exactly the same closed-triad
zero-frequency unit-cell readout. -/
theorem physicalUnitCell_enstrophyStretchingWork_physicalVelocity_integral
    (source : RawVorticityFourierSource) :
    (∫ x in physicalUnitCell,
      enstrophyStretchingWork (physicalVelocity source) x) =
      (generatedEnstrophyZeroFrequencyCoefficient source).re := by
  rw [enstrophyStretchingWork_physicalVelocity_eq_generatedTriadField]
  exact
    physicalUnitCell_generatedEnstrophyTriadPhysicalField_integral source

/-- Since the generated closed-triad coefficient is real, the real physical
unit-cell readout casts back to the exact complex coefficient. -/
theorem physicalUnitCell_enstrophyStretchingWork_physicalVelocity_integral_cast
    (source : RawVorticityFourierSource) :
    (((∫ x in physicalUnitCell,
      enstrophyStretchingWork (physicalVelocity source) x) : ℝ) : ℂ) =
      generatedEnstrophyZeroFrequencyCoefficient source := by
  rw [physicalUnitCell_enstrophyStretchingWork_physicalVelocity_integral]
  apply Complex.ext
  · simp
  · simpa using
      (generatedEnstrophyZeroFrequencyCoefficient_im_eq_zero source).symm

/-! ## Finite physical state splice -/

private theorem rawFiniteSource_generatedVorticityCoefficient_eq
    (modes : Finset IntegerWavevector)
    (zeroNotMem : 0 ∉ modes)
    (negClosed : ∀ wave, wave ∈ modes → waveNeg wave ∈ modes)
    (state : ComplexVorticityHilbertState)
    (supported : ∀ wave, wave ∉ modes → state wave = 0)
    (transverse : ∀ wave ∈ modes,
      complexWavevector wave ⬝ᵥ state wave = 0)
    (reality : FiniteStateFourierReality state)
    (wave : IntegerWavevector) :
    generatedVorticityCoefficient
        (rawSourceOfFiniteVorticityState modes state) wave =
      state wave := by
  let source := rawSourceOfFiniteVorticityState modes state
  have supportEq : generatedSupport source = modes := by
    simpa only [source] using
      rawSourceOfFiniteVorticityState_generatedSupport
        modes zeroNotMem negClosed state
  have compiledEq :=
    generatedComplexVorticityState_rawSourceOfFinitePhysicalState
      modes zeroNotMem negClosed state supported transverse reality
  by_cases waveMem : wave ∈ modes
  · have supportMem : wave ∈ generatedSupport source := by
      simpa only [supportEq] using waveMem
    have applied := congrArg
      (fun compiled : ComplexVorticityHilbertState => compiled wave)
      compiledEq
    simpa only [source, generatedComplexVorticityState_apply,
      if_pos supportMem] using applied
  · rw [generatedVorticityCoefficient_eq_zero_of_not_mem]
    · exact (supported wave waveMem).symm
    · simpa only [source, supportEq] using waveMem

private theorem rawFiniteSource_generatedVelocityCoefficient_eq
    (modes : Finset IntegerWavevector)
    (zeroNotMem : 0 ∉ modes)
    (negClosed : ∀ wave, wave ∈ modes → waveNeg wave ∈ modes)
    (state : ComplexVorticityHilbertState)
    (supported : ∀ wave, wave ∉ modes → state wave = 0)
    (transverse : ∀ wave ∈ modes,
      complexWavevector wave ⬝ᵥ state wave = 0)
    (reality : FiniteStateFourierReality state)
    (wave : IntegerWavevector) :
    generatedVelocityCoefficient
        (rawSourceOfFiniteVorticityState modes state) wave =
      finiteStateVelocityCoefficient state wave := by
  unfold generatedVelocityCoefficient finiteStateVelocityCoefficient
  rw [rawFiniteSource_generatedVorticityCoefficient_eq
    modes zeroNotMem negClosed state supported transverse reality wave]

private theorem rawFiniteSource_generatedStretchingPairContribution_eq
    (modes : Finset IntegerWavevector)
    (zeroNotMem : 0 ∉ modes)
    (negClosed : ∀ wave, wave ∈ modes → waveNeg wave ∈ modes)
    (state : ComplexVorticityHilbertState)
    (supported : ∀ wave, wave ∉ modes → state wave = 0)
    (transverse : ∀ wave ∈ modes,
      complexWavevector wave ⬝ᵥ state wave = 0)
    (reality : FiniteStateFourierReality state)
    (pair : StretchingPair) :
    generatedStretchingPairContribution
        (rawSourceOfFiniteVorticityState modes state) pair =
      finiteStateVorticityStretchingPairContribution state pair := by
  unfold generatedStretchingPairContribution
    finiteStateVorticityStretchingPairContribution
  rw [rawFiniteSource_generatedVorticityCoefficient_eq
      modes zeroNotMem negClosed state supported transverse reality pair.1,
    rawFiniteSource_generatedVelocityCoefficient_eq
      modes zeroNotMem negClosed state supported transverse reality pair.2]

private def finiteStateVorticityStretchingCoefficientAt
    (modes : Finset IntegerWavevector)
    (state : ComplexVorticityHilbertState)
    (output : IntegerWavevector) : ComplexCoordinateVector :=
  ∑ first ∈ modes, ∑ second ∈ modes,
    if first + second = output then
      finiteStateVorticityStretchingPairContribution state (first, second)
    else 0

private theorem rawFiniteSource_generatedStretchingCoefficientAt_eq
    (modes : Finset IntegerWavevector)
    (zeroNotMem : 0 ∉ modes)
    (negClosed : ∀ wave, wave ∈ modes → waveNeg wave ∈ modes)
    (state : ComplexVorticityHilbertState)
    (supported : ∀ wave, wave ∉ modes → state wave = 0)
    (transverse : ∀ wave ∈ modes,
      complexWavevector wave ⬝ᵥ state wave = 0)
    (reality : FiniteStateFourierReality state)
    (output : IntegerWavevector) :
    generatedStretchingCoefficientAt
        (rawSourceOfFiniteVorticityState modes state) output =
      finiteStateVorticityStretchingCoefficientAt modes state output := by
  rw [generatedStretchingCoefficientAt_eq_fullPairTableSum]
  unfold generatedStretchingPairTable
  rw [rawSourceOfFiniteVorticityState_generatedSupport
    modes zeroNotMem negClosed state]
  rw [Finset.sum_product]
  unfold finiteStateVorticityStretchingCoefficientAt
  apply Finset.sum_congr rfl
  intro first firstMem
  apply Finset.sum_congr rfl
  intro second secondMem
  by_cases outputEq : first + second = output
  · simp only [stretchingPairOutput, outputEq, if_true]
    exact rawFiniteSource_generatedStretchingPairContribution_eq
      modes zeroNotMem negClosed state supported transverse reality
        (first, second)
  · simp [stretchingPairOutput, outputEq]

private theorem finiteStateVorticityStretchingWork_eq_outer_sum
    (modes : Finset IntegerWavevector)
    (state : ComplexVorticityHilbertState) :
    finiteStateVorticityStretchingWork modes state =
      ∑ output ∈ modes,
        complexCoordinateRealInner (state output)
          (finiteStateVorticityStretchingCoefficientAt modes state output) := by
  unfold finiteStateVorticityStretchingWork
    finiteVorticityInteractionInventory
  rw [Finset.sum_filter, Finset.sum_product, Finset.sum_product]
  unfold finiteStateVorticityStretchingCoefficientAt
    finiteStateVorticityStretchingOccurrenceWork
    finiteVorticityInteractionOutput finiteVorticityInteractionFirst
    finiteVorticityInteractionSecond
  apply Finset.sum_congr rfl
  intro output outputMem
  rw [complexCoordinateRealInner_sum_right]
  apply Finset.sum_congr rfl
  intro first firstMem
  rw [complexCoordinateRealInner_sum_right]
  apply Finset.sum_congr rfl
  intro second secondMem
  by_cases outputEq : first + second = output
  · simp only [outputEq, if_true]
  · simp [outputEq, complexCoordinateRealInner_zero_right]

private theorem rawFiniteSource_generatedEnstrophyZeroFrequency_re_eq
    (modes : Finset IntegerWavevector)
    (zeroNotMem : 0 ∉ modes)
    (negClosed : ∀ wave, wave ∈ modes → waveNeg wave ∈ modes)
    (state : ComplexVorticityHilbertState)
    (supported : ∀ wave, wave ∉ modes → state wave = 0)
    (transverse : ∀ wave ∈ modes,
      complexWavevector wave ⬝ᵥ state wave = 0)
    (reality : FiniteStateFourierReality state) :
    (generatedEnstrophyZeroFrequencyCoefficient
      (rawSourceOfFiniteVorticityState modes state)).re =
        finiteStateVorticityStretchingWork modes state := by
  let source := rawSourceOfFiniteVorticityState modes state
  have supportEq : generatedSupport source = modes := by
    simpa only [source] using
      rawSourceOfFiniteVorticityState_generatedSupport
        modes zeroNotMem negClosed state
  rw [generatedEnstrophyZeroFrequencyCoefficient_eq_outer_sum]
  rw [supportEq]
  simp_rw [rawFiniteSource_generatedVorticityCoefficient_eq
    modes zeroNotMem negClosed state supported transverse reality]
  simp_rw [rawFiniteSource_generatedStretchingCoefficientAt_eq
    modes zeroNotMem negClosed state supported transverse reality]
  rw [Complex.re_sum]
  rw [finiteStateVorticityStretchingWork_eq_outer_sum]
  refine Finset.sum_bij (fun testing _ => waveNeg testing) ?_ ?_ ?_ ?_
  · intro testing testingMem
    exact negClosed testing testingMem
  · intro left leftMem right rightMem negEq
    simpa using congrArg waveNeg negEq
  · intro output outputMem
    exact ⟨waveNeg output, negClosed output outputMem, by simp⟩
  · intro testing testingMem
    rw [complexCoordinateRealInner_eq_re_dot]
    have realityAt := reality (waveNeg testing)
    simpa using congrArg
      (fun vector : ComplexCoordinateVector =>
        (vector ⬝ᵥ
          finiteStateVorticityStretchingCoefficientAt modes state
            (waveNeg testing)).re)
      realityAt

/-- Recompiling a finite physical state as a raw source preserves its
physical vorticity field exactly. -/
theorem physicalVorticity_rawSourceOfFinitePhysicalState_eq
    (modes : Finset IntegerWavevector)
    (zeroNotMem : 0 ∉ modes)
    (negClosed : ∀ wave, wave ∈ modes → waveNeg wave ∈ modes)
    (state : ComplexVorticityHilbertState)
    (supported : ∀ wave, wave ∉ modes → state wave = 0)
    (transverse : ∀ wave ∈ modes,
      complexWavevector wave ⬝ᵥ state wave = 0)
    (reality : FiniteStateFourierReality state) :
    physicalVorticity (rawSourceOfFiniteVorticityState modes state) =
      finiteRealComplexFourierField modes state := by
  unfold physicalVorticity
  rw [rawSourceOfFiniteVorticityState_generatedSupport
    modes zeroNotMem negClosed state]
  congr 1
  funext wave
  exact rawFiniteSource_generatedVorticityCoefficient_eq
    modes zeroNotMem negClosed state supported transverse reality wave

/-- The signed finite-state stretching work is the exact unit-cell physical
vortex-stretching integral of the canonically recompiled source. -/
theorem physicalUnitCell_enstrophyStretchingWork_rawFiniteSource_integral
    (modes : Finset IntegerWavevector)
    (zeroNotMem : 0 ∉ modes)
    (negClosed : ∀ wave, wave ∈ modes → waveNeg wave ∈ modes)
    (state : ComplexVorticityHilbertState)
    (supported : ∀ wave, wave ∉ modes → state wave = 0)
    (transverse : ∀ wave ∈ modes,
      complexWavevector wave ⬝ᵥ state wave = 0)
    (reality : FiniteStateFourierReality state) :
    (∫ x in physicalUnitCell,
      enstrophyStretchingWork
        (physicalVelocity
          (rawSourceOfFiniteVorticityState modes state)) x) =
      finiteStateVorticityStretchingWork modes state := by
  rw [physicalUnitCell_enstrophyStretchingWork_physicalVelocity_integral]
  exact rawFiniteSource_generatedEnstrophyZeroFrequency_re_eq
    modes zeroNotMem negClosed state supported transverse reality

/-- Exact physical Cauchy--Schwarz turns nonzero signed finite-state
stretching into a scale-critical vorticity `L⁴` demand. -/
theorem finiteStateVorticityStretchingWork_abs_le_physicalL4
    (modes : Finset IntegerWavevector)
    (zeroNotMem : 0 ∉ modes)
    (negClosed : ∀ wave, wave ∈ modes → waveNeg wave ∈ modes)
    (state : ComplexVorticityHilbertState)
    (supported : ∀ wave, wave ∉ modes → state wave = 0)
    (transverse : ∀ wave ∈ modes,
      complexWavevector wave ⬝ᵥ state wave = 0)
    (reality : FiniteStateFourierReality state) :
    |finiteStateVorticityStretchingWork modes state| ≤
      Real.sqrt
          (∫ x in physicalUnitCell,
            ‖finiteRealComplexFourierField modes state x‖ ^ 4) *
        Real.sqrt
          (finiteStateVorticityCoefficientEnstrophy modes state) := by
  let source := rawSourceOfFiniteVorticityState modes state
  let u := physicalVelocity source
  let omega := physicalVorticity source
  let f : PhysicalSpace → Real := fun x => ‖omega x‖ ^ 2
  let g : PhysicalSpace → Real := fun x =>
    Real.sqrt (gradientDissipation u x)
  let μ := volume.restrict physicalUnitCell
  have omegaContinuous : Continuous omega :=
    (physicalVorticity_contDiff source).continuous
  have uSmooth := physicalVelocity_contDiff source
  have gradientContinuous :
      Continuous (fun x => gradientDissipation u x) := by
    unfold gradientDissipation
    have derivativeContinuous : Continuous (fderiv ℝ u) :=
      uSmooth.continuous_fderiv (by simp)
    fun_prop
  have fContinuous : Continuous f := by
    exact omegaContinuous.norm.pow 2
  have gContinuous : Continuous g := by
    exact Real.continuous_sqrt.comp gradientContinuous
  have fSqIntegrable : Integrable (fun x => f x ^ 2) μ := by
    change IntegrableOn (fun x => f x ^ 2) physicalUnitCell volume
    exact (fContinuous.pow 2).continuousOn.integrableOn_compact
      physicalUnitCell_isCompact
  have gSqIntegrable : Integrable (fun x => g x ^ 2) μ := by
    change IntegrableOn (fun x => g x ^ 2) physicalUnitCell volume
    exact (gContinuous.pow 2).continuousOn.integrableOn_compact
      physicalUnitCell_isCompact
  have fMemLpNat : MemLp f 2 μ :=
    (memLp_two_iff_integrable_sq fContinuous.aestronglyMeasurable).mpr
      fSqIntegrable
  have gMemLpNat : MemLp g 2 μ :=
    (memLp_two_iff_integrable_sq gContinuous.aestronglyMeasurable).mpr
      gSqIntegrable
  have fMemLp : MemLp f (ENNReal.ofReal (2 : Real)) μ := by
    simpa using fMemLpNat
  have gMemLp : MemLp g (ENNReal.ofReal (2 : Real)) μ := by
    simpa using gMemLpNat
  have cauchy :=
    integral_mul_le_Lp_mul_Lq_of_nonneg
      Real.HolderConjugate.two_two
      (μ := μ) (f := f) (g := g)
      (Filter.Eventually.of_forall fun x => sq_nonneg ‖omega x‖)
      (Filter.Eventually.of_forall fun x => Real.sqrt_nonneg _)
      fMemLp gMemLp
  have cauchySqrt :
      (∫ x in physicalUnitCell, f x * g x) ≤
        Real.sqrt (∫ x in physicalUnitCell, f x ^ 2) *
          Real.sqrt (∫ x in physicalUnitCell, g x ^ 2) := by
    change (∫ x, f x * g x ∂μ) ≤ _
    norm_num [Real.sqrt_eq_rpow] at cauchy ⊢
    exact cauchy
  have pointwise (x : PhysicalSpace) :
      |enstrophyStretchingWork u x| ≤ f x * g x := by
    have raw :=
      enstrophyStretchingWork_abs_le_vorticitySq_mul_sqrt_gradientDissipation
        u x
    rw [show vorticityField u = omega by
      simpa only [u, omega] using vorticityField_physicalVelocity source] at raw
    calc
      |enstrophyStretchingWork u x| ≤
          velocityDot omega omega x *
            Real.sqrt (gradientDissipation u x) := raw
      _ = f x * g x := by
        dsimp only [f, g]
        rw [EuclideanSpace.real_norm_sq_eq]
        unfold velocityDot
        congr 1
        apply Finset.sum_congr rfl
        intro coordinate coordinateMem
        ring
  have stretchingIntegrable :
      IntegrableOn (fun x => |enstrophyStretchingWork u x|)
        physicalUnitCell volume := by
    have triadIntegrable :
        IntegrableOn (generatedEnstrophyTriadPhysicalField source)
          physicalUnitCell volume := by
      unfold generatedEnstrophyTriadPhysicalField
      exact integrable_finsetSum
        (generatedEnstrophyTriadInventory source)
        (fun triad _ =>
          realComplexScalarFourierMode_integrableOn_physicalUnitCell
            (enstrophyTriadFrequency triad)
            (closedEnstrophyTriadContribution source triad))
    have base :
        IntegrableOn (fun x => enstrophyStretchingWork u x)
          physicalUnitCell volume := by
      simpa only [u,
        enstrophyStretchingWork_physicalVelocity_eq_generatedTriadField] using
        triadIntegrable
    exact base.abs
  have productIntegrable :
      IntegrableOn (fun x => f x * g x) physicalUnitCell volume :=
    (fContinuous.mul gContinuous).continuousOn.integrableOn_compact
      physicalUnitCell_isCompact
  have absoluteToProduct :
      (∫ x in physicalUnitCell, |enstrophyStretchingWork u x|) ≤
        ∫ x in physicalUnitCell, f x * g x :=
    setIntegral_mono_on stretchingIntegrable productIntegrable
      physicalUnitCell_isCompact.measurableSet (fun x _ => pointwise x)
  have integralToProduct :
      |∫ x in physicalUnitCell, enstrophyStretchingWork u x| ≤
        ∫ x in physicalUnitCell, f x * g x :=
    abs_integral_le_integral_abs.trans absoluteToProduct
  have gradientIntegral :
      (∫ x in physicalUnitCell, g x ^ 2) =
        finiteStateVorticityCoefficientEnstrophy modes state := by
    have sqrtSq (x : PhysicalSpace) :
        g x ^ 2 = gradientDissipation u x := by
      dsimp only [g]
      rw [Real.sq_sqrt]
      unfold gradientDissipation
      positivity
    simp_rw [sqrtSq]
    rw [physicalUnitCell_physicalVelocity_gradient_eq_vorticityNormSq]
    unfold finiteStateVorticityCoefficientEnstrophy
    rw [rawSourceOfFiniteVorticityState_generatedSupport
      modes zeroNotMem negClosed state]
    apply Finset.sum_congr rfl
    intro wave waveMem
    rw [rawFiniteSource_generatedVorticityCoefficient_eq
      modes zeroNotMem negClosed state supported transverse reality]
    simp only [
      ThreeDimensionalVorticityCoefficientGeneratedShellSerrinGeometry.complexCoordinateAmplitudeSq_eq_complexCoordinateVectorNormSq]
  have vorticityIntegral :
      (∫ x in physicalUnitCell, f x ^ 2) =
        ∫ x in physicalUnitCell,
          ‖finiteRealComplexFourierField modes state x‖ ^ 4 := by
    have omegaEq :
        omega = finiteRealComplexFourierField modes state := by
      simpa only [omega, source] using
        physicalVorticity_rawSourceOfFinitePhysicalState_eq
          modes zeroNotMem negClosed state supported transverse reality
    apply setIntegral_congr_fun physicalUnitCell_isCompact.measurableSet
    intro x xMem
    dsimp only [f]
    rw [omegaEq]
    ring
  rw [← physicalUnitCell_enstrophyStretchingWork_rawFiniteSource_integral
    modes zeroNotMem negClosed state supported transverse reality]
  change |∫ x in physicalUnitCell, enstrophyStretchingWork u x| ≤ _
  rw [← vorticityIntegral, ← gradientIntegral]
  exact integralToProduct.trans cauchySqrt

end

end ThreeDimensionalVorticityCoefficientClosedEnstrophyPhysicalBridge
end NavierStokes
end SaturationMonoid
