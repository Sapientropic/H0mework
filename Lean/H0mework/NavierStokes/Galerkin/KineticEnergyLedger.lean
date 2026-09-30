import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import H0mework.NavierStokes.InitialData.FiniteSupportRealityTrajectory

/-!
# Kinetic-energy ledger for the finite three-dimensional vorticity Galerkin flow

This module proves the kinetic-energy cancellation and viscous ledger for the
actual finite vorticity generator.  The algebra is uniform in a finite,
zero-free, negation-closed Fourier inventory.  Reality, transversality, and
sharp support are state invariants; no energy inequality is accepted as a
premise.

The nonlinear proof does not inspect a fixed triad.  It first reconstructs
the velocity convection coefficient whose curl is the complete ordered-pair
vorticity coefficient.  The remaining energy sum is reindexed by the
source-free triad involution

```text
q ↦ -p-q.
```

The two terms cancel because the advecting velocity row is transverse.
-/

namespace SaturationMonoid
namespace NavierStokes
namespace ThreeDimensionalVorticityCoefficientFiniteGalerkinKineticEnergyLedger

open scoped BigOperators Matrix Topology Interval

open Set
open Matrix
open MeasureTheory
open ThreeDimensionalPeriodicCoarseFilterCore
open ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open ThreeDimensionalVorticityCoefficientFiniteSupportPhysicalInvariantTrajectory
open ThreeDimensionalVorticityCoefficientFiniteSupportRealityTrajectory
open ThreeDimensionalVorticityCoefficientGeneratedShellViscousParseval
open ThreeDimensionalVorticityCoefficientCoarseFilterProcess
open ThreeDimensionalVorticityCoefficientStretchingPairTable

noncomputable section

/-! ## Finite physical carrier invariants -/

/-- A finite Fourier inventory is closed under the physical reality
involution. -/
def FiniteModeNegClosed
    (modes : Finset IntegerWavevector) : Prop :=
  ∀ wave, wave ∈ modes → waveNeg wave ∈ modes

/-- Reality of an arbitrary coefficient state on one finite inventory. -/
def FiniteStateRealityOn
    (modes : Finset IntegerWavevector)
    (state : ComplexVorticityHilbertState) : Prop :=
  ∀ wave, wave ∈ modes →
    state (waveNeg wave) = vectorConj (state wave)

theorem finiteModeNegClosed_mem_iff
    {modes : Finset IntegerWavevector}
    (negClosed : FiniteModeNegClosed modes)
    (wave : IntegerWavevector) :
    waveNeg wave ∈ modes ↔ wave ∈ modes := by
  constructor
  · intro negMem
    simpa using negClosed (waveNeg wave) negMem
  · exact negClosed wave

/-- Biot--Savart velocity preserves a supplied reality row. -/
theorem finiteStateVelocityCoefficient_waveNeg
    {state : ComplexVorticityHilbertState}
    {wave : IntegerWavevector}
    (reality :
      state (waveNeg wave) = vectorConj (state wave)) :
    finiteStateVelocityCoefficient state (waveNeg wave) =
      vectorConj (finiteStateVelocityCoefficient state wave) := by
  unfold finiteStateVelocityCoefficient
  rw [reality,
    biotSavartVelocityCoefficient_waveNeg_vectorConj]

/-! ## Real Hermitian pairing -/

/-- The coordinate real pairing is the real part of the Hermitian pairing. -/
theorem complexCoordinateRealInner_eq_re_dot
    (left right : ComplexCoordinateVector) :
    complexCoordinateRealInner left right =
      (vectorConj left ⬝ᵥ right).re := by
  unfold complexCoordinateRealInner dotProduct
  change
    (∑ coordinate : Coordinate,
      ((left coordinate).re * (right coordinate).re +
        (left coordinate).im * (right coordinate).im)) =
      ∑ coordinate : Coordinate,
        (vectorConj left coordinate * right coordinate).re
  apply Finset.sum_congr rfl
  intro coordinate _
  simp [vectorConj]

theorem complexCoordinateRealInner_zero_right
    (left : ComplexCoordinateVector) :
    complexCoordinateRealInner left 0 = 0 := by
  simp [complexCoordinateRealInner]

theorem complexCoordinateRealInner_add_right
    (left right₁ right₂ : ComplexCoordinateVector) :
    complexCoordinateRealInner left (right₁ + right₂) =
      complexCoordinateRealInner left right₁ +
        complexCoordinateRealInner left right₂ := by
  unfold complexCoordinateRealInner
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro coordinate _
  simp only [Pi.add_apply, Complex.add_re, Complex.add_im]
  ring

theorem complexCoordinateRealInner_sub_right
    (left right₁ right₂ : ComplexCoordinateVector) :
    complexCoordinateRealInner left (right₁ - right₂) =
      complexCoordinateRealInner left right₁ -
        complexCoordinateRealInner left right₂ := by
  unfold complexCoordinateRealInner
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro coordinate _
  simp only [Pi.sub_apply, Complex.sub_re, Complex.sub_im]
  ring

theorem complexCoordinateRealInner_sum_right
    {ι : Type*}
    (index : Finset ι)
    (left : ComplexCoordinateVector)
    (right : ι → ComplexCoordinateVector) :
    complexCoordinateRealInner left (∑ i ∈ index, right i) =
      ∑ i ∈ index, complexCoordinateRealInner left (right i) := by
  classical
  induction index using Finset.induction_on with
  | empty =>
      simp [complexCoordinateRealInner_zero_right]
  | @insert item tail itemNotMem inductionHypothesis =>
      rw [Finset.sum_insert itemNotMem,
        complexCoordinateRealInner_add_right,
        inductionHypothesis,
        Finset.sum_insert itemNotMem]

theorem complexCoordinateRealInner_real_smul_right
    (left right : ComplexCoordinateVector)
    (scalar : ℝ) :
    complexCoordinateRealInner left (scalar • right) =
      scalar * complexCoordinateRealInner left right := by
  rw [complexCoordinateRealInner_eq_re_dot,
    complexCoordinateRealInner_eq_re_dot]
  change
    (vectorConj left ⬝ᵥ
        ((scalar : ℂ) • right)).re =
      scalar * (vectorConj left ⬝ᵥ right).re
  rw [dotProduct_smul]
  simp

/-- A transverse row is orthogonal, in the real Hermitian pairing, to the
longitudinal part removed by the finite Hodge projection. -/
theorem complexCoordinateRealInner_transverseProjection
    (wave : IntegerWavevector)
    (left right : ComplexCoordinateVector)
    (waveNe : wave ≠ 0)
    (leftTransverse :
      complexWavevector wave ⬝ᵥ left = 0) :
    complexCoordinateRealInner left
        (transverseProjection wave right) =
      complexCoordinateRealInner left right := by
  rw [complexCoordinateRealInner_eq_re_dot,
    complexCoordinateRealInner_eq_re_dot,
    transverseProjection, if_neg waveNe,
    dotProduct_sub, dotProduct_smul]
  have conjugateTransverse :
      vectorConj left ⬝ᵥ complexWavevector wave = 0 := by
    rw [dotProduct_comm,
      complexWavevector_dot_vectorConj,
      leftTransverse]
    simp
  rw [conjugateTransverse]
  simp

/-! ## Generic finite Hodge identities -/

/-- Curl followed by Biot--Savart recovers every nonzero transverse row. -/
theorem fourierCurlCoefficient_biotSavartVelocityCoefficient_of_transverse
    (wave : IntegerWavevector)
    (vorticity : ComplexCoordinateVector)
    (waveNe : wave ≠ 0)
    (transverse :
      complexWavevector wave ⬝ᵥ vorticity = 0) :
    fourierCurlCoefficient wave
        (biotSavartVelocityCoefficient wave vorticity) =
      vorticity := by
  have normSqComplexNe :
      (integerWaveNormSq wave : ℂ) ≠ 0 := by
    exact_mod_cast integerWaveNormSq_ne_zero waveNe
  have twoPiNormSqNe :
      2 * Real.pi * integerWaveNormSq wave ≠ 0 := by
    have normSqPos := integerWaveNormSq_pos waveNe
    positivity
  rw [fourierCurlCoefficient,
    biotSavartVelocityCoefficient, if_neg waveNe,
    map_smul, cross_cross_eq_smul_sub_smul',
    transverse, complexWavevector_dot_self]
  simp only [zero_smul, zero_sub]
  simp only [smul_smul, ← neg_smul]
  rw [← one_smul ℂ vorticity]
  congr 1
  push_cast
  field_simp [twoPiNormSqNe]
  all_goals simp

/-- Biot--Savart after curl is exactly the transverse projection. -/
theorem biotSavartVelocityCoefficient_fourierCurlCoefficient
    (wave : IntegerWavevector)
    (velocity : ComplexCoordinateVector)
    (waveNe : wave ≠ 0) :
    biotSavartVelocityCoefficient wave
        (fourierCurlCoefficient wave velocity) =
      transverseProjection wave velocity := by
  have normSqComplexNe :
      (integerWaveNormSq wave : ℂ) ≠ 0 := by
    exact_mod_cast integerWaveNormSq_ne_zero waveNe
  have twoPiNormSqNe :
      2 * Real.pi * integerWaveNormSq wave ≠ 0 := by
    have normSqPos := integerWaveNormSq_pos waveNe
    positivity
  rw [biotSavartVelocityCoefficient, if_neg waveNe,
    fourierCurlCoefficient, map_smul,
    cross_cross_eq_smul_sub_smul',
    transverseProjection, if_neg waveNe,
    complexWavevector_dot_self]
  funext coordinate
  simp only [Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
  push_cast
  field_simp [twoPiNormSqNe]
  norm_num [pow_two]

/-! ## Velocity convection reconstructed from the vorticity carrier -/

/-- One ordered velocity convection row
`-(u_p · ∇) u_q` in Fourier coordinates. -/
def finiteStateVelocityNonlinearPairContribution
    (state : ComplexVorticityHilbertState)
    (pair : IntegerWavevector × IntegerWavevector) :
    ComplexCoordinateVector :=
  -((Complex.I * (((2 * Real.pi : ℝ) : ℂ))) *
      (complexWavevector pair.2 ⬝ᵥ
        finiteStateVelocityCoefficient state pair.1)) •
    finiteStateVelocityCoefficient state pair.2

/-- Complete finite velocity convection coefficient at one output wave. -/
def finiteStateVelocityNonlinearCoefficientAt
    (modes : Finset IntegerWavevector)
    (state : ComplexVorticityHilbertState)
    (output : IntegerWavevector) :
    ComplexCoordinateVector :=
  ∑ first ∈ modes,
    ∑ second ∈ modes,
      if first + second = output then
        finiteStateVelocityNonlinearPairContribution
          state (first, second)
      else 0

/-- On a nonzero transverse row, the state is the curl of its
Biot--Savart velocity coefficient. -/
theorem fourierCurlCoefficient_finiteStateVelocityCoefficient
    (state : ComplexVorticityHilbertState)
    (wave : IntegerWavevector)
    (waveNe : wave ≠ 0)
    (transverse :
      complexWavevector wave ⬝ᵥ state wave = 0) :
    fourierCurlCoefficient wave
        (finiteStateVelocityCoefficient state wave) =
      state wave := by
  exact
    fourierCurlCoefficient_biotSavartVelocityCoefficient_of_transverse
      wave (state wave) waveNe transverse

/-- Polynomial four-vector identity behind the symmetrized curl of
convection. -/
theorem convectionCurlCoreIdentity
    (firstWave secondWave firstVelocity secondVelocity :
      ComplexCoordinateVector) :
    (secondWave ⬝ᵥ firstVelocity) •
          (firstWave ⨯₃ secondVelocity) +
        (firstWave ⬝ᵥ secondVelocity) •
          (secondWave ⨯₃ firstVelocity) +
        (secondWave ⬝ᵥ
            (firstWave ⨯₃ firstVelocity)) •
          secondVelocity +
        (firstWave ⬝ᵥ
            (secondWave ⨯₃ secondVelocity)) •
          firstVelocity =
      (firstWave ⬝ᵥ firstVelocity) •
          (secondWave ⨯₃ secondVelocity) +
        (secondWave ⬝ᵥ secondVelocity) •
          (firstWave ⨯₃ firstVelocity) := by
  simp_rw [cross_apply, vec3_dotProduct]
  ext coordinate
  fin_cases coordinate <;>
    simp only [Fin.isValue, Nat.succ_eq_add_one,
      Nat.reduceAdd, Fin.reduceFinMk, cons_val,
      Pi.add_apply, Pi.smul_apply, smul_eq_mul] <;>
    ring

private theorem complexWavevector_add
    (first second : IntegerWavevector) :
    complexWavevector (first + second) =
      complexWavevector first + complexWavevector second := by
  funext coordinate
  simp [complexWavevector]

/--
The two ordered convection rows of one input pair have curl equal to the two
ordered vorticity rows.  Pair symmetrization is essential: the statement is
false for one ordered row in isolation.
-/
theorem fourierCurlCoefficient_velocityPair_add_swap
    (state : ComplexVorticityHilbertState)
    (first second : IntegerWavevector)
    (firstNe : first ≠ 0)
    (secondNe : second ≠ 0)
    (firstTransverse :
      complexWavevector first ⬝ᵥ state first = 0)
    (secondTransverse :
      complexWavevector second ⬝ᵥ state second = 0) :
    fourierCurlCoefficient (first + second)
        (finiteStateVelocityNonlinearPairContribution
            state (first, second) +
          finiteStateVelocityNonlinearPairContribution
            state (second, first)) =
      finiteStateVorticityNonlinearPairContribution
          state (first, second) +
        finiteStateVorticityNonlinearPairContribution
          state (second, first) := by
  have curlFirst :=
    fourierCurlCoefficient_finiteStateVelocityCoefficient
      state first firstNe firstTransverse
  have curlSecond :=
    fourierCurlCoefficient_finiteStateVelocityCoefficient
      state second secondNe secondTransverse
  have velocityFirstTransverse :
      complexWavevector first ⬝ᵥ
          finiteStateVelocityCoefficient state first = 0 :=
    complexWavevector_dot_biotSavartVelocityCoefficient
      first (state first)
  have velocitySecondTransverse :
      complexWavevector second ⬝ᵥ
          finiteStateVelocityCoefficient state second = 0 :=
    complexWavevector_dot_biotSavartVelocityCoefficient
      second (state second)
  let A : ℂ :=
    Complex.I * (((2 * Real.pi : ℝ) : ℂ))
  let p := complexWavevector first
  let q := complexWavevector second
  let u := finiteStateVelocityCoefficient state first
  let v := finiteStateVelocityCoefficient state second
  have core :
      (q ⬝ᵥ u) • (p ⨯₃ v) +
          (p ⬝ᵥ v) • (q ⨯₃ u) +
          (q ⬝ᵥ (p ⨯₃ u)) • v +
          (p ⬝ᵥ (q ⨯₃ v)) • u =
        0 := by
    have identity :=
    convectionCurlCoreIdentity
      (complexWavevector first)
      (complexWavevector second)
      (finiteStateVelocityCoefficient state first)
      (finiteStateVelocityCoefficient state second)
    rw [velocityFirstTransverse,
      velocitySecondTransverse] at identity
    simpa only [zero_smul, zero_add, p, q, u, v] using identity
  unfold finiteStateVorticityNonlinearPairContribution
  rw [← curlFirst, ← curlSecond]
  rw [finiteStateVelocityNonlinearPairContribution,
    finiteStateVelocityNonlinearPairContribution,
    fourierCurlCoefficient,
    complexWavevector_add]
  change
    A • ((p + q) ⨯₃
      (-(A * (q ⬝ᵥ u)) • v +
        -(A * (p ⬝ᵥ v)) • u)) =
      (A * (q ⬝ᵥ (A • (p ⨯₃ u)))) • v -
          (A * (q ⬝ᵥ u)) • (A • (q ⨯₃ v)) +
        ((A * (p ⬝ᵥ (A • (q ⨯₃ v)))) • u -
          (A * (p ⬝ᵥ v)) • (A • (p ⨯₃ u)))
  have scaledCore :
      (A * A) •
          ((q ⬝ᵥ u) • (p ⨯₃ v) +
            (p ⬝ᵥ v) • (q ⨯₃ u) +
            (q ⬝ᵥ (p ⨯₃ u)) • v +
            (p ⬝ᵥ (q ⨯₃ v)) • u) =
        0 := by
    rw [core, smul_zero]
  clear core
  simp only [smul_add, smul_smul] at scaledCore
  simp only [map_add, map_smul, LinearMap.add_apply,
    dotProduct_smul, smul_add, smul_smul]
  ext coordinate
  have scaledCoreCoordinate :=
    congrFun scaledCore coordinate
  simp at scaledCoreCoordinate ⊢
  linear_combination -scaledCoreCoordinate

/-! ## Complete ordered-pair curl reconstruction -/

/-- Every complete ordered-pair sum is half of its explicit pair
symmetrization. -/
theorem orderedPairSum_two_smul_eq_add_swap
    (modes : Finset IntegerWavevector)
    (output : IntegerWavevector)
    (row :
      (IntegerWavevector × IntegerWavevector) →
        ComplexCoordinateVector) :
    (2 : ℂ) •
        (∑ first ∈ modes,
          ∑ second ∈ modes,
            if first + second = output then
              row (first, second)
            else 0) =
      ∑ first ∈ modes,
        ∑ second ∈ modes,
          if first + second = output then
            row (first, second) + row (second, first)
          else 0 := by
  classical
  let orderedSum : ComplexCoordinateVector :=
    ∑ first ∈ modes,
      ∑ second ∈ modes,
        if first + second = output then
          row (first, second)
        else 0
  have swapped :
      (∑ first ∈ modes,
        ∑ second ∈ modes,
          if first + second = output then
            row (second, first)
          else 0) =
        orderedSum := by
    dsimp only [orderedSum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro first firstMem
    apply Finset.sum_congr rfl
    intro second secondMem
    by_cases pairSum : first + second = output
    · have swappedSum : second + first = output := by
        simpa [add_comm] using pairSum
      simp [pairSum, swappedSum]
    · have swappedNotSum : second + first ≠ output := by
        simpa [add_comm] using pairSum
      simp [pairSum, swappedNotSum]
  change (2 : ℂ) • orderedSum = _
  calc
    (2 : ℂ) • orderedSum =
        orderedSum + orderedSum := by module
    _ =
        orderedSum +
          (∑ first ∈ modes,
            ∑ second ∈ modes,
              if first + second = output then
                row (second, first)
              else 0) := by rw [swapped]
    _ =
        ∑ first ∈ modes,
          ∑ second ∈ modes,
            ((if first + second = output then
                row (first, second)
              else 0) +
            (if first + second = output then
                row (second, first)
              else 0)) := by
      dsimp only [orderedSum]
      simp only [Finset.sum_add_distrib]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro first firstMem
      apply Finset.sum_congr rfl
      intro second secondMem
      by_cases pairSum : first + second = output <;>
        simp [pairSum]

theorem fourierCurlCoefficient_smul
    (wave : IntegerWavevector)
    (scalar : ℂ)
    (vector : ComplexCoordinateVector) :
    fourierCurlCoefficient wave (scalar • vector) =
      scalar • fourierCurlCoefficient wave vector := by
  simp [fourierCurlCoefficient, map_smul, smul_smul]
  module

theorem fourierCurlCoefficient_finset_sum
    {ι : Type*}
    (wave : IntegerWavevector)
    (index : Finset ι)
    (vector : ι → ComplexCoordinateVector) :
    fourierCurlCoefficient wave
        (∑ item ∈ index, vector item) =
      ∑ item ∈ index,
        fourierCurlCoefficient wave (vector item) := by
  classical
  induction index using Finset.induction_on with
  | empty =>
      simp [fourierCurlCoefficient]
  | @insert item tail itemNotMem inductionHypothesis =>
      rw [Finset.sum_insert itemNotMem,
        Finset.sum_insert itemNotMem,
        fourierCurlCoefficient]
      simp only [map_add, smul_add]
      rw [← fourierCurlCoefficient,
        ← fourierCurlCoefficient,
        inductionHypothesis]

/--
The complete finite vorticity nonlinearity is exactly the curl of the
complete finite velocity convection coefficient.  Zero-freeness and
transversality are read from the supplied finite physical state; the
ordered-pair identity itself is uniform in the output wave.
-/
theorem finiteStateVorticityNonlinearCoefficientAt_eq_fourierCurl
    (modes : Finset IntegerWavevector)
    (zeroNotMem : 0 ∉ modes)
    (state : ComplexVorticityHilbertState)
    (stateTransverse : FiniteStateTransverseOn modes state)
    (output : IntegerWavevector) :
    finiteStateVorticityNonlinearCoefficientAt
        modes state output =
      fourierCurlCoefficient output
        (finiteStateVelocityNonlinearCoefficientAt
          modes state output) := by
  classical
  have doubledVorticity :=
    orderedPairSum_two_smul_eq_add_swap
      modes output
      (finiteStateVorticityNonlinearPairContribution state)
  have doubledVelocity :=
    orderedPairSum_two_smul_eq_add_swap
      modes output
      (finiteStateVelocityNonlinearPairContribution state)
  have doubledEquality :
      (2 : ℂ) •
          finiteStateVorticityNonlinearCoefficientAt
            modes state output =
        (2 : ℂ) •
          fourierCurlCoefficient output
            (finiteStateVelocityNonlinearCoefficientAt
              modes state output) := by
    calc
      (2 : ℂ) •
            finiteStateVorticityNonlinearCoefficientAt
              modes state output =
          ∑ first ∈ modes,
            ∑ second ∈ modes,
              if first + second = output then
                finiteStateVorticityNonlinearPairContribution
                    state (first, second) +
                  finiteStateVorticityNonlinearPairContribution
                    state (second, first)
              else 0 := by
        simpa [finiteStateVorticityNonlinearCoefficientAt] using
          doubledVorticity
      _ =
          ∑ first ∈ modes,
            ∑ second ∈ modes,
              if first + second = output then
                fourierCurlCoefficient output
                  (finiteStateVelocityNonlinearPairContribution
                      state (first, second) +
                    finiteStateVelocityNonlinearPairContribution
                      state (second, first))
              else 0 := by
        apply Finset.sum_congr rfl
        intro first firstMem
        apply Finset.sum_congr rfl
        intro second secondMem
        by_cases pairSum : first + second = output
        · rw [if_pos pairSum, if_pos pairSum, ← pairSum]
          symm
          exact
            fourierCurlCoefficient_velocityPair_add_swap
              state first second
              (fun firstZero => zeroNotMem (firstZero ▸ firstMem))
              (fun secondZero => zeroNotMem (secondZero ▸ secondMem))
              (stateTransverse first firstMem)
              (stateTransverse second secondMem)
        · simp [pairSum]
      _ =
          fourierCurlCoefficient output
            (∑ first ∈ modes,
              ∑ second ∈ modes,
                if first + second = output then
                  finiteStateVelocityNonlinearPairContribution
                      state (first, second) +
                    finiteStateVelocityNonlinearPairContribution
                      state (second, first)
                else 0) := by
        symm
        rw [fourierCurlCoefficient_finset_sum]
        apply Finset.sum_congr rfl
        intro first firstMem
        rw [fourierCurlCoefficient_finset_sum]
        apply Finset.sum_congr rfl
        intro second secondMem
        by_cases pairSum : first + second = output <;>
          simp [pairSum, fourierCurlCoefficient]
      _ =
          fourierCurlCoefficient output
            ((2 : ℂ) •
              finiteStateVelocityNonlinearCoefficientAt
                modes state output) := by
        congr 1
        simpa [finiteStateVelocityNonlinearCoefficientAt] using
          doubledVelocity.symm
      _ =
          (2 : ℂ) •
            fourierCurlCoefficient output
              (finiteStateVelocityNonlinearCoefficientAt
                modes state output) := by
        exact fourierCurlCoefficient_smul _ _ _
  apply funext
  intro coordinate
  have coordinateEquality :=
    congrFun doubledEquality coordinate
  simp only [Pi.smul_apply, smul_eq_mul] at coordinateEquality
  linear_combination (1 / 2 : ℂ) * coordinateEquality

/-! ## Triad involution and velocity-energy cancellation -/

/-- Real kinetic pairing of the finite velocity state with its complete
convection coefficient. -/
def finiteStateVelocityNonlinearEnergyPairing
    (modes : Finset IntegerWavevector)
    (state : ComplexVorticityHilbertState) : ℝ :=
  ∑ output ∈ modes,
    complexCoordinateRealInner
      (finiteStateVelocityCoefficient state output)
      (finiteStateVelocityNonlinearCoefficientAt
        modes state output)

/-- Eliminating the output sum leaves precisely those ordered input pairs
whose sum remains in the finite Galerkin inventory. -/
theorem finiteStateVelocityNonlinearEnergyPairing_eq_pair_sum
    (modes : Finset IntegerWavevector)
    (state : ComplexVorticityHilbertState) :
    finiteStateVelocityNonlinearEnergyPairing modes state =
      ∑ first ∈ modes,
        ∑ second ∈ modes,
          if first + second ∈ modes then
            complexCoordinateRealInner
              (finiteStateVelocityCoefficient state (first + second))
              (finiteStateVelocityNonlinearPairContribution
                state (first, second))
          else 0 := by
  classical
  unfold finiteStateVelocityNonlinearEnergyPairing
    finiteStateVelocityNonlinearCoefficientAt
  simp_rw [complexCoordinateRealInner_sum_right]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro first firstMem
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro second secondMem
  by_cases outputMem : first + second ∈ modes
  · rw [Finset.sum_eq_single (first + second)]
    · simp [outputMem]
    · intro other otherMem otherNe
      simp [Ne.symm otherNe,
        complexCoordinateRealInner_zero_right]
    · intro outputNotMem
      exact (outputNotMem outputMem).elim
  · have noOutput :
        ∀ output ∈ modes, first + second ≠ output := by
      intro output outputInModes equality
      exact outputMem (equality ▸ outputInModes)
    rw [Finset.sum_eq_zero]
    · simp [outputMem]
    · intro output outputInModes
      simp [noOutput output outputInModes,
        complexCoordinateRealInner_zero_right]

/-- For fixed first input, negating the output is an involution of the
second input lattice. -/
def outputNegSecondEquiv
    (first : IntegerWavevector) :
    IntegerWavevector ≃ IntegerWavevector where
  toFun second := waveNeg (first + second)
  invFun second := waveNeg (first + second)
  left_inv second := by
    ext coordinate
    simp [waveNeg]
  right_inv second := by
    ext coordinate
    simp [waveNeg]

@[simp] theorem outputNegSecondEquiv_apply
    (first second : IntegerWavevector) :
    outputNegSecondEquiv first second =
      waveNeg (first + second) :=
  rfl

private theorem first_add_outputNegSecond
    (first second : IntegerWavevector) :
    first + outputNegSecondEquiv first second =
      waveNeg second := by
  ext coordinate
  simp [outputNegSecondEquiv, waveNeg]

@[simp] theorem outputNegSecondEquiv_involutive
    (first second : IntegerWavevector) :
    outputNegSecondEquiv first
        (outputNegSecondEquiv first second) =
      second := by
  ext coordinate
  simp [outputNegSecondEquiv, waveNeg]

/-- The admissible second-slot inventory for one fixed first input. -/
def admissibleVelocitySeconds
    (modes : Finset IntegerWavevector)
    (first : IntegerWavevector) :
    Finset IntegerWavevector :=
  modes.filter fun second => first + second ∈ modes

theorem outputNegSecondEquiv_mem_admissible_iff
    {modes : Finset IntegerWavevector}
    (negClosed : FiniteModeNegClosed modes)
    (first second : IntegerWavevector) :
    outputNegSecondEquiv first second ∈
        admissibleVelocitySeconds modes first ↔
      second ∈ admissibleVelocitySeconds modes first := by
  simp only [admissibleVelocitySeconds,
    Finset.mem_filter]
  constructor
  · rintro ⟨reflectedMem, reflectedOutputMem⟩
    have secondMem : second ∈ modes := by
      have negSecondMem : waveNeg second ∈ modes := by
        rw [← first_add_outputNegSecond first second]
        exact reflectedOutputMem
      have := negClosed (waveNeg second) negSecondMem
      simpa using this
    have outputMem : first + second ∈ modes := by
      have := negClosed
        (outputNegSecondEquiv first second) reflectedMem
      simpa using this
    exact ⟨secondMem, outputMem⟩
  · rintro ⟨secondMem, outputMem⟩
    have reflectedMem :
        outputNegSecondEquiv first second ∈ modes := by
      exact negClosed (first + second) outputMem
    have reflectedOutputMem :
        first + outputNegSecondEquiv first second ∈ modes := by
      rw [first_add_outputNegSecond]
      exact negClosed second secondMem
    exact ⟨reflectedMem, reflectedOutputMem⟩

/--
For one fixed advecting mode, the source-free triad involution changes the
sign of the kinetic-energy row.  Reality supplies the two reflected velocity
rows; transversality of the advecting Biot--Savart row removes its own
frequency from the reflected derivative.
-/
theorem velocityEnergyPairRow_outputNegSecond
    {modes : Finset IntegerWavevector}
    (state : ComplexVorticityHilbertState)
    (reality : FiniteStateRealityOn modes state)
    (first : IntegerWavevector)
    (second : IntegerWavevector)
    (secondAdmissible :
      second ∈ admissibleVelocitySeconds modes first) :
    complexCoordinateRealInner
        (finiteStateVelocityCoefficient state
          (first + outputNegSecondEquiv first second))
        (finiteStateVelocityNonlinearPairContribution
          state (first, outputNegSecondEquiv first second)) =
      -complexCoordinateRealInner
        (finiteStateVelocityCoefficient state (first + second))
        (finiteStateVelocityNonlinearPairContribution
          state (first, second)) := by
  have secondMem : second ∈ modes :=
    (Finset.mem_filter.mp secondAdmissible).1
  have outputMem : first + second ∈ modes :=
    (Finset.mem_filter.mp secondAdmissible).2
  have reflectedOutput :
      first + outputNegSecondEquiv first second =
        waveNeg second :=
    first_add_outputNegSecond first second
  have reflectedOutputVelocity :
      finiteStateVelocityCoefficient state
          (first + outputNegSecondEquiv first second) =
        vectorConj
          (finiteStateVelocityCoefficient state second) := by
    rw [reflectedOutput]
    exact
      finiteStateVelocityCoefficient_waveNeg
        (reality second secondMem)
  have reflectedSecondVelocity :
      finiteStateVelocityCoefficient state
          (outputNegSecondEquiv first second) =
        vectorConj
          (finiteStateVelocityCoefficient state (first + second)) := by
    exact
      finiteStateVelocityCoefficient_waveNeg
        (reality (first + second) outputMem)
  have reflectedDerivative :
      complexWavevector (outputNegSecondEquiv first second) ⬝ᵥ
          finiteStateVelocityCoefficient state first =
        -(complexWavevector second ⬝ᵥ
          finiteStateVelocityCoefficient state first) := by
    have advectingTransverse :
        complexWavevector first ⬝ᵥ
            finiteStateVelocityCoefficient state first = 0 :=
      complexWavevector_dot_biotSavartVelocityCoefficient
        first (state first)
    rw [outputNegSecondEquiv_apply,
      complexWavevector_waveNeg,
      complexWavevector_add,
      neg_dotProduct,
      add_dotProduct,
      advectingTransverse]
    simp
  rw [reflectedOutputVelocity,
    finiteStateVelocityNonlinearPairContribution,
    finiteStateVelocityNonlinearPairContribution,
    reflectedDerivative,
    reflectedSecondVelocity,
    complexCoordinateRealInner_eq_re_dot,
    complexCoordinateRealInner_eq_re_dot,
    vectorConj_involutive,
    dotProduct_smul,
    dotProduct_smul]
  rw [dotProduct_comm
    (finiteStateVelocityCoefficient state second)
    (vectorConj
      (finiteStateVelocityCoefficient state (first + second)))]
  simp
  ring

/--
For one fixed advecting mode, every complete admissible second-slot sum
vanishes.  The inventory is preserved by the triad involution because it is
closed under frequency negation; no cancellation certificate is supplied by
the caller.
-/
theorem admissibleVelocitySeconds_energyPairSum_eq_zero
    {modes : Finset IntegerWavevector}
    (negClosed : FiniteModeNegClosed modes)
    (state : ComplexVorticityHilbertState)
    (reality : FiniteStateRealityOn modes state)
    (first : IntegerWavevector) :
    (∑ second ∈ admissibleVelocitySeconds modes first,
      complexCoordinateRealInner
        (finiteStateVelocityCoefficient state (first + second))
        (finiteStateVelocityNonlinearPairContribution
          state (first, second))) = 0 := by
  classical
  let row : IntegerWavevector → ℝ := fun second =>
    complexCoordinateRealInner
      (finiteStateVelocityCoefficient state (first + second))
      (finiteStateVelocityNonlinearPairContribution
        state (first, second))
  have reindexed :
      (∑ second ∈ admissibleVelocitySeconds modes first,
          row second) =
        ∑ second ∈ admissibleVelocitySeconds modes first,
          row (outputNegSecondEquiv first second) := by
    refine Finset.sum_equiv (outputNegSecondEquiv first) ?_ ?_
    · intro second
      exact
        (outputNegSecondEquiv_mem_admissible_iff
          negClosed first second).symm
    · intro second secondMem
      rw [outputNegSecondEquiv_involutive]
  have negated :
      (∑ second ∈ admissibleVelocitySeconds modes first,
          row (outputNegSecondEquiv first second)) =
        -(∑ second ∈ admissibleVelocitySeconds modes first,
          row second) := by
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro second secondMem
    exact
      velocityEnergyPairRow_outputNegSecond
        state reality first second secondMem
  have selfNeg :
      (∑ second ∈ admissibleVelocitySeconds modes first,
          row second) =
        -(∑ second ∈ admissibleVelocitySeconds modes first,
          row second) :=
    reindexed.trans negated
  have sumZero :
      (∑ second ∈ admissibleVelocitySeconds modes first,
          row second) = 0 := by
    linarith
  simpa [row] using sumZero

/--
The complete finite velocity convection has exactly zero kinetic-energy
pairing on every negation-closed reality state.  This is the full
ordered-pair coefficient used by the Galerkin generator, not a selected
triad or an averaged surrogate.
-/
theorem finiteStateVelocityNonlinearEnergyPairing_eq_zero
    (modes : Finset IntegerWavevector)
    (negClosed : FiniteModeNegClosed modes)
    (state : ComplexVorticityHilbertState)
    (reality : FiniteStateRealityOn modes state) :
    finiteStateVelocityNonlinearEnergyPairing modes state = 0 := by
  classical
  rw [finiteStateVelocityNonlinearEnergyPairing_eq_pair_sum]
  apply Finset.sum_eq_zero
  intro first firstMem
  have cancellation :=
    admissibleVelocitySeconds_energyPairSum_eq_zero
      negClosed state reality first
  unfold admissibleVelocitySeconds at cancellation
  rw [Finset.sum_filter] at cancellation
  exact cancellation

/-! ## Vorticity-carrier kinetic pairing and exact nonlinear cancellation -/

/--
Kinetic pairing on the vorticity carrier: the current vorticity and tangent
are both inverted by Biot--Savart before taking the real Hermitian pairing.
-/
def finiteStateVorticityKineticPairing
    (modes : Finset IntegerWavevector)
    (state : ComplexVorticityHilbertState)
    (tangent : IntegerWavevector → ComplexCoordinateVector) : ℝ :=
  ∑ wave ∈ modes,
    complexCoordinateRealInner
      (finiteStateVelocityCoefficient state wave)
      (biotSavartVelocityCoefficient wave (tangent wave))

/--
For a zero-free transverse finite state, the vorticity nonlinear kinetic
pairing is exactly the reconstructed velocity-convection pairing.  This is
the whole-carrier Hodge step connecting the original vorticity generator to
the cancellation above.
-/
theorem finiteStateVorticityNonlinearKineticPairing_eq_velocity
    (modes : Finset IntegerWavevector)
    (zeroNotMem : 0 ∉ modes)
    (state : ComplexVorticityHilbertState)
    (stateTransverse : FiniteStateTransverseOn modes state) :
    finiteStateVorticityKineticPairing modes state
        (fun output =>
          finiteStateVorticityNonlinearCoefficientAt
            modes state output) =
      finiteStateVelocityNonlinearEnergyPairing modes state := by
  classical
  unfold finiteStateVorticityKineticPairing
    finiteStateVelocityNonlinearEnergyPairing
  apply Finset.sum_congr rfl
  intro output outputMem
  have outputNe : output ≠ 0 := by
    intro outputZero
    exact zeroNotMem (outputZero ▸ outputMem)
  change
    complexCoordinateRealInner
        (finiteStateVelocityCoefficient state output)
        (biotSavartVelocityCoefficient output
          (finiteStateVorticityNonlinearCoefficientAt
            modes state output)) =
      complexCoordinateRealInner
        (finiteStateVelocityCoefficient state output)
        (finiteStateVelocityNonlinearCoefficientAt
          modes state output)
  rw [finiteStateVorticityNonlinearCoefficientAt_eq_fourierCurl
      modes zeroNotMem state stateTransverse output,
    biotSavartVelocityCoefficient_fourierCurlCoefficient
      output
      (finiteStateVelocityNonlinearCoefficientAt
        modes state output)
      outputNe]
  exact
    complexCoordinateRealInner_transverseProjection
      output
      (finiteStateVelocityCoefficient state output)
      (finiteStateVelocityNonlinearCoefficientAt
        modes state output)
      outputNe
      (complexWavevector_dot_biotSavartVelocityCoefficient
        output (state output))

/--
The original finite vorticity nonlinearity performs exactly zero kinetic
work on every finite physical state.  The geometric hypotheses are the
actual zero-free/negation-closed/transverse/reality invariants; the zero work
is a conclusion.
-/
theorem finiteStateVorticityNonlinearKineticPairing_eq_zero
    (modes : Finset IntegerWavevector)
    (zeroNotMem : 0 ∉ modes)
    (negClosed : FiniteModeNegClosed modes)
    (state : ComplexVorticityHilbertState)
    (stateTransverse : FiniteStateTransverseOn modes state)
    (reality : FiniteStateRealityOn modes state) :
    finiteStateVorticityKineticPairing modes state
        (fun output =>
          finiteStateVorticityNonlinearCoefficientAt
            modes state output) = 0 := by
  rw [finiteStateVorticityNonlinearKineticPairing_eq_velocity
      modes zeroNotMem state stateTransverse,
    finiteStateVelocityNonlinearEnergyPairing_eq_zero
      modes negClosed state reality]

/-! ## Exact viscous kinetic dissipation -/

/--
Unweighted finite vorticity mass.  This is the kinetic-energy dissipation
density after the Laplacian multiplier cancels the Biot--Savart
`|k|⁻²` weight.
-/
def finiteStateVorticityMass
    (modes : Finset IntegerWavevector)
    (state : ComplexVorticityHilbertState) : ℝ :=
  ∑ wave ∈ modes,
    complexCoordinateVectorNormSq (state wave)

/--
At one nonzero transverse Fourier row, the `-Delta` multiplier cancels the
Biot--Savart kinetic weight exactly.  Consequently the positive viscous
kinetic work is `ν |omega_k|²`, with no remaining frequency weight.
-/
theorem finiteStateVorticityViscousKineticPairRow_eq
    (ν : ℝ)
    (state : ComplexVorticityHilbertState)
    (wave : IntegerWavevector)
    (waveNe : wave ≠ 0)
    (transverse :
      complexWavevector wave ⬝ᵥ state wave = 0) :
    complexCoordinateRealInner
        (finiteStateVelocityCoefficient state wave)
        (biotSavartVelocityCoefficient wave
          ((ν * integerWaveViscousMultiplier wave) •
            state wave)) =
      ν * complexCoordinateVectorNormSq (state wave) := by
  have velocitySmul :
      biotSavartVelocityCoefficient wave
          ((ν * integerWaveViscousMultiplier wave) • state wave) =
        (ν * integerWaveViscousMultiplier wave) •
          finiteStateVelocityCoefficient state wave := by
    change
      biotSavartVelocityCoefficient wave
          (((ν * integerWaveViscousMultiplier wave : ℝ) : ℂ) •
            state wave) =
        (((ν * integerWaveViscousMultiplier wave : ℝ) : ℂ) •
          biotSavartVelocityCoefficient wave (state wave))
    exact
      biotSavartVelocityCoefficient_smul wave
        ((ν * integerWaveViscousMultiplier wave : ℝ) : ℂ)
        (state wave)
  rw [velocitySmul,
    complexCoordinateRealInner_real_smul_right,
    complexCoordinateRealInner_self]
  change
    ν * integerWaveViscousMultiplier wave *
        complexCoordinateVectorNormSq
          (biotSavartVelocityCoefficient wave (state wave)) =
      ν * complexCoordinateVectorNormSq (state wave)
  rw [biotSavartVelocityCoefficient_normSq_of_transverse
    wave (state wave) waveNe transverse]
  have waveNormNe : integerWaveNormSq wave ≠ 0 :=
    integerWaveNormSq_ne_zero waveNe
  have piNe : Real.pi ≠ 0 := Real.pi_ne_zero
  unfold integerWaveViscousMultiplier
  field_simp

/--
On an arbitrary zero-free transverse finite inventory, the exact positive
viscous kinetic pairing is viscosity times the unweighted vorticity mass.
This is deliberately different from the enstrophy dissipation, which carries
one additional `|k|²` weight.
-/
theorem finiteStateVorticityViscousKineticPairing_eq
    (modes : Finset IntegerWavevector)
    (zeroNotMem : 0 ∉ modes)
    (ν : ℝ)
    (state : ComplexVorticityHilbertState)
    (stateTransverse : FiniteStateTransverseOn modes state) :
    finiteStateVorticityKineticPairing modes state
        (fun wave =>
          (ν * integerWaveViscousMultiplier wave) •
            state wave) =
      ν * finiteStateVorticityMass modes state := by
  classical
  unfold finiteStateVorticityKineticPairing
    finiteStateVorticityMass
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro wave waveMem
  exact
    finiteStateVorticityViscousKineticPairRow_eq
      ν state wave
      (fun waveZero => zeroNotMem (waveZero ▸ waveMem))
      (stateTransverse wave waveMem)

/-- Biot--Savart inversion preserves subtraction on every frequency row. -/
theorem biotSavartVelocityCoefficient_sub
    (wave : IntegerWavevector)
    (left right : ComplexCoordinateVector) :
    biotSavartVelocityCoefficient wave (left - right) =
      biotSavartVelocityCoefficient wave left -
        biotSavartVelocityCoefficient wave right := by
  by_cases waveZero : wave = 0
  · subst wave
    simp
  · rw [biotSavartVelocityCoefficient, if_neg waveZero,
      biotSavartVelocityCoefficient, if_neg waveZero,
      biotSavartVelocityCoefficient, if_neg waveZero,
      map_sub, smul_sub]

/--
Exact kinetic work of the original finite vorticity generator.  The complete
nonlinear contribution cancels and the remaining derivative is precisely
`-ν` times the unweighted vorticity mass.
-/
theorem finiteStateVorticityGeneratorKineticPairing_eq
    (modes : Finset IntegerWavevector)
    (zeroNotMem : 0 ∉ modes)
    (negClosed : FiniteModeNegClosed modes)
    (ν : ℝ)
    (state : ComplexVorticityHilbertState)
    (stateTransverse : FiniteStateTransverseOn modes state)
    (reality : FiniteStateRealityOn modes state) :
    finiteStateVorticityKineticPairing modes state
        (finiteStateVorticityGenerator modes ν state) =
      -ν * finiteStateVorticityMass modes state := by
  classical
  calc
    finiteStateVorticityKineticPairing modes state
        (finiteStateVorticityGenerator modes ν state) =
      finiteStateVorticityKineticPairing modes state
          (fun output =>
            finiteStateVorticityNonlinearCoefficientAt
              modes state output) -
        finiteStateVorticityKineticPairing modes state
          (fun wave =>
            (ν * integerWaveViscousMultiplier wave) •
              state wave) := by
        unfold finiteStateVorticityKineticPairing
        rw [← Finset.sum_sub_distrib]
        apply Finset.sum_congr rfl
        intro wave waveMem
        rw [finiteStateVorticityGenerator_apply,
          if_pos waveMem,
          biotSavartVelocityCoefficient_sub,
          complexCoordinateRealInner_sub_right]
    _ =
      0 -
        ν * finiteStateVorticityMass modes state := by
        rw [finiteStateVorticityNonlinearKineticPairing_eq_zero
            modes zeroNotMem negClosed state stateTransverse reality,
          finiteStateVorticityViscousKineticPairing_eq
            modes zeroNotMem ν state stateTransverse]
    _ = _ := by ring

/-! ## Kinetic-energy derivative on the actual coefficient trajectory -/

/-- Biot--Savart inversion at one frequency as a complex-linear map. -/
def biotSavartVelocityLinearMap
    (wave : IntegerWavevector) :
    ComplexCoordinateVector →ₗ[ℂ] ComplexCoordinateVector where
  toFun := biotSavartVelocityCoefficient wave
  map_add' := by
    intro left right
    by_cases waveZero : wave = 0
    · subst wave
      simp
    · rw [biotSavartVelocityCoefficient, if_neg waveZero,
        biotSavartVelocityCoefficient, if_neg waveZero,
        biotSavartVelocityCoefficient, if_neg waveZero,
        map_add, smul_add]
  map_smul' := by
    intro scalar vector
    exact
      biotSavartVelocityCoefficient_smul
        wave scalar vector

/-- Continuous real-linear Biot--Savart readout used by time calculus. -/
def biotSavartVelocityCLM
    (wave : IntegerWavevector) :
    ComplexCoordinateVector →L[ℝ] ComplexCoordinateVector :=
  (biotSavartVelocityLinearMap wave).toContinuousLinearMap
    |>.restrictScalars ℝ

@[simp] theorem biotSavartVelocityCLM_apply
    (wave : IntegerWavevector)
    (vorticity : ComplexCoordinateVector) :
    biotSavartVelocityCLM wave vorticity =
      biotSavartVelocityCoefficient wave vorticity :=
  rfl

/-- Every differentiable vorticity trajectory differentiates through the
actual rowwise Biot--Savart velocity readout. -/
theorem finiteStateVelocityTrajectoryWave_hasDerivAt
    (trajectory : ℝ → ComplexVorticityHilbertState)
    (t : ℝ)
    (tangent : ComplexVorticityHilbertState)
    (wave : IntegerWavevector)
    (evolves : HasDerivAt trajectory tangent t) :
    HasDerivAt
      (fun time =>
        finiteStateVelocityCoefficient (trajectory time) wave)
      (biotSavartVelocityCoefficient wave (tangent wave)) t := by
  have rowEvolves :=
    complexVorticityTrajectoryWave_hasDerivAt
      trajectory t tangent wave evolves
  have transported :=
    (biotSavartVelocityCLM wave).hasFDerivAt
      |>.comp_hasDerivAt t rowEvolves
  exact transported

/-- Derivative of the exact squared norm of a complex coordinate path. -/
theorem complexCoordinateVectorNormSq_hasDerivAt
    (path : ℝ → ComplexCoordinateVector)
    (t : ℝ)
    (tangent : ComplexCoordinateVector)
    (evolves : HasDerivAt path tangent t) :
    HasDerivAt
      (fun time =>
        complexCoordinateVectorNormSq (path time))
      (2 * complexCoordinateRealInner (path t) tangent) t := by
  unfold complexCoordinateVectorNormSq
  have coordinateDerivative :
      ∀ coordinate ∈ (Finset.univ : Finset Coordinate),
        HasDerivAt
          (fun time => Complex.normSq (path time coordinate))
          (2 *
            ((path t coordinate).re * (tangent coordinate).re +
              (path t coordinate).im * (tangent coordinate).im)) t := by
    intro coordinate coordinateMem
    have coordinateEvolves :
        HasDerivAt
          (fun time => path time coordinate)
          (tangent coordinate) t := by
      have projected :=
        (ContinuousLinearMap.proj coordinate :
          ComplexCoordinateVector →L[ℝ] ℂ).hasFDerivAt
          |>.comp_hasDerivAt t evolves
      exact projected
    have normDerivative := coordinateEvolves.norm_sq
    simpa [Complex.sq_norm, mul_comm] using normDerivative
  have summed := HasDerivAt.fun_sum coordinateDerivative
  rw [← Finset.mul_sum] at summed
  simpa [complexCoordinateRealInner] using summed

/-- Conventional half kinetic energy of one finite vorticity state. -/
def finiteStateVorticityKineticEnergy
    (modes : Finset IntegerWavevector)
    (state : ComplexVorticityHilbertState) : ℝ :=
  (1 / 2 : ℝ) *
    ∑ wave ∈ modes,
      complexCoordinateVectorNormSq
        (finiteStateVelocityCoefficient state wave)

/--
On a zero-free transverse inventory, kinetic energy has the exact vorticity
Fourier weight

`(1 / 2) * (2*pi)⁻² * |k|⁻²`.
-/
theorem finiteStateVorticityKineticEnergy_eq_weightedVorticity
    (modes : Finset IntegerWavevector)
    (zeroNotMem : 0 ∉ modes)
    (state : ComplexVorticityHilbertState)
    (stateTransverse : FiniteStateTransverseOn modes state) :
    finiteStateVorticityKineticEnergy modes state =
      (1 / 2 : ℝ) *
        ∑ wave ∈ modes,
          complexCoordinateVectorNormSq (state wave) /
            ((2 * Real.pi) ^ 2 *
              integerWaveNormSq wave) := by
  unfold finiteStateVorticityKineticEnergy
  congr 1
  apply Finset.sum_congr rfl
  intro wave waveMem
  exact
    biotSavartVelocityCoefficient_normSq_of_transverse
      wave (state wave)
      (fun waveZero => zeroNotMem (waveZero ▸ waveMem))
      (stateTransverse wave waveMem)

/--
Along an arbitrary differentiable coefficient trajectory, finite kinetic
energy differentiates to the vorticity-carrier kinetic pairing.  This is a
calculus identity and does not assume the Navier--Stokes update.
-/
theorem finiteStateVorticityKineticEnergy_hasDerivAt
    (modes : Finset IntegerWavevector)
    (trajectory : ℝ → ComplexVorticityHilbertState)
    (t : ℝ)
    (tangent : ComplexVorticityHilbertState)
    (evolves : HasDerivAt trajectory tangent t) :
    HasDerivAt
      (fun time =>
        finiteStateVorticityKineticEnergy modes
          (trajectory time))
      (finiteStateVorticityKineticPairing
        modes (trajectory t) tangent) t := by
  have waveDerivative :
      ∀ wave ∈ modes,
        HasDerivAt
          (fun time =>
            complexCoordinateVectorNormSq
              (finiteStateVelocityCoefficient
                (trajectory time) wave))
          (2 * complexCoordinateRealInner
            (finiteStateVelocityCoefficient
              (trajectory t) wave)
            (biotSavartVelocityCoefficient
              wave (tangent wave))) t := by
    intro wave waveMem
    exact
      complexCoordinateVectorNormSq_hasDerivAt
        (fun time =>
          finiteStateVelocityCoefficient
            (trajectory time) wave)
        t
        (biotSavartVelocityCoefficient wave (tangent wave))
        (finiteStateVelocityTrajectoryWave_hasDerivAt
          trajectory t tangent wave evolves)
  have summed := HasDerivAt.fun_sum waveDerivative
  have halved := summed.const_mul (1 / 2 : ℝ)
  unfold finiteStateVorticityKineticEnergy
  rw [← Finset.mul_sum] at halved
  simpa [finiteStateVorticityKineticPairing] using halved

/--
Pointwise kinetic-energy law on the original finite Galerkin update.  The
right side is exactly the unweighted vorticity mass generated by viscosity.
-/
theorem finiteStateVorticityKineticEnergy_hasDerivAt_generator
    (modes : Finset IntegerWavevector)
    (zeroNotMem : 0 ∉ modes)
    (negClosed : FiniteModeNegClosed modes)
    (ν : ℝ)
    (trajectory : ℝ → ComplexVorticityHilbertState)
    (t : ℝ)
    (evolves :
      HasDerivAt trajectory
        (finiteStateVorticityGenerator
          modes ν (trajectory t)) t)
    (stateTransverse :
      FiniteStateTransverseOn modes (trajectory t))
    (reality :
      FiniteStateRealityOn modes (trajectory t)) :
    HasDerivAt
      (fun time =>
        finiteStateVorticityKineticEnergy modes
          (trajectory time))
      (-ν * finiteStateVorticityMass
        modes (trajectory t)) t := by
  have energyDerivative :=
    finiteStateVorticityKineticEnergy_hasDerivAt
      modes trajectory t
      (finiteStateVorticityGenerator
        modes ν (trajectory t))
      evolves
  rw [finiteStateVorticityGeneratorKineticPairing_eq
    modes zeroNotMem negClosed ν (trajectory t)
    stateTransverse reality] at energyDerivative
  exact energyDerivative

private theorem continuousAt_finset_sum
    {ι : Type*}
    [DecidableEq ι]
    (indices : Finset ι)
    {f : ι → ℝ → ℝ}
    {t : ℝ}
    (continuous :
      ∀ index ∈ indices, ContinuousAt (f index) t) :
    ContinuousAt
      (fun time => ∑ index ∈ indices, f index time) t := by
  induction indices using Finset.induction_on with
  | empty =>
      simpa using
        (continuousAt_const :
          ContinuousAt (fun _ : ℝ => (0 : ℝ)) t)
  | @insert index tail indexNotMem inductionHypothesis =>
      simp only [Finset.sum_insert indexNotMem]
      exact
        (continuous index (by simp)).add
          (inductionHypothesis fun later laterMem =>
            continuous later (by simp [laterMem]))

/-- Unweighted vorticity mass is continuous wherever the coefficient
trajectory is differentiable. -/
theorem finiteStateVorticityMass_continuousAt_of_hasDerivAt
    (modes : Finset IntegerWavevector)
    (trajectory : ℝ → ComplexVorticityHilbertState)
    (t : ℝ)
    (tangent : ComplexVorticityHilbertState)
    (evolves : HasDerivAt trajectory tangent t) :
    ContinuousAt
      (fun time =>
        finiteStateVorticityMass modes (trajectory time)) t := by
  unfold finiteStateVorticityMass
  apply continuousAt_finset_sum
  intro wave waveMem
  have waveContinuous :
      ContinuousAt (fun time => trajectory time wave) t :=
    (complexVorticityTrajectoryWave_hasDerivAt
      trajectory t tangent wave evolves).continuousAt
  unfold complexCoordinateVectorNormSq
  apply continuousAt_finset_sum
  intro coordinate coordinateMem
  exact
    Complex.continuous_normSq.continuousAt.comp
      ((continuous_apply coordinate).continuousAt.comp
        waveContinuous)

/--
Exact finite-time kinetic-energy ledger on every actual physical finite
Galerkin trajectory.  The integrated density is the unweighted vorticity
mass; no energy inequality or integrability certificate is accepted from the
caller.
-/
theorem finiteStateVorticityKineticEnergy_integral_generator
    (modes : Finset IntegerWavevector)
    (zeroNotMem : 0 ∉ modes)
    (negClosed : FiniteModeNegClosed modes)
    (ν : ℝ)
    (trajectory : ℝ → ComplexVorticityHilbertState)
    (a b : ℝ)
    (hab : a ≤ b)
    (evolves :
      ∀ t ∈ Icc a b,
        HasDerivAt trajectory
          (finiteStateVorticityGenerator
            modes ν (trajectory t)) t)
    (transverse :
      ∀ t ∈ Icc a b,
        FiniteStateTransverseOn modes (trajectory t))
    (reality :
      ∀ t ∈ Icc a b,
        FiniteStateRealityOn modes (trajectory t)) :
    (∫ t in a..b,
      -ν * finiteStateVorticityMass
        modes (trajectory t)) =
      finiteStateVorticityKineticEnergy modes (trajectory b) -
        finiteStateVorticityKineticEnergy modes (trajectory a) := by
  let rate : ℝ → ℝ := fun t =>
    -ν * finiteStateVorticityMass modes (trajectory t)
  have rateContinuousOn :
      ContinuousOn rate (Icc a b) := by
    intro t timeMem
    have actual := evolves t timeMem
    exact
      (finiteStateVorticityMass_continuousAt_of_hasDerivAt
        modes trajectory t
        (finiteStateVorticityGenerator
          modes ν (trajectory t))
        actual
        |>.const_mul (-ν)).continuousWithinAt
  have rateContinuousOnU :
      ContinuousOn rate (uIcc a b) := by
    simpa [uIcc_of_le hab] using rateContinuousOn
  have derivative :
      ∀ t ∈ uIcc a b,
        HasDerivAt
          (fun time =>
            finiteStateVorticityKineticEnergy modes
              (trajectory time))
          (rate t) t := by
    intro t timeMem
    have intervalMem : t ∈ Icc a b := by
      simpa [uIcc_of_le hab] using timeMem
    exact
      finiteStateVorticityKineticEnergy_hasDerivAt_generator
        modes zeroNotMem negClosed ν trajectory t
        (evolves t intervalMem)
        (transverse t intervalMem)
        (reality t intervalMem)
  exact
    intervalIntegral.integral_eq_sub_of_hasDerivAt
      derivative rateContinuousOnU.intervalIntegrable

/-! ## Source-generated physical kinetic ledger -/

/--
Every raw source generates a positive-time physical Galerkin trajectory with
the pointwise and integrated kinetic-energy balance.

The theorem mouth contains only the raw source and viscosity.  Negation
closure, zero-frequency exclusion, support, transversality, Fourier reality,
the exact nonlinear cancellation, and interval integrability are all
generated internally.
-/
theorem generatedSource_transverseRealityKineticEnergyBalanceLocalTrajectory
    (source : RawVorticityFourierSource)
    (ν : ℝ) :
    ∃ (trajectory : ℝ → ComplexVorticityHilbertState)
        (physicalTime : ℝ),
      0 < physicalTime ∧
        trajectory 0 =
          generatedComplexVorticityState source
            (generatedSupport source) ∧
        ∀ t ∈ Icc (0 : ℝ) physicalTime,
          HasDerivAt trajectory
              (finiteStateVorticityGenerator
                (generatedSupport source) ν (trajectory t)) t ∧
            (∀ wave,
              wave ∉ generatedSupport source →
                trajectory t wave = 0) ∧
            (∀ wave,
              complexWavevector wave ⬝ᵥ trajectory t wave = 0) ∧
            FiniteStateFourierReality (trajectory t) ∧
            HasDerivAt
              (fun time =>
                finiteStateVorticityKineticEnergy
                  (generatedSupport source) (trajectory time))
              (-ν * finiteStateVorticityMass
                (generatedSupport source) (trajectory t)) t ∧
            (∫ time in (0 : ℝ)..t,
              -ν * finiteStateVorticityMass
                (generatedSupport source) (trajectory time)) =
              finiteStateVorticityKineticEnergy
                  (generatedSupport source) (trajectory t) -
                finiteStateVorticityKineticEnergy
                  (generatedSupport source) (trajectory 0) := by
  obtain
      ⟨trajectory, physicalTime, physicalTimePos, initial,
        physicalProperties⟩ :=
    generatedSource_transverseRealityLocalTrajectory source ν
  have negClosed :
      FiniteModeNegClosed (generatedSupport source) := by
    intro wave waveMem
    exact generatedSupport_waveNeg_mem source waveMem
  refine
    ⟨trajectory, physicalTime, physicalTimePos, initial, ?_⟩
  intro t timeMem
  obtain
      ⟨actual, supported, transverse, reality⟩ :=
    physicalProperties t timeMem
  have transverseOn :
      FiniteStateTransverseOn
        (generatedSupport source) (trajectory t) := by
    intro wave waveMem
    exact transverse wave
  have realityOn :
      FiniteStateRealityOn
        (generatedSupport source) (trajectory t) := by
    intro wave waveMem
    exact reality wave
  refine
    ⟨actual, supported, transverse, reality, ?_, ?_⟩
  · exact
      finiteStateVorticityKineticEnergy_hasDerivAt_generator
        (generatedSupport source)
        (zero_not_mem_generatedSupport source)
        negClosed ν trajectory t actual transverseOn realityOn
  · apply
      finiteStateVorticityKineticEnergy_integral_generator
        (generatedSupport source)
        (zero_not_mem_generatedSupport source)
        negClosed ν trajectory 0 t timeMem.1
    · intro time timeWithin
      exact
        (physicalProperties time
          ⟨timeWithin.1, timeWithin.2.trans timeMem.2⟩).1
    · intro time timeWithin wave waveMem
      exact
        (physicalProperties time
          ⟨timeWithin.1, timeWithin.2.trans timeMem.2⟩).2.2.1
          wave
    · intro time timeWithin wave waveMem
      exact
        (physicalProperties time
          ⟨timeWithin.1, timeWithin.2.trans timeMem.2⟩).2.2.2
          wave

end

end ThreeDimensionalVorticityCoefficientFiniteGalerkinKineticEnergyLedger
end NavierStokes
end SaturationMonoid
