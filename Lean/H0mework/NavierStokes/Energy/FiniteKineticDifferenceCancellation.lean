import H0mework.NavierStokes.Galerkin.KineticEnergyLedger
import H0mework.NavierStokes.Fourier.FixedOutputNonlinearContinuity

/-!
# Finite kinetic cancellation for a nonlinear difference

The vorticity difference is first returned to the actual velocity carrier by
Biot--Savart.  Exact bilinear polarization then splits
`N(left) - N(right)` into

```text
B(diff, left) + B(right, diff).
```

In kinetic pairing with `diff`, the second term is a genuine transport term:
the same difference velocity occupies the transported and testing slots.
The full triad involution cancels it exactly.  The surviving first term has
the sharp finite estimate

```text
|pairing| ≤ M(left) * sqrt (2 * kineticEnergy(diff))
                       * sqrt (vorticityMass(diff)).
```

Consequently Young absorption leaves one half of the viscous difference
mass plus the Serrin coefficient `M(left)² / ν` multiplying only the kinetic
difference energy.  No critical-smallness premise, mode count, maximal
frequency, or nonlinear-difference certificate is used.
-/

namespace SaturationMonoid
namespace NavierStokes
namespace ThreeDimensionalVorticityCoefficientFiniteKineticDifferenceCancellation

open scoped BigOperators Matrix

open ThreeDimensionalPeriodicCoarseFilterCore
open ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientStretchingPairTable
open ThreeDimensionalVorticityCoefficientGeneratedShellSerrinGeometry
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open ThreeDimensionalVorticityCoefficientFiniteSupportPhysicalInvariantTrajectory
open ThreeDimensionalVorticityCoefficientFiniteSupportCriticalSobolev
open ThreeDimensionalVorticityCoefficientFiniteSupportRealityTrajectory
open ThreeDimensionalVorticityCoefficientGeneratedShellViscousParseval
open ThreeDimensionalVorticityCoefficientFiniteGalerkinEnstrophyBalance
open ThreeDimensionalVorticityCoefficientFiniteGalerkinKineticEnergyLedger
open ThreeDimensionalVorticityCoefficientFiniteGalerkinNonlinearNegativeSobolev
open ThreeDimensionalVorticityCoefficientFixedOutputNonlinearContinuity

noncomputable section

/-! ## Velocity bilinearization -/

private theorem complexWavevector_add_local
    (first second : IntegerWavevector) :
    complexWavevector (first + second) =
      complexWavevector first + complexWavevector second := by
  funext coordinate
  simp [complexWavevector]

private theorem first_add_outputNegSecond_local
    (first second : IntegerWavevector) :
    first + outputNegSecondEquiv first second =
      waveNeg second := by
  ext coordinate
  simp [outputNegSecondEquiv, waveNeg]

/-- One ordered velocity-convection row with independent advecting and
transported vorticity states. -/
def finiteStateVelocityBilinearPairContribution
    (advecting transported : ComplexVorticityHilbertState)
    (pair : IntegerWavevector × IntegerWavevector) :
    ComplexCoordinateVector :=
  -((Complex.I * (((2 * Real.pi : ℝ) : ℂ))) *
      (complexWavevector pair.2 ⬝ᵥ
        finiteStateVelocityCoefficient advecting pair.1)) •
    finiteStateVelocityCoefficient transported pair.2

/-- Pair symmetrization commutes with the physical curl before frequency
aggregation.  The two ordered velocity occurrences use opposite state roles;
their curl is exactly the corresponding two ordered vorticity occurrences.

This is the occurrence-level commuting square needed to transport a native
triad relation without first quotienting by the fixed-output pair sum. -/
theorem fourierCurlCoefficient_velocityBilinearPair_add_swap
    (left right : ComplexVorticityHilbertState)
    (first second : IntegerWavevector)
    (firstNe : first ≠ 0)
    (secondNe : second ≠ 0)
    (firstTransverse :
      complexWavevector first ⬝ᵥ left first = 0)
    (secondTransverse :
      complexWavevector second ⬝ᵥ right second = 0) :
    fourierCurlCoefficient (first + second)
        (finiteStateVelocityBilinearPairContribution
            left right (first, second) +
          finiteStateVelocityBilinearPairContribution
            right left (second, first)) =
      finiteStateVorticityBilinearPairContribution
          left right (first, second) +
        finiteStateVorticityBilinearPairContribution
          right left (second, first) := by
  have curlFirst :=
    fourierCurlCoefficient_finiteStateVelocityCoefficient
      left first firstNe firstTransverse
  have curlSecond :=
    fourierCurlCoefficient_finiteStateVelocityCoefficient
      right second secondNe secondTransverse
  have velocityFirstTransverse :
      complexWavevector first ⬝ᵥ
          finiteStateVelocityCoefficient left first = 0 :=
    complexWavevector_dot_biotSavartVelocityCoefficient
      first (left first)
  have velocitySecondTransverse :
      complexWavevector second ⬝ᵥ
          finiteStateVelocityCoefficient right second = 0 :=
    complexWavevector_dot_biotSavartVelocityCoefficient
      second (right second)
  let A : ℂ :=
    Complex.I * (((2 * Real.pi : ℝ) : ℂ))
  let p := complexWavevector first
  let q := complexWavevector second
  let u := finiteStateVelocityCoefficient left first
  let v := finiteStateVelocityCoefficient right second
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
        (finiteStateVelocityCoefficient left first)
        (finiteStateVelocityCoefficient right second)
    rw [velocityFirstTransverse,
      velocitySecondTransverse] at identity
    simpa only [zero_smul, zero_add, p, q, u, v] using identity
  unfold finiteStateVorticityBilinearPairContribution
  rw [← curlFirst, ← curlSecond]
  rw [finiteStateVelocityBilinearPairContribution,
    finiteStateVelocityBilinearPairContribution,
    fourierCurlCoefficient,
    complexWavevector_add_local]
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

theorem finiteStateVelocityBilinearPairContribution_add_left
    (left₁ left₂ right : ComplexVorticityHilbertState)
    (pair : IntegerWavevector × IntegerWavevector) :
    finiteStateVelocityBilinearPairContribution
        (left₁ + left₂) right pair =
      finiteStateVelocityBilinearPairContribution left₁ right pair +
        finiteStateVelocityBilinearPairContribution left₂ right pair := by
  have velocityAdd :
      finiteStateVelocityCoefficient (left₁ + left₂) pair.1 =
        finiteStateVelocityCoefficient left₁ pair.1 +
          finiteStateVelocityCoefficient left₂ pair.1 := by
    change
      biotSavartVelocityCoefficient pair.1
          (left₁ pair.1 + left₂ pair.1) =
        biotSavartVelocityCoefficient pair.1 (left₁ pair.1) +
          biotSavartVelocityCoefficient pair.1 (left₂ pair.1)
    by_cases waveZero : pair.1 = 0
    · simp [waveZero, biotSavartVelocityCoefficient]
    · simp [biotSavartVelocityCoefficient, waveZero,
        map_add, smul_add]
  unfold finiteStateVelocityBilinearPairContribution
  rw [velocityAdd, dotProduct_add]
  module

theorem finiteStateVelocityBilinearPairContribution_add_right
    (left right₁ right₂ : ComplexVorticityHilbertState)
    (pair : IntegerWavevector × IntegerWavevector) :
    finiteStateVelocityBilinearPairContribution
        left (right₁ + right₂) pair =
      finiteStateVelocityBilinearPairContribution left right₁ pair +
        finiteStateVelocityBilinearPairContribution left right₂ pair := by
  have velocityAdd :
      finiteStateVelocityCoefficient (right₁ + right₂) pair.2 =
        finiteStateVelocityCoefficient right₁ pair.2 +
          finiteStateVelocityCoefficient right₂ pair.2 := by
    change
      biotSavartVelocityCoefficient pair.2
          (right₁ pair.2 + right₂ pair.2) =
        biotSavartVelocityCoefficient pair.2 (right₁ pair.2) +
          biotSavartVelocityCoefficient pair.2 (right₂ pair.2)
    by_cases waveZero : pair.2 = 0
    · simp [waveZero, biotSavartVelocityCoefficient]
    · simp [biotSavartVelocityCoefficient, waveZero,
        map_add, smul_add]
  unfold finiteStateVelocityBilinearPairContribution
  rw [velocityAdd, smul_add]

/-- Zero Fourier rows remove the endpoint exceptions of Biot--Savart, so the
occurrence-level curl square is total on the physical source carrier. -/
theorem fourierCurlCoefficient_velocityBilinearPair_add_swap_of_zero
    (left right : ComplexVorticityHilbertState)
    (leftZero : left 0 = 0)
    (rightZero : right 0 = 0)
    (leftTransverse :
      ∀ wave, complexWavevector wave ⬝ᵥ left wave = 0)
    (rightTransverse :
      ∀ wave, complexWavevector wave ⬝ᵥ right wave = 0)
    (first second : IntegerWavevector) :
    fourierCurlCoefficient (first + second)
        (finiteStateVelocityBilinearPairContribution
            left right (first, second) +
          finiteStateVelocityBilinearPairContribution
            right left (second, first)) =
      finiteStateVorticityBilinearPairContribution
          left right (first, second) +
        finiteStateVorticityBilinearPairContribution
          right left (second, first) := by
  by_cases firstZero : first = 0
  · subst first
    have velocityZero : finiteStateVelocityCoefficient left 0 = 0 := by
      simp [finiteStateVelocityCoefficient,
        biotSavartVelocityCoefficient]
    simp [finiteStateVelocityBilinearPairContribution,
      finiteStateVorticityBilinearPairContribution,
      leftZero, velocityZero, fourierCurlCoefficient]
  by_cases secondZero : second = 0
  · subst second
    have velocityZero : finiteStateVelocityCoefficient right 0 = 0 := by
      simp [finiteStateVelocityCoefficient,
        biotSavartVelocityCoefficient]
    simp [finiteStateVelocityBilinearPairContribution,
      finiteStateVorticityBilinearPairContribution,
      rightZero, velocityZero, fourierCurlCoefficient]
  exact
    fourierCurlCoefficient_velocityBilinearPair_add_swap
      left right first second firstZero secondZero
      (leftTransverse first) (rightTransverse second)

/-- Complete finite bilinear velocity-convection coefficient. -/
def finiteStateVelocityBilinearCoefficientAt
    (modes : Finset IntegerWavevector)
    (advecting transported : ComplexVorticityHilbertState)
    (output : IntegerWavevector) :
    ComplexCoordinateVector :=
  ∑ first ∈ modes,
    ∑ second ∈ modes,
      if first + second = output then
        finiteStateVelocityBilinearPairContribution
          advecting transported (first, second)
      else 0

theorem finiteStateVelocityNonlinearPairContribution_sub
    (left right : ComplexVorticityHilbertState)
    (pair : IntegerWavevector × IntegerWavevector) :
    finiteStateVelocityNonlinearPairContribution left pair -
        finiteStateVelocityNonlinearPairContribution right pair =
      finiteStateVelocityBilinearPairContribution
          (left - right) left pair +
        finiteStateVelocityBilinearPairContribution
          right (left - right) pair := by
  simp [finiteStateVelocityNonlinearPairContribution,
    finiteStateVelocityBilinearPairContribution,
    finiteStateVelocityCoefficient_sub, dotProduct_sub, smul_sub]
  module

theorem finiteStateVelocityNonlinearCoefficientAt_sub
    (modes : Finset IntegerWavevector)
    (left right : ComplexVorticityHilbertState)
    (output : IntegerWavevector) :
    finiteStateVelocityNonlinearCoefficientAt modes left output -
        finiteStateVelocityNonlinearCoefficientAt modes right output =
      finiteStateVelocityBilinearCoefficientAt
          modes (left - right) left output +
        finiteStateVelocityBilinearCoefficientAt
          modes right (left - right) output := by
  unfold finiteStateVelocityNonlinearCoefficientAt
    finiteStateVelocityBilinearCoefficientAt
  rw [← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro first firstMem
  rw [← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro second secondMem
  by_cases incidence : first + second = output
  · simp [incidence,
      finiteStateVelocityNonlinearPairContribution_sub]
  · simp [incidence]

/-- Real kinetic pairing of an arbitrary testing state with one bilinear
velocity-convection coefficient. -/
def finiteStateVelocityBilinearEnergyPairing
    (modes : Finset IntegerWavevector)
    (test advecting transported : ComplexVorticityHilbertState) : ℝ :=
  ∑ output ∈ modes,
    complexCoordinateRealInner
      (finiteStateVelocityCoefficient test output)
      (finiteStateVelocityBilinearCoefficientAt
        modes advecting transported output)

/-- One pre-summation kinetic occurrence with all three state roles retained.
The output frequency is generated by the two input frequencies; no mode
inventory or aggregate observer has yet identified distinct occurrences. -/
def finiteStateVelocityBilinearEnergyOccurrence
    (test advecting transported : ComplexVorticityHilbertState)
    (first second : IntegerWavevector) : ℝ :=
  complexCoordinateRealInner
    (finiteStateVelocityCoefficient test (first + second))
    (finiteStateVelocityBilinearPairContribution
      advecting transported (first, second))

theorem finiteStateVelocityBilinearEnergyPairing_eq_pair_sum
    (modes : Finset IntegerWavevector)
    (test advecting transported : ComplexVorticityHilbertState) :
    finiteStateVelocityBilinearEnergyPairing
        modes test advecting transported =
      ∑ first ∈ modes,
        ∑ second ∈ modes,
          if first + second ∈ modes then
            complexCoordinateRealInner
              (finiteStateVelocityCoefficient test (first + second))
              (finiteStateVelocityBilinearPairContribution
                advecting transported (first, second))
          else 0 := by
  classical
  unfold finiteStateVelocityBilinearEnergyPairing
    finiteStateVelocityBilinearCoefficientAt
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

/-! ## Exact transport cancellation -/

theorem velocityBilinearEnergyPairRow_outputNegSecond
    {modes : Finset IntegerWavevector}
    (advecting transported : ComplexVorticityHilbertState)
    (transportedReality : FiniteStateRealityOn modes transported)
    (first second : IntegerWavevector)
    (secondAdmissible :
      second ∈ admissibleVelocitySeconds modes first) :
    complexCoordinateRealInner
        (finiteStateVelocityCoefficient transported
          (first + outputNegSecondEquiv first second))
        (finiteStateVelocityBilinearPairContribution
          advecting transported
          (first, outputNegSecondEquiv first second)) =
      -complexCoordinateRealInner
        (finiteStateVelocityCoefficient transported (first + second))
        (finiteStateVelocityBilinearPairContribution
          advecting transported (first, second)) := by
  have secondMem : second ∈ modes :=
    (Finset.mem_filter.mp secondAdmissible).1
  have outputMem : first + second ∈ modes :=
    (Finset.mem_filter.mp secondAdmissible).2
  have reflectedOutput :
      first + outputNegSecondEquiv first second =
        waveNeg second :=
    first_add_outputNegSecond_local first second
  have reflectedOutputVelocity :
      finiteStateVelocityCoefficient transported
          (first + outputNegSecondEquiv first second) =
        vectorConj
          (finiteStateVelocityCoefficient transported second) := by
    rw [reflectedOutput]
    exact
      finiteStateVelocityCoefficient_waveNeg
        (transportedReality second secondMem)
  have reflectedSecondVelocity :
      finiteStateVelocityCoefficient transported
          (outputNegSecondEquiv first second) =
        vectorConj
          (finiteStateVelocityCoefficient transported (first + second)) := by
    exact
      finiteStateVelocityCoefficient_waveNeg
        (transportedReality (first + second) outputMem)
  have reflectedDerivative :
      complexWavevector (outputNegSecondEquiv first second) ⬝ᵥ
          finiteStateVelocityCoefficient advecting first =
        -(complexWavevector second ⬝ᵥ
          finiteStateVelocityCoefficient advecting first) := by
    have advectingTransverse :
        complexWavevector first ⬝ᵥ
            finiteStateVelocityCoefficient advecting first = 0 :=
      complexWavevector_dot_biotSavartVelocityCoefficient
        first (advecting first)
    rw [outputNegSecondEquiv_apply,
      complexWavevector_waveNeg,
      complexWavevector_add_local,
      neg_dotProduct,
      add_dotProduct,
      advectingTransverse]
    simp
  rw [reflectedOutputVelocity,
    finiteStateVelocityBilinearPairContribution,
    finiteStateVelocityBilinearPairContribution,
    reflectedDerivative,
    reflectedSecondVelocity,
    complexCoordinateRealInner_eq_re_dot,
    complexCoordinateRealInner_eq_re_dot,
    vectorConj_involutive,
    dotProduct_smul,
    dotProduct_smul]
  rw [dotProduct_comm
    (finiteStateVelocityCoefficient transported second)
    (vectorConj
      (finiteStateVelocityCoefficient transported (first + second)))]
  simp
  ring

/-- The source-free triad involution is genuinely three-slot skew, not only
a cancellation available after setting the testing and transported states
equal.  Reflecting the transported frequency exchanges those two roles and
negates the exact pre-summation occurrence.

Global Fourier reality supplies the reflected coefficients directly, so the
theorem has no finite cutoff, admissibility inventory, branch, or nonzero
premise. -/
theorem finiteStateVelocityBilinearEnergyOccurrence_reflect_swap
    (test advecting transported : ComplexVorticityHilbertState)
    (testReality : FiniteStateFourierReality test)
    (transportedReality : FiniteStateFourierReality transported)
    (first second : IntegerWavevector) :
    finiteStateVelocityBilinearEnergyOccurrence
        transported advecting test
        first (outputNegSecondEquiv first second) =
      -finiteStateVelocityBilinearEnergyOccurrence
        test advecting transported first second := by
  have reflectedOutput :
      first + outputNegSecondEquiv first second =
        waveNeg second :=
    first_add_outputNegSecond_local first second
  have reflectedOutputVelocity :
      finiteStateVelocityCoefficient transported
          (first + outputNegSecondEquiv first second) =
        vectorConj
          (finiteStateVelocityCoefficient transported second) := by
    rw [reflectedOutput]
    exact
      finiteStateVelocityCoefficient_waveNeg
        (transportedReality second)
  have reflectedSecondVelocity :
      finiteStateVelocityCoefficient test
          (outputNegSecondEquiv first second) =
        vectorConj
          (finiteStateVelocityCoefficient test (first + second)) := by
    exact
      finiteStateVelocityCoefficient_waveNeg
        (testReality (first + second))
  have reflectedDerivative :
      complexWavevector (outputNegSecondEquiv first second) ⬝ᵥ
          finiteStateVelocityCoefficient advecting first =
        -(complexWavevector second ⬝ᵥ
          finiteStateVelocityCoefficient advecting first) := by
    have advectingTransverse :
        complexWavevector first ⬝ᵥ
            finiteStateVelocityCoefficient advecting first = 0 :=
      complexWavevector_dot_biotSavartVelocityCoefficient
        first (advecting first)
    rw [outputNegSecondEquiv_apply,
      complexWavevector_waveNeg,
      complexWavevector_add_local,
      neg_dotProduct,
      add_dotProduct,
      advectingTransverse]
    simp
  unfold finiteStateVelocityBilinearEnergyOccurrence
  rw [reflectedOutputVelocity,
    finiteStateVelocityBilinearPairContribution,
    finiteStateVelocityBilinearPairContribution,
    reflectedDerivative,
    reflectedSecondVelocity,
    complexCoordinateRealInner_eq_re_dot,
    complexCoordinateRealInner_eq_re_dot,
    vectorConj_involutive,
    dotProduct_smul,
    dotProduct_smul]
  rw [dotProduct_comm
    (finiteStateVelocityCoefficient transported second)
    (vectorConj
      (finiteStateVelocityCoefficient test (first + second)))]
  simp
  ring

/-- For one source-generated advecting frequency, the complete admissible
second-slot inventory is carried to the role-swapped inventory by the same
triad involution.  The equality is occurrencewise before either side is
collapsed into the total kinetic observer. -/
theorem admissibleVelocitySeconds_bilinearEnergyPairSum_reflect_swap
    {modes : Finset IntegerWavevector}
    (negClosed : FiniteModeNegClosed modes)
    (test advecting transported : ComplexVorticityHilbertState)
    (testReality : FiniteStateFourierReality test)
    (transportedReality : FiniteStateFourierReality transported)
    (first : IntegerWavevector) :
    (∑ second ∈ admissibleVelocitySeconds modes first,
      finiteStateVelocityBilinearEnergyOccurrence
        transported advecting test first second) =
      -(∑ second ∈ admissibleVelocitySeconds modes first,
        finiteStateVelocityBilinearEnergyOccurrence
          test advecting transported first second) := by
  classical
  let direct : IntegerWavevector → ℝ := fun second =>
    finiteStateVelocityBilinearEnergyOccurrence
      test advecting transported first second
  let reflected : IntegerWavevector → ℝ := fun second =>
    finiteStateVelocityBilinearEnergyOccurrence
      transported advecting test first second
  have reindexed :
      (∑ second ∈ admissibleVelocitySeconds modes first,
          reflected second) =
        ∑ second ∈ admissibleVelocitySeconds modes first,
          reflected (outputNegSecondEquiv first second) := by
    refine Finset.sum_equiv (outputNegSecondEquiv first) ?_ ?_
    · intro second
      exact
        (outputNegSecondEquiv_mem_admissible_iff
          negClosed first second).symm
    · intro second secondMem
      rw [outputNegSecondEquiv_involutive]
  have negated :
      (∑ second ∈ admissibleVelocitySeconds modes first,
          reflected (outputNegSecondEquiv first second)) =
        -(∑ second ∈ admissibleVelocitySeconds modes first,
          direct second) := by
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro second secondMem
    exact
      finiteStateVelocityBilinearEnergyOccurrence_reflect_swap
        test advecting transported testReality transportedReality
        first second
  simpa [direct, reflected] using reindexed.trans negated

/-- Complete finite kinetic transfer is skew in its testing and transported
slots.  This is the summed native relation generated by the occurrencewise
triad redirect above, not a scalar cancellation certificate supplied by a
caller. -/
theorem finiteStateVelocityBilinearEnergyPairing_reflect_swap
    (modes : Finset IntegerWavevector)
    (negClosed : FiniteModeNegClosed modes)
    (test advecting transported : ComplexVorticityHilbertState)
    (testReality : FiniteStateFourierReality test)
    (transportedReality : FiniteStateFourierReality transported) :
    finiteStateVelocityBilinearEnergyPairing
        modes transported advecting test =
      -finiteStateVelocityBilinearEnergyPairing
        modes test advecting transported := by
  classical
  rw [finiteStateVelocityBilinearEnergyPairing_eq_pair_sum,
    finiteStateVelocityBilinearEnergyPairing_eq_pair_sum,
    ← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro first firstMem
  have swap :=
    admissibleVelocitySeconds_bilinearEnergyPairSum_reflect_swap
      negClosed test advecting transported
      testReality transportedReality first
  unfold admissibleVelocitySeconds at swap
  rw [Finset.sum_filter, Finset.sum_filter] at swap
  simpa [finiteStateVelocityBilinearEnergyOccurrence] using swap

theorem admissibleVelocitySeconds_bilinearEnergyPairSum_eq_zero
    {modes : Finset IntegerWavevector}
    (negClosed : FiniteModeNegClosed modes)
    (advecting transported : ComplexVorticityHilbertState)
    (transportedReality : FiniteStateRealityOn modes transported)
    (first : IntegerWavevector) :
    (∑ second ∈ admissibleVelocitySeconds modes first,
      complexCoordinateRealInner
        (finiteStateVelocityCoefficient transported (first + second))
        (finiteStateVelocityBilinearPairContribution
          advecting transported (first, second))) = 0 := by
  classical
  let row : IntegerWavevector → ℝ := fun second =>
    complexCoordinateRealInner
      (finiteStateVelocityCoefficient transported (first + second))
      (finiteStateVelocityBilinearPairContribution
        advecting transported (first, second))
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
      velocityBilinearEnergyPairRow_outputNegSecond
        advecting transported transportedReality
        first second secondMem
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

/-- The transported and testing difference velocity occupy the same slot,
so the complete bilinear transport contribution cancels exactly. -/
theorem finiteStateVelocityBilinearTransportEnergyPairing_eq_zero
    (modes : Finset IntegerWavevector)
    (negClosed : FiniteModeNegClosed modes)
    (advecting transported : ComplexVorticityHilbertState)
    (transportedReality : FiniteStateRealityOn modes transported) :
    finiteStateVelocityBilinearEnergyPairing
        modes transported advecting transported = 0 := by
  classical
  rw [finiteStateVelocityBilinearEnergyPairing_eq_pair_sum]
  apply Finset.sum_eq_zero
  intro first firstMem
  have cancellation :=
    admissibleVelocitySeconds_bilinearEnergyPairSum_eq_zero
      negClosed advecting transported transportedReality first
  unfold admissibleVelocitySeconds at cancellation
  rw [Finset.sum_filter] at cancellation
  exact cancellation

/-! ## Exact difference reduction -/

/-- Velocity kinetic pairing of the actual finite nonlinear difference. -/
def finiteStateVelocityNonlinearDifferenceEnergyPairing
    (modes : Finset IntegerWavevector)
    (left right : ComplexVorticityHilbertState) : ℝ :=
  ∑ output ∈ modes,
    complexCoordinateRealInner
      (finiteStateVelocityCoefficient (left - right) output)
      (finiteStateVelocityNonlinearCoefficientAt modes left output -
        finiteStateVelocityNonlinearCoefficientAt modes right output)

theorem finiteStateVelocityNonlinearDifferenceEnergyPairing_eq_bilinear
    (modes : Finset IntegerWavevector)
    (left right : ComplexVorticityHilbertState) :
    finiteStateVelocityNonlinearDifferenceEnergyPairing
        modes left right =
      finiteStateVelocityBilinearEnergyPairing
          modes (left - right) (left - right) left +
        finiteStateVelocityBilinearEnergyPairing
          modes (left - right) right (left - right) := by
  unfold finiteStateVelocityNonlinearDifferenceEnergyPairing
    finiteStateVelocityBilinearEnergyPairing
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro output outputMem
  rw [finiteStateVelocityNonlinearCoefficientAt_sub,
    complexCoordinateRealInner_add_right]

theorem finiteStateRealityOn_sub
    (modes : Finset IntegerWavevector)
    (left right : ComplexVorticityHilbertState)
    (leftReality : FiniteStateRealityOn modes left)
    (rightReality : FiniteStateRealityOn modes right) :
    FiniteStateRealityOn modes (left - right) := by
  intro wave waveMem
  change
    left (waveNeg wave) - right (waveNeg wave) =
      vectorConj (left wave - right wave)
  rw [leftReality wave waveMem, rightReality wave waveMem,
    vectorConj_sub]

/-- Exact kinetic cancellation reduces the full nonlinear difference to the
single surviving placement `B(diff, left)`. -/
theorem finiteStateVelocityNonlinearDifferenceEnergyPairing_eq_surviving
    (modes : Finset IntegerWavevector)
    (negClosed : FiniteModeNegClosed modes)
    (left right : ComplexVorticityHilbertState)
    (leftReality : FiniteStateRealityOn modes left)
    (rightReality : FiniteStateRealityOn modes right) :
    finiteStateVelocityNonlinearDifferenceEnergyPairing
        modes left right =
      finiteStateVelocityBilinearEnergyPairing
        modes (left - right) (left - right) left := by
  rw [finiteStateVelocityNonlinearDifferenceEnergyPairing_eq_bilinear,
    finiteStateVelocityBilinearTransportEnergyPairing_eq_zero
      modes negClosed right (left - right)
      (finiteStateRealityOn_sub
        modes left right leftReality rightReality),
    add_zero]

/-- Vorticity-carrier kinetic pairing of the actual nonlinear difference. -/
def finiteStateVorticityNonlinearDifferenceKineticPairing
    (modes : Finset IntegerWavevector)
    (left right : ComplexVorticityHilbertState) : ℝ :=
  finiteStateVorticityKineticPairing modes (left - right)
    (fun output =>
      finiteStateVorticityNonlinearCoefficientAt modes left output -
        finiteStateVorticityNonlinearCoefficientAt modes right output)

/-- The vorticity difference pairing is exactly its reconstructed velocity
pairing on the same zero-free finite carrier. -/
theorem
    finiteStateVorticityNonlinearDifferenceKineticPairing_eq_velocity
    (modes : Finset IntegerWavevector)
    (zeroNotMem : 0 ∉ modes)
    (left right : ComplexVorticityHilbertState)
    (leftTransverse : FiniteStateTransverseOn modes left)
    (rightTransverse : FiniteStateTransverseOn modes right) :
    finiteStateVorticityNonlinearDifferenceKineticPairing
        modes left right =
      finiteStateVelocityNonlinearDifferenceEnergyPairing
        modes left right := by
  classical
  unfold finiteStateVorticityNonlinearDifferenceKineticPairing
    finiteStateVorticityKineticPairing
    finiteStateVelocityNonlinearDifferenceEnergyPairing
  apply Finset.sum_congr rfl
  intro output outputMem
  have outputNe : output ≠ 0 := by
    intro outputZero
    exact zeroNotMem (outputZero ▸ outputMem)
  have differenceTransverse :=
    finiteStateTransverseOn_sub
      modes left right leftTransverse rightTransverse
  simp only
  rw [finiteStateVorticityNonlinearCoefficientAt_eq_fourierCurl
      modes zeroNotMem left leftTransverse output,
    finiteStateVorticityNonlinearCoefficientAt_eq_fourierCurl
      modes zeroNotMem right rightTransverse output,
    biotSavartVelocityCoefficient_sub,
    complexCoordinateRealInner_sub_right,
    biotSavartVelocityCoefficient_fourierCurlCoefficient
      output
      (finiteStateVelocityNonlinearCoefficientAt
        modes left output)
      outputNe,
    biotSavartVelocityCoefficient_fourierCurlCoefficient
      output
      (finiteStateVelocityNonlinearCoefficientAt
        modes right output)
      outputNe,
    complexCoordinateRealInner_transverseProjection
      output
      (finiteStateVelocityCoefficient (left - right) output)
      (finiteStateVelocityNonlinearCoefficientAt
        modes left output)
      outputNe
      (complexWavevector_dot_biotSavartVelocityCoefficient
        output ((left - right) output)),
    complexCoordinateRealInner_transverseProjection
      output
      (finiteStateVelocityCoefficient (left - right) output)
      (finiteStateVelocityNonlinearCoefficientAt
        modes right output)
      outputNe
      (complexWavevector_dot_biotSavartVelocityCoefficient
        output ((left - right) output))]
  rw [complexCoordinateRealInner_sub_right]

/-- On the original vorticity carrier, exact transport cancellation leaves
the same single velocity-bilinear placement. -/
theorem
    finiteStateVorticityNonlinearDifferenceKineticPairing_eq_surviving
    (modes : Finset IntegerWavevector)
    (zeroNotMem : 0 ∉ modes)
    (negClosed : FiniteModeNegClosed modes)
    (left right : ComplexVorticityHilbertState)
    (leftTransverse : FiniteStateTransverseOn modes left)
    (rightTransverse : FiniteStateTransverseOn modes right)
    (leftReality : FiniteStateRealityOn modes left)
    (rightReality : FiniteStateRealityOn modes right) :
    finiteStateVorticityNonlinearDifferenceKineticPairing
        modes left right =
      finiteStateVelocityBilinearEnergyPairing
        modes (left - right) (left - right) left := by
  rw [
    finiteStateVorticityNonlinearDifferenceKineticPairing_eq_velocity
      modes zeroNotMem left right leftTransverse rightTransverse,
    finiteStateVelocityNonlinearDifferenceEnergyPairing_eq_surviving
      modes negClosed left right leftReality rightReality]

/-! ## Cutoff-independent bound for the surviving placement -/

private def finiteStateVelocityGradientAmplitude
    (state : ComplexVorticityHilbertState)
    (wave : IntegerWavevector) : ℝ :=
  Real.sqrt
    ((2 * Real.pi) ^ 2 * integerWaveNormSq wave *
      complexCoordinateAmplitudeSq
        (finiteStateVelocityCoefficient state wave))

private theorem finiteStateVelocityGradientAmplitude_nonneg
    (state : ComplexVorticityHilbertState)
    (wave : IntegerWavevector) :
    0 ≤ finiteStateVelocityGradientAmplitude state wave :=
  Real.sqrt_nonneg _

private theorem finiteStateVelocityGradientAmplitude_sq
    (state : ComplexVorticityHilbertState)
    (wave : IntegerWavevector) :
    finiteStateVelocityGradientAmplitude state wave ^ 2 =
      (2 * Real.pi) ^ 2 * integerWaveNormSq wave *
        complexCoordinateAmplitudeSq
          (finiteStateVelocityCoefficient state wave) := by
  rw [finiteStateVelocityGradientAmplitude, Real.sq_sqrt]
  exact
    mul_nonneg
      (mul_nonneg (sq_nonneg _)
        (integerWaveNormSq_nonneg wave))
      (complexCoordinateAmplitudeSq_nonneg _)

private theorem complexCoordinateRealInner_sq_le_local
    (left right : ComplexCoordinateVector) :
    complexCoordinateRealInner left right ^ 2 ≤
      complexCoordinateAmplitudeSq left *
        complexCoordinateAmplitudeSq right := by
  have coordinateBound :
      ∀ coordinate : Coordinate,
        ((left coordinate).re * (right coordinate).re +
            (left coordinate).im * (right coordinate).im) ^ 2 ≤
          Complex.normSq (left coordinate) *
            Complex.normSq (right coordinate) := by
    intro coordinate
    rw [Complex.normSq_apply, Complex.normSq_apply]
    nlinarith
      [sq_nonneg
        ((left coordinate).re * (right coordinate).im -
          (left coordinate).im * (right coordinate).re)]
  have cauchy :=
    Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul
      (Finset.univ : Finset Coordinate)
      (r := fun coordinate =>
        (left coordinate).re * (right coordinate).re +
          (left coordinate).im * (right coordinate).im)
      (f := fun coordinate => Complex.normSq (left coordinate))
      (g := fun coordinate => Complex.normSq (right coordinate))
      (fun coordinate _ => Complex.normSq_nonneg _)
      (fun coordinate _ => Complex.normSq_nonneg _)
      (fun coordinate _ => coordinateBound coordinate)
  simpa [complexCoordinateRealInner,
    complexCoordinateAmplitudeSq] using cauchy

private theorem second_dot_advectingVelocity_eq_output_dot
    (advecting : ComplexVorticityHilbertState)
    (output first second : IntegerWavevector)
    (incidence : first + second = output) :
    complexWavevector second ⬝ᵥ
        finiteStateVelocityCoefficient advecting first =
      complexWavevector output ⬝ᵥ
        finiteStateVelocityCoefficient advecting first := by
  have transverse :
      complexWavevector first ⬝ᵥ
          finiteStateVelocityCoefficient advecting first = 0 :=
    complexWavevector_dot_biotSavartVelocityCoefficient
      first (advecting first)
  rw [← incidence, complexWavevector_add_local,
    add_dotProduct, transverse]
  simp

private theorem
    finiteStateVelocityBilinearPairContribution_amplitudeSq_le
    (advecting transported : ComplexVorticityHilbertState)
    (output first second : IntegerWavevector)
    (incidence : first + second = output) :
    complexCoordinateAmplitudeSq
        (finiteStateVelocityBilinearPairContribution
          advecting transported (first, second)) ≤
      (2 * Real.pi) ^ 2 * integerWaveNormSq output *
        complexCoordinateAmplitudeSq
          (finiteStateVelocityCoefficient advecting first) *
        complexCoordinateAmplitudeSq
          (finiteStateVelocityCoefficient transported second) := by
  have dotBound :=
    complexWavevector_dot_normSq_le
      output (finiteStateVelocityCoefficient advecting first)
  rw [← second_dot_advectingVelocity_eq_output_dot
    advecting output first second incidence] at dotBound
  simp only
    [complexCoordinateAmplitudeSq_eq_complexCoordinateVectorNormSq]
    at dotBound
  rw [finiteStateVelocityBilinearPairContribution,
    complexCoordinateAmplitudeSq_eq_complexCoordinateVectorNormSq,
    complexCoordinateVectorNormSq_smul]
  simp only [Complex.normSq_neg, Complex.normSq_mul, Complex.normSq_I,
    Complex.normSq_ofReal, one_mul]
  simp only
    [complexCoordinateAmplitudeSq_eq_complexCoordinateVectorNormSq]
  have angularNonneg : 0 ≤ (2 * Real.pi) ^ 2 :=
    sq_nonneg _
  have scaled :=
    mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left dotBound angularNonneg)
      (complexCoordinateVectorNormSq_nonneg
        (finiteStateVelocityCoefficient transported second))
  simpa only [pow_two, mul_assoc] using scaled

private theorem finiteStateVelocityBilinearPairWork_abs_le
    (test advecting transported : ComplexVorticityHilbertState)
    (output first second : IntegerWavevector)
    (incidence : first + second = output) :
    |complexCoordinateRealInner
        (finiteStateVelocityCoefficient test output)
        (finiteStateVelocityBilinearPairContribution
          advecting transported (first, second))| ≤
      velocityRowAmplitude transported second *
        velocityRowAmplitude advecting first *
        finiteStateVelocityGradientAmplitude test output := by
  have innerBound :=
    complexCoordinateRealInner_sq_le_local
      (finiteStateVelocityCoefficient test output)
      (finiteStateVelocityBilinearPairContribution
        advecting transported (first, second))
  have pairBound :=
    finiteStateVelocityBilinearPairContribution_amplitudeSq_le
      advecting transported output first second incidence
  have testNonneg :=
    complexCoordinateAmplitudeSq_nonneg
      (finiteStateVelocityCoefficient test output)
  have combined :
      complexCoordinateRealInner
          (finiteStateVelocityCoefficient test output)
          (finiteStateVelocityBilinearPairContribution
            advecting transported (first, second)) ^ 2 ≤
        (velocityRowAmplitude transported second *
          velocityRowAmplitude advecting first *
          finiteStateVelocityGradientAmplitude test output) ^ 2 := by
    calc
      complexCoordinateRealInner
          (finiteStateVelocityCoefficient test output)
          (finiteStateVelocityBilinearPairContribution
            advecting transported (first, second)) ^ 2 ≤
          complexCoordinateAmplitudeSq
              (finiteStateVelocityCoefficient test output) *
            complexCoordinateAmplitudeSq
              (finiteStateVelocityBilinearPairContribution
                advecting transported (first, second)) :=
        innerBound
      _ ≤
          complexCoordinateAmplitudeSq
              (finiteStateVelocityCoefficient test output) *
            ((2 * Real.pi) ^ 2 * integerWaveNormSq output *
              complexCoordinateAmplitudeSq
                (finiteStateVelocityCoefficient advecting first) *
              complexCoordinateAmplitudeSq
                (finiteStateVelocityCoefficient transported second)) :=
        mul_le_mul_of_nonneg_left pairBound testNonneg
      _ =
          (velocityRowAmplitude transported second *
            velocityRowAmplitude advecting first *
            finiteStateVelocityGradientAmplitude test output) ^ 2 := by
        simp only [mul_pow, velocityRowAmplitude_sq,
          finiteStateVelocityGradientAmplitude_sq]
        ring
  exact
    (sq_le_sq₀
      (abs_nonneg _)
      (mul_nonneg
        (mul_nonneg
          (velocityRowAmplitude_nonneg transported second)
          (velocityRowAmplitude_nonneg advecting first))
        (finiteStateVelocityGradientAmplitude_nonneg test output))).mp
      (by simpa [sq_abs] using combined)

private def admissibleVelocityFirsts
    (modes : Finset IntegerWavevector)
    (second : IntegerWavevector) : Finset IntegerWavevector :=
  modes.filter fun first => first + second ∈ modes

private theorem
    finiteStateVelocityBilinearEnergyPairing_eq_first_slices
    (modes : Finset IntegerWavevector)
    (test advecting transported : ComplexVorticityHilbertState) :
    finiteStateVelocityBilinearEnergyPairing
        modes test advecting transported =
      ∑ second ∈ modes,
        ∑ first ∈ admissibleVelocityFirsts modes second,
          complexCoordinateRealInner
            (finiteStateVelocityCoefficient test (first + second))
            (finiteStateVelocityBilinearPairContribution
              advecting transported (first, second)) := by
  rw [finiteStateVelocityBilinearEnergyPairing_eq_pair_sum,
    Finset.sum_comm]
  unfold admissibleVelocityFirsts
  simp only [Finset.sum_filter]

private theorem admissibleVelocityFirsts_amplitudeSq_sum_le
    (modes : Finset IntegerWavevector)
    (second : IntegerWavevector)
    (state : ComplexVorticityHilbertState) :
    (∑ first ∈ admissibleVelocityFirsts modes second,
        complexCoordinateAmplitudeSq
          (finiteStateVelocityCoefficient state first)) ≤
      ∑ first ∈ modes,
        complexCoordinateAmplitudeSq
          (finiteStateVelocityCoefficient state first) := by
  exact
    Finset.sum_le_sum_of_subset_of_nonneg
      (Finset.filter_subset _ _)
      (fun first firstMem firstNotMem =>
        complexCoordinateAmplitudeSq_nonneg _)

private theorem admissibleVelocityFirsts_gradient_sum_le
    (modes : Finset IntegerWavevector)
    (second : IntegerWavevector)
    (state : ComplexVorticityHilbertState) :
    (∑ first ∈ admissibleVelocityFirsts modes second,
        (2 * Real.pi) ^ 2 *
          integerWaveNormSq (first + second) *
          complexCoordinateAmplitudeSq
            (finiteStateVelocityCoefficient state (first + second))) ≤
      ∑ output ∈ modes,
        (2 * Real.pi) ^ 2 * integerWaveNormSq output *
          complexCoordinateAmplitudeSq
            (finiteStateVelocityCoefficient state output) := by
  let outputImage :=
    (admissibleVelocityFirsts modes second).image
      (fun first => first + second)
  have imageSubset : outputImage ⊆ modes := by
    intro output outputMem
    rcases Finset.mem_image.mp outputMem with
      ⟨first, firstMem, rfl⟩
    exact (Finset.mem_filter.mp firstMem).2
  have outputInjective :
      Set.InjOn (fun first : IntegerWavevector => first + second)
        (admissibleVelocityFirsts modes second : Set IntegerWavevector) := by
    intro left leftMem right rightMem sameOutput
    exact add_right_cancel sameOutput
  calc
    (∑ first ∈ admissibleVelocityFirsts modes second,
        (2 * Real.pi) ^ 2 *
          integerWaveNormSq (first + second) *
          complexCoordinateAmplitudeSq
            (finiteStateVelocityCoefficient state (first + second))) =
      ∑ output ∈ outputImage,
        (2 * Real.pi) ^ 2 * integerWaveNormSq output *
          complexCoordinateAmplitudeSq
            (finiteStateVelocityCoefficient state output) := by
      symm
      exact Finset.sum_image outputInjective
    _ ≤
      ∑ output ∈ modes,
        (2 * Real.pi) ^ 2 * integerWaveNormSq output *
          complexCoordinateAmplitudeSq
            (finiteStateVelocityCoefficient state output) :=
      Finset.sum_le_sum_of_subset_of_nonneg imageSubset
        (fun output outputMem outputNotMem =>
          mul_nonneg
            (mul_nonneg (sq_nonneg _)
              (integerWaveNormSq_nonneg output))
            (complexCoordinateAmplitudeSq_nonneg _))

private theorem admissibleVelocityFirsts_cauchy
    (modes : Finset IntegerWavevector)
    (second : IntegerWavevector)
    (advecting test : ComplexVorticityHilbertState) :
    (∑ first ∈ admissibleVelocityFirsts modes second,
        velocityRowAmplitude advecting first *
          finiteStateVelocityGradientAmplitude
            test (first + second)) ≤
      Real.sqrt
          (∑ first ∈ modes,
            complexCoordinateAmplitudeSq
              (finiteStateVelocityCoefficient advecting first)) *
        Real.sqrt
          (∑ output ∈ modes,
            (2 * Real.pi) ^ 2 * integerWaveNormSq output *
              complexCoordinateAmplitudeSq
                (finiteStateVelocityCoefficient test output)) := by
  have cauchy :=
    Real.sum_sqrt_mul_sqrt_le
      (admissibleVelocityFirsts modes second)
      (f := fun first =>
        complexCoordinateAmplitudeSq
          (finiteStateVelocityCoefficient advecting first))
      (g := fun first =>
        (2 * Real.pi) ^ 2 * integerWaveNormSq (first + second) *
          complexCoordinateAmplitudeSq
            (finiteStateVelocityCoefficient test (first + second)))
      (fun first =>
        complexCoordinateAmplitudeSq_nonneg _)
      (fun first =>
        mul_nonneg
          (mul_nonneg (sq_nonneg _)
            (integerWaveNormSq_nonneg (first + second)))
          (complexCoordinateAmplitudeSq_nonneg _))
  have firstBound :=
    admissibleVelocityFirsts_amplitudeSq_sum_le
      modes second advecting
  have outputBound :=
    admissibleVelocityFirsts_gradient_sum_le
      modes second test
  calc
    (∑ first ∈ admissibleVelocityFirsts modes second,
        velocityRowAmplitude advecting first *
          finiteStateVelocityGradientAmplitude
            test (first + second)) ≤
      Real.sqrt
          (∑ first ∈ admissibleVelocityFirsts modes second,
            complexCoordinateAmplitudeSq
              (finiteStateVelocityCoefficient advecting first)) *
        Real.sqrt
          (∑ first ∈ admissibleVelocityFirsts modes second,
            (2 * Real.pi) ^ 2 *
              integerWaveNormSq (first + second) *
              complexCoordinateAmplitudeSq
                (finiteStateVelocityCoefficient
                  test (first + second))) := by
      simpa [velocityRowAmplitude,
        finiteStateVelocityGradientAmplitude] using cauchy
    _ ≤
      Real.sqrt
          (∑ first ∈ modes,
            complexCoordinateAmplitudeSq
              (finiteStateVelocityCoefficient advecting first)) *
        Real.sqrt
          (∑ output ∈ modes,
            (2 * Real.pi) ^ 2 * integerWaveNormSq output *
              complexCoordinateAmplitudeSq
                (finiteStateVelocityCoefficient test output)) := by
      exact
        mul_le_mul
          (Real.sqrt_le_sqrt firstBound)
          (Real.sqrt_le_sqrt outputBound)
          (Real.sqrt_nonneg _)
          (Real.sqrt_nonneg _)

/--
The surviving velocity-bilinear placement has a cutoff-independent
`ℓ¹ × ℓ² × Ḣ¹` bound.  This is the static receipt-square cascade estimate:
no mode count or maximal generated frequency occurs.
-/
theorem finiteStateVelocityBilinearEnergyPairing_abs_le
    (modes : Finset IntegerWavevector)
    (state ambient : ComplexVorticityHilbertState) :
    |finiteStateVelocityBilinearEnergyPairing
        modes state state ambient| ≤
      finiteStateVelocityMajorant modes ambient *
        Real.sqrt
          (∑ wave ∈ modes,
            complexCoordinateAmplitudeSq
              (finiteStateVelocityCoefficient state wave)) *
        Real.sqrt
          (∑ wave ∈ modes,
            (2 * Real.pi) ^ 2 * integerWaveNormSq wave *
              complexCoordinateAmplitudeSq
                (finiteStateVelocityCoefficient state wave)) := by
  classical
  rw [finiteStateVelocityBilinearEnergyPairing_eq_first_slices]
  calc
    |∑ second ∈ modes,
        ∑ first ∈ admissibleVelocityFirsts modes second,
          complexCoordinateRealInner
            (finiteStateVelocityCoefficient state (first + second))
            (finiteStateVelocityBilinearPairContribution
              state ambient (first, second))| ≤
      ∑ second ∈ modes,
        |∑ first ∈ admissibleVelocityFirsts modes second,
          complexCoordinateRealInner
            (finiteStateVelocityCoefficient state (first + second))
            (finiteStateVelocityBilinearPairContribution
              state ambient (first, second))| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤
      ∑ second ∈ modes,
        ∑ first ∈ admissibleVelocityFirsts modes second,
          |complexCoordinateRealInner
            (finiteStateVelocityCoefficient state (first + second))
            (finiteStateVelocityBilinearPairContribution
              state ambient (first, second))| := by
      apply Finset.sum_le_sum
      intro second secondMem
      exact Finset.abs_sum_le_sum_abs _ _
    _ ≤
      ∑ second ∈ modes,
        velocityRowAmplitude ambient second *
          (∑ first ∈ admissibleVelocityFirsts modes second,
            velocityRowAmplitude state first *
              finiteStateVelocityGradientAmplitude
                state (first + second)) := by
      apply Finset.sum_le_sum
      intro second secondMem
      calc
        (∑ first ∈ admissibleVelocityFirsts modes second,
            |complexCoordinateRealInner
              (finiteStateVelocityCoefficient state (first + second))
              (finiteStateVelocityBilinearPairContribution
                state ambient (first, second))|) ≤
          ∑ first ∈ admissibleVelocityFirsts modes second,
            velocityRowAmplitude ambient second *
              (velocityRowAmplitude state first *
                finiteStateVelocityGradientAmplitude
                  state (first + second)) := by
          apply Finset.sum_le_sum
          intro first firstMem
          have incidence :
              first + second = first + second :=
            rfl
          simpa only [mul_assoc] using
            finiteStateVelocityBilinearPairWork_abs_le
              state state ambient
              (first + second) first second incidence
        _ =
          velocityRowAmplitude ambient second *
            (∑ first ∈ admissibleVelocityFirsts modes second,
              velocityRowAmplitude state first *
                finiteStateVelocityGradientAmplitude
                  state (first + second)) := by
          rw [Finset.mul_sum]
    _ ≤
      ∑ second ∈ modes,
        velocityRowAmplitude ambient second *
          (Real.sqrt
            (∑ first ∈ modes,
              complexCoordinateAmplitudeSq
                (finiteStateVelocityCoefficient state first)) *
          Real.sqrt
            (∑ output ∈ modes,
              (2 * Real.pi) ^ 2 * integerWaveNormSq output *
                complexCoordinateAmplitudeSq
                  (finiteStateVelocityCoefficient state output))) := by
      apply Finset.sum_le_sum
      intro second secondMem
      exact
        mul_le_mul_of_nonneg_left
          (admissibleVelocityFirsts_cauchy
            modes second state state)
          (velocityRowAmplitude_nonneg ambient second)
    _ =
      finiteStateVelocityMajorant modes ambient *
        Real.sqrt
          (∑ wave ∈ modes,
            complexCoordinateAmplitudeSq
              (finiteStateVelocityCoefficient state wave)) *
        Real.sqrt
          (∑ wave ∈ modes,
            (2 * Real.pi) ^ 2 * integerWaveNormSq wave *
              complexCoordinateAmplitudeSq
                (finiteStateVelocityCoefficient state wave)) := by
      rw [← Finset.sum_mul]
      unfold finiteStateVelocityMajorant
        finiteVelocityFourierMajorant velocityRowAmplitude
      ring

/-- The unweighted velocity coefficient sum is exactly twice the
conventional half kinetic energy. -/
theorem finiteStateVelocityAmplitudeSq_sum_eq_two_kineticEnergy
    (modes : Finset IntegerWavevector)
    (state : ComplexVorticityHilbertState) :
    (∑ wave ∈ modes,
        complexCoordinateAmplitudeSq
          (finiteStateVelocityCoefficient state wave)) =
      2 * finiteStateVorticityKineticEnergy modes state := by
  unfold finiteStateVorticityKineticEnergy
  simp only
    [complexCoordinateAmplitudeSq_eq_complexCoordinateVectorNormSq]
  ring

/--
On a zero-free transverse carrier, the full velocity-gradient square sum is
exactly the unweighted vorticity mass.  This is the static Biot--Savart
receipt-square identity consumed by the kinetic difference estimate.
-/
theorem finiteStateVelocityGradientSq_sum_eq_vorticityMass
    (modes : Finset IntegerWavevector)
    (zeroNotMem : 0 ∉ modes)
    (state : ComplexVorticityHilbertState)
    (stateTransverse : FiniteStateTransverseOn modes state) :
    (∑ wave ∈ modes,
        (2 * Real.pi) ^ 2 * integerWaveNormSq wave *
          complexCoordinateAmplitudeSq
            (finiteStateVelocityCoefficient state wave)) =
      finiteStateVorticityMass modes state := by
  classical
  unfold finiteStateVorticityMass
  apply Finset.sum_congr rfl
  intro wave waveMem
  have waveNe : wave ≠ 0 := by
    intro waveZero
    exact zeroNotMem (waveZero ▸ waveMem)
  unfold finiteStateVelocityCoefficient
  rw [complexCoordinateAmplitudeSq_eq_complexCoordinateVectorNormSq,
    biotSavartVelocityCoefficient_normSq_of_transverse
      wave (state wave) waveNe
      (stateTransverse wave waveMem)]
  have waveNormNe : integerWaveNormSq wave ≠ 0 :=
    integerWaveNormSq_ne_zero waveNe
  have piNe : Real.pi ≠ 0 := Real.pi_ne_zero
  field_simp

/--
The surviving placement has the exact kinetic-scale bound required by the
difference energy method.  Its constant is one and is independent of the
finite cutoff.
-/
theorem finiteStateVelocityBilinearEnergyPairing_abs_le_kinetic
    (modes : Finset IntegerWavevector)
    (zeroNotMem : 0 ∉ modes)
    (state ambient : ComplexVorticityHilbertState)
    (stateTransverse : FiniteStateTransverseOn modes state) :
    |finiteStateVelocityBilinearEnergyPairing
        modes state state ambient| ≤
      finiteStateVelocityMajorant modes ambient *
        Real.sqrt
          (2 * finiteStateVorticityKineticEnergy modes state) *
        Real.sqrt (finiteStateVorticityMass modes state) := by
  have bound :=
    finiteStateVelocityBilinearEnergyPairing_abs_le
      modes state ambient
  rw [finiteStateVelocityAmplitudeSq_sum_eq_two_kineticEnergy,
    finiteStateVelocityGradientSq_sum_eq_vorticityMass
      modes zeroNotMem state stateTransverse] at bound
  exact bound

/--
After exact transport cancellation, the actual vorticity nonlinear
difference obeys the sharp kinetic estimate with the strong state only in
the velocity majorant.
-/
theorem
    finiteStateVorticityNonlinearDifferenceKineticPairing_abs_le
    (modes : Finset IntegerWavevector)
    (zeroNotMem : 0 ∉ modes)
    (negClosed : FiniteModeNegClosed modes)
    (left right : ComplexVorticityHilbertState)
    (leftTransverse : FiniteStateTransverseOn modes left)
    (rightTransverse : FiniteStateTransverseOn modes right)
    (leftReality : FiniteStateRealityOn modes left)
    (rightReality : FiniteStateRealityOn modes right) :
    |finiteStateVorticityNonlinearDifferenceKineticPairing
        modes left right| ≤
      finiteStateVelocityMajorant modes left *
        Real.sqrt
          (2 * finiteStateVorticityKineticEnergy
            modes (left - right)) *
        Real.sqrt
          (finiteStateVorticityMass modes (left - right)) := by
  rw [
    finiteStateVorticityNonlinearDifferenceKineticPairing_eq_surviving
      modes zeroNotMem negClosed left right
      leftTransverse rightTransverse leftReality rightReality]
  exact
    finiteStateVelocityBilinearEnergyPairing_abs_le_kinetic
      modes zeroNotMem (left - right) left
      (finiteStateTransverseOn_sub
        modes left right leftTransverse rightTransverse)

/--
Young absorption converts the receipt-square cascade bound into one half of
the viscous difference mass plus the endpoint velocity-majorant coefficient
multiplying only kinetic difference energy.
-/
theorem
    finiteStateVorticityNonlinearDifferenceKineticPairing_abs_le_young
    (modes : Finset IntegerWavevector)
    (zeroNotMem : 0 ∉ modes)
    (negClosed : FiniteModeNegClosed modes)
    (left right : ComplexVorticityHilbertState)
    (leftTransverse : FiniteStateTransverseOn modes left)
    (rightTransverse : FiniteStateTransverseOn modes right)
    (leftReality : FiniteStateRealityOn modes left)
    (rightReality : FiniteStateRealityOn modes right)
    (ν : ℝ)
    (νPos : 0 < ν) :
    |finiteStateVorticityNonlinearDifferenceKineticPairing
        modes left right| ≤
      (ν / 2) *
          finiteStateVorticityMass modes (left - right) +
        ν⁻¹ * finiteStateVelocityMajorant modes left ^ 2 *
          finiteStateVorticityKineticEnergy modes (left - right) := by
  let mass :=
    finiteStateVorticityMass modes (left - right)
  let energy :=
    finiteStateVorticityKineticEnergy modes (left - right)
  let majorant :=
    finiteStateVelocityMajorant modes left
  have massNonneg : 0 ≤ mass := by
    unfold mass finiteStateVorticityMass
    exact Finset.sum_nonneg fun wave waveMem =>
      complexCoordinateVectorNormSq_nonneg _
  have energyNonneg : 0 ≤ energy := by
    unfold energy finiteStateVorticityKineticEnergy
    exact
      mul_nonneg (by norm_num)
        (Finset.sum_nonneg fun wave waveMem =>
          complexCoordinateVectorNormSq_nonneg _)
  have sharpBound :
      |finiteStateVorticityNonlinearDifferenceKineticPairing
          modes left right| ≤
        majorant * Real.sqrt (2 * energy) *
          Real.sqrt mass := by
    simpa [mass, energy, majorant] using
      finiteStateVorticityNonlinearDifferenceKineticPairing_abs_le
        modes zeroNotMem negClosed left right
        leftTransverse rightTransverse leftReality rightReality
  have young :=
    two_mul_le_add_mul_sq
      (a := Real.sqrt mass)
      (b := majorant * Real.sqrt (2 * energy))
      νPos
  have doubled :
      2 *
          |finiteStateVorticityNonlinearDifferenceKineticPairing
            modes left right| ≤
        ν * mass + 2 * ν⁻¹ * majorant ^ 2 * energy := by
    calc
      2 *
          |finiteStateVorticityNonlinearDifferenceKineticPairing
            modes left right| ≤
        2 * (majorant * Real.sqrt (2 * energy) *
          Real.sqrt mass) :=
        mul_le_mul_of_nonneg_left sharpBound (by norm_num)
      _ =
        2 * Real.sqrt mass *
          (majorant * Real.sqrt (2 * energy)) := by
        ring
      _ ≤
        ν * Real.sqrt mass ^ 2 +
          ν⁻¹ *
            (majorant * Real.sqrt (2 * energy)) ^ 2 :=
        young
      _ =
        ν * mass + 2 * ν⁻¹ * majorant ^ 2 * energy := by
        rw [Real.sq_sqrt massNonneg,
          mul_pow,
          Real.sq_sqrt
            (mul_nonneg (by norm_num) energyNonneg)]
        ring
  dsimp [mass, energy, majorant] at doubled
  nlinarith

/-- One-sided form used directly by the kinetic difference ledger. -/
theorem finiteStateVorticityNonlinearDifferenceKineticPairing_le_young
    (modes : Finset IntegerWavevector)
    (zeroNotMem : 0 ∉ modes)
    (negClosed : FiniteModeNegClosed modes)
    (left right : ComplexVorticityHilbertState)
    (leftTransverse : FiniteStateTransverseOn modes left)
    (rightTransverse : FiniteStateTransverseOn modes right)
    (leftReality : FiniteStateRealityOn modes left)
    (rightReality : FiniteStateRealityOn modes right)
    (ν : ℝ)
    (νPos : 0 < ν) :
    finiteStateVorticityNonlinearDifferenceKineticPairing
        modes left right ≤
      (ν / 2) *
          finiteStateVorticityMass modes (left - right) +
        ν⁻¹ * finiteStateVelocityMajorant modes left ^ 2 *
          finiteStateVorticityKineticEnergy modes (left - right) := by
  exact
    le_trans
      (le_abs_self _)
      (finiteStateVorticityNonlinearDifferenceKineticPairing_abs_le_young
        modes zeroNotMem negClosed left right
        leftTransverse rightTransverse leftReality rightReality
        ν νPos)

end

end ThreeDimensionalVorticityCoefficientFiniteKineticDifferenceCancellation
end NavierStokes
end SaturationMonoid
