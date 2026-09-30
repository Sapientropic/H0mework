import Mathlib.Algebra.Module.ZLattice.Basic
import H0mework.NavierStokes.Crossing.TangentPaymentCascade
import H0mework.NavierStokes.Restart.HighFrequencyEscape
import H0mework.NavierStokes.Crossing.HighFrequencyKineticCharge
import H0mework.NavierStokes.WholeSpace.WholeSpaceTimeCriticalSerrin
import H0mework.NavierStokes.WholeSpace.WholeSerrinEnstrophyGronwall
import H0mework.NavierStokes.Fourier.FullVorticityDifferentialTransport
import H0mework.NavierStokes.Energy.ClosedEnstrophyPhysicalBridge
import H0mework.NavierStokes.WholeSpace.WholeContinuousMildSerrinWeakAction

/-!
# Source-generated crossing frequency-support exhaustion

Finite physical-time accumulation cannot hide simultaneously in a bounded
family of source-selected crossing cores and inside every corresponding
pair-output support.  The lattice addition law first proves that the pair
outputs of a punctured radius-`r` cube lie in the ordinary radius-`2r` cube.
The existing high-frequency escape theorem then yields the no-parameter
alternative

```text
least crossing-core radii are unbounded
or
one actual crossing has a nonzero physical mode outside its own pair support.
```

On the second branch the same crossing either transports a nonzero gluing
residual, or its faithful-zero outgoing whole receipt has a strictly negative
viscous coefficient-energy derivative at that generated mode and therefore
generates a positive physical time before the same receipt endpoint where
that coefficient energy has strictly dropped.  No radius, crossing
occurrence, output, branch, target path, local time, or continuation witness
is accepted by the terminal theorem.
-/

namespace SaturationMonoid
namespace NavierStokes
namespace
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartCrossingFrequencySupportExhaustion

open scoped BigOperators Matrix ContDiff FourierTransform SchwartzMap Pointwise Topology

open Set Filter MeasureTheory Complex Function LineDeriv Real
open ThreeDimensionalPeriodicCoarseFilterCore
open ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicIntegerCharacterUnitCellMean
open ThreeDimensionalPeriodicCoarseCorrelationResidual
open ThreeDimensionalPeriodicCoarseNonlinearDivergence
open ThreeDimensionalPeriodicCoarseVectorCalculus
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalPeriodicLocalEnergyAlgebra
open ThreeDimensionalPeriodicLocalEnergyFluxTransport
open ThreeDimensionalPeriodicUnitCellDivergence
open ThreeDimensionalPeriodicFullVorticityStretching
open ThreeDimensionalPeriodicFullVorticityDifferentialTransport
open ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientPhysicalCompiler
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open ThreeDimensionalVorticityCoefficientFiniteSupportRealityTrajectory
open ThreeDimensionalVorticityCoefficientFinitePhysicalStateRestart
open ThreeDimensionalVorticityCoefficientGeneratedShellSerrinGeometry
open ThreeDimensionalVorticityCoefficientGeneratedShellViscousParseval
open ThreeDimensionalVorticityCoefficientStretchingPairTable
open ThreeDimensionalVorticityCoefficientStretchingOutputCarrier
open ThreeDimensionalVorticityCoefficientNonlinearPairGenerator
open ThreeDimensionalVorticityCoefficientNonlinearPhysicalBridge
open ThreeDimensionalVorticityCoefficientNonlinearOutputCompiler
open ThreeDimensionalVorticityCoefficientClosedEnstrophyPhysicalBridge
open ThreeDimensionalIntegerLatticeCriticalKernel
open ThreeDimensionalVorticityCoefficientFiniteSupportCriticalSobolev
open ThreeDimensionalVorticityCoefficientFiniteGalerkinEnstrophyBalance
open ThreeDimensionalVorticityCoefficientFiniteGalerkinStretchingCriticalBound
open ThreeDimensionalVorticityCoefficientFixedOutputNonlinearContinuity
open ThreeDimensionalVorticityCoefficientInfiniteFixedOutputNonlinearRow
open
  ThreeDimensionalVorticityCoefficientGeneratedPathInfiniteNonlinearNegativeOneTimeBudget
open
  ThreeDimensionalVorticityCoefficientInfiniteNonlinearNegativeSobolev
open
  ThreeDimensionalVorticityCoefficientFiniteNonlinearDifferenceNegativeOne
open
  ThreeDimensionalVorticityCoefficientWholeNonlinearDifferenceNegativeOne
open
  ThreeDimensionalVorticityCoefficientWholeKineticDifferenceCancellation
open
  ThreeDimensionalVorticityCoefficientGeneratedIntegerShellInfiniteLineageHilbertCompletion
open
  ThreeDimensionalVorticityCoefficientWholeSpaceTimeCriticalSerrin
open
  ThreeDimensionalVorticityCoefficientWholeSerrinEnstrophyGronwall
open
  ThreeDimensionalVorticityCoefficientWholeContinuousMildSerrinWeakAction
open
  ThreeDimensionalVorticityCoefficientWholeContinuousMildSerrinUniqueness
open
  ThreeDimensionalVorticityCoefficientPuncturedCanonicalGalerkinTarget
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartCanonicalReplay
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion.GeneratedWholeRestartCurrent
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartCumulativeCriticalDissipation
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartCumulativeKineticDissipation
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartHighFrequencyEscape
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartCrossingFiniteCore
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartComponentGluingResidualNativeProcess
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartCrossingGluingNegativeOneBridge
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartCrossingUnforcedTangentPayment
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartCrossingHighFrequencyKineticCharge
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartSourcePairOccurrence
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartCrossingTangentPaymentCascade
open AffineRelaxation

noncomputable section

attribute [local instance] Measure.Subtype.measureSpace

/-- Integer frequency cubes are monotone in their source-generated radius. -/
theorem integerWaveFrequencyCube_mono
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

/-- Every ordered pair output from a punctured radius-`r` cube lies in the
ordinary radius-`2r` cube.  This is the geometric fact that removes the
apparent quantifier cycle between high-frequency escape and the adaptive
crossing core. -/
theorem finiteVorticityPairOutputSupport_puncturedCube_subset_doubledCube
    (radius : ℕ) :
    finiteVorticityPairOutputSupport
        (puncturedIntegerWaveFrequencyCube radius) ⊆
      integerWaveFrequencyCube (2 * radius) := by
  intro output outputMem
  rw [finiteVorticityPairOutputSupport, Finset.mem_image] at outputMem
  obtain ⟨pair, pairMem, rfl⟩ := outputMem
  obtain ⟨firstMem, secondMem⟩ := Finset.mem_product.mp pairMem
  rw [puncturedIntegerWaveFrequencyCube, Finset.mem_erase] at firstMem
  rw [puncturedIntegerWaveFrequencyCube, Finset.mem_erase] at secondMem
  rw [integerWaveFrequencyCube, Fintype.mem_piFinset] at firstMem
  rw [integerWaveFrequencyCube, Fintype.mem_piFinset] at secondMem ⊢
  intro coordinate
  have firstCoordinateMem := firstMem.2 coordinate
  have secondCoordinateMem := secondMem.2 coordinate
  rw [Finset.mem_Icc] at firstCoordinateMem secondCoordinateMem ⊢
  simp only [Pi.add_apply]
  constructor <;> omega

private theorem finiteVorticityPairOutputSupport_cube_subset_doubledCube
    (radius : ℕ) :
    finiteVorticityPairOutputSupport
        (integerWaveFrequencyCube radius) ⊆
      integerWaveFrequencyCube (2 * radius) := by
  intro output outputMem
  rw [finiteVorticityPairOutputSupport, Finset.mem_image] at outputMem
  obtain ⟨pair, pairMem, rfl⟩ := outputMem
  obtain ⟨firstMem, secondMem⟩ := Finset.mem_product.mp pairMem
  rw [integerWaveFrequencyCube, Fintype.mem_piFinset] at firstMem secondMem ⊢
  intro coordinate
  have firstCoordinateMem := firstMem coordinate
  have secondCoordinateMem := secondMem coordinate
  rw [Finset.mem_Icc] at firstCoordinateMem secondCoordinateMem ⊢
  simp only [Pi.add_apply]
  constructor <;> omega

/-- Finite accumulated physical time generates an unbounded native
frequency responsibility at every requested scale.  Either the same run
produces a larger least crossing core, or an actual crossing produces a
nonzero mode beyond twice that scale and outside its own pair-output support.
The escape is consumed before quotient loss: nonzero gluing is transported
by the native residual process, while faithful zero gives the exact strictly
negative viscous coefficient-energy derivative and its actual positive-time
physical write-back on the same outgoing receipt.

The scale is universally quantified conclusion structure, not a cutoff
premise controlling the source producer. -/
theorem
    elapsedTime_bddAbove_forces_arbitrarily_large_native_frequency_responsibility
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (elapsedBounded : BddAbove (Set.range (elapsedTime initial))) :
    ∀ radius : ℕ,
      ∃ index : ℕ,
        ∃ crossed : wholeRestartHalfCriticalCrossed initial index,
          radius <
            wholeRestartCrossingFiniteCoreRadius
              initial index crossed ∨
            ∃ output : IntegerWavevector,
              2 * radius < integerWaveCoordinateRadius output ∧
              output ∉ finiteVorticityPairOutputSupport
                  (wholeRestartCrossingFiniteCoreModes
                    initial index crossed) ∧
              (run initial index).contact.physicalState output ≠ 0 ∧
              ((wholeRestartCrossingCompleteSourceGluingNegativeOneState
                    initial index crossed ≠ 0 ∧
                  (wholeRestartComponentGluingResidualRow
                        initial (index + 1) ≠ 0 ∨
                    linearResidualTrace
                        wholeRestartComponentGluingResidualTailKeep
                        (wholeRestartComponentGluingResidualTail
                          initial index) 0 ≠ 0) ∧
                  0 < wholeRestartCrossingTangentPayment initial index) ∨
                (∃ actual :
                    Ioo (0 : ℝ) (run initial index).nextContact.time.1,
                  let initialAmplitude :=
                    complexCoordinateAmplitudeSq
                      ((run initial index).contact.physicalState output)
                  let charge := ν.coeff * actual.1 * initialAmplitude
                  0 < charge ∧
                    charge ≤
                      wholeRestartNextKineticDissipationPayment
                        initial index ∧
                    integerWaveViscousMultiplier output * charge <
                      initialAmplitude -
                        complexCoordinateAmplitudeSq
                          ((run initial index).nextContact.prefixReceipt.wholePath
                            ⟨actual.1, actual.2.1.le,
                              actual.2.2.le⟩ output))) := by
  classical
  intro radius
  by_cases coreEscapes :
      ∃ index : ℕ,
        ∃ crossed : wholeRestartHalfCriticalCrossed initial index,
          radius <
            wholeRestartCrossingFiniteCoreRadius initial index crossed
  · obtain ⟨index, crossed, radiusLt⟩ := coreEscapes
    exact ⟨index, crossed, Or.inl radiusLt⟩
  · have coreRadiusLe :
        ∀ index : ℕ,
          ∀ crossed : wholeRestartHalfCriticalCrossed initial index,
            wholeRestartCrossingFiniteCoreRadius
                initial index crossed ≤ radius := by
      intro index crossed
      exact le_of_not_gt fun radiusLt =>
        coreEscapes ⟨index, crossed, radiusLt⟩
    obtain ⟨index, output, outputOutside, stateNonzero⟩ :=
      elapsedTime_bddAbove_generates_nonzero_wave_outside
        initial elapsedBounded (2 * radius)
    let crossed : wholeRestartHalfCriticalCrossed initial index :=
      elapsedTime_bddAbove_forces_every_halfCriticalCrossing
        initial elapsedBounded index
    have outputNonzero : output ≠ 0 := by
      intro outputZero
      subst output
      exact stateNonzero (run initial index).contact.physicalState_zero
    have outputRadiusLarge :
        2 * radius < integerWaveCoordinateRadius output := by
      apply lt_of_not_ge
      intro outputRadiusLe
      have outputInCube :
          output ∈ integerWaveFrequencyCube (2 * radius) :=
        integerWave_mem_frequencyCube_of_radius_le
          output (2 * radius) outputRadiusLe
      apply outputOutside
      simpa [wholeRestartModes, puncturedIntegerWaveFrequencyCube] using
        (Finset.mem_erase.mpr ⟨outputNonzero, outputInCube⟩)
    have outputNotMem :
        output ∉ finiteVorticityPairOutputSupport
          (wholeRestartCrossingFiniteCoreModes
            initial index crossed) := by
      intro outputMem
      have outputInOwnDoubledCube :
          output ∈ integerWaveFrequencyCube
            (2 * wholeRestartCrossingFiniteCoreRadius
              initial index crossed) := by
        apply
          finiteVorticityPairOutputSupport_puncturedCube_subset_doubledCube
            (wholeRestartCrossingFiniteCoreRadius initial index crossed)
        simpa [wholeRestartCrossingFiniteCoreModes, wholeRestartModes] using
          outputMem
      have doubledRadiusLe :
          2 * wholeRestartCrossingFiniteCoreRadius initial index crossed ≤
            2 * radius :=
        Nat.mul_le_mul_left 2 (coreRadiusLe index crossed)
      have outputInBoundedCube :
          output ∈ integerWaveFrequencyCube (2 * radius) :=
        integerWaveFrequencyCube_mono
          doubledRadiusLe outputInOwnDoubledCube
      apply outputOutside
      simpa [wholeRestartModes, puncturedIntegerWaveFrequencyCube] using
        (Finset.mem_erase.mpr ⟨outputNonzero, outputInBoundedCube⟩)
    refine ⟨index, crossed, Or.inr
      ⟨output, outputRadiusLarge, outputNotMem, stateNonzero, ?_⟩⟩
    by_cases gluingZero :
        wholeRestartCrossingCompleteSourceGluingNegativeOneState
          initial index crossed = 0
    · right
      exact
        wholeRestartCrossingActualWholeRowAmplitudeSq_generates_kineticCharge_of_gluing_zero
          initial index crossed gluingZero output outputNotMem outputNonzero
          stateNonzero
    · left
      have nativeNonzero :
          wholeRestartComponentGluingResidualRow initial index ≠ 0 :=
        (wholeRestartComponentGluingResidualRow_nonzero_iff_negativeOne
          initial index crossed).2 gluingZero
      exact
        ⟨gluingZero,
          wholeRestartComponentGluingResidual_nonzero_next_or_trace
            initial index nativeNonzero,
          wholeRestartCrossingTangentPayment_pos_of_crossed
            initial index crossed⟩

/-! ## Cutoff-independent scale-critical lattice split -/

private theorem integerWaveFrequencyCube_shell_card_agmon
    (radius : ℕ) :
    (integerWaveFrequencyCube (radius + 1) \
      integerWaveFrequencyCube radius).card =
        24 * (radius + 1) ^ 2 + 2 := by
  have cubeCard (later : ℕ) :
      (integerWaveFrequencyCube later).card =
        (2 * later + 1) ^ 3 := by
    (simp [integerWaveFrequencyCube, Fintype.card_piFinset,
      Int.card_Icc]; omega)
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

private theorem integerWaveCoordinateRadius_succ_sq_le_normSq_agmon
    (radius : ℕ)
    (wave : IntegerWavevector)
    (radiusLarge : radius < integerWaveCoordinateRadius wave) :
    ((radius + 1 : ℕ) : ℝ) ^ 2 ≤
      integerWaveNormSq wave := by
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
        (sq_le_sq₀ (by positivity) (abs_nonneg _)).2
          radiusSuccCastLe
      _ = (wave coordinate : ℝ) ^ 2 := sq_abs _
  exact coordinateSqLe.trans (by
    unfold integerWaveNormSq
    exact Finset.single_le_sum
      (fun other _otherMem => sq_nonneg (wave other : ℝ))
      (Finset.mem_univ coordinate))

private theorem integerWaveFrequencyCube_shell_normSq_agmon
    (radius : ℕ)
    (wave : IntegerWavevector)
    (waveMem :
      wave ∈ integerWaveFrequencyCube (radius + 1) \
        integerWaveFrequencyCube radius) :
    ((radius + 1 : ℕ) : ℝ) ^ 2 ≤
      integerWaveNormSq wave := by
  have notMem : wave ∉ integerWaveFrequencyCube radius :=
    (Finset.mem_sdiff.mp waveMem).2
  have radiusLarge : radius < integerWaveCoordinateRadius wave := by
    by_contra notLarge
    exact notMem
      (integerWave_mem_frequencyCube_of_radius_le
        wave radius (Nat.le_of_not_gt notLarge))
  exact integerWaveCoordinateRadius_succ_sq_le_normSq_agmon
    radius wave radiusLarge

private theorem integerWaveSubcriticalKernel_shell_sum_le
    (radius : ℕ) :
    ∑ wave ∈
        integerWaveFrequencyCube (radius + 1) \
          integerWaveFrequencyCube radius,
      (integerWaveNormSq wave)⁻¹ ≤ 26 := by
  let shell :=
    integerWaveFrequencyCube (radius + 1) \
      integerWaveFrequencyCube radius
  have radiusPos : 0 < ((radius + 1 : ℕ) : ℝ) := by
    positivity
  have pointwise :
      ∀ wave ∈ shell,
        (integerWaveNormSq wave)⁻¹ ≤
          (((radius + 1 : ℕ) : ℝ) ^ 2)⁻¹ := by
    intro wave waveMem
    exact inv_anti₀ (sq_pos_of_pos radiusPos)
      (integerWaveFrequencyCube_shell_normSq_agmon
        radius wave waveMem)
  have sumBound :=
    Finset.sum_le_card_nsmul shell
      (fun wave => (integerWaveNormSq wave)⁻¹)
      ((((radius + 1 : ℕ) : ℝ) ^ 2)⁻¹)
      pointwise
  change
    (∑ wave ∈ shell, (integerWaveNormSq wave)⁻¹) ≤ 26
  calc
    (∑ wave ∈ shell, (integerWaveNormSq wave)⁻¹) ≤
        shell.card • ((((radius + 1 : ℕ) : ℝ) ^ 2)⁻¹) :=
      sumBound
    _ = ((shell.card : ℕ) : ℝ) *
          ((((radius + 1 : ℕ) : ℝ) ^ 2)⁻¹) := by
      rw [nsmul_eq_mul]
    _ = ((24 * (radius + 1) ^ 2 + 2 : ℕ) : ℝ) *
          ((((radius + 1 : ℕ) : ℝ) ^ 2)⁻¹) := by
      rw [show shell.card =
          24 * (radius + 1) ^ 2 + 2 by
        exact integerWaveFrequencyCube_shell_card_agmon radius]
    _ ≤ 26 := by
      push_cast
      rw [← div_eq_mul_inv]
      have denomPos : 0 < ((radius : ℝ) + 1) ^ 2 := by
        positivity
      apply (div_le_iff₀ denomPos).2
      have radiusNonneg : 0 ≤ (radius : ℝ) :=
        Nat.cast_nonneg radius
      have radiusOne : 1 ≤ ((radius : ℝ) + 1) ^ 2 := by
        nlinarith
      nlinarith

private theorem integerWaveSubcriticalKernel_frequencyCube_sum_le
    (radius : ℕ) :
    ∑ wave ∈ integerWaveFrequencyCube radius,
      (integerWaveNormSq wave)⁻¹ ≤
        26 * radius := by
  rw [Finset.sum_eq_sum_range_sdiff
    integerWaveFrequencyCube
      (fun _ _ radiusLe => integerWaveFrequencyCube_mono radiusLe)
      (fun wave => (integerWaveNormSq wave)⁻¹) radius]
  have initialZero :
      ∑ wave ∈ integerWaveFrequencyCube 0,
        (integerWaveNormSq wave)⁻¹ = 0 := by
    simp [integerWaveFrequencyCube, integerWaveNormSq]
  rw [initialZero, zero_add]
  calc
    (∑ index ∈ Finset.range radius,
      ∑ wave ∈
          integerWaveFrequencyCube (index + 1) \
            integerWaveFrequencyCube index,
        (integerWaveNormSq wave)⁻¹) ≤
        ∑ _index ∈ Finset.range radius, (26 : ℝ) := by
      apply Finset.sum_le_sum
      intro index indexMem
      exact integerWaveSubcriticalKernel_shell_sum_le index
    _ = 26 * radius := by
      simp [mul_comm]

private theorem integerWaveCriticalKernel_shell_sum_le_agmon
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
        (integerWaveFrequencyCube_shell_normSq_agmon
          radius wave waveMem)
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
          (((((radius + 1 : ℕ) : ℝ) ^ 2)⁻¹) ^ 2) :=
      sumBound
    _ = ((shell.card : ℕ) : ℝ) *
          (((((radius + 1 : ℕ) : ℝ) ^ 2)⁻¹) ^ 2) := by
      rw [nsmul_eq_mul]
    _ = ((24 * (radius + 1) ^ 2 + 2 : ℕ) : ℝ) *
          (((((radius + 1 : ℕ) : ℝ) ^ 2)⁻¹) ^ 2) := by
      rw [show shell.card =
          24 * (radius + 1) ^ 2 + 2 by
        exact integerWaveFrequencyCube_shell_card_agmon radius]
    _ ≤ 26 * ((((radius + 1 : ℕ) : ℝ) ^ 2)⁻¹) := by
      push_cast
      have radiusNonneg : 0 ≤ (radius : ℝ) :=
        Nat.cast_nonneg radius
      have xPos : 0 < ((radius : ℝ) + 1) ^ 2 := by
        positivity
      have xOne : 1 ≤ ((radius : ℝ) + 1) ^ 2 := by
        nlinarith
      field_simp
      nlinarith

private theorem inverseSquare_Ico_sum_le_agmon
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
          ((index : ℝ)⁻¹ -
            (((index + 1 : ℕ) : ℝ)⁻¹)) := by
      apply Finset.sum_le_sum
      intro index indexMem
      have oneLeIndex : 1 ≤ index :=
        lowerPos.trans_le (Finset.mem_Ico.mp indexMem).1
      have indexPos : 0 < (index : ℝ) := by
        exact_mod_cast
          (lt_of_lt_of_le Nat.zero_lt_one oneLeIndex)
      have successorPos :
          0 < ((index + 1 : ℕ) : ℝ) := by
        positivity
      push_cast
      field_simp
      ring_nf
      norm_num
    _ = ((0 : ℝ)⁻¹ - (upper : ℝ)⁻¹) -
          ((0 : ℝ)⁻¹ - (lower : ℝ)⁻¹) := by
      rw [Finset.sum_Ico_eq_sub
        (fun index : ℕ =>
          ((index : ℝ)⁻¹ -
            (((index + 1 : ℕ) : ℝ)⁻¹)))
        lowerLe]
      rw [Finset.sum_range_sub', Finset.sum_range_sub']
      norm_num
    _ ≤ (lower : ℝ)⁻¹ := by
      have upperInvNonneg : 0 ≤ (upper : ℝ)⁻¹ :=
        inv_nonneg.mpr (Nat.cast_nonneg upper)
      simp only [_root_.inv_zero, zero_sub, sub_neg_eq_add]
      linarith

private theorem integerWaveCriticalKernel_frequencyCube_tail_le_agmon
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
  have rangeSplit :=
    Finset.sum_sdiff (Finset.range_mono lowerLe)
      (f := shellSum)
  have tailExpansion :
      ∑ wave ∈
          integerWaveFrequencyCube upper \
            integerWaveFrequencyCube lower,
        integerWaveCriticalKernel wave =
      ∑ index ∈ Finset.range upper \ Finset.range lower,
        shellSum index := by
    rw [upperExpansion] at cubeSplit
    rw [lowerExpansion] at cubeSplit
    linarith
  rw [tailExpansion]
  have rangeDiffEq :
      Finset.range upper \ Finset.range lower =
        Finset.Ico lower upper := by
    ext index
    simp only [Finset.mem_sdiff, Finset.mem_range,
      Finset.mem_Ico]
    omega
  rw [rangeDiffEq]
  calc
    (∑ index ∈ Finset.Ico lower upper, shellSum index) ≤
        ∑ index ∈ Finset.Ico lower upper,
          26 * ((((index + 1 : ℕ) : ℝ) ^ 2)⁻¹) := by
      apply Finset.sum_le_sum
      intro index indexMem
      exact integerWaveCriticalKernel_shell_sum_le_agmon index
    _ = 26 * ∑ index ∈ Finset.Ico lower upper,
          ((((index + 1 : ℕ) : ℝ) ^ 2)⁻¹) := by
      rw [Finset.mul_sum]
    _ ≤ 26 * (lower : ℝ)⁻¹ := by
      exact mul_le_mul_of_nonneg_left
        (inverseSquare_Ico_sum_le_agmon
          lower upper lowerPos lowerLe)
        (by norm_num)

private theorem finiteModes_integerWaveCriticalKernel_tail_le_agmon
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
    have waveModes : wave ∈ modes :=
      (Finset.mem_sdiff.mp waveMem).1
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
      integerWaveCriticalKernel_frequencyCube_tail_le_agmon
        radius upper radiusPos (Nat.le_max_left _ _)

private theorem
    finiteStateVelocityCoefficient_subcriticalAmplitudeSq_le
    (state : ComplexVorticityHilbertState)
    (wave : IntegerWavevector) :
    complexCoordinateAmplitudeSq
        (finiteStateVelocityCoefficient state wave) ≤
      biotSavartSerrinConstant *
        (integerWaveNormSq wave)⁻¹ *
          complexCoordinateAmplitudeSq (state wave) := by
  have critical :=
    finiteStateVelocityCoefficient_criticalAmplitudeSq_le
      state wave
  calc
    complexCoordinateAmplitudeSq
        (finiteStateVelocityCoefficient state wave) ≤
      biotSavartSerrinConstant * integerWaveCriticalKernel wave *
        (integerWaveNormSq wave *
          complexCoordinateAmplitudeSq (state wave)) :=
      critical
    _ = biotSavartSerrinConstant *
          (integerWaveNormSq wave)⁻¹ *
            complexCoordinateAmplitudeSq (state wave) := by
      by_cases waveZero : wave = 0
      · subst wave
        simp [integerWaveCriticalKernel]
      · have normNe := integerWaveNormSq_ne_zero waveZero
        unfold integerWaveCriticalKernel
        field_simp

private theorem
    finiteStateVelocityMajorant_sq_le_subcriticalFiniteSum
    (modes : Finset IntegerWavevector)
    (state : ComplexVorticityHilbertState) :
    finiteStateVelocityMajorant modes state ^ 2 ≤
      biotSavartSerrinConstant *
        (∑ wave ∈ modes, (integerWaveNormSq wave)⁻¹) *
        finiteStateVorticityCoefficientEnstrophy modes state := by
  have cauchyBound :=
    Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul
      modes
      (r := fun wave =>
        Real.sqrt
          (complexCoordinateAmplitudeSq
            (finiteStateVelocityCoefficient state wave)))
      (f := fun wave =>
        biotSavartSerrinConstant *
          (integerWaveNormSq wave)⁻¹)
      (g := fun wave =>
        complexCoordinateAmplitudeSq (state wave))
      (fun wave waveMem =>
        mul_nonneg biotSavartSerrinConstant_nonneg
          (inv_nonneg.mpr (integerWaveNormSq_nonneg wave)))
      (fun wave waveMem =>
        complexCoordinateAmplitudeSq_nonneg _)
      (fun wave waveMem => by
        rw [Real.sq_sqrt
          (complexCoordinateAmplitudeSq_nonneg
            (finiteStateVelocityCoefficient state wave))]
        exact
          finiteStateVelocityCoefficient_subcriticalAmplitudeSq_le
            state wave)
  unfold finiteStateVelocityMajorant finiteVelocityFourierMajorant
    finiteStateVorticityCoefficientEnstrophy
  calc
    (∑ wave ∈ modes,
        √(complexCoordinateAmplitudeSq
          (finiteStateVelocityCoefficient state wave))) ^ 2 ≤
        (∑ wave ∈ modes,
          biotSavartSerrinConstant *
            (integerWaveNormSq wave)⁻¹) *
          ∑ wave ∈ modes,
            complexCoordinateAmplitudeSq (state wave) :=
      cauchyBound
    _ = biotSavartSerrinConstant *
          (∑ wave ∈ modes, (integerWaveNormSq wave)⁻¹) *
          ∑ wave ∈ modes,
            complexCoordinateAmplitudeSq (state wave) := by
      have factorEq :
          (∑ wave ∈ modes,
            biotSavartSerrinConstant *
              (integerWaveNormSq wave)⁻¹) =
            biotSavartSerrinConstant *
              (∑ wave ∈ modes,
                (integerWaveNormSq wave)⁻¹) := by
        rw [Finset.mul_sum]
      rw [factorEq]

private theorem finiteStateVorticityCoefficientEnstrophy_mono_agmon
    {smaller larger : Finset IntegerWavevector}
    (subset : smaller ⊆ larger)
    (state : ComplexVorticityHilbertState) :
    finiteStateVorticityCoefficientEnstrophy smaller state ≤
      finiteStateVorticityCoefficientEnstrophy larger state := by
  unfold finiteStateVorticityCoefficientEnstrophy
  exact Finset.sum_le_sum_of_subset_of_nonneg subset
    (fun wave waveMem waveNotMem =>
      complexCoordinateAmplitudeSq_nonneg (state wave))

private theorem finiteStateVorticityEnstrophyMass_mono_agmon
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

private theorem finiteStateVelocityMajorant_low_sq_le_agmon
    (modes : Finset IntegerWavevector)
    (state : ComplexVorticityHilbertState)
    (radius : ℕ) :
    finiteStateVelocityMajorant
        (modes ∩ integerWaveFrequencyCube radius) state ^ 2 ≤
      26 * biotSavartSerrinConstant * (radius : ℝ) *
        finiteStateVorticityCoefficientEnstrophy modes state := by
  let lowModes := modes ∩ integerWaveFrequencyCube radius
  have lowSubsetModes : lowModes ⊆ modes := Finset.inter_subset_left
  have lowSubsetCube : lowModes ⊆ integerWaveFrequencyCube radius :=
    Finset.inter_subset_right
  have lowKernelBound :
      (∑ wave ∈ lowModes, (integerWaveNormSq wave)⁻¹) ≤
        26 * radius := by
    exact
      (Finset.sum_le_sum_of_subset_of_nonneg lowSubsetCube
        (fun wave waveMem waveNotMem =>
          inv_nonneg.mpr (integerWaveNormSq_nonneg wave))).trans
      (integerWaveSubcriticalKernel_frequencyCube_sum_le radius)
  calc
    finiteStateVelocityMajorant lowModes state ^ 2 ≤
        biotSavartSerrinConstant *
          (∑ wave ∈ lowModes, (integerWaveNormSq wave)⁻¹) *
          finiteStateVorticityCoefficientEnstrophy lowModes state :=
      finiteStateVelocityMajorant_sq_le_subcriticalFiniteSum
        lowModes state
    _ ≤ biotSavartSerrinConstant * (26 * radius) *
          finiteStateVorticityCoefficientEnstrophy lowModes state := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left lowKernelBound
          biotSavartSerrinConstant_nonneg)
        (by
          unfold finiteStateVorticityCoefficientEnstrophy
          exact Finset.sum_nonneg fun wave waveMem =>
            complexCoordinateAmplitudeSq_nonneg _)
    _ ≤ biotSavartSerrinConstant * (26 * radius) *
          finiteStateVorticityCoefficientEnstrophy modes state := by
      exact mul_le_mul_of_nonneg_left
        (finiteStateVorticityCoefficientEnstrophy_mono_agmon
          lowSubsetModes state)
        (mul_nonneg biotSavartSerrinConstant_nonneg
          (mul_nonneg (by norm_num) (Nat.cast_nonneg radius)))
    _ = 26 * biotSavartSerrinConstant * (radius : ℝ) *
          finiteStateVorticityCoefficientEnstrophy modes state := by
      ring

private theorem finiteStateVelocityMajorant_high_sq_le_agmon
    (modes : Finset IntegerWavevector)
    (state : ComplexVorticityHilbertState)
    (radius : ℕ)
    (radiusPos : 0 < radius) :
    finiteStateVelocityMajorant
        (modes \ integerWaveFrequencyCube radius) state ^ 2 ≤
      26 * biotSavartSerrinConstant * (radius : ℝ)⁻¹ *
        finiteStateVorticityEnstrophyMass modes state := by
  let highModes := modes \ integerWaveFrequencyCube radius
  have highSubsetModes : highModes ⊆ modes := Finset.sdiff_subset
  have highKernelBound :
      (∑ wave ∈ highModes, integerWaveCriticalKernel wave) ≤
        26 * (radius : ℝ)⁻¹ :=
    finiteModes_integerWaveCriticalKernel_tail_le_agmon
      radius radiusPos modes
  calc
    finiteStateVelocityMajorant highModes state ^ 2 ≤
        biotSavartSerrinConstant *
          (∑ wave ∈ highModes, integerWaveCriticalKernel wave) *
          finiteStateVorticityEnstrophyMass highModes state :=
      finiteStateVelocityMajorant_sq_le_criticalFiniteSum
        highModes state
    _ ≤ biotSavartSerrinConstant * (26 * (radius : ℝ)⁻¹) *
          finiteStateVorticityEnstrophyMass highModes state := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left highKernelBound
          biotSavartSerrinConstant_nonneg)
        (finiteStateVorticityEnstrophyMass_nonneg highModes state)
    _ ≤ biotSavartSerrinConstant * (26 * (radius : ℝ)⁻¹) *
          finiteStateVorticityEnstrophyMass modes state := by
      exact mul_le_mul_of_nonneg_left
        (finiteStateVorticityEnstrophyMass_mono_agmon
          highSubsetModes state)
        (mul_nonneg biotSavartSerrinConstant_nonneg
          (mul_nonneg (by norm_num)
            (inv_nonneg.mpr (Nat.cast_nonneg radius))))
    _ = 26 * biotSavartSerrinConstant * (radius : ℝ)⁻¹ *
          finiteStateVorticityEnstrophyMass modes state := by
      ring

private theorem
    finiteStateVorticityCoefficientEnstrophy_high_mul_radius_sq_le_agmon
    (modes : Finset IntegerWavevector)
    (state : ComplexVorticityHilbertState)
    (radius : ℕ) :
    (radius : ℝ) ^ 2 *
        finiteStateVorticityCoefficientEnstrophy
          (modes \ integerWaveFrequencyCube radius) state ≤
      finiteStateVorticityEnstrophyMass modes state := by
  have pointwise :
      ∀ wave ∈ modes \ integerWaveFrequencyCube radius,
        (radius : ℝ) ^ 2 *
            complexCoordinateAmplitudeSq (state wave) ≤
          integerWaveNormSq wave *
            complexCoordinateAmplitudeSq (state wave) := by
    intro wave waveMem
    have waveNotLow : wave ∉ integerWaveFrequencyCube radius :=
      (Finset.mem_sdiff.mp waveMem).2
    have radiusLarge : radius < integerWaveCoordinateRadius wave := by
      by_contra notLarge
      exact waveNotLow
        (integerWave_mem_frequencyCube_of_radius_le
          wave radius (Nat.le_of_not_gt notLarge))
    have successorBound :=
      integerWaveCoordinateRadius_succ_sq_le_normSq_agmon
        radius wave radiusLarge
    have radiusSqLe :
        (radius : ℝ) ^ 2 ≤ integerWaveNormSq wave := by
      have radiusLeSucc :
          (radius : ℝ) ≤ ((radius + 1 : ℕ) : ℝ) := by
        exact_mod_cast radius.le_succ
      nlinarith
    exact mul_le_mul_of_nonneg_right radiusSqLe
      (complexCoordinateAmplitudeSq_nonneg (state wave))
  unfold finiteStateVorticityCoefficientEnstrophy
    finiteStateVorticityEnstrophyMass
  rw [Finset.mul_sum]
  exact
    (Finset.sum_le_sum pointwise).trans
      (Finset.sum_le_sum_of_subset_of_nonneg
        Finset.sdiff_subset
        (fun wave waveMem waveNotMem =>
          mul_nonneg (integerWaveNormSq_nonneg wave)
            (complexCoordinateAmplitudeSq_nonneg (state wave))))

/-- The actual whole-state mass omitted by a frequency cube is paid by the
same state's whole gradient mass with the sharp inverse-square scale. -/
theorem wholeVorticity_cubeComplement_mul_radius_sq_le_gradient
    (state : ComplexVorticityHilbertState)
    (gradientSummable :
      Summable fun wave : IntegerWavevector =>
        integerWaveNormSq wave *
          complexCoordinateAmplitudeSq (state wave))
    (radius : ℕ) :
    (radius : ℝ) ^ 2 *
        wholeVorticityEuclideanMass
          (complexSharpSupportProjection
            (integerWaveFrequencyCube radius) state - state) ≤
      wholeStateVorticityGradientMass state := by
  let tail :=
    complexSharpSupportProjection
      (integerWaveFrequencyCube radius) state - state
  have tailSummable := summable_vorticityRowAmplitude_sq tail
  have leftSummable :
      Summable fun wave : IntegerWavevector =>
        (radius : ℝ) ^ 2 * vorticityRowAmplitude tail wave ^ 2 :=
    tailSummable.mul_left _
  have pointwise :
      ∀ wave : IntegerWavevector,
        (radius : ℝ) ^ 2 * vorticityRowAmplitude tail wave ^ 2 ≤
          integerWaveNormSq wave *
            complexCoordinateAmplitudeSq (state wave) := by
    intro wave
    by_cases waveMem : wave ∈ integerWaveFrequencyCube radius
    · have tailZero : tail wave = 0 := by
        simp [tail, complexSharpSupportProjection_apply, waveMem]
      rw [vorticityRowAmplitude_sq,
        ← complexCoordinateAmplitudeSq_eq_complexCoordinateVectorNormSq,
        tailZero]
      simpa [complexCoordinateAmplitudeSq] using
        mul_nonneg (integerWaveNormSq_nonneg wave)
          (complexCoordinateAmplitudeSq_nonneg (state wave))
    · have radiusLarge :
          radius < integerWaveCoordinateRadius wave := by
        by_contra notLarge
        exact waveMem
          (integerWave_mem_frequencyCube_of_radius_le
            wave radius (Nat.le_of_not_gt notLarge))
      have radiusSqLe :
          (radius : ℝ) ^ 2 ≤ integerWaveNormSq wave := by
        unfold integerWaveCoordinateRadius at radiusLarge
        obtain ⟨coordinate, _coordinateMem, coordinateLarge⟩ :=
          Finset.lt_sup_iff.mp radiusLarge
        have radiusLeAbs :
            radius ≤ Int.natAbs (wave coordinate) :=
          Nat.le_of_lt coordinateLarge
        have radiusCastLe :
            (radius : ℝ) ≤ |(wave coordinate : ℝ)| := by
          have natAbsCast :
              ((Int.natAbs (wave coordinate) : ℕ) : ℝ) =
                |(wave coordinate : ℝ)| := by
            rw [← Int.cast_natCast]
            rw [Int.natCast_natAbs]
            norm_cast
          rw [← natAbsCast]
          exact_mod_cast radiusLeAbs
        have coordinateSqLe :
            (radius : ℝ) ^ 2 ≤ (wave coordinate : ℝ) ^ 2 := by
          calc
            (radius : ℝ) ^ 2 ≤ |(wave coordinate : ℝ)| ^ 2 :=
              (sq_le_sq₀ (by positivity) (abs_nonneg _)).2 radiusCastLe
            _ = (wave coordinate : ℝ) ^ 2 := sq_abs _
        exact coordinateSqLe.trans (by
          unfold integerWaveNormSq
          exact Finset.single_le_sum
            (fun other _otherMem => sq_nonneg (wave other : ℝ))
            (Finset.mem_univ coordinate))
      have amplitudeEq :
          vorticityRowAmplitude tail wave ^ 2 =
            complexCoordinateAmplitudeSq (state wave) := by
        rw [vorticityRowAmplitude_sq,
          ← complexCoordinateAmplitudeSq_eq_complexCoordinateVectorNormSq]
        simp [tail, complexSharpSupportProjection_apply, waveMem,
          complexCoordinateAmplitudeSq]
      rw [amplitudeEq]
      exact mul_le_mul_of_nonneg_right radiusSqLe
        (complexCoordinateAmplitudeSq_nonneg _)
  unfold wholeVorticityEuclideanMass wholeStateVorticityGradientMass
  change
    (radius : ℝ) ^ 2 *
        (∑' wave : IntegerWavevector,
          vorticityRowAmplitude tail wave ^ 2) ≤ _
  rw [← tsum_mul_left]
  exact Summable.tsum_le_tsum
    pointwise leftSummable gradientSummable

/-- The canonical punctured restart inventory has the same quantitative
tail bound whenever the physical zero row vanishes. -/
theorem wholeVorticity_puncturedCubeTail_le_gradient_div_sq
    (state : ComplexVorticityHilbertState)
    (zeroRow : state 0 = 0)
    (gradientSummable :
      Summable fun wave : IntegerWavevector =>
        integerWaveNormSq wave *
          complexCoordinateAmplitudeSq (state wave))
    (radius : ℕ)
    (radiusPos : 0 < radius) :
    wholeVorticityEuclideanMass
        (complexSharpSupportProjection
          (wholeRestartModes radius) state - state) ≤
      wholeStateVorticityGradientMass state / (radius : ℝ) ^ 2 := by
  have projectionEq :
      complexSharpSupportProjection (wholeRestartModes radius) state =
        complexSharpSupportProjection
          (integerWaveFrequencyCube radius) state := by
    ext wave coordinate
    by_cases waveZero : wave = 0
    · subst wave
      simp [wholeRestartModes, puncturedIntegerWaveFrequencyCube,
        complexSharpSupportProjection_apply, zeroRow]
    · simp [wholeRestartModes, puncturedIntegerWaveFrequencyCube,
        complexSharpSupportProjection_apply, waveZero]
  rw [projectionEq]
  have core :=
    wholeVorticity_cubeComplement_mul_radius_sq_le_gradient
      state gradientSummable radius
  have radiusRealPos : 0 < (radius : ℝ) := by
    exact_mod_cast radiusPos
  apply (le_div_iff₀ (sq_pos_of_pos radiusRealPos)).2
  simpa [mul_comm] using core

private theorem finiteStateVelocityMajorant_projection_of_subset_agmon
    {smaller larger : Finset IntegerWavevector}
    (subset : smaller ⊆ larger)
    (state : ComplexVorticityHilbertState) :
    finiteStateVelocityMajorant larger
        (complexSharpSupportProjection smaller state) =
      finiteStateVelocityMajorant smaller state := by
  rw [← finiteStateVelocityMajorant_sharpSupportProjection smaller state]
  unfold finiteStateVelocityMajorant finiteVelocityFourierMajorant
  symm
  apply Finset.sum_subset_zero_on_sdiff subset
  · intro wave waveDiff
    have waveNotMem : wave ∉ smaller :=
      (Finset.mem_sdiff.mp waveDiff).2
    simp [finiteStateVelocityCoefficient,
      complexSharpSupportProjection_apply, waveNotMem,
      biotSavartVelocityCoefficient_zero_vorticity,
      complexCoordinateAmplitudeSq]
  · intro wave waveMem
    rfl

private theorem
    finiteStateVorticityCoefficientEnstrophy_projection_of_subset_agmon
    {smaller larger : Finset IntegerWavevector}
    (subset : smaller ⊆ larger)
    (state : ComplexVorticityHilbertState) :
    finiteStateVorticityCoefficientEnstrophy larger
        (complexSharpSupportProjection smaller state) =
      finiteStateVorticityCoefficientEnstrophy smaller state := by
  unfold finiteStateVorticityCoefficientEnstrophy
  symm
  apply Finset.sum_subset_zero_on_sdiff subset
  · intro wave waveDiff
    have waveNotMem : wave ∉ smaller :=
      (Finset.mem_sdiff.mp waveDiff).2
    simp [complexSharpSupportProjection_apply, waveNotMem,
      complexCoordinateAmplitudeSq]
  · intro wave waveMem
    simp [complexSharpSupportProjection_apply, waveMem]

private theorem finiteStateVelocityMajorant_projection_sub_eq_high_agmon
    (ambient lowModes : Finset IntegerWavevector)
    (state : ComplexVorticityHilbertState) :
    finiteStateVelocityMajorant ambient
        (complexSharpSupportProjection lowModes state - state) =
      finiteStateVelocityMajorant (ambient \ lowModes) state := by
  unfold finiteStateVelocityMajorant finiteVelocityFourierMajorant
  rw [← Finset.sum_inter_add_sum_sdiff ambient lowModes
    (fun wave =>
      √(complexCoordinateAmplitudeSq
        (finiteStateVelocityCoefficient
          (complexSharpSupportProjection lowModes state - state) wave)))]
  have lowZero :
      (∑ wave ∈ ambient ∩ lowModes,
        √(complexCoordinateAmplitudeSq
          (finiteStateVelocityCoefficient
            (complexSharpSupportProjection lowModes state - state)
              wave))) = 0 := by
    apply Finset.sum_eq_zero
    intro wave waveMem
    have waveLow : wave ∈ lowModes :=
      (Finset.mem_inter.mp waveMem).2
    have rowZero :
        (complexSharpSupportProjection lowModes state - state) wave = 0 := by
      simp [complexSharpSupportProjection_apply, waveLow]
    have coefficientZero :
        finiteStateVelocityCoefficient
            (complexSharpSupportProjection lowModes state - state) wave =
          0 := by
      unfold finiteStateVelocityCoefficient
      rw [rowZero]
      exact biotSavartVelocityCoefficient_zero_vorticity wave
    rw [coefficientZero]
    simp [complexCoordinateAmplitudeSq]
  rw [lowZero, zero_add]
  apply Finset.sum_congr rfl
  intro wave waveMem
  have waveNotLow : wave ∉ lowModes :=
    (Finset.mem_sdiff.mp waveMem).2
  have coefficientNeg :
      finiteStateVelocityCoefficient
          (complexSharpSupportProjection lowModes state - state) wave =
        -finiteStateVelocityCoefficient state wave := by
    rw [finiteStateVelocityCoefficient_sub]
    simp [finiteStateVelocityCoefficient,
      complexSharpSupportProjection_apply, waveNotLow,
      biotSavartVelocityCoefficient_zero_vorticity]
  rw [coefficientNeg]
  congr 1
  unfold complexCoordinateAmplitudeSq
  apply Finset.sum_congr rfl
  intro coordinate coordinateMem
  simp

private theorem
    finiteStateVorticityCoefficientEnstrophy_projection_sub_eq_high_agmon
    (ambient lowModes : Finset IntegerWavevector)
    (state : ComplexVorticityHilbertState) :
    finiteStateVorticityCoefficientEnstrophy ambient
        (complexSharpSupportProjection lowModes state - state) =
      finiteStateVorticityCoefficientEnstrophy
        (ambient \ lowModes) state := by
  unfold finiteStateVorticityCoefficientEnstrophy
  rw [← Finset.sum_inter_add_sum_sdiff ambient lowModes
    (fun wave => complexCoordinateAmplitudeSq
      ((complexSharpSupportProjection lowModes state - state) wave))]
  have lowZero :
      (∑ wave ∈ ambient ∩ lowModes,
        complexCoordinateAmplitudeSq
          ((complexSharpSupportProjection lowModes state - state)
            wave)) = 0 := by
    apply Finset.sum_eq_zero
    intro wave waveMem
    have waveLow : wave ∈ lowModes :=
      (Finset.mem_inter.mp waveMem).2
    simp [complexSharpSupportProjection_apply, waveLow,
      complexCoordinateAmplitudeSq]
  rw [lowZero, zero_add]
  apply Finset.sum_congr rfl
  intro wave waveMem
  have waveNotLow : wave ∉ lowModes :=
    (Finset.mem_sdiff.mp waveMem).2
  simp [complexSharpSupportProjection_apply, waveNotLow,
    complexCoordinateAmplitudeSq]

/-- The finite velocity majorant admits a scale-critical low/high split
whose constant is independent of the retained Fourier inventory. -/
theorem finiteStateVelocityMajorant_sq_le_agmonSplit
    (modes : Finset IntegerWavevector)
    (state : ComplexVorticityHilbertState)
    (radius : ℕ)
    (radiusPos : 0 < radius) :
    finiteStateVelocityMajorant modes state ^ 2 ≤
      52 * biotSavartSerrinConstant *
        ((radius : ℝ) *
            finiteStateVorticityCoefficientEnstrophy modes state +
          (radius : ℝ)⁻¹ *
            finiteStateVorticityEnstrophyMass modes state) := by
  let lowModes := modes ∩ integerWaveFrequencyCube radius
  let highModes := modes \ integerWaveFrequencyCube radius
  let low := finiteStateVelocityMajorant lowModes state
  let high := finiteStateVelocityMajorant highModes state
  have split :
      low + high = finiteStateVelocityMajorant modes state := by
    unfold low high lowModes highModes finiteStateVelocityMajorant
      finiteVelocityFourierMajorant
    exact Finset.sum_inter_add_sum_sdiff
      modes (integerWaveFrequencyCube radius) _
  have lowBound :
      low ^ 2 ≤
        26 * biotSavartSerrinConstant * (radius : ℝ) *
          finiteStateVorticityCoefficientEnstrophy modes state :=
    finiteStateVelocityMajorant_low_sq_le_agmon modes state radius
  have highBound :
      high ^ 2 ≤
        26 * biotSavartSerrinConstant * (radius : ℝ)⁻¹ *
          finiteStateVorticityEnstrophyMass modes state :=
    finiteStateVelocityMajorant_high_sq_le_agmon
      modes state radius radiusPos
  rw [← split]
  nlinarith [sq_nonneg (low - high)]

/-- On one complete frequency cube, the Biot--Savart velocity majorant is
subcritical: its square costs only one power of the cube radius and the
unweighted vorticity mass. -/
theorem finiteStateVelocityMajorant_frequencyCube_sq_le_subcritical
    (radius : ℕ)
    (state : ComplexVorticityHilbertState) :
    finiteStateVelocityMajorant
        (integerWaveFrequencyCube radius) state ^ 2 ≤
      26 * biotSavartSerrinConstant * (radius : ℝ) *
        finiteStateVorticityCoefficientEnstrophy
          (integerWaveFrequencyCube radius) state := by
  simpa only [Finset.inter_self] using
    finiteStateVelocityMajorant_low_sq_le_agmon
      (integerWaveFrequencyCube radius) state radius

/-- Pointwise velocity on a fixed physical band has the scale-critical
parabolic bound.  The two factors on the right are precisely the normalized
band radius and normalized vorticity mass. -/
theorem finiteRealComplexFourierVelocityField_parabolicScale_norm_sq_le
    (radius : ℕ)
    (state : ComplexVorticityHilbertState)
    (scale : ℝ)
    (scaleNonneg : 0 ≤ scale)
    (center point : PhysicalSpace) :
    ‖scale •
        finiteRealComplexFourierField
          (integerWaveFrequencyCube radius)
          (finiteStateVelocityCoefficient state)
          (center + scale • point)‖ ^ 2 ≤
      26 * biotSavartSerrinConstant *
        (scale * (radius : ℝ)) *
        (scale * finiteStateVorticityCoefficientEnstrophy
          (integerWaveFrequencyCube radius) state) := by
  let modes := integerWaveFrequencyCube radius
  let field := finiteRealComplexFourierField modes
    (finiteStateVelocityCoefficient state) (center + scale • point)
  have fieldBound :
      ‖field‖ ^ 2 ≤ finiteStateVelocityMajorant modes state ^ 2 := by
    simpa only [field, modes, finiteStateVelocityMajorant] using
      finiteRealComplexFourierField_norm_sq_le_velocityMajorant_sq
        modes (finiteStateVelocityCoefficient state)
          (center + scale • point)
  have majorantBound :=
    finiteStateVelocityMajorant_frequencyCube_sq_le_subcritical
      radius state
  calc
    ‖scale • field‖ ^ 2 = scale ^ 2 * ‖field‖ ^ 2 := by
      rw [norm_smul, Real.norm_of_nonneg scaleNonneg]
      ring
    _ ≤ scale ^ 2 * finiteStateVelocityMajorant modes state ^ 2 :=
      mul_le_mul_of_nonneg_left fieldBound (sq_nonneg scale)
    _ ≤ scale ^ 2 *
        (26 * biotSavartSerrinConstant * (radius : ℝ) *
          finiteStateVorticityCoefficientEnstrophy modes state) :=
      mul_le_mul_of_nonneg_left majorantBound (sq_nonneg scale)
    _ = 26 * biotSavartSerrinConstant *
        (scale * (radius : ℝ)) *
        (scale * finiteStateVorticityCoefficientEnstrophy modes state) := by
      ring

/-- The same fixed-band estimate applied to a state difference is the
uniform time modulus needed by the scaled velocity family. -/
theorem finiteRealComplexFourierVelocityField_parabolicScale_norm_sub_sq_le
    (radius : ℕ)
    (left right : ComplexVorticityHilbertState)
    (scale : ℝ)
    (scaleNonneg : 0 ≤ scale)
    (center point : PhysicalSpace) :
    ‖scale •
          finiteRealComplexFourierField
            (integerWaveFrequencyCube radius)
            (finiteStateVelocityCoefficient left)
            (center + scale • point) -
        scale •
          finiteRealComplexFourierField
            (integerWaveFrequencyCube radius)
            (finiteStateVelocityCoefficient right)
            (center + scale • point)‖ ^ 2 ≤
      26 * biotSavartSerrinConstant *
        (scale * (radius : ℝ)) *
        (scale * finiteStateVorticityCoefficientEnstrophy
          (integerWaveFrequencyCube radius) (left - right)) := by
  let modes := integerWaveFrequencyCube radius
  let point' := center + scale • point
  have fieldSub :
      finiteRealComplexFourierField modes
          (finiteStateVelocityCoefficient left) point' -
        finiteRealComplexFourierField modes
          (finiteStateVelocityCoefficient right) point' =
      finiteRealComplexFourierField modes
          (finiteStateVelocityCoefficient (left - right)) point' := by
    unfold finiteRealComplexFourierField
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro wave _waveMem
    rw [finiteStateVelocityCoefficient_sub]
    ext coordinate
    simp [realComplexFourierMode, coefficientReal, coefficientImag]
    ring
  rw [← smul_sub, fieldSub]
  exact finiteRealComplexFourierVelocityField_parabolicScale_norm_sq_le
    radius (left - right) scale scaleNonneg center point

/-- The finite Biot--Savart velocity gradient is paid by the unweighted
vorticity mass on the same inventory. -/
theorem finiteBiotSavartVelocityState_gradientMass_le
    (modes : Finset IntegerWavevector)
    (state : ComplexVorticityHilbertState) :
    finiteStateVorticityEnstrophyMass modes
        (finiteComplexVorticityState modes
          (finiteStateVelocityCoefficient state)) ≤
      biotSavartSerrinConstant *
        finiteStateVorticityCoefficientEnstrophy modes state := by
  unfold finiteStateVorticityEnstrophyMass
    finiteStateVorticityCoefficientEnstrophy
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro wave waveMem
  rw [finiteComplexVorticityState_apply, if_pos waveMem]
  by_cases waveZero : wave = 0
  · subst wave
    have normZero : integerWaveNormSq (0 : IntegerWavevector) = 0 := by
      simp [integerWaveNormSq]
    rw [normZero, zero_mul]
    exact mul_nonneg biotSavartSerrinConstant_nonneg
      (complexCoordinateAmplitudeSq_nonneg (state 0))
  · have rowBound :=
      finiteStateVelocityCoefficient_subcriticalAmplitudeSq_le state wave
    have normNonneg : 0 ≤ integerWaveNormSq wave :=
      integerWaveNormSq_nonneg wave
    calc
      integerWaveNormSq wave *
            complexCoordinateAmplitudeSq
              (finiteStateVelocityCoefficient state wave) ≤
          integerWaveNormSq wave *
            (biotSavartSerrinConstant *
              (integerWaveNormSq wave)⁻¹ *
                complexCoordinateAmplitudeSq (state wave)) :=
        mul_le_mul_of_nonneg_left rowBound normNonneg
      _ = biotSavartSerrinConstant *
            complexCoordinateAmplitudeSq (state wave) := by
        field_simp [integerWaveNormSq_ne_zero waveZero]

/-- Spatial equicontinuity of the scaled fixed-band velocity.  In source
applications, `scale³ * card` and `scale * mass` are both uniformly bounded,
so the displayed constant is independent of the expanding torus. -/
theorem finiteRealComplexFourierVelocityField_parabolicScale_norm_sub_le
    (modes : Finset IntegerWavevector)
    (state : ComplexVorticityHilbertState)
    (scale : ℝ)
    (scaleNonneg : 0 ≤ scale)
    (center x y : PhysicalSpace) :
    ‖scale •
          finiteRealComplexFourierField modes
            (finiteStateVelocityCoefficient state) (center + scale • y) -
        scale •
          finiteRealComplexFourierField modes
            (finiteStateVelocityCoefficient state) (center + scale • x)‖ ≤
      scale ^ 2 *
        Real.sqrt
          ((modes.card : ℝ) * (2 * Real.pi) ^ 2 *
            (biotSavartSerrinConstant *
              finiteStateVorticityCoefficientEnstrophy modes state)) *
        ‖y - x‖ := by
  let velocityState : ComplexVorticityHilbertState :=
    finiteComplexVorticityState modes (finiteStateVelocityCoefficient state)
  have fieldEq (point : PhysicalSpace) :
      finiteRealComplexFourierField modes velocityState point =
        finiteRealComplexFourierField modes
          (finiteStateVelocityCoefficient state) point := by
    unfold finiteRealComplexFourierField
    apply Finset.sum_congr rfl
    intro wave waveMem
    rw [show velocityState wave = finiteStateVelocityCoefficient state wave by
      simp [velocityState, waveMem]]
  have gradientBound :
      finiteStateVorticityEnstrophyMass modes velocityState ≤
        biotSavartSerrinConstant *
          finiteStateVorticityCoefficientEnstrophy modes state := by
    simpa only [velocityState] using
      finiteBiotSavartVelocityState_gradientMass_le modes state
  have unscaled :=
    finiteRealComplexFourierField_norm_sub_le_sqrt_card_gradientMass_mul_norm_sub
      modes velocityState (center + scale • x) (center + scale • y)
  rw [fieldEq, fieldEq] at unscaled
  have sqrtBound :
      Real.sqrt
          ((modes.card : ℝ) * (2 * Real.pi) ^ 2 *
            finiteStateVorticityEnstrophyMass modes velocityState) ≤
        Real.sqrt
          ((modes.card : ℝ) * (2 * Real.pi) ^ 2 *
            (biotSavartSerrinConstant *
              finiteStateVorticityCoefficientEnstrophy modes state)) := by
    apply Real.sqrt_le_sqrt
    exact mul_le_mul_of_nonneg_left gradientBound
      (mul_nonneg (Nat.cast_nonneg modes.card) (sq_nonneg _))
  calc
    ‖scale •
          finiteRealComplexFourierField modes
            (finiteStateVelocityCoefficient state) (center + scale • y) -
        scale •
          finiteRealComplexFourierField modes
            (finiteStateVelocityCoefficient state) (center + scale • x)‖ =
        scale *
          ‖finiteRealComplexFourierField modes
                (finiteStateVelocityCoefficient state) (center + scale • y) -
            finiteRealComplexFourierField modes
                (finiteStateVelocityCoefficient state)
                (center + scale • x)‖ := by
      rw [← smul_sub, norm_smul, Real.norm_of_nonneg scaleNonneg]
    _ ≤ scale *
        (Real.sqrt
            ((modes.card : ℝ) * (2 * Real.pi) ^ 2 *
              finiteStateVorticityEnstrophyMass modes velocityState) *
          ‖(center + scale • y) - (center + scale • x)‖) :=
      mul_le_mul_of_nonneg_left unscaled scaleNonneg
    _ ≤ scale *
        (Real.sqrt
            ((modes.card : ℝ) * (2 * Real.pi) ^ 2 *
              (biotSavartSerrinConstant *
                finiteStateVorticityCoefficientEnstrophy modes state)) *
          ‖(center + scale • y) - (center + scale • x)‖) := by
      gcongr
    _ = scale ^ 2 *
        Real.sqrt
          ((modes.card : ℝ) * (2 * Real.pi) ^ 2 *
            (biotSavartSerrinConstant *
              finiteStateVorticityCoefficientEnstrophy modes state)) *
        ‖y - x‖ := by
      have argumentDifference :
          (center + scale • y) - (center + scale • x) =
            scale • (y - x) := by
        module
      rw [argumentDifference, norm_smul,
        Real.norm_of_nonneg scaleNonneg]
      ring

private theorem finiteStateVorticityCoefficientEnstrophy_nonneg_agmon
    (modes : Finset IntegerWavevector)
    (state : ComplexVorticityHilbertState) :
    0 ≤ finiteStateVorticityCoefficientEnstrophy modes state := by
  unfold finiteStateVorticityCoefficientEnstrophy
  exact Finset.sum_nonneg fun wave waveMem =>
    complexCoordinateAmplitudeSq_nonneg _

private theorem finiteStateVorticityCoefficientEnstrophy_le_gradientMass
    (modes : Finset IntegerWavevector)
    (state : ComplexVorticityHilbertState)
    (zeroNotMem : (0 : IntegerWavevector) ∉ modes) :
    finiteStateVorticityCoefficientEnstrophy modes state ≤
      finiteStateVorticityEnstrophyMass modes state := by
  unfold finiteStateVorticityCoefficientEnstrophy
    finiteStateVorticityEnstrophyMass
  apply Finset.sum_le_sum
  intro wave waveMem
  have waveNe : wave ≠ 0 := by
    intro waveZero
    subst wave
    exact zeroNotMem waveMem
  have frequencyOne : 1 ≤ integerWaveNormSq wave :=
    one_le_integerWaveNormSq wave waveNe
  have amplitudeNonneg :=
    complexCoordinateAmplitudeSq_nonneg (state wave)
  nlinarith

/-- On a punctured finite carrier the Fourier velocity majorant satisfies
the scale-critical Agmon fourth-power estimate. -/
theorem finiteStateVelocityMajorant_pow_four_le_agmon
    (modes : Finset IntegerWavevector)
    (state : ComplexVorticityHilbertState)
    (zeroNotMem : (0 : IntegerWavevector) ∉ modes) :
    finiteStateVelocityMajorant modes state ^ 4 ≤
      24336 * biotSavartSerrinConstant ^ 2 *
        finiteStateVorticityCoefficientEnstrophy modes state *
        finiteStateVorticityEnstrophyMass modes state := by
  let M := finiteStateVorticityCoefficientEnstrophy modes state
  let W := finiteStateVorticityEnstrophyMass modes state
  let U := finiteStateVelocityMajorant modes state
  have Mnonneg : 0 ≤ M :=
    finiteStateVorticityCoefficientEnstrophy_nonneg_agmon modes state
  have Wnonneg : 0 ≤ W :=
    finiteStateVorticityEnstrophyMass_nonneg modes state
  have MleW : M ≤ W :=
    finiteStateVorticityCoefficientEnstrophy_le_gradientMass
      modes state zeroNotMem
  by_cases Mzero : M = 0
  · have termsZero :
        ∀ wave ∈ modes,
          complexCoordinateAmplitudeSq (state wave) = 0 := by
      have sumZero :
          ∑ wave ∈ modes,
            complexCoordinateAmplitudeSq (state wave) = 0 := by
        simpa [M, finiteStateVorticityCoefficientEnstrophy]
          using Mzero
      exact
        (Finset.sum_eq_zero_iff_of_nonneg
          (fun wave waveMem =>
            complexCoordinateAmplitudeSq_nonneg (state wave))).mp
          sumZero
    have Wzero : W = 0 := by
      unfold W finiteStateVorticityEnstrophyMass
      exact Finset.sum_eq_zero fun wave waveMem => by
        rw [termsZero wave waveMem, mul_zero]
    have base :=
      finiteStateVelocityMajorant_sq_le_agmonSplit
        modes state 1 (by norm_num)
    have base' :
        U ^ 2 ≤
          52 * biotSavartSerrinConstant *
            ((1 : ℝ) * M + (1 : ℝ)⁻¹ * W) := by
      simpa [U, M, W] using base
    change U ^ 4 ≤
      24336 * biotSavartSerrinConstant ^ 2 * M * W
    rw [Mzero, Wzero] at base' ⊢
    norm_num at base' ⊢
    rw [base']
    norm_num
  · have Mpos : 0 < M :=
      lt_of_le_of_ne Mnonneg (Ne.symm Mzero)
    have Wpos : 0 < W := Mpos.trans_le MleW
    let q : ℝ := Real.sqrt (W / M)
    have ratioNonneg : 0 ≤ W / M :=
      div_nonneg Wnonneg Mnonneg
    have ratioOne : 1 ≤ W / M :=
      (le_div_iff₀ Mpos).2 (by simpa using MleW)
    have qNonneg : 0 ≤ q := Real.sqrt_nonneg _
    have qPos : 0 < q :=
      Real.sqrt_pos.2 (div_pos Wpos Mpos)
    have qSq : q ^ 2 = W / M :=
      Real.sq_sqrt ratioNonneg
    have qOne : 1 ≤ q := by
      nlinarith
    have WMul : W = q ^ 2 * M :=
      ((eq_div_iff (ne_of_gt Mpos)).mp qSq).symm
    let radius : ℕ := Nat.ceil q
    have radiusPos : 0 < radius := Nat.ceil_pos.mpr qPos
    have qLeRadius : q ≤ (radius : ℝ) := Nat.le_ceil q
    have radiusLt : (radius : ℝ) < q + 1 :=
      Nat.ceil_lt_add_one qNonneg
    have radiusLeTwoQ : (radius : ℝ) ≤ 2 * q := by
      linarith
    have radiusM : (radius : ℝ) * M ≤ 2 * q * M :=
      mul_le_mul_of_nonneg_right radiusLeTwoQ Mnonneg
    have inverseRadiusLe : (radius : ℝ)⁻¹ ≤ q⁻¹ :=
      inv_anti₀ qPos qLeRadius
    have inverseRadiusW : (radius : ℝ)⁻¹ * W ≤ q * M := by
      calc
        (radius : ℝ)⁻¹ * W ≤ q⁻¹ * W :=
          mul_le_mul_of_nonneg_right inverseRadiusLe Wnonneg
        _ = q * M := by
          rw [WMul]
          field_simp [ne_of_gt qPos]
    have bracket :
        (radius : ℝ) * M + (radius : ℝ)⁻¹ * W ≤
          3 * q * M := by
      linarith
    have base :=
      finiteStateVelocityMajorant_sq_le_agmonSplit
        modes state radius radiusPos
    have base' :
        U ^ 2 ≤ 52 * biotSavartSerrinConstant *
          ((radius : ℝ) * M + (radius : ℝ)⁻¹ * W) := by
      simpa [U, M, W] using base
    have coefficientNonneg :
        0 ≤ 52 * biotSavartSerrinConstant :=
      mul_nonneg (by norm_num) biotSavartSerrinConstant_nonneg
    have UBound :
        U ^ 2 ≤
          156 * biotSavartSerrinConstant * q * M := by
      calc
        U ^ 2 ≤ 52 * biotSavartSerrinConstant *
            ((radius : ℝ) * M + (radius : ℝ)⁻¹ * W) :=
          base'
        _ ≤ 52 * biotSavartSerrinConstant * (3 * q * M) :=
          mul_le_mul_of_nonneg_left bracket coefficientNonneg
        _ = 156 * biotSavartSerrinConstant * q * M := by
          ring
    have rightNonneg :
        0 ≤ 156 * biotSavartSerrinConstant * q * M :=
      mul_nonneg
        (mul_nonneg
          (mul_nonneg (by norm_num)
            biotSavartSerrinConstant_nonneg)
          qNonneg)
        Mnonneg
    change U ^ 4 ≤
      24336 * biotSavartSerrinConstant ^ 2 * M * W
    calc
      U ^ 4 = (U ^ 2) ^ 2 := by ring
      _ ≤ (156 * biotSavartSerrinConstant * q * M) ^ 2 :=
        (sq_le_sq₀ (sq_nonneg U) rightNonneg).2 UBound
      _ = 24336 * biotSavartSerrinConstant ^ 2 * M * W := by
        rw [WMul]
        ring

/-- The finite Agmon estimate exhausts the whole Fourier carrier whenever
the actual whole vorticity-gradient density is summable. -/
theorem wholeStateVelocityMajorant_pow_four_le_agmon
    (state : ComplexVorticityHilbertState)
    (gradientSummable :
      Summable fun wave : IntegerWavevector =>
        integerWaveNormSq wave *
          complexCoordinateAmplitudeSq (state wave)) :
    wholeStateVelocityMajorant state ^ 4 ≤
      24336 * biotSavartSerrinConstant ^ 2 *
        wholeVorticityEuclideanMass state *
        wholeStateVorticityGradientMass state := by
  let term := fun wave : IntegerWavevector =>
    Real.sqrt
      (complexCoordinateAmplitudeSq
        (finiteStateVelocityCoefficient state wave))
  have termSummable : Summable term := by
    simpa only [term] using
      summable_wholeStateVelocityAmplitude state gradientSummable
  have zeroTerm : term 0 = 0 := by
    simp [term, finiteStateVelocityCoefficient,
      complexCoordinateAmplitudeSq]
  unfold wholeStateVelocityMajorant
  apply le_of_tendsto (termSummable.hasSum.pow 4)
  exact Filter.Eventually.of_forall fun modes => by
    have eraseMajorant :
        (∑ wave ∈ modes, term wave) =
          finiteStateVelocityMajorant (modes.erase 0) state := by
      unfold finiteStateVelocityMajorant finiteVelocityFourierMajorant
      change (∑ wave ∈ modes, term wave) =
        ∑ wave ∈ modes.erase 0, term wave
      by_cases zeroMem : (0 : IntegerWavevector) ∈ modes
      · have eraseAdd :=
          Finset.sum_erase_add (s := modes) (f := term) zeroMem
        linarith
      · rw [Finset.erase_eq_of_notMem zeroMem]
    rw [eraseMajorant]
    have zeroNotMem :
        (0 : IntegerWavevector) ∉ modes.erase 0 := by
      simp
    have finiteBound :=
      finiteStateVelocityMajorant_pow_four_le_agmon
        (modes.erase 0) state zeroNotMem
    have finiteMassLe :=
      finiteStateVorticityCoefficientEnstrophy_le_wholeMass
        (modes.erase 0) state
    have finiteGradientLe :=
      finiteStateVorticityEnstrophyMass_le_wholeGradientMass
        (modes.erase 0) state gradientSummable
    have coefficientNonneg :
        0 ≤ 24336 * biotSavartSerrinConstant ^ 2 := by
      positivity
    have finiteGradientNonneg :
        0 ≤ finiteStateVorticityEnstrophyMass
          (modes.erase 0) state :=
      finiteStateVorticityEnstrophyMass_nonneg _ _
    have wholeMassNonneg :
        0 ≤ wholeVorticityEuclideanMass state := by
      unfold wholeVorticityEuclideanMass
      exact tsum_nonneg fun wave => sq_nonneg _
    calc
      finiteStateVelocityMajorant (modes.erase 0) state ^ 4 ≤
          24336 * biotSavartSerrinConstant ^ 2 *
            finiteStateVorticityCoefficientEnstrophy
              (modes.erase 0) state *
            finiteStateVorticityEnstrophyMass
              (modes.erase 0) state :=
        finiteBound
      _ ≤
          24336 * biotSavartSerrinConstant ^ 2 *
            wholeVorticityEuclideanMass state *
            finiteStateVorticityEnstrophyMass
              (modes.erase 0) state :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left finiteMassLe coefficientNonneg)
          finiteGradientNonneg
      _ ≤
          24336 * biotSavartSerrinConstant ^ 2 *
            wholeVorticityEuclideanMass state *
            wholeStateVorticityGradientMass state :=
        mul_le_mul_of_nonneg_left finiteGradientLe
          (mul_nonneg coefficientNonneg wholeMassNonneg)

private theorem
    canonicalCubeVorticityNonlinearNegativeOneDensity_highOutputs_sum_le_agmon
    (state : ComplexVorticityHilbertState)
    (stateTransverse : WholeStateTransverse state)
    (radius : ℕ)
    (radiusPos : 0 < radius)
    (ambientRadius : ℕ)
    (outputs : Finset IntegerWavevector)
    (outputsSubset : outputs ⊆ integerWaveFrequencyCube ambientRadius)
    (outputsHigh :
      ∀ output ∈ outputs,
        output ∉ integerWaveFrequencyCube (2 * radius)) :
    (∑ output ∈ outputs,
        canonicalCubeVorticityNonlinearNegativeOneDensity
          ambientRadius state output) ≤
      728 * biotSavartSerrinConstant * (radius : ℝ)⁻¹ *
        finiteStateVorticityCoefficientEnstrophy
          (integerWaveFrequencyCube ambientRadius) state *
        finiteStateVorticityEnstrophyMass
          (integerWaveFrequencyCube ambientRadius) state := by
  classical
  let modes := integerWaveFrequencyCube ambientRadius
  let lowModes := modes ∩ integerWaveFrequencyCube radius
  let highModes := modes \ integerWaveFrequencyCube radius
  let lowState := complexSharpSupportProjection lowModes state
  let Ulow := finiteStateVelocityMajorant lowModes state
  let Uhigh := finiteStateVelocityMajorant highModes state
  let U := finiteStateVelocityMajorant modes state
  let Mlow := finiteStateVorticityCoefficientEnstrophy lowModes state
  let Mhigh := finiteStateVorticityCoefficientEnstrophy highModes state
  let M := finiteStateVorticityCoefficientEnstrophy modes state
  let W := finiteStateVorticityEnstrophyMass modes state
  let Q :=
    26 * biotSavartSerrinConstant * (radius : ℝ)⁻¹ * M * W
  have lowSubsetModes : lowModes ⊆ modes := Finset.inter_subset_left
  have lowSubsetCube : lowModes ⊆ integerWaveFrequencyCube radius :=
    Finset.inter_subset_right
  have highSubsetModes : highModes ⊆ modes := Finset.sdiff_subset
  have lowPairSubset :
      finiteVorticityPairOutputSupport lowModes ⊆
        integerWaveFrequencyCube (2 * radius) := by
    intro output outputMem
    apply finiteVorticityPairOutputSupport_cube_subset_doubledCube radius
    rw [finiteVorticityPairOutputSupport, Finset.mem_image] at outputMem ⊢
    obtain ⟨pair, pairMem, rfl⟩ := outputMem
    obtain ⟨firstMem, secondMem⟩ := Finset.mem_product.mp pairMem
    exact ⟨pair,
      Finset.mem_product.mpr
        ⟨lowSubsetCube firstMem, lowSubsetCube secondMem⟩,
      rfl⟩
  have lowRowZero :
      ∀ output ∈ outputs,
        finiteStateVorticityNonlinearCoefficientAt modes lowState output =
          0 := by
    intro output outputMem
    rw [finiteStateVorticityNonlinearCoefficientAt_projection_of_subset
      lowSubsetModes]
    apply finiteStateVorticityNonlinearCoefficientAt_eq_zero_of_not_mem_pairOutput
    intro outputPairMem
    exact (outputsHigh output outputMem) (lowPairSubset outputPairMem)
  have densityEq :
      ∀ output ∈ outputs,
        canonicalCubeVorticityNonlinearNegativeOneDensity
            ambientRadius state output =
          canonicalCubeVorticityNonlinearDifferenceNegativeOneDensity
            ambientRadius lowState state output := by
    intro output outputMem
    unfold canonicalCubeVorticityNonlinearNegativeOneDensity
      canonicalCubeVorticityNonlinearDifferenceNegativeOneDensity
    by_cases outputZero : output = 0
    · simp [outputZero]
    · rw [if_neg outputZero, if_neg outputZero]
      have rowZero := lowRowZero output outputMem
      have rowZero' :
          finiteStateVorticityNonlinearCoefficientAt
              (integerWaveFrequencyCube ambientRadius) lowState output = 0 := by
        simpa [modes] using rowZero
      rw [rowZero']
      simp
  have densitySumEq :
      (∑ output ∈ outputs,
          canonicalCubeVorticityNonlinearNegativeOneDensity
            ambientRadius state output) =
        ∑ output ∈ outputs,
          canonicalCubeVorticityNonlinearDifferenceNegativeOneDensity
            ambientRadius lowState state output := by
    apply Finset.sum_congr rfl
    intro output outputMem
    exact densityEq output outputMem
  have lowTransverse : WholeStateTransverse lowState := by
    exact wholeStateTransverse_sharpSupportProjection
      lowModes state stateTransverse
  have differenceMassBound :=
    finiteStateVorticityNonlinearDifferenceNegativeOneMass_le
      modes lowState state
      (finiteStateTransverseOn_of_wholeStateTransverse
        modes lowState lowTransverse)
      (finiteStateTransverseOn_of_wholeStateTransverse
        modes state stateTransverse)
  have lowVelocityEq :
      finiteStateVelocityMajorant modes lowState = Ulow := by
    simpa [lowState, Ulow] using
      finiteStateVelocityMajorant_projection_of_subset_agmon
        lowSubsetModes state
  have lowMassEq :
      finiteStateVorticityCoefficientEnstrophy modes lowState = Mlow := by
    simpa [lowState, Mlow] using
      finiteStateVorticityCoefficientEnstrophy_projection_of_subset_agmon
        lowSubsetModes state
  have highModesEq : modes \ lowModes = highModes := by
    ext wave
    simp [lowModes, highModes]
  have highVelocityEq :
      finiteStateVelocityMajorant modes (lowState - state) = Uhigh := by
    rw [finiteStateVelocityMajorant_projection_sub_eq_high_agmon]
    simp [highModesEq, Uhigh]
  have highMassEq :
      finiteStateVorticityCoefficientEnstrophy modes
          (lowState - state) = Mhigh := by
    rw [finiteStateVorticityCoefficientEnstrophy_projection_sub_eq_high_agmon]
    simp [highModesEq, Mhigh]
  rw [lowVelocityEq, lowMassEq, highVelocityEq, highMassEq] at differenceMassBound
  have differenceMassBound' :
      finiteStateVorticityNonlinearDifferenceNegativeOneMass
          modes lowState state ≤
        4 * ((Ulow ^ 2 + U ^ 2) * Mhigh +
          Uhigh ^ 2 * (Mlow + M)) := by
    simpa [U, M] using differenceMassBound
  have lowVelocityBound :
      Ulow ^ 2 ≤
        26 * biotSavartSerrinConstant * (radius : ℝ) * M := by
    simpa [Ulow, M, lowModes] using
      finiteStateVelocityMajorant_low_sq_le_agmon
        modes state radius
  have highVelocityBound :
      Uhigh ^ 2 ≤
        26 * biotSavartSerrinConstant * (radius : ℝ)⁻¹ * W := by
    simpa [Uhigh, W, highModes] using
      finiteStateVelocityMajorant_high_sq_le_agmon
        modes state radius radiusPos
  have highMassRadiusBound :
      (radius : ℝ) ^ 2 * Mhigh ≤ W := by
    simpa [Mhigh, W, highModes] using
      finiteStateVorticityCoefficientEnstrophy_high_mul_radius_sq_le_agmon
        modes state radius
  have lowMassLe : Mlow ≤ M := by
    exact finiteStateVorticityCoefficientEnstrophy_mono_agmon
      lowSubsetModes state
  have highMassLe : Mhigh ≤ M := by
    exact finiteStateVorticityCoefficientEnstrophy_mono_agmon
      highSubsetModes state
  have velocitySplit : Ulow + Uhigh = U := by
    unfold Ulow Uhigh U lowModes highModes
      finiteStateVelocityMajorant finiteVelocityFourierMajorant
    exact Finset.sum_inter_add_sum_sdiff
      modes (integerWaveFrequencyCube radius) _
  have UlowNonneg : 0 ≤ Ulow := by
    exact finiteStateVelocityMajorant_nonneg lowModes state
  have UhighNonneg : 0 ≤ Uhigh := by
    exact finiteStateVelocityMajorant_nonneg highModes state
  have MlowNonneg : 0 ≤ Mlow := by
    unfold Mlow finiteStateVorticityCoefficientEnstrophy
    exact Finset.sum_nonneg fun wave waveMem =>
      complexCoordinateAmplitudeSq_nonneg _
  have MhighNonneg : 0 ≤ Mhigh := by
    unfold Mhigh finiteStateVorticityCoefficientEnstrophy
    exact Finset.sum_nonneg fun wave waveMem =>
      complexCoordinateAmplitudeSq_nonneg _
  have Mnonneg : 0 ≤ M := by
    unfold M finiteStateVorticityCoefficientEnstrophy
    exact Finset.sum_nonneg fun wave waveMem =>
      complexCoordinateAmplitudeSq_nonneg _
  have Wnonneg : 0 ≤ W := by
    exact finiteStateVorticityEnstrophyMass_nonneg modes state
  have radiusRealPos : 0 < (radius : ℝ) := by
    exact_mod_cast radiusPos
  have radiusRealNe : (radius : ℝ) ≠ 0 := ne_of_gt radiusRealPos
  have Qnonneg : 0 ≤ Q := by
    unfold Q
    exact mul_nonneg
      (mul_nonneg
        (mul_nonneg
          (mul_nonneg (by norm_num) biotSavartSerrinConstant_nonneg)
          (inv_nonneg.mpr radiusRealPos.le))
        Mnonneg)
      Wnonneg
  have lowHighProductBound : Ulow ^ 2 * Mhigh ≤ Q := by
    calc
      Ulow ^ 2 * Mhigh ≤
          (26 * biotSavartSerrinConstant * (radius : ℝ) * M) *
            Mhigh :=
        mul_le_mul_of_nonneg_right lowVelocityBound MhighNonneg
      _ =
          (26 * biotSavartSerrinConstant * (radius : ℝ)⁻¹ * M) *
            ((radius : ℝ) ^ 2 * Mhigh) := by
        field_simp [radiusRealNe]
      _ ≤
          (26 * biotSavartSerrinConstant * (radius : ℝ)⁻¹ * M) *
            W := by
        exact mul_le_mul_of_nonneg_left highMassRadiusBound
          (mul_nonneg
            (mul_nonneg
              (mul_nonneg (by norm_num) biotSavartSerrinConstant_nonneg)
              (inv_nonneg.mpr radiusRealPos.le))
            Mnonneg)
      _ = Q := by rfl
  have highHighProductBound : Uhigh ^ 2 * Mhigh ≤ Q := by
    calc
      Uhigh ^ 2 * Mhigh ≤ Uhigh ^ 2 * M :=
        mul_le_mul_of_nonneg_left highMassLe (sq_nonneg Uhigh)
      _ ≤
          (26 * biotSavartSerrinConstant * (radius : ℝ)⁻¹ * W) *
            M :=
        mul_le_mul_of_nonneg_right highVelocityBound Mnonneg
      _ = Q := by
        unfold Q
        ring
  have highLowProductBound : Uhigh ^ 2 * Mlow ≤ Q := by
    calc
      Uhigh ^ 2 * Mlow ≤ Uhigh ^ 2 * M :=
        mul_le_mul_of_nonneg_left lowMassLe (sq_nonneg Uhigh)
      _ ≤
          (26 * biotSavartSerrinConstant * (radius : ℝ)⁻¹ * W) *
            M :=
        mul_le_mul_of_nonneg_right highVelocityBound Mnonneg
      _ = Q := by
        unfold Q
        ring
  have highWholeProductBound : Uhigh ^ 2 * M ≤ Q := by
    calc
      Uhigh ^ 2 * M ≤
          (26 * biotSavartSerrinConstant * (radius : ℝ)⁻¹ * W) *
            M :=
        mul_le_mul_of_nonneg_right highVelocityBound Mnonneg
      _ = Q := by
        unfold Q
        ring
  have stateVelocitySq :
      U ^ 2 ≤ 2 * Ulow ^ 2 + 2 * Uhigh ^ 2 := by
    rw [← velocitySplit]
    nlinarith [sq_nonneg (Ulow - Uhigh)]
  have firstTermBound :
      (Ulow ^ 2 + U ^ 2) * Mhigh ≤ 5 * Q := by
    calc
      (Ulow ^ 2 + U ^ 2) * Mhigh ≤
          (3 * Ulow ^ 2 + 2 * Uhigh ^ 2) * Mhigh := by
        exact mul_le_mul_of_nonneg_right
          (by linarith) MhighNonneg
      _ = 3 * (Ulow ^ 2 * Mhigh) +
          2 * (Uhigh ^ 2 * Mhigh) := by ring
      _ ≤ 3 * Q + 2 * Q := by
        exact add_le_add
          (mul_le_mul_of_nonneg_left lowHighProductBound (by norm_num))
          (mul_le_mul_of_nonneg_left highHighProductBound (by norm_num))
      _ = 5 * Q := by ring
  have secondTermBound :
      Uhigh ^ 2 * (Mlow + M) ≤ 2 * Q := by
    calc
      Uhigh ^ 2 * (Mlow + M) =
          Uhigh ^ 2 * Mlow + Uhigh ^ 2 * M := by ring
      _ ≤ Q + Q :=
        add_le_add highLowProductBound highWholeProductBound
      _ = 2 * Q := by ring
  rw [densitySumEq]
  calc
    (∑ output ∈ outputs,
        canonicalCubeVorticityNonlinearDifferenceNegativeOneDensity
          ambientRadius lowState state output) ≤
        finiteStateVorticityNonlinearDifferenceNegativeOneMass
          modes lowState state := by
      simpa [modes] using
        canonicalCubeVorticityNonlinearDifferenceNegativeOneDensity_sum_le_mass
          outputs ambientRadius lowState state outputsSubset
    _ ≤
        4 * ((Ulow ^ 2 + U ^ 2) * Mhigh +
          Uhigh ^ 2 * (Mlow + M)) := differenceMassBound'
    _ ≤ 4 * (5 * Q + 2 * Q) := by
      exact mul_le_mul_of_nonneg_left
        (add_le_add firstTermBound secondTermBound) (by norm_num)
    _ =
        728 * biotSavartSerrinConstant * (radius : ℝ)⁻¹ *
          finiteStateVorticityCoefficientEnstrophy
            (integerWaveFrequencyCube ambientRadius) state *
          finiteStateVorticityEnstrophyMass
            (integerWaveFrequencyCube ambientRadius) state := by
      unfold Q M W modes
      ring

/-- Every finite family of nonlinear outputs beyond twice a positive
frequency radius is paid by the same state's complete enstrophy and viscous
gradient ledger, with one inverse power of that radius. -/
theorem
    wholeStateVorticityNonlinearNegativeOneDensity_highOutputs_sum_le_agmon
    (outputs : Finset IntegerWavevector)
    (state : ComplexVorticityHilbertState)
    (stateTransverse : WholeStateTransverse state)
    (gradientSummable :
      Summable fun wave : IntegerWavevector =>
        integerWaveNormSq wave *
          complexCoordinateAmplitudeSq (state wave))
    (radius : ℕ)
    (radiusPos : 0 < radius)
    (outputsHigh :
      ∀ output ∈ outputs,
        output ∉ integerWaveFrequencyCube (2 * radius)) :
    (∑ output ∈ outputs,
        wholeStateVorticityNonlinearNegativeOneDensity state output) ≤
      728 * biotSavartSerrinConstant * (radius : ℝ)⁻¹ *
        wholeVorticityEuclideanMass state *
        wholeStateVorticityGradientMass state := by
  have sumTendsto :
      Filter.Tendsto
        (fun ambientRadius =>
          ∑ output ∈ outputs,
            canonicalCubeVorticityNonlinearNegativeOneDensity
              ambientRadius state output)
        Filter.atTop
        (nhds
          (∑ output ∈ outputs,
            wholeStateVorticityNonlinearNegativeOneDensity
              state output)) := by
    apply tendsto_finsetSum
    intro output outputMem
    exact canonicalCubeVorticityNonlinearNegativeOneDensity_tendsto
      state stateTransverse output
  have eventuallySubset :
      ∀ᶠ ambientRadius : ℕ in Filter.atTop,
        outputs ⊆ integerWaveFrequencyCube ambientRadius :=
    Filter.tendsto_atTop.1 integerWaveFrequencyCube_tendsto_atTop outputs
  apply le_of_tendsto sumTendsto
  filter_upwards [eventuallySubset] with ambientRadius outputsSubset
  have finiteBound :=
    canonicalCubeVorticityNonlinearNegativeOneDensity_highOutputs_sum_le_agmon
      state stateTransverse radius radiusPos ambientRadius outputs
      outputsSubset outputsHigh
  have finiteMassLe :=
    finiteStateVorticityCoefficientEnstrophy_le_wholeMass
      (integerWaveFrequencyCube ambientRadius) state
  have finiteGradientLe :=
    finiteStateVorticityEnstrophyMass_le_wholeGradientMass
      (integerWaveFrequencyCube ambientRadius) state gradientSummable
  have coefficientNonneg :
      0 ≤ 728 * biotSavartSerrinConstant * (radius : ℝ)⁻¹ := by
    exact mul_nonneg
      (mul_nonneg (by norm_num) biotSavartSerrinConstant_nonneg)
      (inv_nonneg.mpr (Nat.cast_nonneg radius))
  have finiteGradientNonneg :
      0 ≤ finiteStateVorticityEnstrophyMass
        (integerWaveFrequencyCube ambientRadius) state :=
    finiteStateVorticityEnstrophyMass_nonneg _ _
  have wholeMassNonneg : 0 ≤ wholeVorticityEuclideanMass state := by
    unfold wholeVorticityEuclideanMass
    exact tsum_nonneg fun wave => sq_nonneg _
  calc
    (∑ output ∈ outputs,
        canonicalCubeVorticityNonlinearNegativeOneDensity
          ambientRadius state output) ≤
        728 * biotSavartSerrinConstant * (radius : ℝ)⁻¹ *
          finiteStateVorticityCoefficientEnstrophy
            (integerWaveFrequencyCube ambientRadius) state *
          finiteStateVorticityEnstrophyMass
            (integerWaveFrequencyCube ambientRadius) state := finiteBound
    _ ≤
        728 * biotSavartSerrinConstant * (radius : ℝ)⁻¹ *
          wholeVorticityEuclideanMass state *
          finiteStateVorticityEnstrophyMass
            (integerWaveFrequencyCube ambientRadius) state :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left finiteMassLe coefficientNonneg)
        finiteGradientNonneg
    _ ≤
        728 * biotSavartSerrinConstant * (radius : ℝ)⁻¹ *
          wholeVorticityEuclideanMass state *
          wholeStateVorticityGradientMass state :=
      mul_le_mul_of_nonneg_left finiteGradientLe
        (mul_nonneg coefficientNonneg wholeMassNonneg)

private theorem
    wholeStateVelocityMajorant_projection_sub_sq_le_agmon
    (state : ComplexVorticityHilbertState)
    (gradientSummable :
      Summable fun wave : IntegerWavevector =>
        integerWaveNormSq wave *
          complexCoordinateAmplitudeSq (state wave))
    (radius : Nat)
    (radiusPos : 0 < radius) :
    wholeStateVelocityMajorant
          (complexSharpSupportProjection
            (integerWaveFrequencyCube radius) state - state) ^ 2 <=
      26 * biotSavartSerrinConstant * (radius : Real)⁻¹ *
        wholeStateVorticityGradientMass state := by
  let modes := integerWaveFrequencyCube radius
  let tail := complexSharpSupportProjection modes state - state
  have projectedGradientSummable :
      Summable fun wave : IntegerWavevector =>
        integerWaveNormSq wave *
          complexCoordinateAmplitudeSq
            ((complexSharpSupportProjection modes state) wave) :=
    summable_wholeStateVorticityGradientDensity_of_supported
      modes (complexSharpSupportProjection modes state)
      (complexSharpSupportProjection_supported modes state)
  have tailGradientSummable :
      Summable fun wave : IntegerWavevector =>
        integerWaveNormSq wave *
          complexCoordinateAmplitudeSq (tail wave) := by
    simpa only [tail] using
      summable_wholeStateVorticityGradientDensity_sub
        (complexSharpSupportProjection modes state) state
        projectedGradientSummable gradientSummable
  let term := fun wave : IntegerWavevector =>
    Real.sqrt
      (complexCoordinateAmplitudeSq
        (finiteStateVelocityCoefficient tail wave))
  have termSummable : Summable term := by
    simpa only [term] using
      summable_wholeStateVelocityAmplitude tail tailGradientSummable
  unfold wholeStateVelocityMajorant
  apply le_of_tendsto (termSummable.hasSum.pow 2)
  exact Filter.Eventually.of_forall fun ambient => by
    have tailEq :
        finiteStateVelocityMajorant ambient tail =
          finiteStateVelocityMajorant (ambient \ modes) state := by
      simpa only [tail] using
        finiteStateVelocityMajorant_projection_sub_eq_high_agmon
          ambient modes state
    have finiteBound :=
      finiteStateVelocityMajorant_high_sq_le_agmon
        ambient state radius radiusPos
    have finiteGradientLe :=
      finiteStateVorticityEnstrophyMass_le_wholeGradientMass
        ambient state gradientSummable
    have coefficientNonneg :
        0 <= 26 * biotSavartSerrinConstant * (radius : Real)⁻¹ := by
      exact mul_nonneg
        (mul_nonneg (by norm_num) biotSavartSerrinConstant_nonneg)
        (inv_nonneg.mpr (Nat.cast_nonneg radius))
    change
      (Finset.sum ambient term) ^ 2 <=
        26 * biotSavartSerrinConstant * (radius : Real)⁻¹ *
          wholeStateVorticityGradientMass state
    have finiteEq :
        Finset.sum ambient term = finiteStateVelocityMajorant ambient tail := by
      rfl
    rw [finiteEq, tailEq]
    exact finiteBound.trans
      (mul_le_mul_of_nonneg_left finiteGradientLe coefficientNonneg)

private theorem
    radius_sq_mul_wholeVorticityMass_projection_sub_le_gradientMass
    (state : ComplexVorticityHilbertState)
    (gradientSummable :
      Summable fun wave : IntegerWavevector =>
        integerWaveNormSq wave *
          complexCoordinateAmplitudeSq (state wave))
    (radius : Nat) :
    (radius : Real) ^ 2 *
        wholeVorticityEuclideanMass
          (complexSharpSupportProjection
            (integerWaveFrequencyCube radius) state - state) <=
      wholeStateVorticityGradientMass state := by
  let modes := integerWaveFrequencyCube radius
  let tail := complexSharpSupportProjection modes state - state
  have tailAmplitudeSummable :
      Summable fun wave : IntegerWavevector =>
        vorticityRowAmplitude tail wave ^ 2 :=
    summable_vorticityRowAmplitude_sq tail
  unfold wholeVorticityEuclideanMass
  apply le_of_tendsto
    ((tailAmplitudeSummable.hasSum.const_mul ((radius : Real) ^ 2)))
  exact Filter.Eventually.of_forall fun ambient => by
    have tailMassEq :
        (∑ wave ∈ ambient,
          vorticityRowAmplitude tail wave ^ 2) =
          finiteStateVorticityCoefficientEnstrophy
            (ambient \ modes) state := by
      rw [← finiteStateVorticityCoefficientEnstrophy_projection_sub_eq_high_agmon
        ambient modes state]
      unfold finiteStateVorticityCoefficientEnstrophy
      apply Finset.sum_congr rfl
      intro wave waveMem
      exact vorticityRowAmplitude_sq tail wave
    have finiteHigh :=
      finiteStateVorticityCoefficientEnstrophy_high_mul_radius_sq_le_agmon
        ambient state radius
    have finiteGradientLe :=
      finiteStateVorticityEnstrophyMass_le_wholeGradientMass
        ambient state gradientSummable
    change
      (radius : Real) ^ 2 *
          (∑ wave ∈ ambient,
            vorticityRowAmplitude tail wave ^ 2) <=
        wholeStateVorticityGradientMass state
    rw [tailMassEq]
    exact finiteHigh.trans finiteGradientLe

/-- Removing all inputs above a positive source radius changes the genuine
whole nonlinear `H^-1` action by at most the scale-critical `M * W / R`
debit.  The estimate is on the same state and does not supply a cutoff,
compactness certificate, or target landing. -/
theorem
    wholeStateVorticityNonlinearDifferenceNegativeOneMass_projection_le_agmon
    (state : ComplexVorticityHilbertState)
    (stateTransverse : WholeStateTransverse state)
    (gradientSummable :
      Summable fun wave : IntegerWavevector =>
        integerWaveNormSq wave *
          complexCoordinateAmplitudeSq (state wave))
    (radius : Nat)
    (radiusPos : 0 < radius) :
    wholeStateVorticityNonlinearDifferenceNegativeOneMass
        (complexSharpSupportProjection
          (integerWaveFrequencyCube radius) state)
        state <=
      728 * biotSavartSerrinConstant * (radius : Real)⁻¹ *
        wholeVorticityEuclideanMass state *
        wholeStateVorticityGradientMass state := by
  let modes := integerWaveFrequencyCube radius
  let low := complexSharpSupportProjection modes state
  let high := low - state
  let Ulow := wholeStateVelocityMajorant low
  let Uhigh := wholeStateVelocityMajorant high
  let U := wholeStateVelocityMajorant state
  let Mlow := wholeVorticityEuclideanMass low
  let Mhigh := wholeVorticityEuclideanMass high
  let M := wholeVorticityEuclideanMass state
  let W := wholeStateVorticityGradientMass state
  let Q :=
    26 * biotSavartSerrinConstant * (radius : Real)⁻¹ * M * W
  have lowGradientSummable :
      Summable fun wave : IntegerWavevector =>
        integerWaveNormSq wave *
          complexCoordinateAmplitudeSq (low wave) :=
    summable_wholeStateVorticityGradientDensity_of_supported
      modes low (complexSharpSupportProjection_supported modes state)
  have highGradientSummable :
      Summable fun wave : IntegerWavevector =>
        integerWaveNormSq wave *
          complexCoordinateAmplitudeSq (high wave) := by
    simpa only [high, low] using
      summable_wholeStateVorticityGradientDensity_sub
        low state lowGradientSummable gradientSummable
  have lowTransverse : WholeStateTransverse low :=
    wholeStateTransverse_sharpSupportProjection modes state stateTransverse
  have differenceBound :=
    wholeStateVorticityNonlinearDifferenceNegativeOneMass_le
      low state lowTransverse stateTransverse
      lowGradientSummable gradientSummable highGradientSummable
  have lowVelocityBound :
      Ulow ^ 2 <=
        26 * biotSavartSerrinConstant * (radius : Real) * M := by
    rw [show Ulow = finiteStateVelocityMajorant modes state by
      unfold Ulow low
      rw [wholeStateVelocityMajorant_eq_finite_of_supported
        modes (complexSharpSupportProjection modes state)
        (complexSharpSupportProjection_supported modes state)]
      exact finiteStateVelocityMajorant_sharpSupportProjection modes state]
    have finiteBound :=
      finiteStateVelocityMajorant_low_sq_le_agmon modes state radius
    have modesSelf :
        modes ∩ integerWaveFrequencyCube radius = modes := by
      simp [modes]
    rw [modesSelf] at finiteBound
    have finiteMassLe :=
      finiteStateVorticityCoefficientEnstrophy_le_wholeMass modes state
    have coefficientNonneg :
        0 <= 26 * biotSavartSerrinConstant * (radius : Real) := by
      exact mul_nonneg
        (mul_nonneg (by norm_num) biotSavartSerrinConstant_nonneg)
        (Nat.cast_nonneg radius)
    simpa only [M] using finiteBound.trans
      (mul_le_mul_of_nonneg_left finiteMassLe coefficientNonneg)
  have highVelocityBound :
      Uhigh ^ 2 <=
        26 * biotSavartSerrinConstant * (radius : Real)⁻¹ * W := by
    simpa only [Uhigh, high, modes, W] using
      wholeStateVelocityMajorant_projection_sub_sq_le_agmon
        state gradientSummable radius radiusPos
  have highMassRadiusBound : (radius : Real) ^ 2 * Mhigh <= W := by
    simpa only [Mhigh, high, modes, W] using
      radius_sq_mul_wholeVorticityMass_projection_sub_le_gradientMass
        state gradientSummable radius
  have massSplit : M = Mlow + Mhigh := by
    simpa only [M, Mlow, Mhigh, low, high, modes] using
      wholeVorticityEuclideanMass_eq_projection_add_complement modes state
  have MlowNonneg : 0 <= Mlow := by
    unfold Mlow wholeVorticityEuclideanMass
    exact tsum_nonneg fun wave => sq_nonneg _
  have MhighNonneg : 0 <= Mhigh := by
    unfold Mhigh wholeVorticityEuclideanMass
    exact tsum_nonneg fun wave => sq_nonneg _
  have Mnonneg : 0 <= M := by linarith
  have Wnonneg : 0 <= W := by
    unfold W wholeStateVorticityGradientMass
    exact tsum_nonneg fun wave =>
      mul_nonneg (integerWaveNormSq_nonneg wave)
        (complexCoordinateAmplitudeSq_nonneg _)
  have MlowLe : Mlow <= M := by linarith
  have MhighLe : Mhigh <= M := by linarith
  have velocitySplit : Ulow + Uhigh = U := by
    unfold Ulow Uhigh U wholeStateVelocityMajorant
    rw [← (summable_wholeStateVelocityAmplitude
        low
        lowGradientSummable).tsum_add
      (summable_wholeStateVelocityAmplitude
        high
        highGradientSummable)]
    apply tsum_congr
    intro wave
    by_cases waveMem : wave ∈ modes
    · have lowWave : low wave = state wave := by
        simp [low, complexSharpSupportProjection_apply, waveMem]
      have highWave : high wave = 0 := by
        simp [high, lowWave]
      have lowCoefficient :
          finiteStateVelocityCoefficient low wave =
            finiteStateVelocityCoefficient state wave := by
        unfold finiteStateVelocityCoefficient
        rw [lowWave]
      have highCoefficient :
          finiteStateVelocityCoefficient high wave = 0 := by
        unfold finiteStateVelocityCoefficient
        rw [highWave]
        exact biotSavartVelocityCoefficient_zero_vorticity wave
      rw [lowCoefficient, highCoefficient]
      simp [finiteStateVelocityCoefficient, complexCoordinateAmplitudeSq]
    · have lowWave : low wave = 0 := by
        simp [low, complexSharpSupportProjection_apply, waveMem]
      have highWave : high wave = -state wave := by
        rw [show high = low - state by rfl]
        simp [lowWave]
      have lowCoefficient :
          finiteStateVelocityCoefficient low wave = 0 := by
        unfold finiteStateVelocityCoefficient
        rw [lowWave]
        exact biotSavartVelocityCoefficient_zero_vorticity wave
      have coefficientNeg :
          finiteStateVelocityCoefficient high wave =
            -finiteStateVelocityCoefficient state wave := by
        change
          biotSavartVelocityCoefficient wave (high wave) =
            -biotSavartVelocityCoefficient wave (state wave)
        rw [highWave]
        have difference :=
          ThreeDimensionalVorticityCoefficientFiniteGalerkinKineticEnergyLedger.biotSavartVelocityCoefficient_sub
            wave 0 (state wave)
        simpa using difference
      rw [lowCoefficient, coefficientNeg]
      simp [finiteStateVelocityCoefficient, complexCoordinateAmplitudeSq,
        Complex.normSq_neg]
  have UlowNonneg : 0 <= Ulow :=
    wholeStateVelocityMajorant_nonneg low
  have UhighNonneg : 0 <= Uhigh :=
    wholeStateVelocityMajorant_nonneg high
  have radiusRealPos : 0 < (radius : Real) := by exact_mod_cast radiusPos
  have radiusRealNe : (radius : Real) ≠ 0 := ne_of_gt radiusRealPos
  have Qnonneg : 0 <= Q := by
    unfold Q
    exact mul_nonneg
      (mul_nonneg
        (mul_nonneg
          (mul_nonneg (by norm_num) biotSavartSerrinConstant_nonneg)
          (inv_nonneg.mpr radiusRealPos.le))
        Mnonneg)
      Wnonneg
  have lowHighProductBound : Ulow ^ 2 * Mhigh <= Q := by
    calc
      Ulow ^ 2 * Mhigh <=
          (26 * biotSavartSerrinConstant * (radius : Real) * M) *
            Mhigh :=
        mul_le_mul_of_nonneg_right lowVelocityBound MhighNonneg
      _ =
          (26 * biotSavartSerrinConstant * (radius : Real)⁻¹ * M) *
            ((radius : Real) ^ 2 * Mhigh) := by
        field_simp [radiusRealNe]
      _ <=
          (26 * biotSavartSerrinConstant * (radius : Real)⁻¹ * M) * W := by
        exact mul_le_mul_of_nonneg_left highMassRadiusBound
          (mul_nonneg
            (mul_nonneg
              (mul_nonneg (by norm_num) biotSavartSerrinConstant_nonneg)
              (inv_nonneg.mpr radiusRealPos.le))
            Mnonneg)
      _ = Q := by rfl
  have highHighProductBound : Uhigh ^ 2 * Mhigh <= Q := by
    calc
      Uhigh ^ 2 * Mhigh <= Uhigh ^ 2 * M :=
        mul_le_mul_of_nonneg_left MhighLe (sq_nonneg Uhigh)
      _ <=
          (26 * biotSavartSerrinConstant * (radius : Real)⁻¹ * W) * M :=
        mul_le_mul_of_nonneg_right highVelocityBound Mnonneg
      _ = Q := by unfold Q; ring
  have highLowProductBound : Uhigh ^ 2 * Mlow <= Q := by
    calc
      Uhigh ^ 2 * Mlow <= Uhigh ^ 2 * M :=
        mul_le_mul_of_nonneg_left MlowLe (sq_nonneg Uhigh)
      _ <=
          (26 * biotSavartSerrinConstant * (radius : Real)⁻¹ * W) * M :=
        mul_le_mul_of_nonneg_right highVelocityBound Mnonneg
      _ = Q := by unfold Q; ring
  have highWholeProductBound : Uhigh ^ 2 * M <= Q := by
    calc
      Uhigh ^ 2 * M <=
          (26 * biotSavartSerrinConstant * (radius : Real)⁻¹ * W) * M :=
        mul_le_mul_of_nonneg_right highVelocityBound Mnonneg
      _ = Q := by unfold Q; ring
  have stateVelocitySq : U ^ 2 <= 2 * Ulow ^ 2 + 2 * Uhigh ^ 2 := by
    rw [← velocitySplit]
    nlinarith [sq_nonneg (Ulow - Uhigh)]
  have firstTermBound :
      (Ulow ^ 2 + U ^ 2) * Mhigh <= 5 * Q := by
    calc
      (Ulow ^ 2 + U ^ 2) * Mhigh <=
          (3 * Ulow ^ 2 + 2 * Uhigh ^ 2) * Mhigh :=
        mul_le_mul_of_nonneg_right (by linarith) MhighNonneg
      _ = 3 * (Ulow ^ 2 * Mhigh) + 2 * (Uhigh ^ 2 * Mhigh) := by ring
      _ <= 3 * Q + 2 * Q :=
        add_le_add
          (mul_le_mul_of_nonneg_left lowHighProductBound (by norm_num))
          (mul_le_mul_of_nonneg_left highHighProductBound (by norm_num))
      _ = 5 * Q := by ring
  have secondTermBound :
      Uhigh ^ 2 * (Mlow + M) <= 2 * Q := by
    calc
      Uhigh ^ 2 * (Mlow + M) =
          Uhigh ^ 2 * Mlow + Uhigh ^ 2 * M := by ring
      _ <= Q + Q := add_le_add highLowProductBound highWholeProductBound
      _ = 2 * Q := by ring
  calc
    wholeStateVorticityNonlinearDifferenceNegativeOneMass low state <=
        4 * ((Ulow ^ 2 + U ^ 2) * Mhigh +
          Uhigh ^ 2 * (Mlow + M)) := by
      simpa only [low, high, Ulow, Uhigh, U, Mlow, Mhigh, M] using
        differenceBound
    _ <= 4 * (5 * Q + 2 * Q) :=
      mul_le_mul_of_nonneg_left
        (add_le_add firstTermBound secondTermBound) (by norm_num)
    _ =
        728 * biotSavartSerrinConstant * (radius : Real)⁻¹ *
          wholeVorticityEuclideanMass state *
          wholeStateVorticityGradientMass state := by
      unfold Q M W
      ring

/-- The complete whole nonlinear tangent inherits the scale-critical
`M^3 W` square estimate from the whole Agmon bound. -/
theorem
    wholeStateVorticityNonlinearNegativeOneMass_sq_le_scaleCritical
    (state : ComplexVorticityHilbertState)
    (stateTransverse : WholeStateTransverse state)
    (gradientSummable :
      Summable fun wave : IntegerWavevector =>
        integerWaveNormSq wave *
          complexCoordinateAmplitudeSq (state wave)) :
    wholeStateVorticityNonlinearNegativeOneMass state ^ 2 ≤
      1557504 * biotSavartSerrinConstant ^ 2 *
        wholeVorticityEuclideanMass state ^ 3 *
        wholeStateVorticityGradientMass state := by
  let N := wholeStateVorticityNonlinearNegativeOneMass state
  let U := wholeStateVelocityMajorant state
  let M := wholeVorticityEuclideanMass state
  let W := wholeStateVorticityGradientMass state
  have Nnonneg : 0 ≤ N := by
    unfold N wholeStateVorticityNonlinearNegativeOneMass
    exact tsum_nonneg fun output =>
      wholeStateVorticityNonlinearNegativeOneDensity_nonneg
        state output
  have Mnonneg : 0 ≤ M := by
    unfold M wholeVorticityEuclideanMass
    exact tsum_nonneg fun wave => sq_nonneg _
  have nonlinear : N ≤ 8 * U ^ 2 * M := by
    simpa [N, U, M] using
      wholeStateVorticityNonlinearNegativeOneMass_le_velocitySerrin
        state stateTransverse gradientSummable
  have nonlinearRightNonneg : 0 ≤ 8 * U ^ 2 * M :=
    mul_nonneg
      (mul_nonneg (by norm_num) (sq_nonneg U)) Mnonneg
  have nonlinearSq : N ^ 2 ≤ (8 * U ^ 2 * M) ^ 2 :=
    (sq_le_sq₀ Nnonneg nonlinearRightNonneg).2 nonlinear
  have agmon :
      U ^ 4 ≤
        24336 * biotSavartSerrinConstant ^ 2 * M * W := by
    simpa [U, M, W] using
      wholeStateVelocityMajorant_pow_four_le_agmon
        state gradientSummable
  have multiplierNonneg : 0 ≤ 64 * M ^ 2 :=
    mul_nonneg (by norm_num) (sq_nonneg M)
  calc
    N ^ 2 ≤ (8 * U ^ 2 * M) ^ 2 := nonlinearSq
    _ = (64 * M ^ 2) * U ^ 4 := by ring
    _ ≤
        (64 * M ^ 2) *
          (24336 * biotSavartSerrinConstant ^ 2 * M * W) :=
      mul_le_mul_of_nonneg_left agmon multiplierNonneg
    _ =
        1557504 * biotSavartSerrinConstant ^ 2 * M ^ 3 * W := by
      ring

/-- The complete finite stretching work inherits the scale-critical
`M^3 W^3` fourth-power estimate from the actual Fourier majorant. -/
theorem finiteStateVorticityStretchingWork_abs_pow_four_le_scaleCritical
    (modes : Finset IntegerWavevector)
    (state : ComplexVorticityHilbertState)
    (zeroNotMem : (0 : IntegerWavevector) ∉ modes)
    (transverse :
      ∀ wave ∈ modes,
        complexWavevector wave ⬝ᵥ state wave = 0) :
    |finiteStateVorticityStretchingWork modes state| ^ 4 ≤
      24336 *
        finiteStateVorticityCoefficientEnstrophy modes state ^ 3 *
        finiteStateVorticityEnstrophyMass modes state ^ 3 := by
  let S := |finiteStateVorticityStretchingWork modes state|
  let U := finiteStateVelocityMajorant modes state
  let M := finiteStateVorticityCoefficientEnstrophy modes state
  let W := finiteStateVorticityEnstrophyMass modes state
  let G := (2 * Real.pi) ^ 2 * W
  have Mnonneg : 0 ≤ M :=
    finiteStateVorticityCoefficientEnstrophy_nonneg_agmon modes state
  have Wnonneg : 0 ≤ W :=
    finiteStateVorticityEnstrophyMass_nonneg modes state
  have Gnonneg : 0 ≤ G :=
    mul_nonneg (sq_nonneg _) Wnonneg
  have Unonneg : 0 ≤ U :=
    finiteStateVelocityMajorant_nonneg modes state
  have critical :
      S ≤ U * Real.sqrt M * Real.sqrt G := by
    simpa [S, U, M, W, G] using
      finiteStateVorticityStretchingWork_abs_le_critical
        modes state transverse
  have criticalRightNonneg :
      0 ≤ U * Real.sqrt M * Real.sqrt G :=
    mul_nonneg
      (mul_nonneg Unonneg (Real.sqrt_nonneg _))
      (Real.sqrt_nonneg _)
  have criticalSq :
      S ^ 2 ≤ U ^ 2 * M * G := by
    calc
      S ^ 2 ≤ (U * Real.sqrt M * Real.sqrt G) ^ 2 :=
        (sq_le_sq₀ (abs_nonneg _) criticalRightNonneg).2 critical
      _ = U ^ 2 * M * G := by
        rw [mul_pow, mul_pow, Real.sq_sqrt Mnonneg,
          Real.sq_sqrt Gnonneg]
  have criticalSqRightNonneg :
      0 ≤ U ^ 2 * M * G :=
    mul_nonneg
      (mul_nonneg (sq_nonneg U) Mnonneg)
      Gnonneg
  have criticalFourth :
      S ^ 4 ≤ U ^ 4 * M ^ 2 * G ^ 2 := by
    calc
      S ^ 4 = (S ^ 2) ^ 2 := by ring
      _ ≤ (U ^ 2 * M * G) ^ 2 :=
        (sq_le_sq₀ (sq_nonneg S) criticalSqRightNonneg).2
          criticalSq
      _ = U ^ 4 * M ^ 2 * G ^ 2 := by ring
  have agmon :=
    finiteStateVelocityMajorant_pow_four_le_agmon
      modes state zeroNotMem
  have agmon' :
      U ^ 4 ≤
        24336 * biotSavartSerrinConstant ^ 2 * M * W := by
    simpa [U, M, W] using agmon
  have multiplierNonneg :
      0 ≤ M ^ 2 * G ^ 2 :=
    mul_nonneg (sq_nonneg M) (sq_nonneg G)
  calc
    S ^ 4 ≤ U ^ 4 * M ^ 2 * G ^ 2 :=
      criticalFourth
    _ = U ^ 4 * (M ^ 2 * G ^ 2) := by ring
    _ ≤
        (24336 * biotSavartSerrinConstant ^ 2 * M * W) *
          (M ^ 2 * G ^ 2) :=
      mul_le_mul_of_nonneg_right agmon' multiplierNonneg
    _ = 24336 * M ^ 3 * W ^ 3 := by
      unfold G biotSavartSerrinConstant
      field_simp [Real.pi_ne_zero]

private abbrev ScaledVelocityCylinder
    (timeLength spatialRadius : Real) :=
  Icc (0 : Real) timeLength ×
    Metric.closedBall (0 : PhysicalSpace) spatialRadius

private def scaledFiniteBandVelocityField
    (timeLength spatialRadius scale : Real)
    (radius : Nat)
    (center : PhysicalSpace)
    (path : Icc (0 : Real) timeLength → ComplexVorticityHilbertState)
    (point : ScaledVelocityCylinder timeLength spatialRadius) :
    PhysicalSpace :=
  scale •
    finiteRealComplexFourierField (integerWaveFrequencyCube radius)
      (finiteStateVelocityCoefficient (path point.1))
      (center + scale • point.2.1)

private theorem integerWaveFrequencyCube_scaled_card_le_probe
    (scale bandRadius : Real)
    (radius : Nat)
    (scalePos : 0 < scale)
    (scaleLeOne : scale ≤ 1)
    (_bandRadiusNonneg : 0 ≤ bandRadius)
    (radiusLe : scale * (radius : Real) ≤ bandRadius) :
    scale ^ 3 * ((integerWaveFrequencyCube radius).card : Real) ≤
      (2 * bandRadius + 1) ^ 3 := by
  have cubeCard :
      (integerWaveFrequencyCube radius).card = (2 * radius + 1) ^ 3 := by
    (simp [integerWaveFrequencyCube, Fintype.card_piFinset, Int.card_Icc];
      omega)
  rw [cubeCard]
  push_cast
  have scaleNonneg : 0 ≤ scale := scalePos.le
  calc
    scale ^ 3 * (2 * (radius : Real) + 1) ^ 3 =
        (scale * (2 * (radius : Real) + 1)) ^ 3 := by ring
    _ ≤ (2 * bandRadius + 1) ^ 3 := by
      gcongr
      nlinarith

private theorem scaledFiniteBandVelocityField_norm_sq_le
    (timeLength spatialRadius scale bandRadius massCeiling : Real)
    (radius : Nat)
    (center : PhysicalSpace)
    (path : Icc (0 : Real) timeLength → ComplexVorticityHilbertState)
    (point : ScaledVelocityCylinder timeLength spatialRadius)
    (scalePos : 0 < scale)
    (bandRadiusNonneg : 0 ≤ bandRadius)
    (_massCeilingNonneg : 0 ≤ massCeiling)
    (radiusLe : scale * (radius : Real) ≤ bandRadius)
    (massLe :
      scale * finiteStateVorticityCoefficientEnstrophy
        (integerWaveFrequencyCube radius) (path point.1) ≤ massCeiling) :
    ‖scaledFiniteBandVelocityField timeLength spatialRadius scale radius
        center path point‖ ^ 2 ≤
      26 * biotSavartSerrinConstant * bandRadius * massCeiling := by
  have raw :=
    finiteRealComplexFourierVelocityField_parabolicScale_norm_sq_le
      radius (path point.1) scale scalePos.le center point.2.1
  have prefactorNonneg :
      0 ≤ 26 * biotSavartSerrinConstant := by
    exact mul_nonneg (by norm_num) biotSavartSerrinConstant_nonneg
  have scaledMassNonneg :
      0 ≤ scale * finiteStateVorticityCoefficientEnstrophy
        (integerWaveFrequencyCube radius) (path point.1) :=
    mul_nonneg scalePos.le
      (by
        unfold finiteStateVorticityCoefficientEnstrophy
        exact Finset.sum_nonneg fun wave _ =>
          complexCoordinateAmplitudeSq_nonneg _)
  calc
    ‖scaledFiniteBandVelocityField timeLength spatialRadius scale radius
        center path point‖ ^ 2 ≤
      26 * biotSavartSerrinConstant *
        (scale * (radius : Real)) *
        (scale * finiteStateVorticityCoefficientEnstrophy
          (integerWaveFrequencyCube radius) (path point.1)) := raw
    _ ≤ 26 * biotSavartSerrinConstant * bandRadius *
        (scale * finiteStateVorticityCoefficientEnstrophy
          (integerWaveFrequencyCube radius) (path point.1)) := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left radiusLe prefactorNonneg)
        scaledMassNonneg
    _ ≤ 26 * biotSavartSerrinConstant * bandRadius * massCeiling :=
      mul_le_mul_of_nonneg_left massLe
        (mul_nonneg prefactorNonneg bandRadiusNonneg)

private theorem scaledFiniteBandVelocityField_time_dist_sq_le
    (timeLength spatialRadius scale bandRadius timeCeiling : Real)
    (radius : Nat)
    (center : PhysicalSpace)
    (path : Icc (0 : Real) timeLength → ComplexVorticityHilbertState)
    (position : Metric.closedBall (0 : PhysicalSpace) spatialRadius)
    (first second : Icc (0 : Real) timeLength)
    (scalePos : 0 < scale)
    (bandRadiusNonneg : 0 ≤ bandRadius)
    (_timeCeilingNonneg : 0 ≤ timeCeiling)
    (radiusLe : scale * (radius : Real) ≤ bandRadius)
    (timeIncrement :
      scale * finiteStateVorticityCoefficientEnstrophy
          (integerWaveFrequencyCube radius) (path first - path second) ≤
        timeCeiling * dist first second) :
    dist
        (scaledFiniteBandVelocityField timeLength spatialRadius scale
          radius center path (first, position))
        (scaledFiniteBandVelocityField timeLength spatialRadius scale
          radius center path (second, position)) ^ 2 ≤
      26 * biotSavartSerrinConstant * bandRadius * timeCeiling *
        dist first second := by
  have raw :=
    finiteRealComplexFourierVelocityField_parabolicScale_norm_sub_sq_le
      radius (path first) (path second) scale scalePos.le center position.1
  have prefactorNonneg :
      0 ≤ 26 * biotSavartSerrinConstant :=
    mul_nonneg (by norm_num) biotSavartSerrinConstant_nonneg
  have scaledDifferenceNonneg :
      0 ≤ scale * finiteStateVorticityCoefficientEnstrophy
        (integerWaveFrequencyCube radius) (path first - path second) :=
    mul_nonneg scalePos.le
      (by
        unfold finiteStateVorticityCoefficientEnstrophy
        exact Finset.sum_nonneg fun wave _ =>
          complexCoordinateAmplitudeSq_nonneg _)
  rw [dist_eq_norm]
  calc
    ‖scaledFiniteBandVelocityField timeLength spatialRadius scale radius
          center path (first, position) -
        scaledFiniteBandVelocityField timeLength spatialRadius scale radius
          center path (second, position)‖ ^ 2 ≤
      26 * biotSavartSerrinConstant *
        (scale * (radius : Real)) *
        (scale * finiteStateVorticityCoefficientEnstrophy
          (integerWaveFrequencyCube radius) (path first - path second)) := raw
    _ ≤ 26 * biotSavartSerrinConstant * bandRadius * timeCeiling *
        dist first second := by
      have productNonneg :
          0 ≤ 26 * biotSavartSerrinConstant * bandRadius :=
        mul_nonneg prefactorNonneg bandRadiusNonneg
      calc
        _ ≤ (26 * biotSavartSerrinConstant * bandRadius) *
            (scale * finiteStateVorticityCoefficientEnstrophy
              (integerWaveFrequencyCube radius) (path first - path second)) := by
          exact mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left radiusLe prefactorNonneg)
            scaledDifferenceNonneg
        _ ≤ (26 * biotSavartSerrinConstant * bandRadius) *
            (timeCeiling * dist first second) :=
          mul_le_mul_of_nonneg_left timeIncrement productNonneg
        _ = _ := by ring

private theorem scaledFiniteBandVelocityField_space_dist_le
    (timeLength spatialRadius scale bandRadius massCeiling : Real)
    (radius : Nat)
    (center : PhysicalSpace)
    (path : Icc (0 : Real) timeLength → ComplexVorticityHilbertState)
    (time : Icc (0 : Real) timeLength)
    (first second : Metric.closedBall (0 : PhysicalSpace) spatialRadius)
    (scalePos : 0 < scale)
    (scaleLeOne : scale ≤ 1)
    (bandRadiusNonneg : 0 ≤ bandRadius)
    (massCeilingNonneg : 0 ≤ massCeiling)
    (radiusLe : scale * (radius : Real) ≤ bandRadius)
    (massLe :
      scale * finiteStateVorticityCoefficientEnstrophy
        (integerWaveFrequencyCube radius) (path time) ≤ massCeiling) :
    dist
        (scaledFiniteBandVelocityField timeLength spatialRadius scale
          radius center path (time, first))
        (scaledFiniteBandVelocityField timeLength spatialRadius scale
          radius center path (time, second)) ≤
      Real.sqrt
          ((2 * bandRadius + 1) ^ 3 * (2 * Real.pi) ^ 2 *
            biotSavartSerrinConstant * massCeiling) *
        dist first second := by
  let modes := integerWaveFrequencyCube radius
  have raw :=
    finiteRealComplexFourierVelocityField_parabolicScale_norm_sub_le
      modes (path time) scale scalePos.le center first.1 second.1
  have scaledCard := integerWaveFrequencyCube_scaled_card_le_probe
    scale bandRadius radius scalePos scaleLeOne bandRadiusNonneg radiusLe
  let rawCoefficient : Real :=
    scale ^ 2 *
      Real.sqrt
        ((modes.card : Real) * (2 * Real.pi) ^ 2 *
          (biotSavartSerrinConstant *
            finiteStateVorticityCoefficientEnstrophy modes (path time)))
  let ceilingCoefficient : Real :=
    Real.sqrt
      ((2 * bandRadius + 1) ^ 3 * (2 * Real.pi) ^ 2 *
        biotSavartSerrinConstant * massCeiling)
  have rawArgumentNonneg :
      0 ≤ (modes.card : Real) * (2 * Real.pi) ^ 2 *
        (biotSavartSerrinConstant *
          finiteStateVorticityCoefficientEnstrophy modes (path time)) := by
    exact mul_nonneg
      (mul_nonneg (Nat.cast_nonneg modes.card) (sq_nonneg _))
      (mul_nonneg biotSavartSerrinConstant_nonneg
        (by
          unfold finiteStateVorticityCoefficientEnstrophy
          exact Finset.sum_nonneg fun wave _ =>
            complexCoordinateAmplitudeSq_nonneg _))
  have ceilingArgumentNonneg :
      0 ≤ (2 * bandRadius + 1) ^ 3 * (2 * Real.pi) ^ 2 *
        biotSavartSerrinConstant * massCeiling := by
    have baseNonneg : 0 ≤ 2 * bandRadius + 1 := by linarith
    exact mul_nonneg
      (mul_nonneg
        (mul_nonneg (pow_nonneg baseNonneg 3) (sq_nonneg _))
        biotSavartSerrinConstant_nonneg)
      massCeilingNonneg
  have coefficientLe : rawCoefficient ≤ ceilingCoefficient := by
    rw [← sq_le_sq₀
      (mul_nonneg (sq_nonneg scale) (Real.sqrt_nonneg _))
      (Real.sqrt_nonneg _)]
    rw [show rawCoefficient ^ 2 =
        (scale ^ 3 * (modes.card : Real)) *
          (scale * finiteStateVorticityCoefficientEnstrophy modes (path time)) *
          ((2 * Real.pi) ^ 2 * biotSavartSerrinConstant) by
      dsimp only [rawCoefficient]
      calc
        (scale ^ 2 *
            Real.sqrt
              ((modes.card : Real) * (2 * Real.pi) ^ 2 *
                (biotSavartSerrinConstant *
                  finiteStateVorticityCoefficientEnstrophy modes
                    (path time)))) ^ 2 =
            scale ^ 4 *
              ((modes.card : Real) * (2 * Real.pi) ^ 2 *
                (biotSavartSerrinConstant *
                  finiteStateVorticityCoefficientEnstrophy modes
                    (path time))) := by
          rw [mul_pow, Real.sq_sqrt rawArgumentNonneg]
          ring
        _ = _ := by ring]
    rw [Real.sq_sqrt ceilingArgumentNonneg]
    have multiplierNonneg :
        0 ≤ (2 * Real.pi) ^ 2 * biotSavartSerrinConstant :=
      mul_nonneg (sq_nonneg _) biotSavartSerrinConstant_nonneg
    have scaledMassNonneg :
        0 ≤ scale * finiteStateVorticityCoefficientEnstrophy modes
          (path time) :=
      mul_nonneg scalePos.le
        (by
          unfold finiteStateVorticityCoefficientEnstrophy
          exact Finset.sum_nonneg fun wave _ =>
            complexCoordinateAmplitudeSq_nonneg _)
    calc
      (scale ^ 3 * (modes.card : Real)) *
            (scale * finiteStateVorticityCoefficientEnstrophy modes (path time)) *
          ((2 * Real.pi) ^ 2 * biotSavartSerrinConstant) ≤
        (2 * bandRadius + 1) ^ 3 * massCeiling *
          ((2 * Real.pi) ^ 2 * biotSavartSerrinConstant) := by
        gcongr
      _ = (2 * bandRadius + 1) ^ 3 * (2 * Real.pi) ^ 2 *
          biotSavartSerrinConstant * massCeiling := by ring
  rw [dist_eq_norm]
  calc
    ‖scaledFiniteBandVelocityField timeLength spatialRadius scale radius
          center path (time, first) -
        scaledFiniteBandVelocityField timeLength spatialRadius scale radius
          center path (time, second)‖ ≤
      rawCoefficient * ‖second.1 - first.1‖ := by
        rw [norm_sub_rev]
        simpa only [scaledFiniteBandVelocityField, modes,
          rawCoefficient] using raw
    _ ≤ ceilingCoefficient * ‖second.1 - first.1‖ :=
      mul_le_mul_of_nonneg_right coefficientLe (norm_nonneg _)
    _ = ceilingCoefficient * dist first second := by
      rw [Subtype.dist_eq, dist_eq_norm]
      rw [norm_sub_rev]

private theorem scaledFiniteBandVelocityField_time_dist_le
    (timeLength spatialRadius scale bandRadius timeCeiling : Real)
    (radius : Nat)
    (center : PhysicalSpace)
    (path : Icc (0 : Real) timeLength → ComplexVorticityHilbertState)
    (position : Metric.closedBall (0 : PhysicalSpace) spatialRadius)
    (first second : Icc (0 : Real) timeLength)
    (scalePos : 0 < scale)
    (bandRadiusNonneg : 0 ≤ bandRadius)
    (timeCeilingNonneg : 0 ≤ timeCeiling)
    (radiusLe : scale * (radius : Real) ≤ bandRadius)
    (timeIncrement :
      scale * finiteStateVorticityCoefficientEnstrophy
          (integerWaveFrequencyCube radius) (path first - path second) ≤
        timeCeiling * dist first second) :
    dist
        (scaledFiniteBandVelocityField timeLength spatialRadius scale
          radius center path (first, position))
        (scaledFiniteBandVelocityField timeLength spatialRadius scale
          radius center path (second, position)) ≤
      Real.sqrt
        (26 * biotSavartSerrinConstant * bandRadius * timeCeiling *
          dist first second) := by
  have squared :=
    scaledFiniteBandVelocityField_time_dist_sq_le timeLength
      spatialRadius scale bandRadius timeCeiling radius center path position
      first second scalePos bandRadiusNonneg timeCeilingNonneg radiusLe
      timeIncrement
  have argumentNonneg :
      0 ≤ 26 * biotSavartSerrinConstant * bandRadius * timeCeiling *
        dist first second := by
    exact mul_nonneg
      (mul_nonneg
        (mul_nonneg
          (mul_nonneg (by norm_num) biotSavartSerrinConstant_nonneg)
          bandRadiusNonneg)
        timeCeilingNonneg)
      dist_nonneg
  rw [← sq_le_sq₀ dist_nonneg (Real.sqrt_nonneg _)]
  rw [Real.sq_sqrt argumentNonneg]
  exact squared

private theorem scaledFiniteBandVelocityField_joint_dist_le
    (timeLength spatialRadius scale bandRadius massCeiling timeCeiling : Real)
    (radius : Nat)
    (center : PhysicalSpace)
    (path : Icc (0 : Real) timeLength → ComplexVorticityHilbertState)
    (first second : ScaledVelocityCylinder timeLength spatialRadius)
    (scalePos : 0 < scale)
    (scaleLeOne : scale ≤ 1)
    (bandRadiusNonneg : 0 ≤ bandRadius)
    (massCeilingNonneg : 0 ≤ massCeiling)
    (timeCeilingNonneg : 0 ≤ timeCeiling)
    (radiusLe : scale * (radius : Real) ≤ bandRadius)
    (massLe : ∀ time,
      scale * finiteStateVorticityCoefficientEnstrophy
        (integerWaveFrequencyCube radius) (path time) ≤ massCeiling)
    (timeIncrement : ∀ first second,
      scale * finiteStateVorticityCoefficientEnstrophy
          (integerWaveFrequencyCube radius) (path first - path second) ≤
        timeCeiling * dist first second) :
    dist
        (scaledFiniteBandVelocityField timeLength spatialRadius scale
          radius center path first)
        (scaledFiniteBandVelocityField timeLength spatialRadius scale
          radius center path second) ≤
      Real.sqrt
          ((2 * bandRadius + 1) ^ 3 * (2 * Real.pi) ^ 2 *
            biotSavartSerrinConstant * massCeiling) * dist first second +
        Real.sqrt
          (26 * biotSavartSerrinConstant * bandRadius * timeCeiling *
            dist first second) := by
  let middle : ScaledVelocityCylinder timeLength spatialRadius :=
    (first.1, second.2)
  have spatial :=
    scaledFiniteBandVelocityField_space_dist_le timeLength spatialRadius
      scale bandRadius massCeiling radius center path first.1 first.2 second.2
      scalePos scaleLeOne bandRadiusNonneg massCeilingNonneg radiusLe
      (massLe first.1)
  have temporal :=
    scaledFiniteBandVelocityField_time_dist_le timeLength spatialRadius
      scale bandRadius timeCeiling radius center path second.2 first.1 second.1
      scalePos bandRadiusNonneg timeCeilingNonneg radiusLe
      (timeIncrement first.1 second.1)
  have firstComponentLe : dist first.1 second.1 ≤ dist first second := by
    rw [Prod.dist_eq]
    exact le_max_left _ _
  have secondComponentLe : dist first.2 second.2 ≤ dist first second := by
    rw [Prod.dist_eq]
    exact le_max_right _ _
  have spatialConstantNonneg :
      0 ≤ Real.sqrt
        ((2 * bandRadius + 1) ^ 3 * (2 * Real.pi) ^ 2 *
          biotSavartSerrinConstant * massCeiling) := Real.sqrt_nonneg _
  have spatial' :
      dist
          (scaledFiniteBandVelocityField timeLength spatialRadius scale
            radius center path first)
          (scaledFiniteBandVelocityField timeLength spatialRadius scale
            radius center path middle) ≤
        Real.sqrt
            ((2 * bandRadius + 1) ^ 3 * (2 * Real.pi) ^ 2 *
              biotSavartSerrinConstant * massCeiling) * dist first second := by
    calc
      _ ≤ Real.sqrt
            ((2 * bandRadius + 1) ^ 3 * (2 * Real.pi) ^ 2 *
              biotSavartSerrinConstant * massCeiling) *
            dist first.2 second.2 := spatial
      _ ≤ _ := mul_le_mul_of_nonneg_left secondComponentLe
        spatialConstantNonneg
  have timeCoefficientNonneg :
      0 ≤ 26 * biotSavartSerrinConstant * bandRadius * timeCeiling := by
    exact mul_nonneg
      (mul_nonneg
        (mul_nonneg (by norm_num) biotSavartSerrinConstant_nonneg)
        bandRadiusNonneg)
      timeCeilingNonneg
  have temporal' :
      dist
          (scaledFiniteBandVelocityField timeLength spatialRadius scale
            radius center path middle)
          (scaledFiniteBandVelocityField timeLength spatialRadius scale
            radius center path second) ≤
        Real.sqrt
          (26 * biotSavartSerrinConstant * bandRadius * timeCeiling *
            dist first second) := by
    calc
      _ ≤ Real.sqrt
          (26 * biotSavartSerrinConstant * bandRadius * timeCeiling *
            dist first.1 second.1) := temporal
      _ ≤ _ := Real.sqrt_le_sqrt
        (mul_le_mul_of_nonneg_left firstComponentLe timeCoefficientNonneg)
  exact (dist_triangle _
      (scaledFiniteBandVelocityField timeLength spatialRadius scale radius
        center path middle) _).trans
    (add_le_add spatial' temporal')

private theorem scaledFiniteBandVelocityField_family_equicontinuous
    (timeLength spatialRadius bandRadius massCeiling timeCeiling : Real)
    (scale : Nat → Real)
    (radius : Nat → Nat)
    (center : Nat → PhysicalSpace)
    (path : Nat → Icc (0 : Real) timeLength →
      ComplexVorticityHilbertState)
    (bandRadiusNonneg : 0 ≤ bandRadius)
    (massCeilingNonneg : 0 ≤ massCeiling)
    (timeCeilingNonneg : 0 ≤ timeCeiling)
    (scalePos : ∀ index, 0 < scale index)
    (scaleLeOne : ∀ index, scale index ≤ 1)
    (radiusLe : ∀ index,
      scale index * (radius index : Real) ≤ bandRadius)
    (massLe : ∀ index time,
      scale index * finiteStateVorticityCoefficientEnstrophy
        (integerWaveFrequencyCube (radius index)) (path index time) ≤
          massCeiling)
    (timeIncrement : ∀ index first second,
      scale index * finiteStateVorticityCoefficientEnstrophy
          (integerWaveFrequencyCube (radius index))
          (path index first - path index second) ≤
        timeCeiling * dist first second) :
    Equicontinuous fun index point =>
      scaledFiniteBandVelocityField timeLength spatialRadius
        (scale index) (radius index) (center index) (path index) point := by
  let spatialConstant : Real :=
    Real.sqrt
      ((2 * bandRadius + 1) ^ 3 * (2 * Real.pi) ^ 2 *
        biotSavartSerrinConstant * massCeiling)
  let timeCoefficient : Real :=
    26 * biotSavartSerrinConstant * bandRadius * timeCeiling
  let modulus : Real → Real := fun distance =>
    spatialConstant * |distance| +
      Real.sqrt (timeCoefficient * |distance|)
  have modulusContinuous : Continuous modulus := by
    exact (continuous_const.mul continuous_abs).add
      (Real.continuous_sqrt.comp (continuous_const.mul continuous_abs))
  have modulusTendsToZero : Tendsto modulus (𝓝 0) (𝓝 0) := by
    have atZero : ContinuousAt modulus 0 := modulusContinuous.continuousAt
    have modulusZero : modulus 0 = 0 := by simp [modulus]
    nth_rewrite 2 [← modulusZero]
    exact atZero
  apply Metric.equicontinuous_of_continuity_modulus modulus
    modulusTendsToZero
  intro first second index
  simpa only [modulus, spatialConstant, timeCoefficient,
    abs_of_nonneg dist_nonneg] using
    scaledFiniteBandVelocityField_joint_dist_le timeLength spatialRadius
      (scale index) bandRadius massCeiling timeCeiling (radius index)
      (center index) (path index) first second (scalePos index)
      (scaleLeOne index) bandRadiusNonneg massCeilingNonneg
      timeCeilingNonneg (radiusLe index) (massLe index)
      (timeIncrement index)

def scaledFiniteBandVelocityBoundedPath
    (timeLength spatialRadius bandRadius massCeiling timeCeiling : Real)
    (scale : Nat → Real)
    (radius : Nat → Nat)
    (center : Nat → PhysicalSpace)
    (path : Nat → Icc (0 : Real) timeLength →
      ComplexVorticityHilbertState)
    (bandRadiusNonneg : 0 ≤ bandRadius)
    (massCeilingNonneg : 0 ≤ massCeiling)
    (timeCeilingNonneg : 0 ≤ timeCeiling)
    (scalePos : ∀ index, 0 < scale index)
    (scaleLeOne : ∀ index, scale index ≤ 1)
    (radiusLe : ∀ index,
      scale index * (radius index : Real) ≤ bandRadius)
    (massLe : ∀ index time,
      scale index * finiteStateVorticityCoefficientEnstrophy
        (integerWaveFrequencyCube (radius index)) (path index time) ≤
          massCeiling)
    (timeIncrement : ∀ index first second,
      scale index * finiteStateVorticityCoefficientEnstrophy
          (integerWaveFrequencyCube (radius index))
          (path index first - path index second) ≤
        timeCeiling * dist first second)
    (index : Nat) :
    BoundedContinuousFunction
      (Icc (0 : Real) timeLength ×
        Metric.closedBall (0 : PhysicalSpace) spatialRadius) PhysicalSpace :=
  BoundedContinuousFunction.mkOfCompact
    ⟨scaledFiniteBandVelocityField timeLength spatialRadius (scale index)
        (radius index) (center index) (path index),
      (scaledFiniteBandVelocityField_family_equicontinuous timeLength
        spatialRadius bandRadius massCeiling timeCeiling scale radius center
        path bandRadiusNonneg massCeilingNonneg timeCeilingNonneg scalePos
        scaleLeOne radiusLe massLe timeIncrement).continuous index⟩

theorem scaledFiniteBandVelocityBoundedPath_apply
    (timeLength spatialRadius bandRadius massCeiling timeCeiling : Real)
    (scale : Nat → Real)
    (radius : Nat → Nat)
    (center : Nat → PhysicalSpace)
    (path : Nat → Icc (0 : Real) timeLength →
      ComplexVorticityHilbertState)
    (bandRadiusNonneg : 0 ≤ bandRadius)
    (massCeilingNonneg : 0 ≤ massCeiling)
    (timeCeilingNonneg : 0 ≤ timeCeiling)
    (scalePos : ∀ index, 0 < scale index)
    (scaleLeOne : ∀ index, scale index ≤ 1)
    (radiusLe : ∀ index,
      scale index * (radius index : Real) ≤ bandRadius)
    (massLe : ∀ index time,
      scale index * finiteStateVorticityCoefficientEnstrophy
        (integerWaveFrequencyCube (radius index)) (path index time) ≤
          massCeiling)
    (timeIncrement : ∀ index first second,
      scale index * finiteStateVorticityCoefficientEnstrophy
          (integerWaveFrequencyCube (radius index))
          (path index first - path index second) ≤
        timeCeiling * dist first second)
    (index : Nat)
    (point : Icc (0 : Real) timeLength ×
      Metric.closedBall (0 : PhysicalSpace) spatialRadius) :
    scaledFiniteBandVelocityBoundedPath timeLength spatialRadius
        bandRadius massCeiling timeCeiling scale radius center path
        bandRadiusNonneg massCeilingNonneg timeCeilingNonneg scalePos
        scaleLeOne radiusLe massLe timeIncrement index point =
      scaledFiniteBandVelocityField timeLength spatialRadius
        (scale index) (radius index) (center index) (path index) point := rfl

/-- Fixed physical velocity bands generated from a uniformly controlled
scaled vorticity family all lie in one compact bounded-continuous-function
range.  This is the compact approximation input for growing-band local
`L²` velocity limits. -/
theorem scaledFiniteBandVelocityBoundedPath_compactRange
    (timeLength spatialRadius bandRadius massCeiling timeCeiling : Real)
    (scale : Nat → Real)
    (radius : Nat → Nat)
    (center : Nat → PhysicalSpace)
    (path : Nat → Icc (0 : Real) timeLength →
      ComplexVorticityHilbertState)
    (bandRadiusNonneg : 0 ≤ bandRadius)
    (massCeilingNonneg : 0 ≤ massCeiling)
    (timeCeilingNonneg : 0 ≤ timeCeiling)
    (scalePos : ∀ index, 0 < scale index)
    (scaleLeOne : ∀ index, scale index ≤ 1)
    (radiusLe : ∀ index,
      scale index * (radius index : Real) ≤ bandRadius)
    (massLe : ∀ index time,
      scale index * finiteStateVorticityCoefficientEnstrophy
        (integerWaveFrequencyCube (radius index)) (path index time) ≤
          massCeiling)
    (timeIncrement : ∀ index first second,
      scale index * finiteStateVorticityCoefficientEnstrophy
          (integerWaveFrequencyCube (radius index))
          (path index first - path index second) ≤
        timeCeiling * dist first second) :
    ∃ compactSet : Set (BoundedContinuousFunction
        (Icc (0 : Real) timeLength ×
          Metric.closedBall (0 : PhysicalSpace) spatialRadius) PhysicalSpace),
      IsCompact compactSet ∧
      ∀ index,
        scaledFiniteBandVelocityBoundedPath timeLength spatialRadius
            bandRadius massCeiling timeCeiling scale radius center path
            bandRadiusNonneg massCeilingNonneg timeCeilingNonneg scalePos
            scaleLeOne radiusLe massLe timeIncrement index ∈ compactSet := by
  let sequence : Nat → BoundedContinuousFunction
      (ScaledVelocityCylinder timeLength spatialRadius) PhysicalSpace :=
    scaledFiniteBandVelocityBoundedPath timeLength spatialRadius
      bandRadius massCeiling timeCeiling scale radius center path
      bandRadiusNonneg massCeilingNonneg timeCeilingNonneg scalePos scaleLeOne
      radiusLe massLe timeIncrement
  let family : Set (BoundedContinuousFunction
      (ScaledVelocityCylinder timeLength spatialRadius) PhysicalSpace) :=
    Set.range sequence
  let valueBall : Set PhysicalSpace :=
    Metric.closedBall 0
      (Real.sqrt
        (26 * biotSavartSerrinConstant * bandRadius * massCeiling))
  have valueCeilingNonneg :
      0 ≤ 26 * biotSavartSerrinConstant * bandRadius * massCeiling := by
    exact mul_nonneg
      (mul_nonneg
        (mul_nonneg (by norm_num) biotSavartSerrinConstant_nonneg)
        bandRadiusNonneg)
      massCeilingNonneg
  have familyEquicontinuous :
      Equicontinuous
        (fun member : family =>
          (member.1 :
            ScaledVelocityCylinder timeLength spatialRadius →
              PhysicalSpace)) := by
    let spatialConstant : Real :=
      Real.sqrt
        ((2 * bandRadius + 1) ^ 3 * (2 * Real.pi) ^ 2 *
          biotSavartSerrinConstant * massCeiling)
    let timeCoefficient : Real :=
      26 * biotSavartSerrinConstant * bandRadius * timeCeiling
    let modulus : Real → Real := fun distance =>
      spatialConstant * |distance| +
        Real.sqrt (timeCoefficient * |distance|)
    have modulusContinuous : Continuous modulus := by
      exact (continuous_const.mul continuous_abs).add
        (Real.continuous_sqrt.comp (continuous_const.mul continuous_abs))
    have modulusTendsToZero : Tendsto modulus (𝓝 0) (𝓝 0) := by
      have atZero : ContinuousAt modulus 0 := modulusContinuous.continuousAt
      have modulusZero : modulus 0 = 0 := by simp [modulus]
      nth_rewrite 2 [← modulusZero]
      exact atZero
    apply Metric.equicontinuous_of_continuity_modulus modulus
      modulusTendsToZero
    intro first second member
    rcases member with ⟨function, ⟨index, functionEq⟩⟩
    subst function
    change dist
        (scaledFiniteBandVelocityField timeLength spatialRadius
          (scale index) (radius index) (center index) (path index) first)
        (scaledFiniteBandVelocityField timeLength spatialRadius
          (scale index) (radius index) (center index) (path index) second) ≤
      modulus (dist first second)
    simpa only [modulus, spatialConstant, timeCoefficient,
      abs_of_nonneg dist_nonneg] using
      scaledFiniteBandVelocityField_joint_dist_le timeLength spatialRadius
        (scale index) bandRadius massCeiling timeCeiling (radius index)
        (center index) (path index) first second (scalePos index)
        (scaleLeOne index) bandRadiusNonneg massCeilingNonneg
        timeCeilingNonneg (radiusLe index) (massLe index)
        (timeIncrement index)
  have compactFamily : IsCompact (closure family) := by
    apply BoundedContinuousFunction.arzela_ascoli valueBall
      (isCompact_closedBall _ _)
    · intro function point functionMem
      rcases functionMem with ⟨index, rfl⟩
      rw [Metric.mem_closedBall, dist_zero_right]
      rw [← sq_le_sq₀ (norm_nonneg _) (Real.sqrt_nonneg _)]
      rw [Real.sq_sqrt valueCeilingNonneg]
      exact scaledFiniteBandVelocityField_norm_sq_le timeLength
        spatialRadius (scale index) bandRadius massCeiling (radius index)
        (center index) (path index) point (scalePos index) bandRadiusNonneg
        massCeilingNonneg (radiusLe index) (massLe index point.1)
    · exact familyEquicontinuous
  refine ⟨closure family, compactFamily, ?_⟩
  intro index
  apply subset_closure
  exact ⟨index, rfl⟩

private theorem scaledFiniteBandVelocityBoundedPath_tendsto_subseq
    (timeLength spatialRadius bandRadius massCeiling timeCeiling : Real)
    (scale : Nat → Real)
    (radius : Nat → Nat)
    (center : Nat → PhysicalSpace)
    (path : Nat → Icc (0 : Real) timeLength →
      ComplexVorticityHilbertState)
    (bandRadiusNonneg : 0 ≤ bandRadius)
    (massCeilingNonneg : 0 ≤ massCeiling)
    (timeCeilingNonneg : 0 ≤ timeCeiling)
    (scalePos : ∀ index, 0 < scale index)
    (scaleLeOne : ∀ index, scale index ≤ 1)
    (radiusLe : ∀ index,
      scale index * (radius index : Real) ≤ bandRadius)
    (massLe : ∀ index time,
      scale index * finiteStateVorticityCoefficientEnstrophy
        (integerWaveFrequencyCube (radius index)) (path index time) ≤
          massCeiling)
    (timeIncrement : ∀ index first second,
      scale index * finiteStateVorticityCoefficientEnstrophy
          (integerWaveFrequencyCube (radius index))
          (path index first - path index second) ≤
        timeCeiling * dist first second) :
    ∃ limit : BoundedContinuousFunction
        (ScaledVelocityCylinder timeLength spatialRadius) PhysicalSpace,
    ∃ subsequence : Nat → Nat,
      StrictMono subsequence ∧
      Tendsto
        (fun index =>
          scaledFiniteBandVelocityBoundedPath timeLength spatialRadius
            bandRadius massCeiling timeCeiling scale radius center path
            bandRadiusNonneg massCeilingNonneg timeCeilingNonneg scalePos
            scaleLeOne radiusLe massLe timeIncrement (subsequence index))
        atTop (𝓝 limit) := by
  let sequence : Nat → BoundedContinuousFunction
      (ScaledVelocityCylinder timeLength spatialRadius) PhysicalSpace :=
    scaledFiniteBandVelocityBoundedPath timeLength spatialRadius
      bandRadius massCeiling timeCeiling scale radius center path
      bandRadiusNonneg massCeilingNonneg timeCeilingNonneg scalePos scaleLeOne
      radiusLe massLe timeIncrement
  let family : Set (BoundedContinuousFunction
      (ScaledVelocityCylinder timeLength spatialRadius) PhysicalSpace) :=
    Set.range sequence
  let valueBall : Set PhysicalSpace :=
    Metric.closedBall 0
      (Real.sqrt
        (26 * biotSavartSerrinConstant * bandRadius * massCeiling))
  have valueCeilingNonneg :
      0 ≤ 26 * biotSavartSerrinConstant * bandRadius * massCeiling := by
    exact mul_nonneg
      (mul_nonneg
        (mul_nonneg (by norm_num) biotSavartSerrinConstant_nonneg)
        bandRadiusNonneg)
      massCeilingNonneg
  have familyEquicontinuous :
      Equicontinuous
        (fun member : family =>
          (member.1 :
            ScaledVelocityCylinder timeLength spatialRadius →
              PhysicalSpace)) := by
    let spatialConstant : Real :=
      Real.sqrt
        ((2 * bandRadius + 1) ^ 3 * (2 * Real.pi) ^ 2 *
          biotSavartSerrinConstant * massCeiling)
    let timeCoefficient : Real :=
      26 * biotSavartSerrinConstant * bandRadius * timeCeiling
    let modulus : Real → Real := fun distance =>
      spatialConstant * |distance| +
        Real.sqrt (timeCoefficient * |distance|)
    have modulusContinuous : Continuous modulus := by
      exact (continuous_const.mul continuous_abs).add
        (Real.continuous_sqrt.comp (continuous_const.mul continuous_abs))
    have modulusTendsToZero : Tendsto modulus (𝓝 0) (𝓝 0) := by
      have atZero : ContinuousAt modulus 0 := modulusContinuous.continuousAt
      have modulusZero : modulus 0 = 0 := by simp [modulus]
      nth_rewrite 2 [← modulusZero]
      exact atZero
    apply Metric.equicontinuous_of_continuity_modulus modulus
      modulusTendsToZero
    intro first second member
    rcases member with ⟨function, ⟨index, functionEq⟩⟩
    subst function
    change dist
        (scaledFiniteBandVelocityField timeLength spatialRadius
          (scale index) (radius index) (center index) (path index) first)
        (scaledFiniteBandVelocityField timeLength spatialRadius
          (scale index) (radius index) (center index) (path index) second) ≤
      modulus (dist first second)
    simpa only [modulus, spatialConstant, timeCoefficient,
      abs_of_nonneg dist_nonneg] using
      scaledFiniteBandVelocityField_joint_dist_le timeLength spatialRadius
        (scale index) bandRadius massCeiling timeCeiling (radius index)
        (center index) (path index) first second (scalePos index)
        (scaleLeOne index) bandRadiusNonneg massCeilingNonneg
        timeCeilingNonneg (radiusLe index) (massLe index)
        (timeIncrement index)
  have compactFamily : IsCompact (closure family) := by
    apply BoundedContinuousFunction.arzela_ascoli valueBall
      (isCompact_closedBall _ _)
    · intro function point functionMem
      rcases functionMem with ⟨index, rfl⟩
      rw [Metric.mem_closedBall, dist_zero_right]
      rw [← sq_le_sq₀ (norm_nonneg _) (Real.sqrt_nonneg _)]
      rw [Real.sq_sqrt valueCeilingNonneg]
      exact scaledFiniteBandVelocityField_norm_sq_le timeLength
        spatialRadius (scale index) bandRadius massCeiling (radius index)
        (center index) (path index) point (scalePos index) bandRadiusNonneg
        massCeilingNonneg (radiusLe index) (massLe index point.1)
    · exact familyEquicontinuous
  have sequenceMem (index : Nat) : sequence index ∈ closure family := by
    apply subset_closure
    exact ⟨index, rfl⟩
  obtain ⟨limit, _limitMem, subsequence, subsequenceMono,
      subsequenceTendsto⟩ := compactFamily.tendsto_subseq sequenceMem
  exact ⟨limit, subsequence, subsequenceMono, by
    simpa only [sequence, Function.comp_def] using subsequenceTendsto⟩

private def velocityVorticityCoordinateTestDensity
    {X : Type*} [TopologicalSpace X]
    (test : BoundedContinuousFunction X Real)
    (velocity vorticity : BoundedContinuousFunction X PhysicalSpace)
    (velocityCoordinate vorticityCoordinate : Coordinate)
    (point : X) : Real :=
  test point * velocity point velocityCoordinate *
    vorticity point vorticityCoordinate

private theorem velocityVorticityCoordinateTestDensity_continuous
    {X : Type*} [TopologicalSpace X]
    (test : BoundedContinuousFunction X Real)
    (velocity vorticity : BoundedContinuousFunction X PhysicalSpace)
    (velocityCoordinate vorticityCoordinate : Coordinate) :
    Continuous
      (velocityVorticityCoordinateTestDensity test velocity vorticity
        velocityCoordinate vorticityCoordinate) := by
  exact
    (test.continuous.mul
      ((PiLp.continuous_apply 2 (fun _ : Coordinate => Real)
        velocityCoordinate).comp velocity.continuous)).mul
      ((PiLp.continuous_apply 2 (fun _ : Coordinate => Real)
        vorticityCoordinate).comp vorticity.continuous)

private theorem velocityVorticityCoordinateTestDensity_integral_tendsto
    {X : Type*}
    [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X]
    (μ : Measure X) [IsFiniteMeasure μ]
    (test : BoundedContinuousFunction X Real)
    (velocity vorticity : Nat →
      BoundedContinuousFunction X PhysicalSpace)
    (velocityLimit vorticityLimit :
      BoundedContinuousFunction X PhysicalSpace)
    (velocityCoordinate vorticityCoordinate : Coordinate)
    (testCeiling velocityCeiling vorticityCeiling : Real)
    (testCeilingNonneg : 0 ≤ testCeiling)
    (velocityCeilingNonneg : 0 ≤ velocityCeiling)
    (_vorticityCeilingNonneg : 0 ≤ vorticityCeiling)
    (testBound : ∀ point, |test point| ≤ testCeiling)
    (velocityBound : ∀ index point,
      ‖velocity index point‖ ≤ velocityCeiling)
    (vorticityBound : ∀ index point,
      ‖vorticity index point‖ ≤ vorticityCeiling)
    (velocityTendsto : Tendsto velocity atTop (𝓝 velocityLimit))
    (vorticityTendsto : Tendsto vorticity atTop (𝓝 vorticityLimit)) :
    Tendsto
      (fun index =>
        ∫ point,
          velocityVorticityCoordinateTestDensity test
            (velocity index) (vorticity index) velocityCoordinate
            vorticityCoordinate point ∂μ)
      atTop
      (𝓝
        (∫ point,
          velocityVorticityCoordinateTestDensity test velocityLimit
            vorticityLimit velocityCoordinate vorticityCoordinate point ∂μ)) := by
  let bound : X → Real := fun _ =>
    testCeiling * velocityCeiling * vorticityCeiling
  apply tendsto_integral_of_dominated_convergence bound
  · intro index
    exact
      (velocityVorticityCoordinateTestDensity_continuous test
        (velocity index) (vorticity index) velocityCoordinate
        vorticityCoordinate).aestronglyMeasurable
  · exact integrable_const _
  · intro index
    exact Filter.Eventually.of_forall fun point => by
      have velocityCoordinateLe :
          |velocity index point velocityCoordinate| ≤ velocityCeiling := by
        rw [← Real.norm_eq_abs]
        exact (PiLp.norm_apply_le
          (velocity index point) velocityCoordinate).trans
            (velocityBound index point)
      have vorticityCoordinateLe :
          |vorticity index point vorticityCoordinate| ≤ vorticityCeiling := by
        rw [← Real.norm_eq_abs]
        exact (PiLp.norm_apply_le
          (vorticity index point) vorticityCoordinate).trans
            (vorticityBound index point)
      rw [Real.norm_eq_abs]
      dsimp only [velocityVorticityCoordinateTestDensity, bound]
      rw [abs_mul, abs_mul]
      exact mul_le_mul
        (mul_le_mul (testBound point) velocityCoordinateLe
          (abs_nonneg _) testCeilingNonneg)
        vorticityCoordinateLe (abs_nonneg _)
        (mul_nonneg testCeilingNonneg velocityCeilingNonneg)
  · exact Filter.Eventually.of_forall fun point => by
      have velocityPoint :
          Tendsto (fun index => velocity index point) atTop
            (𝓝 (velocityLimit point)) :=
        Filter.Tendsto.comp
          ((BoundedContinuousFunction.evalCLM Real point).continuous.tendsto
            velocityLimit)
          velocityTendsto
      have vorticityPoint :
          Tendsto (fun index => vorticity index point) atTop
            (𝓝 (vorticityLimit point)) :=
        Filter.Tendsto.comp
          ((BoundedContinuousFunction.evalCLM Real point).continuous.tendsto
            vorticityLimit)
          vorticityTendsto
      have velocityCoordinateTendsto :
          Tendsto (fun index => velocity index point velocityCoordinate) atTop
            (𝓝 (velocityLimit point velocityCoordinate)) :=
        ((PiLp.continuous_apply 2 (fun _ : Coordinate => Real)
          velocityCoordinate).continuousAt.tendsto).comp velocityPoint
      have vorticityCoordinateTendsto :
          Tendsto (fun index => vorticity index point vorticityCoordinate)
            atTop (𝓝 (vorticityLimit point vorticityCoordinate)) :=
        ((PiLp.continuous_apply 2 (fun _ : Coordinate => Real)
          vorticityCoordinate).continuousAt.tendsto).comp vorticityPoint
      exact
        (tendsto_const_nhds.mul velocityCoordinateTendsto).mul
          vorticityCoordinateTendsto


private def velocityVorticityTensorTestDensity
    {X : Type*} [TopologicalSpace X]
    (test : Coordinate → Coordinate → BoundedContinuousFunction X Real)
    (velocity vorticity : BoundedContinuousFunction X PhysicalSpace)
    (point : X) : Real :=
  ∑ velocityCoordinate : Coordinate,
    ∑ vorticityCoordinate : Coordinate,
      velocityVorticityCoordinateTestDensity
        (test velocityCoordinate vorticityCoordinate) velocity vorticity
        velocityCoordinate vorticityCoordinate point

private theorem velocityVorticityCoordinateTestDensity_integrable
    {X : Type*}
    [TopologicalSpace X] [CompactSpace X]
    [MeasurableSpace X] [BorelSpace X]
    (μ : Measure X) [IsFiniteMeasure μ]
    (test : BoundedContinuousFunction X Real)
    (velocity vorticity : BoundedContinuousFunction X PhysicalSpace)
    (velocityCoordinate vorticityCoordinate : Coordinate) :
    Integrable
      (velocityVorticityCoordinateTestDensity test velocity vorticity
        velocityCoordinate vorticityCoordinate) μ := by
  let density : BoundedContinuousFunction X Real :=
    BoundedContinuousFunction.mkOfCompact
      ⟨velocityVorticityCoordinateTestDensity test velocity vorticity
          velocityCoordinate vorticityCoordinate,
        velocityVorticityCoordinateTestDensity_continuous test velocity
          vorticity velocityCoordinate vorticityCoordinate⟩
  change Integrable (density : X → Real) μ
  exact BoundedContinuousFunction.integrable μ density

private theorem velocityVorticityTensorTestDensity_integral_tendsto
    {X : Type*}
    [TopologicalSpace X] [CompactSpace X]
    [MeasurableSpace X] [BorelSpace X]
    (μ : Measure X) [IsFiniteMeasure μ]
    (test : Coordinate → Coordinate → BoundedContinuousFunction X Real)
    (velocity vorticity : Nat →
      BoundedContinuousFunction X PhysicalSpace)
    (velocityLimit vorticityLimit :
      BoundedContinuousFunction X PhysicalSpace)
    (testCeiling velocityCeiling vorticityCeiling : Real)
    (testCeilingNonneg : 0 ≤ testCeiling)
    (velocityCeilingNonneg : 0 ≤ velocityCeiling)
    (vorticityCeilingNonneg : 0 ≤ vorticityCeiling)
    (testBound : ∀ velocityCoordinate vorticityCoordinate point,
      |test velocityCoordinate vorticityCoordinate point| ≤ testCeiling)
    (velocityBound : ∀ index point,
      ‖velocity index point‖ ≤ velocityCeiling)
    (vorticityBound : ∀ index point,
      ‖vorticity index point‖ ≤ vorticityCeiling)
    (velocityTendsto : Tendsto velocity atTop (𝓝 velocityLimit))
    (vorticityTendsto : Tendsto vorticity atTop (𝓝 vorticityLimit)) :
    Tendsto
      (fun index =>
        ∫ point,
          velocityVorticityTensorTestDensity test (velocity index)
            (vorticity index) point ∂μ)
      atTop
      (𝓝
        (∫ point,
          velocityVorticityTensorTestDensity test velocityLimit
            vorticityLimit point ∂μ)) := by
  have coordinateTendsto
      (velocityCoordinate vorticityCoordinate : Coordinate) :=
    velocityVorticityCoordinateTestDensity_integral_tendsto μ
      (test velocityCoordinate vorticityCoordinate) velocity vorticity
      velocityLimit vorticityLimit velocityCoordinate vorticityCoordinate
      testCeiling velocityCeiling vorticityCeiling testCeilingNonneg
      velocityCeilingNonneg vorticityCeilingNonneg
      (testBound velocityCoordinate vorticityCoordinate) velocityBound
      vorticityBound velocityTendsto vorticityTendsto
  have summedTendsto :
      Tendsto
        (fun index =>
          ∑ velocityCoordinate : Coordinate,
            ∑ vorticityCoordinate : Coordinate,
              ∫ point,
                velocityVorticityCoordinateTestDensity
                  (test velocityCoordinate vorticityCoordinate)
                  (velocity index) (vorticity index) velocityCoordinate
                  vorticityCoordinate point ∂μ)
        atTop
        (𝓝
          (∑ velocityCoordinate : Coordinate,
            ∑ vorticityCoordinate : Coordinate,
              ∫ point,
                velocityVorticityCoordinateTestDensity
                  (test velocityCoordinate vorticityCoordinate)
                  velocityLimit vorticityLimit velocityCoordinate
                  vorticityCoordinate point ∂μ)) := by
    apply tendsto_finsetSum Finset.univ
    intro velocityCoordinate _velocityCoordinateMem
    apply tendsto_finsetSum Finset.univ
    intro vorticityCoordinate _vorticityCoordinateMem
    exact coordinateTendsto velocityCoordinate vorticityCoordinate
  have integralEq
      (velocity' vorticity' : BoundedContinuousFunction X PhysicalSpace) :
      (∫ point,
          velocityVorticityTensorTestDensity test velocity' vorticity'
            point ∂μ) =
        ∑ velocityCoordinate : Coordinate,
          ∑ vorticityCoordinate : Coordinate,
            ∫ point,
              velocityVorticityCoordinateTestDensity
                (test velocityCoordinate vorticityCoordinate) velocity'
                vorticity' velocityCoordinate vorticityCoordinate point
                ∂μ := by
    unfold velocityVorticityTensorTestDensity
    have coordinateIntegrable
        (velocityCoordinate vorticityCoordinate : Coordinate) :
        Integrable
          (velocityVorticityCoordinateTestDensity
            (test velocityCoordinate vorticityCoordinate) velocity'
            vorticity' velocityCoordinate vorticityCoordinate) μ :=
      velocityVorticityCoordinateTestDensity_integrable μ
        (test velocityCoordinate vorticityCoordinate) velocity' vorticity'
        velocityCoordinate vorticityCoordinate
    have rowIntegrable (velocityCoordinate : Coordinate) :
        Integrable
          (fun point =>
            ∑ vorticityCoordinate : Coordinate,
              velocityVorticityCoordinateTestDensity
                (test velocityCoordinate vorticityCoordinate) velocity'
                vorticity' velocityCoordinate vorticityCoordinate point) μ := by
      apply integrable_finsetSum
      intro vorticityCoordinate _vorticityCoordinateMem
      exact coordinateIntegrable velocityCoordinate vorticityCoordinate
    calc
      (∫ point,
          ∑ velocityCoordinate : Coordinate,
            ∑ vorticityCoordinate : Coordinate,
              velocityVorticityCoordinateTestDensity
                (test velocityCoordinate vorticityCoordinate) velocity'
                vorticity' velocityCoordinate vorticityCoordinate point ∂μ) =
          ∑ velocityCoordinate : Coordinate,
            ∫ point,
              ∑ vorticityCoordinate : Coordinate,
                velocityVorticityCoordinateTestDensity
                  (test velocityCoordinate vorticityCoordinate) velocity'
                  vorticity' velocityCoordinate vorticityCoordinate point ∂μ :=
        integral_finsetSum Finset.univ fun velocityCoordinate _ =>
          rowIntegrable velocityCoordinate
      _ = _ := by
        apply Finset.sum_congr rfl
        intro velocityCoordinate _velocityCoordinateMem
        exact integral_finsetSum Finset.univ fun vorticityCoordinate _ =>
          coordinateIntegrable velocityCoordinate vorticityCoordinate
  simpa only [integralEq] using summedTendsto

/-- On one fixed physical band, the scale-critical Biot--Savart velocities
are compact on the same cylinder as any already convergent vorticity
profile.  One further source subsequence preserves the vorticity limit,
produces a velocity limit, and carries every compact tensor test of
`u ⊗ ω` to the corresponding limit pairing. -/
theorem finiteBandVelocity_parabolicScale_pairedTensorTest_tendsto_subseq
    (timeLength spatialRadius bandRadius massCeiling timeCeiling : Real)
    (scale : Nat → Real)
    (radius : Nat → Nat)
    (center : Nat → PhysicalSpace)
    (path : Nat → Icc (0 : Real) timeLength →
      ComplexVorticityHilbertState)
    (bandRadiusNonneg : 0 ≤ bandRadius)
    (massCeilingNonneg : 0 ≤ massCeiling)
    (timeCeilingNonneg : 0 ≤ timeCeiling)
    (scalePos : ∀ index, 0 < scale index)
    (scaleLeOne : ∀ index, scale index ≤ 1)
    (radiusLe : ∀ index,
      scale index * (radius index : Real) ≤ bandRadius)
    (massLe : ∀ index time,
      scale index * finiteStateVorticityCoefficientEnstrophy
        (integerWaveFrequencyCube (radius index)) (path index time) ≤
          massCeiling)
    (timeIncrement : ∀ index first second,
      scale index * finiteStateVorticityCoefficientEnstrophy
          (integerWaveFrequencyCube (radius index))
          (path index first - path index second) ≤
        timeCeiling * dist first second)
    (μ : Measure
      (Icc (0 : Real) timeLength ×
        Metric.closedBall (0 : PhysicalSpace) spatialRadius))
    [IsFiniteMeasure μ]
    (vorticityProfile : Nat → BoundedContinuousFunction
      (Icc (0 : Real) timeLength ×
        Metric.closedBall (0 : PhysicalSpace) spatialRadius) PhysicalSpace)
    (vorticityLimit : BoundedContinuousFunction
      (Icc (0 : Real) timeLength ×
        Metric.closedBall (0 : PhysicalSpace) spatialRadius) PhysicalSpace)
    (vorticityCeiling : Real)
    (vorticityCeilingNonneg : 0 ≤ vorticityCeiling)
    (vorticityBound : ∀ index point,
      ‖vorticityProfile index point‖ ≤ vorticityCeiling)
    (vorticityTendsto : Tendsto vorticityProfile atTop
      (𝓝 vorticityLimit)) :
    ∃ velocityProfile : Nat → BoundedContinuousFunction
        (Icc (0 : Real) timeLength ×
          Metric.closedBall (0 : PhysicalSpace) spatialRadius) PhysicalSpace,
    ∃ velocityLimit : BoundedContinuousFunction
        (Icc (0 : Real) timeLength ×
          Metric.closedBall (0 : PhysicalSpace) spatialRadius) PhysicalSpace,
    ∃ subsequence : Nat → Nat,
      StrictMono subsequence ∧
      (∀ index point,
        velocityProfile index point =
          scale index •
            finiteRealComplexFourierField
              (integerWaveFrequencyCube (radius index))
              (finiteStateVelocityCoefficient (path index point.1))
              (center index + scale index • point.2.1)) ∧
      Tendsto (fun index => velocityProfile (subsequence index)) atTop
        (𝓝 velocityLimit) ∧
      Tendsto (fun index => vorticityProfile (subsequence index)) atTop
        (𝓝 vorticityLimit) ∧
      ∀ (test : Coordinate → Coordinate → BoundedContinuousFunction
            (Icc (0 : Real) timeLength ×
              Metric.closedBall (0 : PhysicalSpace) spatialRadius) Real)
          (testCeiling : Real),
        0 ≤ testCeiling →
        (∀ velocityCoordinate vorticityCoordinate point,
          |test velocityCoordinate vorticityCoordinate point| ≤
            testCeiling) →
        Tendsto
          (fun index =>
            ∫ point,
              ∑ velocityCoordinate : Coordinate,
                ∑ vorticityCoordinate : Coordinate,
                  test velocityCoordinate vorticityCoordinate point *
                    velocityProfile (subsequence index) point
                      velocityCoordinate *
                    vorticityProfile (subsequence index) point
                      vorticityCoordinate ∂μ)
          atTop
          (𝓝
            (∫ point,
              ∑ velocityCoordinate : Coordinate,
                ∑ vorticityCoordinate : Coordinate,
                  test velocityCoordinate vorticityCoordinate point *
                    velocityLimit point velocityCoordinate *
                    vorticityLimit point vorticityCoordinate ∂μ)) := by
  let velocityProfile : Nat → BoundedContinuousFunction
      (ScaledVelocityCylinder timeLength spatialRadius) PhysicalSpace :=
    scaledFiniteBandVelocityBoundedPath timeLength spatialRadius bandRadius
      massCeiling timeCeiling scale radius center path bandRadiusNonneg
      massCeilingNonneg timeCeilingNonneg scalePos scaleLeOne radiusLe massLe
      timeIncrement
  obtain ⟨velocityLimit, subsequence, subsequenceMono,
      velocityTendsto⟩ :=
    scaledFiniteBandVelocityBoundedPath_tendsto_subseq timeLength
      spatialRadius bandRadius massCeiling timeCeiling scale radius center path
      bandRadiusNonneg massCeilingNonneg timeCeilingNonneg scalePos scaleLeOne
      radiusLe massLe timeIncrement
  have vorticitySubsequenceTendsto :
      Tendsto (fun index => vorticityProfile (subsequence index)) atTop
        (𝓝 vorticityLimit) :=
    vorticityTendsto.comp subsequenceMono.tendsto_atTop
  let velocityCeiling : Real :=
    Real.sqrt
      (26 * biotSavartSerrinConstant * bandRadius * massCeiling)
  have velocityCeilingNonneg : 0 ≤ velocityCeiling := Real.sqrt_nonneg _
  have velocityCeilingArgumentNonneg :
      0 ≤ 26 * biotSavartSerrinConstant * bandRadius * massCeiling := by
    exact mul_nonneg
      (mul_nonneg
        (mul_nonneg (by norm_num) biotSavartSerrinConstant_nonneg)
        bandRadiusNonneg)
      massCeilingNonneg
  have velocityBound (index : Nat)
      (point : ScaledVelocityCylinder timeLength spatialRadius) :
      ‖velocityProfile index point‖ ≤ velocityCeiling := by
    rw [← sq_le_sq₀ (norm_nonneg _) velocityCeilingNonneg]
    rw [Real.sq_sqrt velocityCeilingArgumentNonneg]
    exact scaledFiniteBandVelocityField_norm_sq_le timeLength spatialRadius
      (scale index) bandRadius massCeiling (radius index) (center index)
      (path index) point (scalePos index) bandRadiusNonneg
      massCeilingNonneg (radiusLe index) (massLe index point.1)
  refine ⟨velocityProfile, velocityLimit, subsequence, subsequenceMono,
    ?_, ?_, vorticitySubsequenceTendsto, ?_⟩
  · intro index point
    exact scaledFiniteBandVelocityBoundedPath_apply timeLength spatialRadius
      bandRadius massCeiling timeCeiling scale radius center path
      bandRadiusNonneg massCeilingNonneg timeCeilingNonneg scalePos scaleLeOne
      radiusLe massLe timeIncrement index point
  · simpa only [velocityProfile] using velocityTendsto
  · intro test testCeiling testCeilingNonneg testBound
    have productTendsto :=
      velocityVorticityTensorTestDensity_integral_tendsto μ test
        (fun index => velocityProfile (subsequence index))
        (fun index => vorticityProfile (subsequence index)) velocityLimit
        vorticityLimit testCeiling velocityCeiling vorticityCeiling
        testCeilingNonneg velocityCeilingNonneg vorticityCeilingNonneg
        testBound
        (fun index point => velocityBound (subsequence index) point)
        (fun index point => vorticityBound (subsequence index) point)
        (by simpa only [velocityProfile] using velocityTendsto)
        vorticitySubsequenceTendsto
    simpa only [velocityVorticityTensorTestDensity,
      velocityVorticityCoordinateTestDensity] using productTendsto

private theorem integerWaveFrequencyCube_card_real (radius : Nat) :
    ((integerWaveFrequencyCube radius).card : Real) =
      (2 * radius + 1 : Nat) ^ 3 := by
  have cubeCard :
      (integerWaveFrequencyCube radius).card = (2 * radius + 1) ^ 3 := by
    simp [integerWaveFrequencyCube, Fintype.card_piFinset, Int.card_Icc]
    omega
  exact_mod_cast cubeCard

private theorem scaledFrequencyCube_card_tendsto
    (level : Nat → Real)
    (radius : Nat → Nat)
    (limit : Real)
    (levelTendsto : Tendsto level atTop atTop)
    (ratioTendsto : Tendsto
      (fun index => (radius index : Real) / level index) atTop
        (nhds limit)) :
    Tendsto
      (fun index => level index ^ (-3 : Int) *
        ((integerWaveFrequencyCube (radius index)).card : Real))
      atTop (nhds ((2 * limit) ^ 3)) := by
  have levelInvTendsto :
      Tendsto (fun index => (level index)⁻¹) atTop (nhds 0) :=
    tendsto_inv_atTop_zero.comp levelTendsto
  have sideTendsto :
      Tendsto
        (fun index =>
          (2 : Real) * ((radius index : Real) / level index) +
            (level index)⁻¹)
        atTop (nhds (2 * limit + 0)) :=
    (tendsto_const_nhds.mul ratioTendsto).add levelInvTendsto
  have cubeTendsto := sideTendsto.pow 3
  convert cubeTendsto using 1
  · funext index
    rw [integerWaveFrequencyCube_card_real]
    push_cast
    by_cases hlevel : level index = 0
    · norm_num [hlevel]
    · field_simp [hlevel]
  · ring_nf

private theorem scaledInteriorFrequencyCube_card_tendsto
    (level : Nat → Real)
    (sigma : Real)
    (sigmaNonneg : 0 ≤ sigma)
    (levelTendsto : Tendsto level atTop atTop) :
    Tendsto
      (fun index => level index ^ (-3 : Int) *
        ((integerWaveFrequencyCube ⌊sigma * level index⌋₊).card : Real))
      atTop (nhds ((2 * sigma) ^ 3)) := by
  have ratioTendsto :
      Tendsto
        (fun index => (⌊sigma * level index⌋₊ : Real) / level index)
        atTop (nhds sigma) :=
    (tendsto_nat_floor_mul_div_atTop sigmaNonneg).comp levelTendsto
  exact scaledFrequencyCube_card_tendsto level
    (fun index => ⌊sigma * level index⌋₊) sigma levelTendsto ratioTendsto

private theorem scaledFrequencyCubeShell_card_tendsto
    (level : Nat → Real)
    (radius : Nat → Nat)
    (limit sigma : Real)
    (sigmaNonneg : 0 ≤ sigma)
    (sigmaLt : sigma < limit)
    (levelTendsto : Tendsto level atTop atTop)
    (ratioTendsto : Tendsto
      (fun index => (radius index : Real) / level index) atTop
        (nhds limit)) :
    Tendsto
      (fun index => level index ^ (-3 : Int) *
        (((integerWaveFrequencyCube (radius index)) \
          (integerWaveFrequencyCube ⌊sigma * level index⌋₊)).card : Real))
      atTop (nhds ((2 * limit) ^ 3 - (2 * sigma) ^ 3)) := by
  have interiorRatioTendsto :
      Tendsto
        (fun index => (⌊sigma * level index⌋₊ : Real) / level index)
        atTop (nhds sigma) :=
    (tendsto_nat_floor_mul_div_atTop sigmaNonneg).comp levelTendsto
  let midpoint : Real := (sigma + limit) / 2
  have sigmaLtMidpoint : sigma < midpoint := by
    dsimp only [midpoint]
    linarith
  have midpointLtLimit : midpoint < limit := by
    dsimp only [midpoint]
    linarith
  have eventuallyInteriorLt :
      ∀ᶠ index in atTop,
        (⌊sigma * level index⌋₊ : Real) / level index < midpoint :=
    (tendsto_order.1 interiorRatioTendsto).2 midpoint sigmaLtMidpoint
  have eventuallyOuterGt :
      ∀ᶠ index in atTop,
        midpoint < (radius index : Real) / level index :=
    (tendsto_order.1 ratioTendsto).1 midpoint midpointLtLimit
  have eventuallyLevelPos : ∀ᶠ index in atTop, 0 < level index :=
    levelTendsto (Ioi_mem_atTop 0)
  have eventuallySubset : ∀ᶠ index in atTop,
      integerWaveFrequencyCube ⌊sigma * level index⌋₊ ⊆
        integerWaveFrequencyCube (radius index) := by
    filter_upwards [eventuallyInteriorLt, eventuallyOuterGt,
      eventuallyLevelPos] with index interiorLt outerGt levelPos
    apply integerWaveFrequencyCube_mono
    have castLt : (⌊sigma * level index⌋₊ : Real) < radius index :=
      (div_lt_div_iff_of_pos_right levelPos).mp (interiorLt.trans outerGt)
    exact_mod_cast castLt.le
  have outerTendsto :=
    scaledFrequencyCube_card_tendsto level radius limit levelTendsto
      ratioTendsto
  have interiorTendsto :=
    scaledInteriorFrequencyCube_card_tendsto level sigma sigmaNonneg
      levelTendsto
  apply (outerTendsto.sub interiorTendsto).congr'
  filter_upwards [eventuallySubset] with index subset
  rw [Finset.cast_card_sdiff subset]
  ring

private theorem finiteRealComplexFourierField_norm_sq_le_card_mul_amplitude
    (modes : Finset IntegerWavevector)
    (coefficient : IntegerWavevector → ComplexCoordinateVector)
    (point : PhysicalSpace) :
    ‖finiteRealComplexFourierField modes coefficient point‖ ^ 2 ≤
      (modes.card : Real) *
        ∑ wave ∈ modes,
          complexCoordinateAmplitudeSq (coefficient wave) := by
  calc
    ‖finiteRealComplexFourierField modes coefficient point‖ ^ 2 ≤
        finiteVelocityFourierMajorant modes coefficient ^ 2 :=
      finiteRealComplexFourierField_norm_sq_le_velocityMajorant_sq
        modes coefficient point
    _ ≤ (modes.card : Real) *
          ∑ wave ∈ modes,
            (Real.sqrt
              (complexCoordinateAmplitudeSq (coefficient wave))) ^ 2 := by
      unfold finiteVelocityFourierMajorant
      exact sq_sum_le_card_mul_sum_sq
    _ = (modes.card : Real) *
          ∑ wave ∈ modes,
            complexCoordinateAmplitudeSq (coefficient wave) := by
      congr 1
      apply Finset.sum_congr rfl
      intro wave _waveMem
      rw [Real.sq_sqrt (complexCoordinateAmplitudeSq_nonneg _)]

private theorem realComplexFourierMode_real_smul
    (wave : IntegerWavevector)
    (scalar : Real)
    (coefficient : ComplexCoordinateVector)
    (point : PhysicalSpace) :
    realComplexFourierMode wave (scalar • coefficient) point =
      scalar • realComplexFourierMode wave coefficient point := by
  ext coordinate
  simp [realComplexFourierMode, coefficientReal, coefficientImag]
  ring

private theorem complexCoordinateAmplitudeSq_real_smul
    (scalar : Real)
    (coefficient : ComplexCoordinateVector) :
    complexCoordinateAmplitudeSq (scalar • coefficient) =
      scalar ^ 2 * complexCoordinateAmplitudeSq coefficient := by
  simp_rw [complexCoordinateAmplitudeSq_eq_complexCoordinateVectorNormSq]
  change complexCoordinateVectorNormSq ((scalar : Complex) • coefficient) = _
  rw [complexCoordinateVectorNormSq_smul, Complex.normSq_ofReal]
  ring

private theorem finiteRealComplexFourierField_weightedDifference_eq_shell
    (inner outer : Finset IntegerWavevector)
    (innerSubset : inner ⊆ outer)
    (coefficient : IntegerWavevector → ComplexCoordinateVector)
    (weight : IntegerWavevector → Real)
    (weightOne : ∀ wave ∈ inner, weight wave = 1)
    (point : PhysicalSpace) :
    finiteRealComplexFourierField outer coefficient point -
        finiteRealComplexFourierField outer
          (fun wave => weight wave • coefficient wave) point =
      finiteRealComplexFourierField (outer \ inner)
        (fun wave => (1 - weight wave) • coefficient wave) point := by
  unfold finiteRealComplexFourierField
  rw [← Finset.sum_sub_distrib]
  have split := Finset.sum_sdiff innerSubset
    (f := fun wave =>
      realComplexFourierMode wave (coefficient wave) point -
        realComplexFourierMode wave (weight wave • coefficient wave) point)
  rw [← split]
  have innerZero :
      ∑ wave ∈ inner,
          (realComplexFourierMode wave (coefficient wave) point -
            realComplexFourierMode wave
              (weight wave • coefficient wave) point) = 0 := by
    apply Finset.sum_eq_zero
    intro wave waveMem
    rw [realComplexFourierMode_real_smul, weightOne wave waveMem]
    simp
  rw [innerZero, add_zero]
  apply Finset.sum_congr rfl
  intro wave _waveMem
  rw [realComplexFourierMode_real_smul,
    realComplexFourierMode_real_smul]
  module

private theorem scaledWeightedFourierField_difference_norm_sq_le_shell
    (inner outer : Finset IntegerWavevector)
    (innerSubset : inner ⊆ outer)
    (coefficient : IntegerWavevector → ComplexCoordinateVector)
    (weight : IntegerWavevector → Real)
    (weightOne : ∀ wave ∈ inner, weight wave = 1)
    (weightUnit : ∀ wave ∈ outer, 0 ≤ weight wave ∧ weight wave ≤ 1)
    (scale massCeiling : Real)
    (scalePos : 0 < scale)
    (massBound :
      scale *
          ∑ wave ∈ outer,
            complexCoordinateAmplitudeSq (coefficient wave) ≤
        massCeiling)
    (point : PhysicalSpace) :
    ‖(scale ^ 2 : Real) •
        (finiteRealComplexFourierField outer coefficient point -
          finiteRealComplexFourierField outer
            (fun wave => weight wave • coefficient wave) point)‖ ^ 2 ≤
      scale ^ 3 * ((outer \ inner).card : Real) * massCeiling := by
  have weightedShellMassLe :
      ∑ wave ∈ outer \ inner,
          complexCoordinateAmplitudeSq
            ((1 - weight wave) • coefficient wave) ≤
        ∑ wave ∈ outer,
          complexCoordinateAmplitudeSq (coefficient wave) := by
    calc
      ∑ wave ∈ outer \ inner,
          complexCoordinateAmplitudeSq
            ((1 - weight wave) • coefficient wave) ≤
          ∑ wave ∈ outer \ inner,
            complexCoordinateAmplitudeSq (coefficient wave) := by
        apply Finset.sum_le_sum
        intro wave waveMem
        rw [complexCoordinateAmplitudeSq_real_smul]
        have waveOuter : wave ∈ outer := (Finset.mem_sdiff.mp waveMem).1
        have bounds := weightUnit wave waveOuter
        have factorLe : (1 - weight wave) ^ 2 ≤ 1 := by nlinarith
        exact mul_le_of_le_one_left
          (complexCoordinateAmplitudeSq_nonneg _) factorLe
      _ ≤ ∑ wave ∈ outer,
            complexCoordinateAmplitudeSq (coefficient wave) :=
        Finset.sum_le_sum_of_subset_of_nonneg
          (Finset.sdiff_subset : outer \ inner ⊆ outer)
          (fun _ _ _ => complexCoordinateAmplitudeSq_nonneg _)
  have scaledWeightedShellMassLe :
      scale *
          ∑ wave ∈ outer \ inner,
            complexCoordinateAmplitudeSq
              ((1 - weight wave) • coefficient wave) ≤
        massCeiling :=
    (mul_le_mul_of_nonneg_left weightedShellMassLe scalePos.le).trans
      massBound
  rw [finiteRealComplexFourierField_weightedDifference_eq_shell
    inner outer innerSubset coefficient weight weightOne]
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg scale)]
  calc
    (scale ^ 2 *
        ‖finiteRealComplexFourierField (outer \ inner)
          (fun wave => (1 - weight wave) • coefficient wave) point‖) ^ 2 ≤
        (scale ^ 2) ^ 2 *
          (((outer \ inner).card : Real) *
            ∑ wave ∈ outer \ inner,
              complexCoordinateAmplitudeSq
                ((1 - weight wave) • coefficient wave)) := by
      rw [mul_pow]
      gcongr
      exact finiteRealComplexFourierField_norm_sq_le_card_mul_amplitude
        (outer \ inner)
        (fun wave => (1 - weight wave) • coefficient wave) point
    _ = scale ^ 3 * ((outer \ inner).card : Real) *
        (scale *
          ∑ wave ∈ outer \ inner,
            complexCoordinateAmplitudeSq
              ((1 - weight wave) • coefficient wave)) := by ring
    _ ≤ scale ^ 3 * ((outer \ inner).card : Real) * massCeiling :=
      mul_le_mul_of_nonneg_left scaledWeightedShellMassLe (by positivity)

private theorem scaledWeightedFourierField_difference_eventually_lt
    (level : Nat → Real)
    (radius : Nat → Nat)
    (coefficient : Nat → IntegerWavevector → ComplexCoordinateVector)
    (weight : Nat → IntegerWavevector → Real)
    (point : Nat → PhysicalSpace)
    (limit sigma massCeiling threshold : Real)
    (sigmaNonneg : 0 ≤ sigma)
    (sigmaLt : sigma < limit)
    (levelPos : ∀ index, 0 < level index)
    (levelTendsto : Tendsto level atTop atTop)
    (ratioTendsto : Tendsto
      (fun index => (radius index : Real) / level index) atTop
        (nhds limit))
    (weightOne : ∀ index wave,
      wave ∈ integerWaveFrequencyCube ⌊sigma * level index⌋₊ →
        weight index wave = 1)
    (weightUnit : ∀ index wave,
      wave ∈ integerWaveFrequencyCube (radius index) →
        0 ≤ weight index wave ∧ weight index wave ≤ 1)
    (massBound : ∀ index,
      (level index)⁻¹ *
          ∑ wave ∈ integerWaveFrequencyCube (radius index),
            complexCoordinateAmplitudeSq (coefficient index wave) ≤
        massCeiling)
    (costLt :
      (((2 * limit) ^ 3 - (2 * sigma) ^ 3) * massCeiling) < threshold) :
    ∀ᶠ index in atTop,
      ‖((level index)⁻¹ ^ 2 : Real) •
          (finiteRealComplexFourierField
              (integerWaveFrequencyCube (radius index))
              (coefficient index) (point index) -
            finiteRealComplexFourierField
              (integerWaveFrequencyCube (radius index))
              (fun wave => weight index wave • coefficient index wave)
              (point index))‖ ^ 2 < threshold := by
  have interiorRatioTendsto :
      Tendsto
        (fun index => (⌊sigma * level index⌋₊ : Real) / level index)
        atTop (nhds sigma) :=
    (tendsto_nat_floor_mul_div_atTop sigmaNonneg).comp levelTendsto
  let midpoint : Real := (sigma + limit) / 2
  have sigmaLtMidpoint : sigma < midpoint := by
    dsimp only [midpoint]
    linarith
  have midpointLtLimit : midpoint < limit := by
    dsimp only [midpoint]
    linarith
  have eventuallyInteriorLt :
      ∀ᶠ index in atTop,
        (⌊sigma * level index⌋₊ : Real) / level index < midpoint :=
    (tendsto_order.1 interiorRatioTendsto).2 midpoint sigmaLtMidpoint
  have eventuallyOuterGt :
      ∀ᶠ index in atTop,
        midpoint < (radius index : Real) / level index :=
    (tendsto_order.1 ratioTendsto).1 midpoint midpointLtLimit
  have eventuallySubset : ∀ᶠ index in atTop,
      integerWaveFrequencyCube ⌊sigma * level index⌋₊ ⊆
        integerWaveFrequencyCube (radius index) := by
    filter_upwards [eventuallyInteriorLt, eventuallyOuterGt] with
      index interiorLt outerGt
    apply integerWaveFrequencyCube_mono
    have castLt : (⌊sigma * level index⌋₊ : Real) < radius index :=
      (div_lt_div_iff_of_pos_right (levelPos index)).mp
        (interiorLt.trans outerGt)
    exact_mod_cast castLt.le
  have costTendsto :
      Tendsto
        (fun index =>
          (level index ^ (-3 : Int) *
              (((integerWaveFrequencyCube (radius index)) \
                (integerWaveFrequencyCube
                  ⌊sigma * level index⌋₊)).card : Real)) * massCeiling)
        atTop
        (nhds
          (((2 * limit) ^ 3 - (2 * sigma) ^ 3) * massCeiling)) :=
    (scaledFrequencyCubeShell_card_tendsto level radius limit sigma
      sigmaNonneg sigmaLt levelTendsto ratioTendsto).mul
        tendsto_const_nhds
  have eventuallyCost : ∀ᶠ index in atTop,
      (level index ^ (-3 : Int) *
          (((integerWaveFrequencyCube (radius index)) \
            (integerWaveFrequencyCube ⌊sigma * level index⌋₊)).card :
              Real)) * massCeiling < threshold :=
    costTendsto.eventually (Iio_mem_nhds costLt)
  filter_upwards [eventuallySubset, eventuallyCost] with
    index innerSubset costSmall
  calc
    ‖((level index)⁻¹ ^ 2 : Real) •
        (finiteRealComplexFourierField
            (integerWaveFrequencyCube (radius index))
            (coefficient index) (point index) -
          finiteRealComplexFourierField
            (integerWaveFrequencyCube (radius index))
            (fun wave => weight index wave • coefficient index wave)
            (point index))‖ ^ 2 ≤
        (level index)⁻¹ ^ 3 *
          (((integerWaveFrequencyCube (radius index)) \
            (integerWaveFrequencyCube ⌊sigma * level index⌋₊)).card :
              Real) * massCeiling :=
      scaledWeightedFourierField_difference_norm_sq_le_shell
        (integerWaveFrequencyCube ⌊sigma * level index⌋₊)
        (integerWaveFrequencyCube (radius index)) innerSubset
        (coefficient index) (weight index) (weightOne index)
        (weightUnit index) (level index)⁻¹ massCeiling
        (inv_pos.mpr (levelPos index)) (massBound index) (point index)
    _ = (level index ^ (-3 : Int) *
          (((integerWaveFrequencyCube (radius index)) \
            (integerWaveFrequencyCube ⌊sigma * level index⌋₊)).card :
              Real)) * massCeiling := by
      rw [zpow_neg, inv_pow]
      rfl
    _ < threshold := costSmall

private theorem exists_scaledFrequencyCubeShell_cost_lt
    (limit massCeiling threshold : Real)
    (limitPos : 0 < limit)
    (thresholdPos : 0 < threshold) :
    ∃ sigma : Real,
      0 ≤ sigma ∧ sigma < limit ∧
        (((2 * limit) ^ 3 - (2 * sigma) ^ 3) * massCeiling) <
          threshold := by
  let cost : Real → Real := fun sigma =>
    (((2 * limit) ^ 3 - (2 * sigma) ^ 3) * massCeiling)
  have costTendsto :
      Tendsto cost (nhdsWithin limit (Iio limit)) (nhds 0) := by
    have costContinuous : Continuous cost := by
      dsimp only [cost]
      fun_prop
    have costAtLimit : cost limit = 0 := by
      dsimp only [cost]
      ring
    rw [← costAtLimit]
    exact costContinuous.continuousAt.mono_left inf_le_left
  have eventuallySmall :
      ∀ᶠ sigma in nhdsWithin limit (Iio limit), cost sigma < threshold :=
    costTendsto.eventually (Iio_mem_nhds thresholdPos)
  have eventuallyNonneg :
      ∀ᶠ sigma in nhdsWithin limit (Iio limit), 0 ≤ sigma :=
    Filter.Eventually.filter_mono inf_le_left (Ici_mem_nhds limitPos)
  have eventuallyLt :
      ∀ᶠ sigma in nhdsWithin limit (Iio limit), sigma < limit :=
    self_mem_nhdsWithin
  obtain ⟨sigma, sigmaNonneg, sigmaLt, small⟩ :=
    (eventuallyNonneg.and (eventuallyLt.and eventuallySmall)).exists
  exact ⟨sigma, sigmaNonneg, sigmaLt, small⟩

/-- A nonzero scaled finite-band vorticity limit has a quantitative detector
strictly inside its limiting physical-frequency cube.  The coordinate and
interior radius are fixed before the eventual tail, and every real plateau
weight on that interior cube retains a uniform nonzero coordinate. -/
theorem finiteBandVorticity_parabolicScale_weightedCoordinate_lowerBound
    (level : Nat → Real)
    (radius : Nat → Nat)
    (coefficient : Nat → IntegerWavevector → ComplexCoordinateVector)
    (weight : Real → Nat → IntegerWavevector → Real)
    (point : Nat → PhysicalSpace)
    (limitRadius massCeiling : Real)
    (limitValue : PhysicalSpace)
    (limitRadiusPos : 0 < limitRadius)
    (limitValueNe : limitValue ≠ 0)
    (levelPos : ∀ index, 0 < level index)
    (levelTendsto : Tendsto level atTop atTop)
    (ratioTendsto : Tendsto
      (fun index => (radius index : Real) / level index) atTop
        (nhds limitRadius))
    (weightOne : ∀ sigma index wave,
      wave ∈ integerWaveFrequencyCube ⌊sigma * level index⌋₊ →
        weight sigma index wave = 1)
    (weightUnit : ∀ sigma index wave,
      wave ∈ integerWaveFrequencyCube (radius index) →
        0 ≤ weight sigma index wave ∧ weight sigma index wave ≤ 1)
    (massBound : ∀ index,
      (level index)⁻¹ *
          ∑ wave ∈ integerWaveFrequencyCube (radius index),
            complexCoordinateAmplitudeSq (coefficient index wave) ≤
        massCeiling)
    (outerTendsto : Tendsto
      (fun index =>
        ((level index)⁻¹ ^ 2 : Real) •
          finiteRealComplexFourierField
            (integerWaveFrequencyCube (radius index))
            (coefficient index) (point index))
      atTop (nhds limitValue)) :
    ∃ testCoordinate : Coordinate,
      ∃ sigma lowerBound : Real,
        0 ≤ sigma ∧ sigma < limitRadius ∧ 0 < lowerBound ∧
          ∀ᶠ index in atTop,
            lowerBound ≤
              ‖(((level index)⁻¹ ^ 2 : Real) •
                finiteRealComplexFourierField
                  (integerWaveFrequencyCube (radius index))
                  (fun wave =>
                    weight sigma index wave • coefficient index wave)
                  (point index)) testCoordinate‖ := by
  obtain ⟨testCoordinate, limitCoordinateNe⟩ :
      ∃ coordinate : Coordinate, limitValue coordinate ≠ 0 := by
    by_contra allZero
    push Not at allZero
    apply limitValueNe
    ext coordinate
    exact allZero coordinate
  have limitCoordinateNormPos : 0 < ‖limitValue testCoordinate‖ :=
    norm_pos_iff.mpr limitCoordinateNe
  let quarter : Real := ‖limitValue testCoordinate‖ / 4
  let lowerBound : Real := ‖limitValue testCoordinate‖ / 2
  have quarterPos : 0 < quarter := by
    dsimp only [quarter]
    positivity
  have lowerBoundPos : 0 < lowerBound := by
    dsimp only [lowerBound]
    positivity
  obtain ⟨sigma, sigmaNonneg, sigmaLt, shellCostSmall⟩ :=
    exists_scaledFrequencyCubeShell_cost_lt limitRadius massCeiling
      (quarter ^ 2) limitRadiusPos (sq_pos_of_pos quarterPos)
  have shellEventually :=
    scaledWeightedFourierField_difference_eventually_lt
      level radius coefficient (weight sigma) point limitRadius sigma
      massCeiling (quarter ^ 2) sigmaNonneg sigmaLt levelPos levelTendsto
      ratioTendsto (weightOne sigma) (weightUnit sigma) massBound
      shellCostSmall
  have outerEventually : ∀ᶠ index in atTop,
      ((level index)⁻¹ ^ 2 : Real) •
          finiteRealComplexFourierField
            (integerWaveFrequencyCube (radius index))
            (coefficient index) (point index) ∈
        Metric.ball limitValue quarter :=
    outerTendsto.eventually (Metric.ball_mem_nhds _ quarterPos)
  refine ⟨testCoordinate, sigma, lowerBound, sigmaNonneg, sigmaLt,
    lowerBoundPos, ?_⟩
  filter_upwards [shellEventually, outerEventually] with
    index shellSqSmall outerClose
  let outerCoordinate :=
    (((level index)⁻¹ ^ 2 : Real) •
      finiteRealComplexFourierField
        (integerWaveFrequencyCube (radius index))
        (coefficient index) (point index)) testCoordinate
  let weightedCoordinate :=
    (((level index)⁻¹ ^ 2 : Real) •
      finiteRealComplexFourierField
        (integerWaveFrequencyCube (radius index))
        (fun wave => weight sigma index wave • coefficient index wave)
        (point index)) testCoordinate
  have shellNormSmall :
      ‖((level index)⁻¹ ^ 2 : Real) •
          (finiteRealComplexFourierField
              (integerWaveFrequencyCube (radius index))
              (coefficient index) (point index) -
            finiteRealComplexFourierField
              (integerWaveFrequencyCube (radius index))
              (fun wave => weight sigma index wave • coefficient index wave)
              (point index))‖ < quarter :=
    (sq_lt_sq₀ (norm_nonneg _) quarterPos.le).mp shellSqSmall
  have shellCoordinateSmall :
      ‖outerCoordinate - weightedCoordinate‖ < quarter := by
    have coordinateBound :=
      (PiLp.norm_apply_le
        (((level index)⁻¹ ^ 2 : Real) •
          (finiteRealComplexFourierField
              (integerWaveFrequencyCube (radius index))
              (coefficient index) (point index) -
            finiteRealComplexFourierField
              (integerWaveFrequencyCube (radius index))
              (fun wave => weight sigma index wave • coefficient index wave)
              (point index))) testCoordinate).trans_lt shellNormSmall
    simpa only [outerCoordinate, weightedCoordinate, WithLp.ofLp_smul,
      WithLp.ofLp_sub, Pi.smul_apply, Pi.sub_apply, smul_sub] using
      coordinateBound
  rw [Metric.mem_ball, dist_eq_norm] at outerClose
  have outerCoordinateClose :
      ‖outerCoordinate - limitValue testCoordinate‖ < quarter := by
    have coordinateBound :=
      (PiLp.norm_apply_le
        ((((level index)⁻¹ ^ 2 : Real) •
          finiteRealComplexFourierField
            (integerWaveFrequencyCube (radius index))
            (coefficient index) (point index)) - limitValue)
          testCoordinate).trans_lt outerClose
    simpa only [outerCoordinate, WithLp.ofLp_smul, WithLp.ofLp_sub,
      Pi.smul_apply, Pi.sub_apply] using coordinateBound
  have outerNormLe :
      ‖outerCoordinate‖ ≤
        ‖weightedCoordinate‖ + ‖outerCoordinate - weightedCoordinate‖ := by
    have := norm_le_norm_add_norm_sub weightedCoordinate outerCoordinate
    simpa only [norm_sub_rev] using this
  have limitNormLe :
      ‖limitValue testCoordinate‖ ≤
        ‖outerCoordinate‖ +
          ‖outerCoordinate - limitValue testCoordinate‖ :=
    norm_le_norm_add_norm_sub outerCoordinate (limitValue testCoordinate)
  change lowerBound ≤ ‖weightedCoordinate‖
  dsimp only [lowerBound, quarter] at shellCoordinateSmall outerCoordinateClose ⊢
  linarith



private abbrev ProjectedPairingVelocityField := PhysicalSpace → PhysicalSpace

private def rankOneStress
    (left right : ProjectedPairingVelocityField) : StressField :=
  fun x i j => left x i * right x j

private theorem rankOneStress_contDiff
    (left right : ProjectedPairingVelocityField) {n : ℕ∞}
    (leftContDiff : ContDiff ℝ n left)
    (rightContDiff : ContDiff ℝ n right) :
    ContDiff ℝ n (rankOneStress left right) := by
  rw [contDiff_pi]
  intro i
  rw [contDiff_pi]
  intro j
  exact ((contDiff_piLp_apply 2).comp leftContDiff).mul
    ((contDiff_piLp_apply 2).comp rightContDiff)

private theorem rankOneStress_latticePeriodic
    (left right : ProjectedPairingVelocityField)
    (leftPeriodic : LatticePeriodic left)
    (rightPeriodic : LatticePeriodic right) :
    LatticePeriodic (rankOneStress left right) := by
  intro shift x
  unfold rankOneStress
  rw [leftPeriodic shift x, rightPeriodic shift x]

private noncomputable def projectedPairingStressCoordinateReadout
    (i j : Coordinate) : Stress →L[ℝ] ℝ :=
  (ContinuousLinearMap.proj j) ∘L
    (ContinuousLinearMap.proj i)

private lemma projectedPairing_fderiv_velocity_coordinate_apply
    (u : ProjectedPairingVelocityField)
    (uDifferentiable : Differentiable ℝ u)
    (x : PhysicalSpace) (i j : Coordinate) :
    fderiv ℝ (fun y => u y i) x
        (EuclideanSpace.single j 1) =
      fderiv ℝ u x (EuclideanSpace.single j 1) i := by
  change
    fderiv ℝ ((EuclideanSpace.proj i) ∘ u) x
        (EuclideanSpace.single j 1) = _
  rw [fderiv_comp x
    (EuclideanSpace.proj i).differentiableAt
    (uDifferentiable x)]
  rw [ContinuousLinearMap.fderiv]
  rfl

private lemma projectedPairing_fderiv_stress_coordinate_apply
    (stress : StressField)
    (stressDifferentiable : Differentiable ℝ stress)
    (x : PhysicalSpace) (i j k : Coordinate) :
    fderiv ℝ (fun y => stress y i j) x
        (EuclideanSpace.single k 1) =
      fderiv ℝ stress x (EuclideanSpace.single k 1) i j := by
  change
    fderiv ℝ ((projectedPairingStressCoordinateReadout i j) ∘ stress) x
        (EuclideanSpace.single k 1) = _
  rw [fderiv_comp x
    (projectedPairingStressCoordinateReadout i j).differentiableAt
    (stressDifferentiable x)]
  rw [ContinuousLinearMap.fderiv]
  rfl

private lemma projectedPairing_fderiv_scalar_mul_apply
    (a b : PhysicalSpace → ℝ)
    (aDifferentiable : Differentiable ℝ a)
    (bDifferentiable : Differentiable ℝ b)
    (x : PhysicalSpace) (j : Coordinate) :
    fderiv ℝ (fun y => a y * b y) x
        (EuclideanSpace.single j 1) =
      a x * fderiv ℝ b x (EuclideanSpace.single j 1) +
        b x * fderiv ℝ a x (EuclideanSpace.single j 1) := by
  change
    fderiv ℝ (a * b) x
        (EuclideanSpace.single j 1) = _
  rw [fderiv_mul (aDifferentiable x) (bDifferentiable x)]
  simp only [smul_apply, smul_eq_mul, add_apply]

private theorem tensorDivergence_rankOneStress_product_rule
    (left right : ProjectedPairingVelocityField)
    (leftContDiff : ContDiff ℝ 1 left)
    (rightContDiff : ContDiff ℝ 1 right) :
    tensorDivergence (rankOneStress left right) =
      fun x =>
        fderiv ℝ left x (right x) +
          (velocityDivergence right x) • left x := by
  have leftDifferentiable : Differentiable ℝ left :=
    leftContDiff.differentiable (by norm_num)
  have rightDifferentiable : Differentiable ℝ right :=
    rightContDiff.differentiable (by norm_num)
  have stressDifferentiable :
      Differentiable ℝ (rankOneStress left right) :=
    (rankOneStress_contDiff left right leftContDiff rightContDiff)
      |>.differentiable (by norm_num)
  funext x
  ext i
  change
    (∑ j : Coordinate,
      fderiv ℝ (rankOneStress left right) x
        (EuclideanSpace.single j 1) i j) =
      fderiv ℝ left x (right x) i +
        (∑ j : Coordinate,
          fderiv ℝ right x
            (EuclideanSpace.single j 1) j) * left x i
  simp_rw [← projectedPairing_fderiv_stress_coordinate_apply
    (rankOneStress left right) stressDifferentiable x]
  change
    (∑ j : Coordinate,
      fderiv ℝ
          (fun y => left y i * right y j)
          x (EuclideanSpace.single j 1)) = _
  have derivativeEq :
      (∑ j : Coordinate,
        fderiv ℝ
            (fun y => left y i * right y j)
            x (EuclideanSpace.single j 1)) =
        ∑ j : Coordinate,
          (left x i *
              fderiv ℝ right x
                (EuclideanSpace.single j 1) j +
            right x j *
              fderiv ℝ left x
                (EuclideanSpace.single j 1) i) := by
    apply Finset.sum_congr rfl
    intro j _
    rw [projectedPairing_fderiv_scalar_mul_apply
      (fun y => left y i) (fun y => right y j)
      ((differentiable_piLp 2).mp leftDifferentiable i)
      ((differentiable_piLp 2).mp rightDifferentiable j) x j]
    rw [projectedPairing_fderiv_velocity_coordinate_apply right rightDifferentiable
        x j j,
      projectedPairing_fderiv_velocity_coordinate_apply left leftDifferentiable
        x i j]
  have directionalEq :
      fderiv ℝ left x (right x) i =
        ∑ j : Coordinate,
          right x j *
            fderiv ℝ left x
              (EuclideanSpace.single j 1) i := by
    rw [←
      (EuclideanSpace.basisFun Coordinate ℝ).sum_repr
        (right x), map_sum]
    simp only [map_smul,
      EuclideanSpace.basisFun_repr,
      EuclideanSpace.basisFun_apply,
      WithLp.ofLp_sum, Finset.sum_apply,
      WithLp.ofLp_smul, Pi.smul_apply,
      smul_eq_mul, PiLp.single_apply,
      mul_ite, mul_one, mul_zero,
      Fintype.sum_ite_eq]
  rw [derivativeEq, Finset.sum_add_distrib, directionalEq]
  rw [← Finset.mul_sum]
  ring

private theorem tensorDivergence_rankOneStress_of_divergence_eq_zero
    (left right : ProjectedPairingVelocityField)
    (leftContDiff : ContDiff ℝ 1 left)
    (rightContDiff : ContDiff ℝ 1 right)
    (rightDivergence : velocityDivergence right = 0) :
    tensorDivergence (rankOneStress left right) =
      fun x => fderiv ℝ left x (right x) := by
  rw [tensorDivergence_rankOneStress_product_rule left right
    leftContDiff rightContDiff, rightDivergence]
  simp

private theorem projectedPairing_velocityDot_continuous
    (left right : ProjectedPairingVelocityField)
    (leftContinuous : Continuous left)
    (rightContinuous : Continuous right) :
    Continuous (velocityDot left right) := by
  unfold velocityDot
  apply continuous_finsetSum
  intro coordinate _
  exact
    ((EuclideanSpace.proj coordinate).continuous.comp leftContinuous).mul
      ((EuclideanSpace.proj coordinate).continuous.comp rightContinuous)

private theorem projectedPairing_stressGradientContraction_continuous
    (stress : StressField)
    (test : ProjectedPairingVelocityField)
    (stressContDiff : ContDiff ℝ 1 stress)
    (testContDiff : ContDiff ℝ 1 test) :
    Continuous (stressGradientContraction stress test) := by
  have fluxContDiff : ContDiff ℝ 1 (stressEnergyFlux stress test) :=
    stressEnergyFlux_contDiff stress test stressContDiff testContDiff
  have divergenceContinuous : Continuous
      (velocityDivergence (stressEnergyFlux stress test)) :=
    velocityDivergence_continuous (stressEnergyFlux stress test) fluxContDiff
  have tensorDivergenceContinuous : Continuous (tensorDivergence stress) :=
    tensorDivergence_continuous stress stressContDiff
  have pairingContinuous : Continuous
      (velocityDot test (tensorDivergence stress)) :=
    projectedPairing_velocityDot_continuous test (tensorDivergence stress)
      testContDiff.continuous tensorDivergenceContinuous
  have productRule := velocityDot_tensorDivergence stress test
    (stressContDiff.differentiable (by norm_num))
    (testContDiff.differentiable (by norm_num))
  have contractionEq : stressGradientContraction stress test =
      velocityDivergence (stressEnergyFlux stress test) -
        velocityDot test (tensorDivergence stress) := by
    rw [productRule]
    abel
  rw [contractionEq]
  exact divergenceContinuous.sub pairingContinuous

private theorem physicalUnitCell_velocityDot_tensorDivergence_integral
    (stress : StressField)
    (test : ProjectedPairingVelocityField)
    (stressContDiff : ContDiff ℝ 1 stress)
    (testContDiff : ContDiff ℝ 1 test)
    (stressPeriodic : LatticePeriodic stress)
    (testPeriodic : LatticePeriodic test) :
    (∫ x in ThreeDimensionalPeriodicUnitCellDivergence.physicalUnitCell,
        velocityDot test (tensorDivergence stress) x) =
      -(∫ x in ThreeDimensionalPeriodicUnitCellDivergence.physicalUnitCell,
        stressGradientContraction stress test x) := by
  have fluxContDiff : ContDiff ℝ 1 (stressEnergyFlux stress test) :=
    stressEnergyFlux_contDiff stress test stressContDiff testContDiff
  have fluxPeriodic : LatticePeriodic (stressEnergyFlux stress test) :=
    stressEnergyFlux_latticePeriodic stress test stressPeriodic testPeriodic
  have divergenceIntegral :
      (∫ x in ThreeDimensionalPeriodicUnitCellDivergence.physicalUnitCell,
        velocityDivergence (stressEnergyFlux stress test) x) = 0 :=
    physicalUnitCell_velocityDivergence_integral_eq_zero
      (stressEnergyFlux stress test) fluxContDiff fluxPeriodic
  have divergenceIntegrable : IntegrableOn
      (velocityDivergence (stressEnergyFlux stress test))
      ThreeDimensionalPeriodicUnitCellDivergence.physicalUnitCell :=
    (velocityDivergence_continuous (stressEnergyFlux stress test)
      fluxContDiff).continuousOn.integrableOn_compact
        physicalUnitCell_isCompact
  have contractionContinuous : Continuous
      (stressGradientContraction stress test) := by
    exact projectedPairing_stressGradientContraction_continuous stress test
      stressContDiff testContDiff
  have contractionIntegrable : IntegrableOn
      (stressGradientContraction stress test)
      ThreeDimensionalPeriodicUnitCellDivergence.physicalUnitCell :=
    contractionContinuous.continuousOn.integrableOn_compact
      physicalUnitCell_isCompact
  rw [velocityDot_tensorDivergence stress test
    (stressContDiff.differentiable (by norm_num))
    (testContDiff.differentiable (by norm_num))]
  simp only [Pi.sub_apply]
  rw [integral_sub divergenceIntegrable contractionIntegrable,
    divergenceIntegral, zero_sub]

private abbrev physicalBasis : Module.Basis Coordinate ℝ PhysicalSpace :=
  (EuclideanSpace.basisFun Coordinate ℝ).toBasis

private abbrev physicalLattice : Submodule ℤ PhysicalSpace :=
  Submodule.span ℤ (Set.range physicalBasis)

private theorem physicalUnitCell_eq_parallelepiped :
    physicalUnitCell = parallelepiped physicalBasis := by
  ext x
  rw [mem_physicalUnitCell_iff]
  rw [parallelepiped_basis_eq]
  simp only [Set.mem_setOf_eq, Set.mem_Icc]
  constructor
  · intro h coordinate
    simpa [physicalBasis, EuclideanSpace.basisFun_repr] using h coordinate
  · intro h coordinate
    simpa [physicalBasis, EuclideanSpace.basisFun_repr] using h coordinate

private theorem physicalFundamentalDomain_ae_unitCell :
    ZSpan.fundamentalDomain physicalBasis =ᵐ[volume] physicalUnitCell := by
  rw [physicalUnitCell_eq_parallelepiped]
  exact ZSpan.fundamentalDomain_ae_parallelepiped physicalBasis volume

private theorem physicalLattice_exists_integerShift
    (shift : physicalLattice) :
    ∃ integerShift : IntegerShift,
      latticeShift integerShift = (shift : PhysicalSpace) := by
  classical
  have coordinateInteger (coordinate : Coordinate) :
      ∃ value : ℤ, (value : ℝ) = (shift : PhysicalSpace) coordinate := by
    obtain ⟨value, valueEq⟩ :=
      ((physicalBasis.mem_span_iff_repr_mem ℤ (shift : PhysicalSpace)).mp
        shift.property coordinate)
    refine ⟨value, ?_⟩
    simpa [physicalBasis, EuclideanSpace.basisFun_repr] using valueEq
  choose integerShift integerShift_eq using coordinateInteger
  refine ⟨integerShift, ?_⟩
  ext coordinate
  change (integerShift coordinate : ℝ) = (shift : PhysicalSpace) coordinate
  exact integerShift_eq coordinate

private def integerShiftToPhysicalLattice
    (integerShift : IntegerShift) : physicalLattice := by
  refine ⟨latticeShift integerShift, ?_⟩
  rw [physicalBasis.mem_span_iff_repr_mem ℤ]
  intro coordinate
  refine ⟨integerShift coordinate, ?_⟩
  change (integerShift coordinate : ℝ) =
    (latticeShift integerShift : PhysicalSpace) coordinate
  rfl

private theorem integerShiftToPhysicalLattice_injective :
    Function.Injective integerShiftToPhysicalLattice := by
  intro first second equal
  ext coordinate
  have coordinateEqual := congrArg
    (fun shift : physicalLattice =>
      (shift : PhysicalSpace) coordinate) equal
  simpa [integerShiftToPhysicalLattice, latticeShift] using coordinateEqual

private theorem integerShiftToPhysicalLattice_surjective :
    Function.Surjective integerShiftToPhysicalLattice := by
  intro shift
  obtain ⟨integerShift, integerShiftEq⟩ :=
    physicalLattice_exists_integerShift shift
  refine ⟨integerShift, ?_⟩
  apply Subtype.ext
  exact integerShiftEq

private def integerShiftEquivPhysicalLattice :
    IntegerShift ≃ physicalLattice :=
  Equiv.ofBijective integerShiftToPhysicalLattice
    ⟨integerShiftToPhysicalLattice_injective,
      integerShiftToPhysicalLattice_surjective⟩

private theorem lattice_periodic_vadd
    (f : PhysicalSpace → ℝ)
    (periodic : LatticePeriodic f)
    (shift : physicalLattice)
    (x : PhysicalSpace) :
    f (shift +ᵥ x) = f x := by
  obtain ⟨integerShift, shiftEq⟩ := physicalLattice_exists_integerShift shift
  change f ((shift : PhysicalSpace) + x) = f x
  rw [← shiftEq, add_comm]
  exact periodic integerShift x

private theorem physicalLattice_tsum_eq_integerShift_tsum
    {E : Type*} [AddCommMonoid E] [TopologicalSpace E]
    (f : physicalLattice → E) :
    (∑' shift : physicalLattice, f shift) =
      ∑' integerShift : IntegerShift,
        f (integerShiftToPhysicalLattice integerShift) := by
  exact (integerShiftEquivPhysicalLattice.tsum_eq f).symm

private theorem schwartz_affine_int_norm_summable
    (test : SchwartzMap ℝ ℂ)
    (a b : ℝ) (bNe : b ≠ 0) :
    Summable fun shift : ℤ => ‖test (a + b * (shift : ℝ))‖ := by
  have affineTendsto : Tendsto
      (fun shift : ℤ => a + b * (shift : ℝ)) cofinite (cocompact ℝ) :=
    (Homeomorph.addLeft a).isClosedEmbedding.tendsto_cocompact.comp
      ((Filter.tendsto_cocompact_mul_left₀ bNe).comp
        Int.tendsto_coe_cofinite)
  have decay := (test.isBigO_cocompact_rpow (-2)).comp_tendsto affineTendsto
  have shiftedPSeries : Summable fun shift : ℤ =>
      1 / |(shift : ℝ) + a / b| ^ (2 : ℝ) :=
    (Real.summable_one_div_int_add_rpow (a / b) 2).2 (by norm_num)
  have affinePSeries : Summable fun shift : ℤ =>
      |a + b * (shift : ℝ)| ^ (-2 : ℝ) := by
    have scaled := shiftedPSeries.mul_left (|b| ^ (-2 : ℝ))
    apply scaled.congr
    intro shift
    rw [show a + b * (shift : ℝ) =
        b * ((shift : ℝ) + a / b) by field_simp [bNe]; ring]
    rw [abs_mul, Real.mul_rpow (abs_nonneg b)
      (abs_nonneg ((shift : ℝ) + a / b))]
    rw [show |(shift : ℝ) + a / b| ^ (-2 : ℝ) =
        1 / |(shift : ℝ) + a / b| ^ (2 : ℝ) by
      rw [Real.rpow_neg (abs_nonneg _)]
      norm_num]
  exact summable_of_isBigO affinePSeries decay.norm_left

private def integerShiftEquivTriple :
    IntegerShift ≃ (ℤ × ℤ) × ℤ :=
  (Fin.succFunEquiv ℤ 2).trans
    (Equiv.prodCongr (finTwoArrowEquiv ℤ) (Equiv.refl ℤ))

private theorem tsum_integerShift_prod_eq_prod_tsum
    (term : Coordinate → ℤ → ℂ)
    (termNormSummable : ∀ coordinate,
      Summable fun shift => ‖term coordinate shift‖) :
    (∑' integerShift : IntegerShift,
      ∏ coordinate : Coordinate, term coordinate (integerShift coordinate)) =
      ∏ coordinate : Coordinate, ∑' shift : ℤ, term coordinate shift := by
  have tripleTsum :
      (∑' shifts : (ℤ × ℤ) × ℤ,
        (term 0 shifts.1.1 * term 1 shifts.1.2) * term 2 shifts.2) =
        ((∑' first : ℤ, term 0 first) *
          ∑' second : ℤ, term 1 second) *
            ∑' third : ℤ, term 2 third := by
    symm
    rw [tsum_mul_tsum_of_summable_norm
      (termNormSummable 0) (termNormSummable 1)]
    rw [tsum_mul_tsum_of_summable_norm
      ((termNormSummable 0).mul_norm (termNormSummable 1))
      (termNormSummable 2)]
  rw [Fin.prod_univ_three]
  rw [← tripleTsum]
  rw [← integerShiftEquivTriple.tsum_eq]
  apply tsum_congr
  intro shift
  simp [integerShiftEquivTriple, Fin.prod_univ_three]

private def centralTensorScalar
    (spatialTest : Coordinate → SchwartzMap ℝ ℂ)
    (scale : ℝ)
    (center x : PhysicalSpace) : ℂ :=
  ∏ coordinate : Coordinate,
    spatialTest coordinate
      (scale⁻¹ * (x coordinate - center coordinate))

private theorem centralTensorScalar_integerShift_norm_summable
    (spatialTest : Coordinate → SchwartzMap ℝ ℂ)
    (scale : ℝ) (scaleNe : scale ≠ 0)
    (center x : PhysicalSpace) :
    Summable fun integerShift : IntegerShift =>
      ‖centralTensorScalar spatialTest scale center
        (latticeShift integerShift + x)‖ := by
  let term : Coordinate → ℤ → ℂ := fun coordinate shift =>
    spatialTest coordinate
      (scale⁻¹ * (x coordinate - center coordinate + shift))
  have termNormSummable (coordinate : Coordinate) :
      Summable fun shift : ℤ => ‖term coordinate shift‖ := by
    have affine := schwartz_affine_int_norm_summable
      (spatialTest coordinate)
      (scale⁻¹ * (x coordinate - center coordinate)) scale⁻¹
      (inv_ne_zero scaleNe)
    apply affine.congr
    intro shift
    congr 2
    dsimp only [term]
    ring
  have productNormSummable : Summable fun integerShift : IntegerShift =>
      ∏ coordinate : Coordinate,
        ‖term coordinate (integerShift coordinate)‖ := by
    have triple : Summable fun shifts : (ℤ × ℤ) × ℤ =>
        (‖term 0 shifts.1.1‖ * ‖term 1 shifts.1.2‖) *
          ‖term 2 shifts.2‖ :=
      ((termNormSummable 0).mul_of_nonneg (termNormSummable 1)
        (fun _ => norm_nonneg _) (fun _ => norm_nonneg _)).mul_of_nonneg
          (termNormSummable 2) (fun _ => mul_nonneg (norm_nonneg _)
            (norm_nonneg _)) (fun _ => norm_nonneg _)
    have transported := integerShiftEquivTriple.summable_iff.mpr triple
    apply transported.congr
    intro integerShift
    simp [integerShiftEquivTriple, Fin.prod_univ_three]
  apply productNormSummable.congr
  intro integerShift
  have centralEq :
      centralTensorScalar spatialTest scale center
          (latticeShift integerShift + x) =
        ∏ coordinate : Coordinate,
          term coordinate (integerShift coordinate) := by
    unfold centralTensorScalar
    apply Finset.prod_congr rfl
    intro coordinate _coordinateMem
    congr 2
    change (integerShift coordinate : ℝ) + x coordinate - center coordinate =
      x coordinate - center coordinate + (integerShift coordinate : ℝ)
    ring
  rw [centralEq]
  exact (Complex.norm_prod Finset.univ
    (fun coordinate : Coordinate =>
      term coordinate (integerShift coordinate))).symm

private theorem centralTensorScalar_latticePeriodization_eq
    (spatialTest : Coordinate → SchwartzMap ℝ ℂ)
    (scale : ℝ) (scaleNe : scale ≠ 0)
    (center x : PhysicalSpace) :
    (∏ coordinate : Coordinate,
      ∑' shift : ℤ,
        spatialTest coordinate
          (scale⁻¹ * (x coordinate - center coordinate + shift))) =
      ∑' lattice : physicalLattice,
        centralTensorScalar spatialTest scale center (lattice +ᵥ x) := by
  let term : Coordinate → ℤ → ℂ := fun coordinate shift =>
    spatialTest coordinate
      (scale⁻¹ * (x coordinate - center coordinate + shift))
  have termNormSummable (coordinate : Coordinate) :
      Summable fun shift : ℤ => ‖term coordinate shift‖ := by
    have affine := schwartz_affine_int_norm_summable
      (spatialTest coordinate)
      (scale⁻¹ * (x coordinate - center coordinate)) scale⁻¹
      (inv_ne_zero scaleNe)
    apply affine.congr
    intro shift
    congr 2
    dsimp only [term]
    ring
  calc
    (∏ coordinate : Coordinate,
        ∑' shift : ℤ, spatialTest coordinate
          (scale⁻¹ * (x coordinate - center coordinate + shift))) =
        ∑' integerShift : IntegerShift,
          ∏ coordinate : Coordinate,
            term coordinate (integerShift coordinate) := by
      simpa only [term] using
        (tsum_integerShift_prod_eq_prod_tsum term termNormSummable).symm
    _ = ∑' integerShift : IntegerShift,
          centralTensorScalar spatialTest scale center
            (integerShiftToPhysicalLattice integerShift +ᵥ x) := by
      apply tsum_congr
      intro integerShift
      unfold centralTensorScalar
      apply Finset.prod_congr rfl
      intro coordinate _coordinateMem
      apply congrArg (spatialTest coordinate)
      dsimp only [term, integerShiftToPhysicalLattice, latticeShift]
      change scale⁻¹ *
          (x coordinate - center coordinate + (integerShift coordinate : ℝ)) =
        scale⁻¹ *
          ((integerShift coordinate : ℝ) + x coordinate - center coordinate)
      ring
    _ = ∑' lattice : physicalLattice,
          centralTensorScalar spatialTest scale center (lattice +ᵥ x) := by
      symm
      exact physicalLattice_tsum_eq_integerShift_tsum
        (fun lattice =>
          centralTensorScalar spatialTest scale center (lattice +ᵥ x))

/-- The compact recentered tensor-product test before lattice periodization. -/
def centralTensorVectorTest
    (spatialTest : Coordinate → SchwartzMap ℝ ℂ)
    (scale : ℝ)
    (center : PhysicalSpace)
    (scalar : ℂ)
    (testCoordinate : Coordinate) : PhysicalSpace → PhysicalSpace := fun x =>
  EuclideanSpace.single testCoordinate
    (scalar * centralTensorScalar spatialTest scale center x).re

private theorem centralTensorVectorTest_latticePeriodization_eq
    (spatialTest : Coordinate → SchwartzMap ℝ ℂ)
    (scale : ℝ) (scaleNe : scale ≠ 0)
    (center : PhysicalSpace)
    (scalar : ℂ)
    (testCoordinate : Coordinate)
    (x : PhysicalSpace) :
    (∑' lattice : physicalLattice,
      centralTensorVectorTest spatialTest scale center scalar testCoordinate
        (lattice +ᵥ x)) =
      EuclideanSpace.single testCoordinate
        (scalar *
          ∏ coordinate : Coordinate,
            ∑' shift : ℤ,
              spatialTest coordinate
                (scale⁻¹ *
                  (x coordinate - center coordinate + shift))).re := by
  have scalarSummable : Summable fun lattice : physicalLattice =>
      scalar * centralTensorScalar spatialTest scale center (lattice +ᵥ x) := by
    apply Summable.mul_left
    have integerSummable : Summable fun integerShift : IntegerShift =>
        centralTensorScalar spatialTest scale center
          (latticeShift integerShift + x) :=
      (centralTensorScalar_integerShift_norm_summable
        spatialTest scale scaleNe center x).of_norm
    have transported :=
      integerShiftEquivPhysicalLattice.symm.summable_iff.mpr
        integerSummable
    apply transported.congr
    intro lattice
    have underlying :
        latticeShift (integerShiftEquivPhysicalLattice.symm lattice) =
          (lattice : PhysicalSpace) := by
      exact congrArg Subtype.val
        (integerShiftEquivPhysicalLattice.apply_symm_apply lattice)
    change centralTensorScalar spatialTest scale center
        (latticeShift (integerShiftEquivPhysicalLattice.symm lattice) + x) =
      centralTensorScalar spatialTest scale center ((lattice : PhysicalSpace) + x)
    rw [underlying]
  have vectorSummable : Summable fun lattice : physicalLattice =>
      centralTensorVectorTest spatialTest scale center scalar testCoordinate
        (lattice +ᵥ x) := by
    apply Summable.of_norm
    apply Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
      (fun lattice => ?_) scalarSummable.norm
    rw [centralTensorVectorTest, PiLp.norm_single]
    exact Complex.abs_re_le_norm
      (scalar * centralTensorScalar spatialTest scale center (lattice +ᵥ x))
  ext outputCoordinate
  change (EuclideanSpace.proj outputCoordinate)
      (∑' lattice : physicalLattice,
        centralTensorVectorTest spatialTest scale center scalar testCoordinate
          (lattice +ᵥ x)) =
    (EuclideanSpace.proj outputCoordinate)
      (EuclideanSpace.single testCoordinate
        (scalar *
          ∏ coordinate : Coordinate,
            ∑' shift : ℤ,
              spatialTest coordinate
                (scale⁻¹ *
                  (x coordinate - center coordinate + shift))).re)
  rw [(EuclideanSpace.proj outputCoordinate).map_tsum vectorSummable]
  by_cases outputEq : outputCoordinate = testCoordinate
  · subst outputCoordinate
    simp only [EuclideanSpace.coe_proj, centralTensorVectorTest,
      PiLp.single_apply, if_pos]
    rw [← Complex.re_tsum scalarSummable]
    rw [tsum_mul_left]
    rw [← centralTensorScalar_latticePeriodization_eq
      spatialTest scale scaleNe center x]
  · simp [EuclideanSpace.coe_proj, centralTensorVectorTest,
      PiLp.single_apply, outputEq]

private theorem centralTensorVectorTest_lattice_summable
    (spatialTest : Coordinate → SchwartzMap ℝ ℂ)
    (scale : ℝ) (scaleNe : scale ≠ 0)
    (center : PhysicalSpace)
    (scalar : ℂ)
    (testCoordinate : Coordinate)
    (x : PhysicalSpace) :
    Summable fun lattice : physicalLattice =>
      centralTensorVectorTest spatialTest scale center scalar testCoordinate
        (lattice +ᵥ x) := by
  have integerSummable : Summable fun integerShift : IntegerShift =>
      centralTensorScalar spatialTest scale center
        (latticeShift integerShift + x) :=
    (centralTensorScalar_integerShift_norm_summable
      spatialTest scale scaleNe center x).of_norm
  have transported :=
    integerShiftEquivPhysicalLattice.symm.summable_iff.mpr integerSummable
  have scalarSummable : Summable fun lattice : physicalLattice =>
      scalar * centralTensorScalar spatialTest scale center (lattice +ᵥ x) := by
    apply Summable.mul_left
    apply transported.congr
    intro lattice
    have underlying :
        latticeShift (integerShiftEquivPhysicalLattice.symm lattice) =
          (lattice : PhysicalSpace) := by
      exact congrArg Subtype.val
        (integerShiftEquivPhysicalLattice.apply_symm_apply lattice)
    change centralTensorScalar spatialTest scale center
        (latticeShift (integerShiftEquivPhysicalLattice.symm lattice) + x) =
      centralTensorScalar spatialTest scale center ((lattice : PhysicalSpace) + x)
    rw [underlying]
  apply Summable.of_norm
  apply Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
    (fun lattice => ?_) scalarSummable.norm
  rw [centralTensorVectorTest, PiLp.norm_single]
  exact Complex.abs_re_le_norm
    (scalar * centralTensorScalar spatialTest scale center (lattice +ᵥ x))

/-- The lattice periodization of a compact recentered tensor-product test. -/
def periodizedCentralTensorVectorTest
    (spatialTest : Coordinate → SchwartzMap ℝ ℂ)
    (scale : ℝ)
    (center : PhysicalSpace)
    (scalar : ℂ)
    (testCoordinate : Coordinate) : PhysicalSpace → PhysicalSpace := fun x =>
  EuclideanSpace.single testCoordinate
    (scalar *
      ∏ coordinate : Coordinate,
        ∑' shift : ℤ,
          spatialTest coordinate
            (scale⁻¹ * (x coordinate - center coordinate + shift))).re

private theorem periodizedCentralTensorVectorTest_eq_lattice_tsum
    (spatialTest : Coordinate → SchwartzMap ℝ ℂ)
    (scale : ℝ) (scaleNe : scale ≠ 0)
    (center : PhysicalSpace)
    (scalar : ℂ)
    (testCoordinate : Coordinate)
    (x : PhysicalSpace) :
    periodizedCentralTensorVectorTest spatialTest scale center scalar
        testCoordinate x =
      ∑' lattice : physicalLattice,
        centralTensorVectorTest spatialTest scale center scalar testCoordinate
          (lattice +ᵥ x) := by
  exact (centralTensorVectorTest_latticePeriodization_eq
    spatialTest scale scaleNe center scalar testCoordinate x).symm

private theorem velocityDot_periodizedCentralTensorVectorTest_eq_tsum
    (spatialTest : Coordinate → SchwartzMap ℝ ℂ)
    (scale : ℝ) (scaleNe : scale ≠ 0)
    (center : PhysicalSpace)
    (scalar : ℂ)
    (testCoordinate : Coordinate)
    (field : PhysicalSpace → PhysicalSpace)
    (fieldPeriodic : LatticePeriodic field)
    (x : PhysicalSpace) :
    velocityDot
        (periodizedCentralTensorVectorTest spatialTest scale center scalar
          testCoordinate) field x =
      ∑' lattice : physicalLattice,
        velocityDot
          (centralTensorVectorTest spatialTest scale center scalar
            testCoordinate) field (lattice +ᵥ x) := by
  have vectorSummable := centralTensorVectorTest_lattice_summable
    spatialTest scale scaleNe center scalar testCoordinate x
  have coordinateSummable (coordinate : Coordinate) :
      Summable fun lattice : physicalLattice =>
        centralTensorVectorTest spatialTest scale center scalar testCoordinate
            (lattice +ᵥ x) coordinate * field x coordinate := by
    have projectedSummable : Summable fun lattice : physicalLattice =>
        centralTensorVectorTest spatialTest scale center scalar testCoordinate
          (lattice +ᵥ x) coordinate := by
      apply (vectorSummable.map (EuclideanSpace.proj coordinate)
        (EuclideanSpace.proj coordinate).continuous).congr
      intro lattice
      rfl
    exact projectedSummable.mul_right (field x coordinate)
  have coordinateTsum (coordinate : Coordinate) :
      (∑' lattice : physicalLattice,
          centralTensorVectorTest spatialTest scale center scalar testCoordinate
            (lattice +ᵥ x)) coordinate =
        ∑' lattice : physicalLattice,
          centralTensorVectorTest spatialTest scale center scalar testCoordinate
            (lattice +ᵥ x) coordinate := by
    exact (EuclideanSpace.proj coordinate).map_tsum vectorSummable
  unfold velocityDot
  rw [periodizedCentralTensorVectorTest_eq_lattice_tsum
    spatialTest scale scaleNe center scalar testCoordinate x]
  simp_rw [coordinateTsum]
  calc
    (∑ coordinate : Coordinate,
        (∑' lattice : physicalLattice,
          centralTensorVectorTest spatialTest scale center scalar
            testCoordinate (lattice +ᵥ x) coordinate) * field x coordinate) =
        ∑ coordinate : Coordinate,
          ∑' lattice : physicalLattice,
            centralTensorVectorTest spatialTest scale center scalar
                testCoordinate (lattice +ᵥ x) coordinate *
              field x coordinate := by
      apply Finset.sum_congr rfl
      intro coordinate _coordinateMem
      rw [tsum_mul_right]
    _ = ∑' lattice : physicalLattice,
          ∑ coordinate : Coordinate,
            centralTensorVectorTest spatialTest scale center scalar
                testCoordinate (lattice +ᵥ x) coordinate *
              field x coordinate := by
      rw [← Summable.tsum_finsetSum
        (fun coordinate _coordinateMem => coordinateSummable coordinate)]
    _ = ∑' lattice : physicalLattice,
          ∑ coordinate : Coordinate,
            centralTensorVectorTest spatialTest scale center scalar
                testCoordinate (lattice +ᵥ x) coordinate *
              field (lattice +ᵥ x) coordinate := by
      apply tsum_congr
      intro lattice
      have fieldEq : field (lattice +ᵥ x) = field x := by
        obtain ⟨integerShift, shiftEq⟩ :=
          physicalLattice_exists_integerShift lattice
        change field ((lattice : PhysicalSpace) + x) = field x
        rw [← shiftEq, add_comm]
        exact fieldPeriodic integerShift x
      apply Finset.sum_congr rfl
      intro coordinate _coordinateMem
      rw [fieldEq]

private theorem exists_coordinate_abs_gt_of_three_mul_lt_norm
    (point : PhysicalSpace) (supportRadius : ℝ)
    (supportRadiusNonneg : 0 ≤ supportRadius)
    (outside : 3 * supportRadius < ‖point‖) :
    ∃ coordinate : Coordinate,
      supportRadius < |point coordinate| := by
  by_contra noCoordinate
  push_neg at noCoordinate
  have normSq := PiLp.norm_sq_eq_of_L2
    (fun _coordinate : Coordinate => ℝ) point
  rw [Fin.sum_univ_three] at normSq
  simp only [Real.norm_eq_abs] at normSq
  have coordinateZero := noCoordinate (0 : Coordinate)
  have coordinateOne := noCoordinate (1 : Coordinate)
  have coordinateTwo := noCoordinate (2 : Coordinate)
  have zeroAbsNonneg : 0 ≤ |point (0 : Coordinate)| := abs_nonneg _
  have oneAbsNonneg : 0 ≤ |point (1 : Coordinate)| := abs_nonneg _
  have twoAbsNonneg : 0 ≤ |point (2 : Coordinate)| := abs_nonneg _
  have pointNormNonneg : 0 ≤ ‖point‖ := norm_nonneg _
  nlinarith

private theorem centralTensorScalar_eq_zero_of_norm_gt
    (spatialTest : Coordinate → SchwartzMap ℝ ℂ)
    (scale : ℝ) (center x : PhysicalSpace)
    (supportRadius : ℝ)
    (supportRadiusNonneg : 0 ≤ supportRadius)
    (support : ∀ coordinate y,
      supportRadius < |y| → spatialTest coordinate y = 0)
    (outside : 3 * supportRadius <
      ‖scale⁻¹ • (x - center)‖) :
    centralTensorScalar spatialTest scale center x = 0 := by
  obtain ⟨coordinate, coordinateOutside⟩ :=
    exists_coordinate_abs_gt_of_three_mul_lt_norm
      (scale⁻¹ • (x - center)) supportRadius supportRadiusNonneg outside
  unfold centralTensorScalar
  apply Finset.prod_eq_zero (Finset.mem_univ coordinate)
  apply support coordinate
  simpa only [PiLp.smul_apply, PiLp.sub_apply, smul_eq_mul] using
    coordinateOutside

private theorem centralTensorVectorTest_hasCompactSupport
    (spatialTest : Coordinate → SchwartzMap ℝ ℂ)
    (scale : ℝ) (scalePos : 0 < scale)
    (center : PhysicalSpace)
    (scalar : ℂ)
    (testCoordinate : Coordinate)
    (supportRadius : ℝ)
    (supportRadiusNonneg : 0 ≤ supportRadius)
    (support : ∀ coordinate y,
      supportRadius < |y| → spatialTest coordinate y = 0) :
    HasCompactSupport
      (centralTensorVectorTest spatialTest scale center scalar testCoordinate) := by
  let radius : ℝ := scale * (3 * supportRadius)
  apply HasCompactSupport.intro (isCompact_closedBall center radius)
  intro x xOutside
  have distanceOutside : radius < dist x center := by
    exact lt_of_not_ge (by
      simpa only [Metric.mem_closedBall] using xOutside)
  have scaledNorm :
      ‖scale⁻¹ • (x - center)‖ = scale⁻¹ * dist x center := by
    rw [norm_smul, Real.norm_eq_abs,
      abs_of_pos (inv_pos.mpr scalePos), dist_eq_norm]
  have normalizedOutside :
      3 * supportRadius < ‖scale⁻¹ • (x - center)‖ := by
    rw [scaledNorm]
    dsimp only [radius] at distanceOutside
    have divided : 3 * supportRadius < dist x center / scale :=
      (lt_div_iff₀ scalePos).2 (by
        simpa [mul_comm, mul_left_comm, mul_assoc] using distanceOutside)
    simpa [div_eq_inv_mul] using divided
  unfold centralTensorVectorTest
  rw [centralTensorScalar_eq_zero_of_norm_gt spatialTest scale center x
    supportRadius supportRadiusNonneg support normalizedOutside]
  simp

private theorem centralTensorVectorTest_contDiff
    (spatialTest : Coordinate → SchwartzMap ℝ ℂ)
    (scale : ℝ)
    (center : PhysicalSpace)
    (scalar : ℂ)
    (testCoordinate : Coordinate) :
    ContDiff ℝ 1
      (centralTensorVectorTest spatialTest scale center scalar testCoordinate) := by
  rw [contDiff_piLp 2]
  intro outputCoordinate
  by_cases outputEq : outputCoordinate = testCoordinate
  · subst outputCoordinate
    simp only [centralTensorVectorTest, PiLp.single_apply, if_pos]
    have complexContDiff : ContDiff ℝ 1 (fun x : PhysicalSpace =>
        scalar * centralTensorScalar spatialTest scale center x) := by
      have tensorSmooth : ContDiff ℝ 1 (fun point : PhysicalSpace =>
          ∏ coordinate : Coordinate,
            spatialTest coordinate (point coordinate)) := by
        apply contDiff_prod
        intro coordinate _coordinateMem
        exact ((spatialTest coordinate).smooth (1 : ℕ∞)).comp
          (contDiff_piLp_apply 2)
      have affineSmooth : ContDiff ℝ 1 (fun x : PhysicalSpace =>
          scale⁻¹ • (x - center)) := by fun_prop
      have scalarSmooth : ContDiff ℝ 1
          (fun _x : PhysicalSpace => scalar) := contDiff_const
      unfold centralTensorScalar
      convert scalarSmooth.smul (tensorSmooth.comp affineSmooth) using 1
      funext x
      rfl
    exact Complex.reCLM.contDiff.comp complexContDiff
  · simp only [centralTensorVectorTest, PiLp.single_apply,
      if_neg outputEq]
    exact contDiff_const

private theorem vorticityNonlinearity_latticePeriodic
    (u : PhysicalSpace → PhysicalSpace)
    (uPeriodic : LatticePeriodic u) :
    LatticePeriodic (-vorticityAdvection u + vortexStretching u) := by
  have omegaPeriodic : LatticePeriodic (vorticityField u) :=
    vorticityField_latticePeriodic u uPeriodic
  have uDerivativePeriodic : LatticePeriodic (fderiv ℝ u) :=
    fderiv_latticePeriodic u uPeriodic
  have omegaDerivativePeriodic :
      LatticePeriodic (fderiv ℝ (vorticityField u)) :=
    fderiv_latticePeriodic (vorticityField u) omegaPeriodic
  intro shift x
  unfold vorticityAdvection vortexStretching
  change
    -(fderiv ℝ (vorticityField u) (x + latticeShift shift))
          (u (x + latticeShift shift)) +
        (fderiv ℝ u (x + latticeShift shift))
          (vorticityField u (x + latticeShift shift)) =
      -(fderiv ℝ (vorticityField u) x) (u x) +
        (fderiv ℝ u x) (vorticityField u x)
  rw [uPeriodic shift x, omegaPeriodic shift x,
    uDerivativePeriodic shift x, omegaDerivativePeriodic shift x]

private theorem physicalUnitCell_integral_latticePeriodization
    (density : PhysicalSpace → ℝ)
    (densityIntegrable : Integrable density) :
    (∫ x in physicalUnitCell,
        ∑' shift : physicalLattice, density (shift +ᵥ x)) =
      ∫ x, density x := by
  letI : VAddInvariantMeasure physicalLattice PhysicalSpace volume :=
    ⟨fun shift set _setMeasurable => measure_preimage_add volume
      (shift : PhysicalSpace) set⟩
  let fundamental := ZSpan.fundamentalDomain physicalBasis
  have fundamentalDomain : IsAddFundamentalDomain physicalLattice
      fundamental volume :=
    ZSpan.isAddFundamentalDomain physicalBasis volume
  have restrictEq :
      volume.restrict physicalUnitCell = volume.restrict fundamental := by
    exact Measure.restrict_congr_set
      physicalFundamentalDomain_ae_unitCell.symm
  have shiftedMeasurable (shift : physicalLattice) :
      AEStronglyMeasurable (fun x : PhysicalSpace => density (shift +ᵥ x))
        (volume.restrict fundamental) := by
    have shiftedIntegrable : Integrable
        (fun x : PhysicalSpace => density ((shift : PhysicalSpace) + x)) := by
      exact (measurePreserving_add_left volume (shift : PhysicalSpace))
        |>.integrable_comp_of_integrable densityIntegrable
    exact shiftedIntegrable.aestronglyMeasurable.mono_measure
      Measure.restrict_le_self
  have normTsumNeTop :
      (∑' shift : physicalLattice,
        ∫⁻ x : PhysicalSpace in fundamental,
          ‖density (shift +ᵥ x)‖ₑ) ≠ ⊤ := by
    rw [← fundamentalDomain.lintegral_eq_tsum''
      (fun x : PhysicalSpace => ‖density x‖ₑ)]
    exact densityIntegrable.hasFiniteIntegral.ne
  calc
    (∫ x in physicalUnitCell,
        ∑' shift : physicalLattice, density (shift +ᵥ x)) =
        ∫ x : PhysicalSpace in fundamental,
          ∑' shift : physicalLattice, density (shift +ᵥ x) := by
      change (∫ x : PhysicalSpace,
          ∑' shift : physicalLattice, density (shift +ᵥ x)
            ∂volume.restrict physicalUnitCell) = _
      rw [restrictEq]
    _ = ∑' shift : physicalLattice,
        ∫ x : PhysicalSpace in fundamental, density (shift +ᵥ x) := by
      exact integral_tsum shiftedMeasurable normTsumNeTop
    _ = ∫ x : PhysicalSpace, density x :=
      (fundamentalDomain.integral_eq_tsum'' density densityIntegrable).symm



private theorem wholeSpace_integral_velocityDivergence_eq_zero
    (flux : PhysicalSpace → PhysicalSpace)
    (fluxContDiff : ContDiff ℝ 1 flux)
    (fluxCompact : HasCompactSupport flux) :
    (∫ x : PhysicalSpace, velocityDivergence flux x) = 0 := by
  have fluxDifferentiable : Differentiable ℝ flux :=
    fluxContDiff.differentiable (by norm_num)
  have coordinateCompact (coordinate : Coordinate) :
      HasCompactSupport (fun x : PhysicalSpace => flux x coordinate) := by
    rw [hasCompactSupport_iff_eventuallyEq] at fluxCompact ⊢
    filter_upwards [fluxCompact] with x fluxZero
    simp [fluxZero]
  have coordinateContDiff (coordinate : Coordinate) :
      ContDiff ℝ 1 (fun x : PhysicalSpace => flux x coordinate) :=
    (contDiff_piLp_apply 2).comp fluxContDiff
  have coordinateDerivativeIntegrable (coordinate : Coordinate) :
      Integrable (fun x : PhysicalSpace =>
        fderiv ℝ (fun y : PhysicalSpace => flux y coordinate) x
          (EuclideanSpace.single coordinate 1)) := by
    apply Continuous.integrable_of_hasCompactSupport
    · exact (coordinateContDiff coordinate).continuous_fderiv
        (by norm_num) |>.clm_apply continuous_const
    · exact (coordinateCompact coordinate).fderiv_apply (𝕜 := ℝ)
        (EuclideanSpace.single coordinate 1)
  have coordinateIntegralZero (coordinate : Coordinate) :
      (∫ x : PhysicalSpace,
        fderiv ℝ (fun y : PhysicalSpace => flux y coordinate) x
          (EuclideanSpace.single coordinate 1)) = 0 := by
    let g : PhysicalSpace → ℝ := fun x => flux x coordinate
    have gCompact : HasCompactSupport g := coordinateCompact coordinate
    have gContDiff : ContDiff ℝ 1 g := coordinateContDiff coordinate
    have gIntegrable : Integrable g :=
      gContDiff.continuous.integrable_of_hasCompactSupport gCompact
    have derivativeIntegrable : Integrable (fun x : PhysicalSpace =>
        fderiv ℝ g x (EuclideanSpace.single coordinate 1)) := by
      simpa only [g] using coordinateDerivativeIntegrable coordinate
    have integrationByParts :=
      integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
        (μ := volume)
        (f := fun _x : PhysicalSpace => (1 : ℝ))
        (g := g)
        (v := EuclideanSpace.single coordinate 1)
        (by simpa using (integrable_zero : Integrable
          (fun _x : PhysicalSpace => (0 : ℝ))))
        (by simpa using derivativeIntegrable)
        (by simpa using gIntegrable)
        (fun _x _hx => differentiableAt_const (c := (1 : ℝ)))
        (fun x _hx => (gContDiff.differentiable (by norm_num) x))
    simpa using integrationByParts
  unfold velocityDivergence velocityDivergenceReadout
    velocityDivergenceReadoutLinear
  change (∫ x : PhysicalSpace,
    ∑ coordinate : Coordinate,
      fderiv ℝ flux x (EuclideanSpace.single coordinate 1) coordinate) = 0
  rw [integral_finsetSum]
  · simp_rw [← projectedPairing_fderiv_velocity_coordinate_apply
      flux fluxDifferentiable]
    simp_rw [coordinateIntegralZero]
    simp
  · intro coordinate _coordinateMem
    simpa only [← projectedPairing_fderiv_velocity_coordinate_apply
      flux fluxDifferentiable] using
      coordinateDerivativeIntegrable coordinate

private theorem stressEnergyFlux_hasCompactSupport_right
    (stress : StressField)
    (test : PhysicalSpace → PhysicalSpace)
    (testCompact : HasCompactSupport test) :
    HasCompactSupport (stressEnergyFlux stress test) := by
  rw [hasCompactSupport_iff_eventuallyEq] at testCompact ⊢
  filter_upwards [testCompact] with x testZero
  unfold stressEnergyFlux
  ext coordinate
  simp [testZero]

private theorem velocityDot_hasCompactSupport_left
    (test field : PhysicalSpace → PhysicalSpace)
    (testCompact : HasCompactSupport test) :
    HasCompactSupport (velocityDot test field) := by
  rw [hasCompactSupport_iff_eventuallyEq] at testCompact ⊢
  filter_upwards [testCompact] with x testZero
  unfold velocityDot
  simp [testZero]

private theorem stressGradientContraction_hasCompactSupport_right
    (stress : StressField)
    (test : PhysicalSpace → PhysicalSpace)
    (testCompact : HasCompactSupport test) :
    HasCompactSupport (stressGradientContraction stress test) := by
  have derivativeCompact : HasCompactSupport (fderiv ℝ test) :=
    testCompact.fderiv (𝕜 := ℝ)
  rw [hasCompactSupport_iff_eventuallyEq] at derivativeCompact ⊢
  filter_upwards [derivativeCompact] with x derivativeZero
  unfold stressGradientContraction
  simp [derivativeZero]

private theorem velocityDivergence_integrable_of_compactSupport
    (flux : PhysicalSpace → PhysicalSpace)
    (fluxContDiff : ContDiff ℝ 1 flux)
    (fluxCompact : HasCompactSupport flux) :
    Integrable (velocityDivergence flux) := by
  have fluxDerivativeCompact : HasCompactSupport (fderiv ℝ flux) :=
    fluxCompact.fderiv (𝕜 := ℝ)
  have divergenceCompact : HasCompactSupport (velocityDivergence flux) := by
    rw [hasCompactSupport_iff_eventuallyEq] at fluxDerivativeCompact ⊢
    filter_upwards [fluxDerivativeCompact] with x derivativeZero
    unfold velocityDivergence
    simp [derivativeZero]
  exact (velocityDivergence_continuous flux fluxContDiff)
    |>.integrable_of_hasCompactSupport divergenceCompact

private theorem wholeSpace_velocityDot_tensorDivergence_integral
    (stress : StressField)
    (test : PhysicalSpace → PhysicalSpace)
    (stressContDiff : ContDiff ℝ 1 stress)
    (testContDiff : ContDiff ℝ 1 test)
    (testCompact : HasCompactSupport test) :
    (∫ x : PhysicalSpace,
        velocityDot test (tensorDivergence stress) x) =
      -(∫ x : PhysicalSpace,
        stressGradientContraction stress test x) := by
  have fluxContDiff : ContDiff ℝ 1 (stressEnergyFlux stress test) :=
    stressEnergyFlux_contDiff stress test stressContDiff testContDiff
  have fluxCompact : HasCompactSupport (stressEnergyFlux stress test) :=
    stressEnergyFlux_hasCompactSupport_right stress test testCompact
  have divergenceIntegral :
      (∫ x : PhysicalSpace,
        velocityDivergence (stressEnergyFlux stress test) x) = 0 :=
    wholeSpace_integral_velocityDivergence_eq_zero
      (stressEnergyFlux stress test) fluxContDiff fluxCompact
  have divergenceIntegrable : Integrable
      (velocityDivergence (stressEnergyFlux stress test)) :=
    velocityDivergence_integrable_of_compactSupport
      (stressEnergyFlux stress test) fluxContDiff fluxCompact
  have tensorDivergenceContinuous : Continuous (tensorDivergence stress) :=
    tensorDivergence_continuous stress stressContDiff
  have pairingContinuous : Continuous
      (velocityDot test (tensorDivergence stress)) :=
    projectedPairing_velocityDot_continuous test (tensorDivergence stress)
      testContDiff.continuous tensorDivergenceContinuous
  have pairingCompact : HasCompactSupport
      (velocityDot test (tensorDivergence stress)) :=
    velocityDot_hasCompactSupport_left test (tensorDivergence stress)
      testCompact
  have pairingIntegrable : Integrable
      (velocityDot test (tensorDivergence stress)) :=
    pairingContinuous.integrable_of_hasCompactSupport pairingCompact
  have productRule := velocityDot_tensorDivergence stress test
    (stressContDiff.differentiable (by norm_num))
    (testContDiff.differentiable (by norm_num))
  have contractionEq : stressGradientContraction stress test =
      velocityDivergence (stressEnergyFlux stress test) -
        velocityDot test (tensorDivergence stress) := by
    rw [productRule]
    abel
  have contractionIntegrable : Integrable
      (stressGradientContraction stress test) := by
    rw [contractionEq]
    exact divergenceIntegrable.sub pairingIntegrable
  rw [productRule]
  simp only [Pi.sub_apply]
  rw [integral_sub divergenceIntegrable contractionIntegrable,
    divergenceIntegral, zero_sub]

private theorem physicalUnitCell_vorticityNonlinearity_pairing_eq_tensorProduct
    (u test : ProjectedPairingVelocityField)
    (uContDiff : ContDiff ℝ 2 u)
    (testContDiff : ContDiff ℝ 1 test)
    (uPeriodic : LatticePeriodic u)
    (testPeriodic : LatticePeriodic test)
    (uDivergence : velocityDivergence u = 0) :
    (∫ x in ThreeDimensionalPeriodicUnitCellDivergence.physicalUnitCell,
        velocityDot test
          (-vorticityAdvection u + vortexStretching u) x) =
      ∫ x in ThreeDimensionalPeriodicUnitCellDivergence.physicalUnitCell,
        ∑ velocityCoordinate : Coordinate,
          ∑ vorticityCoordinate : Coordinate,
            (fderiv ℝ test x
                (EuclideanSpace.single velocityCoordinate 1)
                  vorticityCoordinate -
              fderiv ℝ test x
                (EuclideanSpace.single vorticityCoordinate 1)
                  velocityCoordinate) *
              u x velocityCoordinate *
              vorticityField u x vorticityCoordinate := by
  let omega : ProjectedPairingVelocityField := vorticityField u
  let advectionStress : StressField := rankOneStress omega u
  let stretchingStress : StressField := rankOneStress u omega
  have uContDiffOne : ContDiff ℝ 1 u := uContDiff.of_le (by norm_num)
  have omegaContDiff : ContDiff ℝ 1 omega := by
    simpa only [omega] using vorticityField_contDiff u uContDiff
  have omegaPeriodic : LatticePeriodic omega := by
    simpa only [omega] using vorticityField_latticePeriodic u uPeriodic
  have omegaDivergence : velocityDivergence omega = 0 := by
    simpa only [omega] using
      velocityDivergence_vorticityField_eq_zero u uContDiff
  have advectionStressContDiff : ContDiff ℝ (1 : ℕ∞) advectionStress := by
    simpa only [advectionStress] using
      rankOneStress_contDiff (n := (1 : ℕ∞)) omega u
        omegaContDiff uContDiffOne
  have stretchingStressContDiff : ContDiff ℝ (1 : ℕ∞) stretchingStress := by
    simpa only [stretchingStress] using
      rankOneStress_contDiff (n := (1 : ℕ∞)) u omega
        uContDiffOne omegaContDiff
  have advectionStressPeriodic : LatticePeriodic advectionStress := by
    simpa only [advectionStress] using
      rankOneStress_latticePeriodic omega u omegaPeriodic uPeriodic
  have stretchingStressPeriodic : LatticePeriodic stretchingStress := by
    simpa only [stretchingStress] using
      rankOneStress_latticePeriodic u omega uPeriodic omegaPeriodic
  have advectionEq :
      tensorDivergence advectionStress = vorticityAdvection u := by
    rw [tensorDivergence_rankOneStress_of_divergence_eq_zero omega u
      omegaContDiff uContDiffOne uDivergence]
    rfl
  have stretchingEq :
      tensorDivergence stretchingStress = vortexStretching u := by
    rw [tensorDivergence_rankOneStress_of_divergence_eq_zero u omega
      uContDiffOne omegaContDiff omegaDivergence]
    rfl
  have advectionPairing :=
    physicalUnitCell_velocityDot_tensorDivergence_integral
      advectionStress test advectionStressContDiff testContDiff
      advectionStressPeriodic testPeriodic
  have stretchingPairing :=
    physicalUnitCell_velocityDot_tensorDivergence_integral
      stretchingStress test stretchingStressContDiff testContDiff
      stretchingStressPeriodic testPeriodic
  rw [advectionEq] at advectionPairing
  rw [stretchingEq] at stretchingPairing
  have advectionPairingIntegrable : IntegrableOn
      (velocityDot test (vorticityAdvection u))
      ThreeDimensionalPeriodicUnitCellDivergence.physicalUnitCell := by
    rw [← advectionEq]
    exact
      (projectedPairing_velocityDot_continuous test
        (tensorDivergence advectionStress) testContDiff.continuous
        (tensorDivergence_continuous advectionStress
          advectionStressContDiff)).continuousOn.integrableOn_compact
            physicalUnitCell_isCompact
  have stretchingPairingIntegrable : IntegrableOn
      (velocityDot test (vortexStretching u))
      ThreeDimensionalPeriodicUnitCellDivergence.physicalUnitCell := by
    rw [← stretchingEq]
    exact
      (projectedPairing_velocityDot_continuous test
        (tensorDivergence stretchingStress) testContDiff.continuous
        (tensorDivergence_continuous stretchingStress
          stretchingStressContDiff)).continuousOn.integrableOn_compact
            physicalUnitCell_isCompact
  calc
    (∫ x in ThreeDimensionalPeriodicUnitCellDivergence.physicalUnitCell,
        velocityDot test
          (-vorticityAdvection u + vortexStretching u) x) =
        -(∫ x in ThreeDimensionalPeriodicUnitCellDivergence.physicalUnitCell,
            velocityDot test (vorticityAdvection u) x) +
          ∫ x in ThreeDimensionalPeriodicUnitCellDivergence.physicalUnitCell,
            velocityDot test (vortexStretching u) x := by
      have pointwise : velocityDot test
          (-vorticityAdvection u + vortexStretching u) =
          -velocityDot test (vorticityAdvection u) +
            velocityDot test (vortexStretching u) := by
        funext x
        unfold velocityDot
        simp only [Pi.add_apply, Pi.neg_apply]
        calc
          (∑ i : Coordinate,
              test x i * (-vorticityAdvection u x i +
                vortexStretching u x i)) =
              ∑ i : Coordinate,
                (-test x i * vorticityAdvection u x i +
                  test x i * vortexStretching u x i) := by
            apply Finset.sum_congr rfl
            intro i _
            ring
          _ = -(∑ i : Coordinate,
                test x i * vorticityAdvection u x i) +
              ∑ i : Coordinate,
                test x i * vortexStretching u x i := by
            rw [Finset.sum_add_distrib]
            congr 1
            calc
              (∑ i : Coordinate,
                  -test x i * vorticityAdvection u x i) =
                  ∑ i : Coordinate,
                    -(test x i * vorticityAdvection u x i) := by
                apply Finset.sum_congr rfl
                intro i _
                ring
              _ = -(∑ i : Coordinate,
                    test x i * vorticityAdvection u x i) := by
                rw [Finset.sum_neg_distrib]
      rw [pointwise]
      change
        (∫ x in ThreeDimensionalPeriodicUnitCellDivergence.physicalUnitCell,
          ((-velocityDot test (vorticityAdvection u)) +
            velocityDot test (vortexStretching u)) x) = _
      rw [integral_add' advectionPairingIntegrable.neg
        stretchingPairingIntegrable, integral_neg']
    _ = (∫ x in ThreeDimensionalPeriodicUnitCellDivergence.physicalUnitCell,
          stressGradientContraction advectionStress test x) -
        ∫ x in ThreeDimensionalPeriodicUnitCellDivergence.physicalUnitCell,
          stressGradientContraction stretchingStress test x := by
      rw [advectionPairing, stretchingPairing]
      ring
    _ = ∫ x in ThreeDimensionalPeriodicUnitCellDivergence.physicalUnitCell,
        ∑ velocityCoordinate : Coordinate,
          ∑ vorticityCoordinate : Coordinate,
            (fderiv ℝ test x
                (EuclideanSpace.single velocityCoordinate 1)
                  vorticityCoordinate -
              fderiv ℝ test x
                (EuclideanSpace.single vorticityCoordinate 1)
                  velocityCoordinate) *
              u x velocityCoordinate *
              vorticityField u x vorticityCoordinate := by
      rw [← integral_sub]
      · apply integral_congr_ae
        filter_upwards with x
        unfold stressGradientContraction advectionStress stretchingStress
          rankOneStress omega
        rw [Finset.sum_comm]
        calc
          (∑ velocityCoordinate : Coordinate,
                ∑ vorticityCoordinate : Coordinate,
                  vorticityField u x vorticityCoordinate *
                    u x velocityCoordinate *
                    fderiv ℝ test x
                      (EuclideanSpace.single velocityCoordinate 1)
                        vorticityCoordinate) -
              ∑ velocityCoordinate : Coordinate,
                ∑ vorticityCoordinate : Coordinate,
                  u x velocityCoordinate *
                    vorticityField u x vorticityCoordinate *
                    fderiv ℝ test x
                      (EuclideanSpace.single vorticityCoordinate 1)
                        velocityCoordinate =
              ∑ velocityCoordinate : Coordinate,
                ((∑ vorticityCoordinate : Coordinate,
                    vorticityField u x vorticityCoordinate *
                      u x velocityCoordinate *
                      fderiv ℝ test x
                        (EuclideanSpace.single velocityCoordinate 1)
                          vorticityCoordinate) -
                  ∑ vorticityCoordinate : Coordinate,
                    u x velocityCoordinate *
                      vorticityField u x vorticityCoordinate *
                      fderiv ℝ test x
                        (EuclideanSpace.single vorticityCoordinate 1)
                          velocityCoordinate) := by
            rw [Finset.sum_sub_distrib]
          _ = ∑ velocityCoordinate : Coordinate,
                ∑ vorticityCoordinate : Coordinate,
                  (vorticityField u x vorticityCoordinate *
                      u x velocityCoordinate *
                      fderiv ℝ test x
                        (EuclideanSpace.single velocityCoordinate 1)
                          vorticityCoordinate -
                    u x velocityCoordinate *
                      vorticityField u x vorticityCoordinate *
                      fderiv ℝ test x
                        (EuclideanSpace.single vorticityCoordinate 1)
                          velocityCoordinate) := by
            apply Finset.sum_congr rfl
            intro velocityCoordinate _
            rw [Finset.sum_sub_distrib]
          _ = ∑ velocityCoordinate : Coordinate,
                ∑ vorticityCoordinate : Coordinate,
                  (fderiv ℝ test x
                      (EuclideanSpace.single velocityCoordinate 1)
                        vorticityCoordinate -
                    fderiv ℝ test x
                      (EuclideanSpace.single vorticityCoordinate 1)
                        velocityCoordinate) *
                    u x velocityCoordinate *
                    vorticityField u x vorticityCoordinate := by
            apply Finset.sum_congr rfl
            intro velocityCoordinate _
            apply Finset.sum_congr rfl
            intro vorticityCoordinate _
            ring
      · exact
          (by
            have : Continuous
                (stressGradientContraction advectionStress test) := by
              exact projectedPairing_stressGradientContraction_continuous
                advectionStress test advectionStressContDiff testContDiff
            exact this.continuousOn.integrableOn_compact
              physicalUnitCell_isCompact)
      · exact
          (by
            have : Continuous
                (stressGradientContraction stretchingStress test) := by
              exact projectedPairing_stressGradientContraction_continuous
                stretchingStress test stretchingStressContDiff testContDiff
            exact this.continuousOn.integrableOn_compact
              physicalUnitCell_isCompact)

/-- Compactly supported whole-space vorticity tests give the conservative
velocity--vorticity tensor form without a boundary term. -/
theorem wholeSpace_vorticityNonlinearity_pairing_eq_tensorProduct
    (u test : ProjectedPairingVelocityField)
    (uContDiff : ContDiff ℝ 2 u)
    (testContDiff : ContDiff ℝ 1 test)
    (testCompact : HasCompactSupport test)
    (uDivergence : velocityDivergence u = 0) :
    (∫ x : PhysicalSpace,
        velocityDot test
          (-vorticityAdvection u + vortexStretching u) x) =
      ∫ x : PhysicalSpace,
        ∑ velocityCoordinate : Coordinate,
          ∑ vorticityCoordinate : Coordinate,
            (fderiv ℝ test x
                (EuclideanSpace.single velocityCoordinate 1)
                  vorticityCoordinate -
              fderiv ℝ test x
                (EuclideanSpace.single vorticityCoordinate 1)
                  velocityCoordinate) *
              u x velocityCoordinate *
              vorticityField u x vorticityCoordinate := by
  let omega : ProjectedPairingVelocityField := vorticityField u
  let advectionStress : StressField := rankOneStress omega u
  let stretchingStress : StressField := rankOneStress u omega
  have uContDiffOne : ContDiff ℝ 1 u := uContDiff.of_le (by norm_num)
  have omegaContDiff : ContDiff ℝ 1 omega := by
    simpa only [omega] using vorticityField_contDiff u uContDiff
  have omegaDivergence : velocityDivergence omega = 0 := by
    simpa only [omega] using
      velocityDivergence_vorticityField_eq_zero u uContDiff
  have advectionStressContDiff : ContDiff ℝ (1 : ℕ∞) advectionStress := by
    simpa only [advectionStress] using
      rankOneStress_contDiff (n := (1 : ℕ∞)) omega u
        omegaContDiff uContDiffOne
  have stretchingStressContDiff : ContDiff ℝ (1 : ℕ∞) stretchingStress := by
    simpa only [stretchingStress] using
      rankOneStress_contDiff (n := (1 : ℕ∞)) u omega
        uContDiffOne omegaContDiff
  have advectionEq :
      tensorDivergence advectionStress = vorticityAdvection u := by
    rw [tensorDivergence_rankOneStress_of_divergence_eq_zero omega u
      omegaContDiff uContDiffOne uDivergence]
    rfl
  have stretchingEq :
      tensorDivergence stretchingStress = vortexStretching u := by
    rw [tensorDivergence_rankOneStress_of_divergence_eq_zero u omega
      uContDiffOne omegaContDiff omegaDivergence]
    rfl
  have advectionPairing :=
    wholeSpace_velocityDot_tensorDivergence_integral
      advectionStress test advectionStressContDiff testContDiff testCompact
  have stretchingPairing :=
    wholeSpace_velocityDot_tensorDivergence_integral
      stretchingStress test stretchingStressContDiff testContDiff testCompact
  rw [advectionEq] at advectionPairing
  rw [stretchingEq] at stretchingPairing
  have advectionPairingIntegrable : Integrable
      (velocityDot test (vorticityAdvection u)) := by
    rw [← advectionEq]
    exact
      (projectedPairing_velocityDot_continuous test
        (tensorDivergence advectionStress) testContDiff.continuous
        (tensorDivergence_continuous advectionStress
          advectionStressContDiff)).integrable_of_hasCompactSupport
            (velocityDot_hasCompactSupport_left test
              (tensorDivergence advectionStress) testCompact)
  have stretchingPairingIntegrable : Integrable
      (velocityDot test (vortexStretching u)) := by
    rw [← stretchingEq]
    exact
      (projectedPairing_velocityDot_continuous test
        (tensorDivergence stretchingStress) testContDiff.continuous
        (tensorDivergence_continuous stretchingStress
          stretchingStressContDiff)).integrable_of_hasCompactSupport
            (velocityDot_hasCompactSupport_left test
              (tensorDivergence stretchingStress) testCompact)
  calc
    (∫ x : PhysicalSpace,
        velocityDot test
          (-vorticityAdvection u + vortexStretching u) x) =
        -(∫ x : PhysicalSpace,
            velocityDot test (vorticityAdvection u) x) +
          ∫ x : PhysicalSpace,
            velocityDot test (vortexStretching u) x := by
      have pointwise : velocityDot test
          (-vorticityAdvection u + vortexStretching u) =
          -velocityDot test (vorticityAdvection u) +
            velocityDot test (vortexStretching u) := by
        funext x
        unfold velocityDot
        simp only [Pi.add_apply, Pi.neg_apply]
        calc
          (∑ i : Coordinate,
              test x i * (-vorticityAdvection u x i +
                vortexStretching u x i)) =
              ∑ i : Coordinate,
                (-test x i * vorticityAdvection u x i +
                  test x i * vortexStretching u x i) := by
            apply Finset.sum_congr rfl
            intro i _
            ring
          _ = -(∑ i : Coordinate,
                test x i * vorticityAdvection u x i) +
              ∑ i : Coordinate,
                test x i * vortexStretching u x i := by
            rw [Finset.sum_add_distrib]
            congr 1
            calc
              (∑ i : Coordinate,
                  -test x i * vorticityAdvection u x i) =
                  ∑ i : Coordinate,
                    -(test x i * vorticityAdvection u x i) := by
                apply Finset.sum_congr rfl
                intro i _
                ring
              _ = -(∑ i : Coordinate,
                    test x i * vorticityAdvection u x i) := by
                rw [Finset.sum_neg_distrib]
      rw [pointwise]
      change
        (∫ x : PhysicalSpace,
          ((-velocityDot test (vorticityAdvection u)) +
            velocityDot test (vortexStretching u)) x) = _
      simp only [Pi.add_apply, Pi.neg_apply]
      calc
        (∫ x : PhysicalSpace,
            -velocityDot test (vorticityAdvection u) x +
              velocityDot test (vortexStretching u) x) =
            (∫ x : PhysicalSpace,
              (-velocityDot test (vorticityAdvection u)) x) +
              ∫ x : PhysicalSpace,
                velocityDot test (vortexStretching u) x := by
          exact integral_add advectionPairingIntegrable.neg
            stretchingPairingIntegrable
        _ = _ := by
          congr 1
          change (∫ x : PhysicalSpace,
            -velocityDot test (vorticityAdvection u) x) = _
          rw [integral_neg]
    _ = (∫ x : PhysicalSpace,
          stressGradientContraction advectionStress test x) -
        ∫ x : PhysicalSpace,
          stressGradientContraction stretchingStress test x := by
      rw [advectionPairing, stretchingPairing]
      ring
    _ = ∫ x : PhysicalSpace,
        ∑ velocityCoordinate : Coordinate,
          ∑ vorticityCoordinate : Coordinate,
            (fderiv ℝ test x
                (EuclideanSpace.single velocityCoordinate 1)
                  vorticityCoordinate -
              fderiv ℝ test x
                (EuclideanSpace.single vorticityCoordinate 1)
                  velocityCoordinate) *
              u x velocityCoordinate *
              vorticityField u x vorticityCoordinate := by
      rw [← integral_sub]
      · apply integral_congr_ae
        filter_upwards with x
        unfold stressGradientContraction advectionStress stretchingStress
          rankOneStress omega
        rw [Finset.sum_comm]
        calc
          (∑ velocityCoordinate : Coordinate,
                ∑ vorticityCoordinate : Coordinate,
                  vorticityField u x vorticityCoordinate *
                    u x velocityCoordinate *
                    fderiv ℝ test x
                      (EuclideanSpace.single velocityCoordinate 1)
                        vorticityCoordinate) -
              ∑ velocityCoordinate : Coordinate,
                ∑ vorticityCoordinate : Coordinate,
                  u x velocityCoordinate *
                    vorticityField u x vorticityCoordinate *
                    fderiv ℝ test x
                      (EuclideanSpace.single vorticityCoordinate 1)
                        velocityCoordinate =
              ∑ velocityCoordinate : Coordinate,
                ((∑ vorticityCoordinate : Coordinate,
                    vorticityField u x vorticityCoordinate *
                      u x velocityCoordinate *
                      fderiv ℝ test x
                        (EuclideanSpace.single velocityCoordinate 1)
                          vorticityCoordinate) -
                  ∑ vorticityCoordinate : Coordinate,
                    u x velocityCoordinate *
                      vorticityField u x vorticityCoordinate *
                      fderiv ℝ test x
                        (EuclideanSpace.single vorticityCoordinate 1)
                          velocityCoordinate) := by
            rw [Finset.sum_sub_distrib]
          _ = ∑ velocityCoordinate : Coordinate,
                ∑ vorticityCoordinate : Coordinate,
                  (vorticityField u x vorticityCoordinate *
                      u x velocityCoordinate *
                      fderiv ℝ test x
                        (EuclideanSpace.single velocityCoordinate 1)
                          vorticityCoordinate -
                    u x velocityCoordinate *
                      vorticityField u x vorticityCoordinate *
                      fderiv ℝ test x
                        (EuclideanSpace.single vorticityCoordinate 1)
                          velocityCoordinate) := by
            apply Finset.sum_congr rfl
            intro velocityCoordinate _
            rw [Finset.sum_sub_distrib]
          _ = ∑ velocityCoordinate : Coordinate,
                ∑ vorticityCoordinate : Coordinate,
                  (fderiv ℝ test x
                      (EuclideanSpace.single velocityCoordinate 1)
                        vorticityCoordinate -
                    fderiv ℝ test x
                      (EuclideanSpace.single vorticityCoordinate 1)
                        velocityCoordinate) *
                    u x velocityCoordinate *
                    vorticityField u x vorticityCoordinate := by
            apply Finset.sum_congr rfl
            intro velocityCoordinate _
            apply Finset.sum_congr rfl
            intro vorticityCoordinate _
            ring
      · exact
          (projectedPairing_stressGradientContraction_continuous
            advectionStress test advectionStressContDiff testContDiff)
            |>.integrable_of_hasCompactSupport
              (stressGradientContraction_hasCompactSupport_right
                advectionStress test testCompact)
      · exact
          (projectedPairing_stressGradientContraction_continuous
            stretchingStress test stretchingStressContDiff testContDiff)
            |>.integrable_of_hasCompactSupport
              (stressGradientContraction_hasCompactSupport_right
                stretchingStress test testCompact)

private theorem centralTensorVectorTest_fderiv_eq_zero_of_norm_gt
    (spatialTest : Coordinate → SchwartzMap ℝ ℂ)
    (scale : ℝ)
    (center x : PhysicalSpace)
    (scalar : ℂ)
    (testCoordinate : Coordinate)
    (supportRadius : ℝ)
    (supportRadiusNonneg : 0 ≤ supportRadius)
    (support : ∀ coordinate y,
      supportRadius < |y| → spatialTest coordinate y = 0)
    (outside : 3 * supportRadius <
      ‖scale⁻¹ • (x - center)‖) :
    fderiv ℝ
      (centralTensorVectorTest spatialTest scale center scalar testCoordinate)
      x = 0 := by
  let outsideSet : Set PhysicalSpace :=
    {y | 3 * supportRadius < ‖scale⁻¹ • (y - center)‖}
  have outsideOpen : IsOpen outsideSet := by
    exact isOpen_lt continuous_const
      (continuous_norm.comp (by fun_prop : Continuous
        (fun y : PhysicalSpace => scale⁻¹ • (y - center))))
  have outsideMem : outsideSet ∈ nhds x := outsideOpen.mem_nhds outside
  have eventuallyZero :
      centralTensorVectorTest spatialTest scale center scalar testCoordinate =ᶠ[nhds x]
        (fun _y : PhysicalSpace => (0 : PhysicalSpace)) := by
    filter_upwards [outsideMem] with y yOutside
    unfold centralTensorVectorTest
    rw [centralTensorScalar_eq_zero_of_norm_gt spatialTest scale center y
      supportRadius supportRadiusNonneg support yOutside]
    simp
  rw [eventuallyZero.fderiv_eq]
  simp

private theorem wholeSpace_centralTensorIntegral_eq_affineBall
    (spatialTest : Coordinate → SchwartzMap ℝ ℂ)
    (scale : ℝ) (scalePos : 0 < scale)
    (center : PhysicalSpace)
    (scalar : ℂ)
    (testCoordinate : Coordinate)
    (supportRadius spatialRadius : ℝ)
    (supportRadiusNonneg : 0 ≤ supportRadius)
    (supportInside : 3 * supportRadius < spatialRadius)
    (support : ∀ coordinate y,
      supportRadius < |y| → spatialTest coordinate y = 0)
    (u omega : PhysicalSpace → PhysicalSpace) :
    (∫ x : PhysicalSpace,
        ∑ velocityCoordinate : Coordinate,
          ∑ vorticityCoordinate : Coordinate,
            (fderiv ℝ
                (centralTensorVectorTest spatialTest scale center scalar
                  testCoordinate) x
                  (EuclideanSpace.single velocityCoordinate 1)
                    vorticityCoordinate -
              fderiv ℝ
                (centralTensorVectorTest spatialTest scale center scalar
                  testCoordinate) x
                  (EuclideanSpace.single vorticityCoordinate 1)
                    velocityCoordinate) *
              u x velocityCoordinate * omega x vorticityCoordinate) =
      ∫ x in
          (fun y : PhysicalSpace => y - center) ⁻¹'
            (scale • Metric.closedBall (0 : PhysicalSpace) spatialRadius),
        ∑ velocityCoordinate : Coordinate,
          ∑ vorticityCoordinate : Coordinate,
            (fderiv ℝ
                (centralTensorVectorTest spatialTest scale center scalar
                  testCoordinate) x
                  (EuclideanSpace.single velocityCoordinate 1)
                    vorticityCoordinate -
              fderiv ℝ
                (centralTensorVectorTest spatialTest scale center scalar
                  testCoordinate) x
                  (EuclideanSpace.single vorticityCoordinate 1)
                    velocityCoordinate) *
              u x velocityCoordinate * omega x vorticityCoordinate := by
  let supportSet : Set PhysicalSpace :=
    (fun y : PhysicalSpace => y - center) ⁻¹'
      (scale • Metric.closedBall (0 : PhysicalSpace) spatialRadius)
  symm
  apply setIntegral_eq_integral_of_forall_compl_eq_zero
  intro x xOutside
  have displacementOutside :
      x - center ∉ scale • Metric.closedBall (0 : PhysicalSpace) spatialRadius :=
    xOutside
  have normalizedOutsideSet :
      scale⁻¹ • (x - center) ∉
        Metric.closedBall (0 : PhysicalSpace) spatialRadius := by
    rwa [← Set.mem_smul_set_iff_inv_smul_mem₀ scalePos.ne']
  have normalizedOutside :
      spatialRadius < ‖scale⁻¹ • (x - center)‖ := by
    simpa only [Metric.mem_closedBall, dist_zero_right, not_le] using
      normalizedOutsideSet
  have derivativeZero :=
    centralTensorVectorTest_fderiv_eq_zero_of_norm_gt spatialTest scale
      center x scalar testCoordinate supportRadius supportRadiusNonneg support
      (supportInside.trans normalizedOutside)
  simp [derivativeZero]

private theorem physicalUnitCell_periodizedCentralPairing_eq_wholeSpace
    (spatialTest : Coordinate → SchwartzMap ℝ ℂ)
    (scale : ℝ) (scaleNe : scale ≠ 0)
    (center : PhysicalSpace)
    (scalar : ℂ)
    (testCoordinate : Coordinate)
    (field : PhysicalSpace → PhysicalSpace)
    (fieldPeriodic : LatticePeriodic field)
    (fieldContinuous : Continuous field)
    (testCompact : HasCompactSupport
      (centralTensorVectorTest spatialTest scale center scalar testCoordinate)) :
    (∫ x in physicalUnitCell,
      velocityDot
        (periodizedCentralTensorVectorTest spatialTest scale center scalar
          testCoordinate) field x) =
      ∫ x : PhysicalSpace,
        velocityDot
          (centralTensorVectorTest spatialTest scale center scalar
            testCoordinate) field x := by
  let density : PhysicalSpace → ℝ := fun x =>
    velocityDot
      (centralTensorVectorTest spatialTest scale center scalar testCoordinate)
      field x
  have testContinuous : Continuous
      (centralTensorVectorTest spatialTest scale center scalar testCoordinate) :=
    (centralTensorVectorTest_contDiff spatialTest scale center scalar
      testCoordinate).continuous
  have densityContinuous : Continuous density := by
    dsimp only [density]
    unfold velocityDot
    apply continuous_finsetSum
    intro coordinate _coordinateMem
    exact (((EuclideanSpace.proj coordinate).continuous.comp testContinuous).mul
      ((EuclideanSpace.proj coordinate).continuous.comp fieldContinuous))
  have densityCompact : HasCompactSupport density :=
    velocityDot_hasCompactSupport_left
      (centralTensorVectorTest spatialTest scale center scalar testCoordinate)
      field testCompact
  have densityIntegrable : Integrable density :=
    densityContinuous.integrable_of_hasCompactSupport densityCompact
  rw [← physicalUnitCell_integral_latticePeriodization density
    densityIntegrable]
  apply integral_congr_ae
  filter_upwards [] with x
  exact velocityDot_periodizedCentralTensorVectorTest_eq_tsum
    spatialTest scale scaleNe center scalar testCoordinate field fieldPeriodic x

/-- The Fourier-periodized compact tensor test unfolds across the physical
unit cell at every center, and its conservative vorticity action is exactly
the affine-ball physical tensor action. -/
theorem periodizedCentralNonlinearity_eq_affineBallTensor
    (spatialTest : Coordinate → SchwartzMap ℝ ℂ)
    (scale : ℝ) (scalePos : 0 < scale)
    (center : PhysicalSpace)
    (scalar : ℂ)
    (testCoordinate : Coordinate)
    (supportRadius spatialRadius : ℝ)
    (supportRadiusNonneg : 0 ≤ supportRadius)
    (supportInside : 3 * supportRadius < spatialRadius)
    (support : ∀ coordinate y,
      supportRadius < |y| → spatialTest coordinate y = 0)
    (u : PhysicalSpace → PhysicalSpace)
    (uContDiff : ContDiff ℝ 2 u)
    (uPeriodic : LatticePeriodic u)
    (uDivergence : velocityDivergence u = 0) :
    (∫ x in physicalUnitCell,
      velocityDot
        (periodizedCentralTensorVectorTest spatialTest scale center scalar
          testCoordinate)
        (-vorticityAdvection u + vortexStretching u) x) =
      ∫ x in
          (fun y : PhysicalSpace => y - center) ⁻¹'
            (scale • Metric.closedBall (0 : PhysicalSpace) spatialRadius),
        ∑ velocityCoordinate : Coordinate,
          ∑ vorticityCoordinate : Coordinate,
            (fderiv ℝ
                (centralTensorVectorTest spatialTest scale center scalar
                  testCoordinate) x
                  (EuclideanSpace.single velocityCoordinate 1)
                    vorticityCoordinate -
              fderiv ℝ
                (centralTensorVectorTest spatialTest scale center scalar
                  testCoordinate) x
                  (EuclideanSpace.single vorticityCoordinate 1)
                    velocityCoordinate) *
              u x velocityCoordinate *
              vorticityField u x vorticityCoordinate := by
  have nonlinearPeriodic :
      LatticePeriodic (-vorticityAdvection u + vortexStretching u) :=
    vorticityNonlinearity_latticePeriodic u uPeriodic
  have nonlinearContinuous :
      Continuous (-vorticityAdvection u + vortexStretching u) := by
    have uContDiffOne : ContDiff ℝ 1 u := uContDiff.of_le (by norm_num)
    have omegaContDiff : ContDiff ℝ 1 (vorticityField u) :=
      vorticityField_contDiff u uContDiff
    unfold vorticityAdvection vortexStretching
    exact
      ((omegaContDiff.continuous_fderiv (by norm_num)).clm_apply
        uContDiffOne.continuous).neg.add
      ((uContDiffOne.continuous_fderiv (by norm_num)).clm_apply
        omegaContDiff.continuous)
  have centralCompact := centralTensorVectorTest_hasCompactSupport
    spatialTest scale scalePos center scalar testCoordinate supportRadius
      supportRadiusNonneg support
  have unfolded := physicalUnitCell_periodizedCentralPairing_eq_wholeSpace
    spatialTest scale scalePos.ne' center scalar testCoordinate
      (-vorticityAdvection u + vortexStretching u) nonlinearPeriodic
      nonlinearContinuous centralCompact
  have centralContDiffOne : ContDiff ℝ 1
      (centralTensorVectorTest spatialTest scale center scalar
        testCoordinate) :=
    (centralTensorVectorTest_contDiff spatialTest scale center scalar
      testCoordinate).of_le (by norm_num)
  have wholeTensor :=
    wholeSpace_vorticityNonlinearity_pairing_eq_tensorProduct
      u (centralTensorVectorTest spatialTest scale center scalar testCoordinate)
      uContDiff centralContDiffOne centralCompact uDivergence
  have restricted := wholeSpace_centralTensorIntegral_eq_affineBall
    spatialTest scale scalePos center scalar testCoordinate supportRadius
      spatialRadius supportRadiusNonneg supportInside support u
      (vorticityField u)
  exact unfolded.trans (wholeTensor.trans restricted)



private theorem projectedReality
    (radius : Nat)
    (state : ComplexVorticityHilbertState)
    (reality : FiniteStateFourierReality state) :
    FiniteStateFourierReality
      (complexSharpSupportProjection
        (puncturedIntegerWaveFrequencyCube radius) state) := by
  intro wave
  by_cases waveMem : wave ∈ puncturedIntegerWaveFrequencyCube radius
  · have negMem :=
      puncturedIntegerWaveFrequencyCube_waveNeg_mem radius waveMem
    simp only [complexSharpSupportProjection_apply, waveMem, negMem]
    exact reality wave
  · have negNotMem :
        waveNeg wave ∉ puncturedIntegerWaveFrequencyCube radius := by
      intro negMem
      have := puncturedIntegerWaveFrequencyCube_waveNeg_mem radius negMem
      exact waveMem (by simpa using this)
    simp [complexSharpSupportProjection_apply, waveMem, negNotMem]

private theorem generatedNonlinearCoefficient_rawProjected_eq
    (radius : Nat)
    (state : ComplexVorticityHilbertState)
    (stateTransverse : WholeStateTransverse state)
    (reality : FiniteStateFourierReality state)
    (output : IntegerWavevector) :
    let modes := puncturedIntegerWaveFrequencyCube radius
    let projected := complexSharpSupportProjection modes state
    let source := rawSourceOfFiniteVorticityState modes projected
    generatedVorticityNonlinearCoefficientAt source output =
      wholeStateVorticityNonlinearCoefficientAt projected output := by
  dsimp only
  let modes := puncturedIntegerWaveFrequencyCube radius
  let projected := complexSharpSupportProjection modes state
  let source := rawSourceOfFiniteVorticityState modes projected
  have zeroNotMem : 0 ∉ modes := by
    exact zero_not_mem_puncturedIntegerWaveFrequencyCube radius
  have negClosed : ∀ wave ∈ modes, waveNeg wave ∈ modes := by
    intro wave waveMem
    exact puncturedIntegerWaveFrequencyCube_waveNeg_mem radius waveMem
  have supported : ∀ wave, wave ∉ modes → projected wave = 0 := by
    intro wave waveNotMem
    simp [projected, complexSharpSupportProjection_apply, waveNotMem]
  have transverse : ∀ wave ∈ modes,
      complexWavevector wave ⬝ᵥ projected wave = 0 := by
    intro wave waveMem
    simp only [projected, complexSharpSupportProjection_apply, waveMem]
    exact stateTransverse wave
  have projectedReality : FiniteStateFourierReality projected := by
    simpa only [projected, modes] using projectedReality radius state reality
  have supportEq : generatedSupport source = modes := by
    simpa only [source] using
      rawSourceOfFiniteVorticityState_generatedSupport
        modes zeroNotMem negClosed projected
  have compiledEq :
      generatedComplexVorticityState source (generatedSupport source) =
        projected := by
    simpa only [source] using
      generatedComplexVorticityState_rawSourceOfFinitePhysicalState
        modes zeroNotMem negClosed projected supported transverse
          projectedReality
  calc
    generatedVorticityNonlinearCoefficientAt source output =
        ∑ pair ∈ generatedStretchingPairTable source,
          if stretchingPairOutput pair = output then
            generatedVorticityNonlinearPairContribution source pair
          else 0 :=
      generatedVorticityNonlinearCoefficientAt_eq_fullPairTableSum
        source output
    _ = ∑ first ∈ modes, ∑ second ∈ modes,
          if first + second = output then
            finiteStateVorticityNonlinearPairContribution
              projected (first, second)
          else 0 := by
      rw [generatedStretchingPairTable, supportEq, Finset.sum_product]
      apply Finset.sum_congr rfl
      intro first firstMem
      apply Finset.sum_congr rfl
      intro second secondMem
      by_cases outputEq : first + second = output
      · simp only [stretchingPairOutput, outputEq, if_true]
        rw [← finiteStateNonlinearPair_generatedPhysicalSource
          source (first, second), compiledEq]
      · simp [stretchingPairOutput, outputEq]
    _ = finiteStateVorticityNonlinearCoefficientAt modes projected output :=
      rfl
    _ = finiteStateVorticityNonlinearCoefficientAt modes state output := by
      exact finiteStateVorticityNonlinearCoefficientAt_projection_of_subset
        (Finset.Subset.rfl) state output
    _ = wholeStateVorticityNonlinearCoefficientAt projected output := by
      simpa only [projected] using
        (wholeStateVorticityNonlinearCoefficientAt_projection_eq_finite
          modes state output).symm

private theorem projectedNonlinearCoefficientPairing_eq_physicalNonlinearity
    (inputRadius : Nat)
    (state : ComplexVorticityHilbertState)
    (stateTransverse : WholeStateTransverse state)
    (reality : FiniteStateFourierReality state)
    (testModes : Finset IntegerWavevector)
    (testCoefficient : IntegerWavevector → ComplexCoordinateVector) :
    let inputModes := puncturedIntegerWaveFrequencyCube inputRadius
    let projected := complexSharpSupportProjection inputModes state
    let source := rawSourceOfFiniteVorticityState inputModes projected
    (∑ wave ∈ testModes,
        complexCoordinateRealInner (testCoefficient wave)
          (wholeStateVorticityNonlinearCoefficientAt projected wave)) =
      ∫ x in ThreeDimensionalPeriodicUnitCellDivergence.physicalUnitCell,
        velocityDot
          (finiteRealComplexFourierField testModes testCoefficient)
          (-vorticityAdvection (physicalVelocity source) +
            vortexStretching (physicalVelocity source)) x := by
  dsimp only
  let inputModes := puncturedIntegerWaveFrequencyCube inputRadius
  let projected := complexSharpSupportProjection inputModes state
  let source := rawSourceOfFiniteVorticityState inputModes projected
  have fieldContinuous : Continuous
      (generatedVorticityNonlinearOutputField source) :=
    (finiteRealComplexFourierField_contDiff
      (generatedStretchingOutputInventory source)
      (generatedVorticityNonlinearCoefficientAt source)).continuous
  rw [← generatedVorticityNonlinearPairField_eq_physicalNonlinearity source,
    generatedVorticityNonlinearPairField_eq_outputField source,
    physicalUnitCell_finiteRealComplexFourierField_pairing
      testModes testCoefficient
        (generatedVorticityNonlinearOutputField source) fieldContinuous]
  apply Finset.sum_congr rfl
  intro wave _
  rw [physicalUnitCellComplexFourierCoordinate_generatedVorticityNonlinearOutputField]
  exact congrArg (complexCoordinateRealInner (testCoefficient wave))
    (generatedNonlinearCoefficient_rawProjected_eq inputRadius state
      stateTransverse reality wave).symm

private theorem projectedNonlinearCoefficientPairing_eq_velocityVorticityTensor
    (inputRadius : Nat)
    (state : ComplexVorticityHilbertState)
    (stateTransverse : WholeStateTransverse state)
    (reality : FiniteStateFourierReality state)
    (testModes : Finset IntegerWavevector)
    (testCoefficient : IntegerWavevector → ComplexCoordinateVector) :
    let inputModes := puncturedIntegerWaveFrequencyCube inputRadius
    let projected := complexSharpSupportProjection inputModes state
    let source := rawSourceOfFiniteVorticityState inputModes projected
    let test := finiteRealComplexFourierField testModes testCoefficient
    (∑ wave ∈ testModes,
        complexCoordinateRealInner (testCoefficient wave)
          (wholeStateVorticityNonlinearCoefficientAt projected wave)) =
      ∫ x in ThreeDimensionalPeriodicUnitCellDivergence.physicalUnitCell,
        ∑ velocityCoordinate : Coordinate,
          ∑ vorticityCoordinate : Coordinate,
            (fderiv ℝ test x
                (EuclideanSpace.single velocityCoordinate 1)
                  vorticityCoordinate -
              fderiv ℝ test x
                (EuclideanSpace.single vorticityCoordinate 1)
                  velocityCoordinate) *
              physicalVelocity source x velocityCoordinate *
              finiteRealComplexFourierField inputModes projected x
                vorticityCoordinate := by
  dsimp only
  let inputModes := puncturedIntegerWaveFrequencyCube inputRadius
  let projected := complexSharpSupportProjection inputModes state
  let source := rawSourceOfFiniteVorticityState inputModes projected
  let test := finiteRealComplexFourierField testModes testCoefficient
  have zeroNotMem : 0 ∉ inputModes := by
    exact zero_not_mem_puncturedIntegerWaveFrequencyCube inputRadius
  have negClosed : ∀ wave ∈ inputModes, waveNeg wave ∈ inputModes := by
    intro wave waveMem
    exact puncturedIntegerWaveFrequencyCube_waveNeg_mem inputRadius waveMem
  have supported : ∀ wave, wave ∉ inputModes → projected wave = 0 := by
    intro wave waveNotMem
    simp [projected, complexSharpSupportProjection_apply, waveNotMem]
  have transverse : ∀ wave ∈ inputModes,
      complexWavevector wave ⬝ᵥ projected wave = 0 := by
    intro wave waveMem
    simp only [projected, complexSharpSupportProjection_apply, waveMem]
    exact stateTransverse wave
  have projectedRealityLaw : FiniteStateFourierReality projected := by
    simpa only [projected, inputModes] using
      projectedReality inputRadius state reality
  have uContDiff : ContDiff ℝ 2 (physicalVelocity source) :=
    (physicalVelocity_contDiff source).of_le
      (show (↑(2 : ℕ∞) : WithTop ℕ∞) ≤
          (↑(⊤ : ℕ∞) : WithTop ℕ∞) from
        WithTop.coe_le_coe.mpr le_top)
  have testContDiff : ContDiff ℝ 1 test := by
    exact (finiteRealComplexFourierField_contDiff
      testModes testCoefficient).of_le (by norm_num)
  have tensorPairing :=
    physicalUnitCell_vorticityNonlinearity_pairing_eq_tensorProduct
      (physicalVelocity source) test uContDiff testContDiff
      (physicalVelocity_latticePeriodic source)
      (finiteRealComplexFourierField_latticePeriodic
        testModes testCoefficient)
      (velocityDivergence_physicalVelocity_eq_zero source)
  rw [vorticityField_physicalVelocity source,
    physicalVorticity_rawSourceOfFinitePhysicalState_eq
      inputModes zeroNotMem negClosed projected supported transverse
        projectedRealityLaw] at tensorPairing
  exact
    (projectedNonlinearCoefficientPairing_eq_physicalNonlinearity
      inputRadius state stateTransverse reality testModes testCoefficient).trans
        tensorPairing

/--
The complete nonlinear row of an ordinary-cube sharp projection is exactly
its periodic conservative physical pairing.  The zero Fourier row is erased
inside the canonically recompiled source, while the conclusion retains the
actual velocity--vorticity tensor against the antisymmetric test gradient.
-/
theorem fullCubeProjectedNonlinearPairing_eq_velocityVorticityTensor
    (inputRadius : Nat)
    (state : ComplexVorticityHilbertState)
    (zeroRow : state 0 = 0)
    (stateTransverse : WholeStateTransverse state)
    (reality : FiniteStateFourierReality state)
    (testModes : Finset IntegerWavevector)
    (testCoefficient : IntegerWavevector → ComplexCoordinateVector) :
    let fullModes := integerWaveFrequencyCube inputRadius
    let inputModes := puncturedIntegerWaveFrequencyCube inputRadius
    let projected := complexSharpSupportProjection fullModes state
    let source := rawSourceOfFiniteVorticityState inputModes projected
    let test := finiteRealComplexFourierField testModes testCoefficient
    (∑ wave ∈ testModes,
        complexCoordinateRealInner (testCoefficient wave)
          (wholeStateVorticityNonlinearCoefficientAt projected wave)) =
      ∫ x in ThreeDimensionalPeriodicUnitCellDivergence.physicalUnitCell,
        ∑ velocityCoordinate : Coordinate,
          ∑ vorticityCoordinate : Coordinate,
            (fderiv ℝ test x
                (EuclideanSpace.single velocityCoordinate 1)
                  vorticityCoordinate -
              fderiv ℝ test x
                (EuclideanSpace.single vorticityCoordinate 1)
                  velocityCoordinate) *
              physicalVelocity source x velocityCoordinate *
              finiteRealComplexFourierField inputModes projected x
                vorticityCoordinate := by
  dsimp only
  have projectionEq :
      complexSharpSupportProjection
          (puncturedIntegerWaveFrequencyCube inputRadius) state =
        complexSharpSupportProjection
          (integerWaveFrequencyCube inputRadius) state := by
    apply lp.ext
    funext wave
    by_cases waveZero : wave = 0
    · subst wave
      simp [puncturedIntegerWaveFrequencyCube,
        complexSharpSupportProjection_apply, zeroRow]
    · by_cases waveMem : wave ∈ integerWaveFrequencyCube inputRadius <;>
        simp [puncturedIntegerWaveFrequencyCube,
          complexSharpSupportProjection_apply, waveZero, waveMem]
  rw [← projectionEq]
  exact projectedNonlinearCoefficientPairing_eq_velocityVorticityTensor
    inputRadius state stateTransverse reality testModes testCoefficient

private theorem projectedPairing_complexCoordinateRealInner_conj_smul_left
    (scalar : ℂ) (left right : ComplexCoordinateVector) :
    complexCoordinateRealInner (star scalar • left) right =
      complexCoordinateRealInner left (scalar • right) := by
  unfold complexCoordinateRealInner
  apply Finset.sum_congr rfl
  intro coordinate _
  simp only [Pi.smul_apply, smul_eq_mul, Complex.star_def,
    Complex.mul_re, Complex.mul_im, Complex.conj_re, Complex.conj_im]
  ring

private theorem fullCubeProjectedNonlinearTemporalPairing_eq_tensor
    (inputRadius : Nat)
    (state : ComplexVorticityHilbertState)
    (zeroRow : state 0 = 0)
    (stateTransverse : WholeStateTransverse state)
    (reality : FiniteStateFourierReality state)
    (testModes : Finset IntegerWavevector)
    (testCoefficient : IntegerWavevector → ComplexCoordinateVector)
    (temporalWeight : Complex) :
    let fullModes := integerWaveFrequencyCube inputRadius
    let inputModes := puncturedIntegerWaveFrequencyCube inputRadius
    let projected := complexSharpSupportProjection fullModes state
    let source := rawSourceOfFiniteVorticityState inputModes projected
    let weightedCoefficient :
        IntegerWavevector → ComplexCoordinateVector := fun wave =>
      star temporalWeight • testCoefficient wave
    let weightedTest :=
      finiteRealComplexFourierField testModes weightedCoefficient
    (∑ wave ∈ testModes,
        complexCoordinateRealInner (testCoefficient wave)
          (temporalWeight •
            wholeStateVorticityNonlinearCoefficientAt projected wave)) =
      ∫ x in ThreeDimensionalPeriodicUnitCellDivergence.physicalUnitCell,
        ∑ velocityCoordinate : Coordinate,
          ∑ vorticityCoordinate : Coordinate,
            (fderiv ℝ weightedTest x
                (EuclideanSpace.single velocityCoordinate 1)
                  vorticityCoordinate -
              fderiv ℝ weightedTest x
                (EuclideanSpace.single vorticityCoordinate 1)
                  velocityCoordinate) *
              physicalVelocity source x velocityCoordinate *
              finiteRealComplexFourierField inputModes projected x
                vorticityCoordinate := by
  dsimp only
  simpa only [projectedPairing_complexCoordinateRealInner_conj_smul_left] using
    fullCubeProjectedNonlinearPairing_eq_velocityVorticityTensor
      inputRadius state zeroRow stateTransverse reality testModes
        (fun wave => star temporalWeight • testCoefficient wave)

/--
The same projected conservative pairing integrated over an actual time
interval with a complex temporal weight.  Fourier reality is consumed only
a.e.; zero-row and transversality laws retain the original whole path.
-/
theorem
    fullCubeProjectedNonlinearTemporalPairing_intervalIntegral_eq_velocityVorticityTensor
    (inputRadius : Nat)
    (path : Real → ComplexVorticityHilbertState)
    (start finish : Real)
    (startLeFinish : start ≤ finish)
    (testModes : Finset IntegerWavevector)
    (testCoefficient : IntegerWavevector → ComplexCoordinateVector)
    (temporalWeight : Real → Complex)
    (zeroRow : ∀ time ∈ Icc start finish, path time 0 = 0)
    (transverse : ∀ time ∈ Icc start finish,
      WholeStateTransverse (path time))
    (realityAE : ∀ᵐ time ∂volume,
      time ∈ Ioc start finish → FiniteStateFourierReality (path time)) :
    (∫ time in start..finish,
      ∑ wave ∈ testModes,
        complexCoordinateRealInner (testCoefficient wave)
          (temporalWeight time •
            wholeStateVorticityNonlinearCoefficientAt
              (complexSharpSupportProjection
                (integerWaveFrequencyCube inputRadius) (path time)) wave)) =
      ∫ time in start..finish,
        let projected := complexSharpSupportProjection
          (integerWaveFrequencyCube inputRadius) (path time)
        let source := rawSourceOfFiniteVorticityState
          (puncturedIntegerWaveFrequencyCube inputRadius) projected
        let weightedCoefficient :
            IntegerWavevector → ComplexCoordinateVector := fun wave =>
          star (temporalWeight time) • testCoefficient wave
        let weightedTest :=
          finiteRealComplexFourierField testModes weightedCoefficient
        ∫ x in ThreeDimensionalPeriodicUnitCellDivergence.physicalUnitCell,
          ∑ velocityCoordinate : Coordinate,
            ∑ vorticityCoordinate : Coordinate,
              (fderiv ℝ weightedTest x
                  (EuclideanSpace.single velocityCoordinate 1)
                    vorticityCoordinate -
                fderiv ℝ weightedTest x
                  (EuclideanSpace.single vorticityCoordinate 1)
                    velocityCoordinate) *
                physicalVelocity source x velocityCoordinate *
                finiteRealComplexFourierField
                  (puncturedIntegerWaveFrequencyCube inputRadius)
                  projected x vorticityCoordinate := by
  apply intervalIntegral.integral_congr_ae
  filter_upwards [realityAE] with time realityAt
  intro timeMem
  have timeIoc : time ∈ Ioc start finish := by
    rwa [uIoc_of_le startLeFinish] at timeMem
  have timeIcc : time ∈ Icc start finish :=
    ⟨timeIoc.1.le, timeIoc.2⟩
  exact fullCubeProjectedNonlinearTemporalPairing_eq_tensor
    inputRadius (path time) (zeroRow time timeIcc)
      (transverse time timeIcc) (realityAt timeIoc) testModes
        testCoefficient (temporalWeight time)

/-- The compact normalized spacetime cylinder used by recentered tensor tests. -/
abbrev Cylinder (timeLength spatialRadius : Real) :=
  Icc (0 : Real) timeLength ×
    Metric.closedBall (0 : PhysicalSpace) spatialRadius

private def scaledProjectedTensorTestRaw
    (scale start : Real)
    (center : PhysicalSpace)
    (testModes : Finset
      ThreeDimensionalPeriodicIntegerCharacterCoarseFilter.IntegerWavevector)
    (testCoefficient :
      ThreeDimensionalPeriodicIntegerCharacterCoarseFilter.IntegerWavevector →
        ComplexCoordinateVector)
    (temporalWeight : Real → Complex)
    (velocityCoordinate vorticityCoordinate : Coordinate)
    (scaledTime : Real) (scaledPoint : PhysicalSpace) : Real :=
  let actualTime := start + scale ^ 2 * scaledTime
  let actualPoint := center + scale • scaledPoint
  let weightedCoefficient :
      ThreeDimensionalPeriodicIntegerCharacterCoarseFilter.IntegerWavevector →
        ComplexCoordinateVector := fun wave =>
    star (temporalWeight actualTime) • testCoefficient wave
  let weightedTest :=
    finiteRealComplexFourierField testModes weightedCoefficient
  scale *
    (fderiv ℝ weightedTest actualPoint
          (EuclideanSpace.single velocityCoordinate 1)
          vorticityCoordinate -
      fderiv ℝ weightedTest actualPoint
          (EuclideanSpace.single vorticityCoordinate 1)
          velocityCoordinate)

private def scaledProjectedTensorTest
    (timeLength spatialRadius scale start : Real)
    (center : PhysicalSpace)
    (testModes : Finset
      ThreeDimensionalPeriodicIntegerCharacterCoarseFilter.IntegerWavevector)
    (testCoefficient :
      ThreeDimensionalPeriodicIntegerCharacterCoarseFilter.IntegerWavevector →
        ComplexCoordinateVector)
    (temporalWeight : Real → Complex)
    (velocityCoordinate vorticityCoordinate : Coordinate) :
    Cylinder timeLength spatialRadius → Real := fun point =>
  scaledProjectedTensorTestRaw scale start center testModes testCoefficient
    temporalWeight velocityCoordinate vorticityCoordinate point.1.1 point.2.1

/-- Physical velocity-vorticity tensor density tested by one finite Fourier
inventory and a complex temporal weight. -/
def projectedTensorRawDensity
    (testModes : Finset
      ThreeDimensionalPeriodicIntegerCharacterCoarseFilter.IntegerWavevector)
    (testCoefficient :
      ThreeDimensionalPeriodicIntegerCharacterCoarseFilter.IntegerWavevector →
        ComplexCoordinateVector)
    (temporalWeight : Real → Complex)
    (rawVelocity rawVorticity : Real → PhysicalSpace → PhysicalSpace)
    (time : Real) (x : PhysicalSpace) : Real :=
  let weightedCoefficient :
      ThreeDimensionalPeriodicIntegerCharacterCoarseFilter.IntegerWavevector →
        ComplexCoordinateVector := fun wave =>
    star (temporalWeight time) • testCoefficient wave
  let weightedTest :=
    finiteRealComplexFourierField testModes weightedCoefficient
  ∑ velocityCoordinate : Coordinate,
    ∑ vorticityCoordinate : Coordinate,
      (fderiv ℝ weightedTest x
            (EuclideanSpace.single velocityCoordinate 1)
            vorticityCoordinate -
        fderiv ℝ weightedTest x
            (EuclideanSpace.single vorticityCoordinate 1)
            velocityCoordinate) *
        rawVelocity time x velocityCoordinate *
        rawVorticity time x vorticityCoordinate

set_option maxHeartbeats 1000000 in
private theorem scaledProjectedTensorTest_continuous
    (timeLength spatialRadius scale start : Real)
    (center : PhysicalSpace)
    (testModes : Finset
      ThreeDimensionalPeriodicIntegerCharacterCoarseFilter.IntegerWavevector)
    (testCoefficient :
      ThreeDimensionalPeriodicIntegerCharacterCoarseFilter.IntegerWavevector →
        ComplexCoordinateVector)
    (temporalWeight : Real → Complex)
    (temporalContinuous : Continuous temporalWeight)
    (velocityCoordinate vorticityCoordinate : Coordinate) :
    Continuous
      (scaledProjectedTensorTest timeLength spatialRadius scale start center
        testModes testCoefficient temporalWeight velocityCoordinate
          vorticityCoordinate) := by
  unfold scaledProjectedTensorTest
  unfold scaledProjectedTensorTestRaw
  simp_rw [finiteRealComplexFourierField_coordinateDerivative]
  have actualTimeContinuous : Continuous
      (fun point : Cylinder timeLength spatialRadius =>
        start + scale ^ 2 * point.1.1) := by
    fun_prop
  have temporalStarContinuous : Continuous
      (fun point : Cylinder timeLength spatialRadius =>
        star (temporalWeight (start + scale ^ 2 * point.1.1))) := by
    exact Complex.continuous_conj.comp
      (temporalContinuous.comp actualTimeContinuous)
  have actualPointContinuous : Continuous
      (fun point : Cylinder timeLength spatialRadius =>
        center + scale • point.2.1) := by
    fun_prop
  have derivativeCoordinateContinuous
      (direction target : Coordinate) : Continuous
      (fun point : Cylinder timeLength spatialRadius =>
        finiteRealComplexFourierField testModes
            (angularDerivativeCoefficient
              (fun wave =>
                star (temporalWeight
                  (start + scale ^ 2 * point.1.1)) • testCoefficient wave)
              direction)
            (center + scale • point.2.1) target) := by
    unfold finiteRealComplexFourierField
    simp only [WithLp.ofLp_sum, Finset.sum_apply]
    apply continuous_finsetSum
    intro wave _waveMem
    have coefficientContinuous : Continuous
        (fun point : Cylinder timeLength spatialRadius =>
          angularDerivativeCoefficient
              (fun row =>
                star (temporalWeight
                  (start + scale ^ 2 * point.1.1)) • testCoefficient row)
              direction wave target) := by
      unfold angularDerivativeCoefficient
      simp only [Pi.smul_apply, smul_eq_mul]
      exact continuous_const.mul
        (temporalStarContinuous.mul continuous_const)
    have cosineContinuous : Continuous
        (fun point : Cylinder timeLength spatialRadius =>
          integerCosine wave (center + scale • point.2.1)) :=
      (integerCosine_contDiff wave).continuous.comp actualPointContinuous
    have sineContinuous : Continuous
        (fun point : Cylinder timeLength spatialRadius =>
          integerSine wave (center + scale • point.2.1)) :=
      (integerSine_contDiff wave).continuous.comp actualPointContinuous
    unfold realComplexFourierMode
    exact
      (cosineContinuous.mul
        (Complex.continuous_re.comp coefficientContinuous)).sub
      (sineContinuous.mul
        (Complex.continuous_im.comp coefficientContinuous))
  apply Continuous.const_mul
  apply Continuous.sub
  · exact derivativeCoordinateContinuous velocityCoordinate
      vorticityCoordinate
  · exact derivativeCoordinateContinuous vorticityCoordinate
      velocityCoordinate

/-- One coordinate of the scaled, recentered finite trigonometric tensor test
as a bounded continuous function on the normalized cylinder. -/
def scaledProjectedTensorBCF
    (timeLength spatialRadius scale start : Real)
    (center : PhysicalSpace)
    (testModes : Finset
      ThreeDimensionalPeriodicIntegerCharacterCoarseFilter.IntegerWavevector)
    (testCoefficient :
      ThreeDimensionalPeriodicIntegerCharacterCoarseFilter.IntegerWavevector →
        ComplexCoordinateVector)
    (temporalWeight : Real → Complex)
    (temporalContinuous : Continuous temporalWeight)
    (velocityCoordinate vorticityCoordinate : Coordinate) :
    BoundedContinuousFunction (Cylinder timeLength spatialRadius) Real :=
  BoundedContinuousFunction.mkOfCompact
    ⟨scaledProjectedTensorTest timeLength spatialRadius scale start center
      testModes testCoefficient temporalWeight velocityCoordinate
        vorticityCoordinate,
      scaledProjectedTensorTest_continuous timeLength spatialRadius scale start
        center testModes testCoefficient temporalWeight temporalContinuous
        velocityCoordinate vorticityCoordinate⟩

private theorem scaledProjectedTensorBCF_apply
    (timeLength spatialRadius scale start : Real)
    (center : PhysicalSpace)
    (testModes : Finset
      ThreeDimensionalPeriodicIntegerCharacterCoarseFilter.IntegerWavevector)
    (testCoefficient :
      ThreeDimensionalPeriodicIntegerCharacterCoarseFilter.IntegerWavevector →
        ComplexCoordinateVector)
    (temporalWeight : Real → Complex)
    (temporalContinuous : Continuous temporalWeight)
    (velocityCoordinate vorticityCoordinate : Coordinate)
    (point : Cylinder timeLength spatialRadius) :
    scaledProjectedTensorBCF timeLength spatialRadius scale start center
        testModes testCoefficient temporalWeight temporalContinuous
        velocityCoordinate vorticityCoordinate point =
      scaledProjectedTensorTest timeLength spatialRadius scale start center
        testModes testCoefficient temporalWeight velocityCoordinate
          vorticityCoordinate point := rfl

private theorem scaledProjectedTensorBCF_density_eq_scaleFour
    (timeLength spatialRadius scale start : Real)
    (center : PhysicalSpace)
    (testModes : Finset
      ThreeDimensionalPeriodicIntegerCharacterCoarseFilter.IntegerWavevector)
    (testCoefficient :
      ThreeDimensionalPeriodicIntegerCharacterCoarseFilter.IntegerWavevector →
        ComplexCoordinateVector)
    (temporalWeight : Real → Complex)
    (temporalContinuous : Continuous temporalWeight)
    (velocity vorticity : PhysicalSpace)
    (point : Cylinder timeLength spatialRadius) :
    let actualTime := start + scale ^ 2 * point.1.1
    let actualPoint := center + scale • point.2.1
    let weightedCoefficient :
        ThreeDimensionalPeriodicIntegerCharacterCoarseFilter.IntegerWavevector →
          ComplexCoordinateVector := fun wave =>
      star (temporalWeight actualTime) • testCoefficient wave
    let weightedTest :=
      finiteRealComplexFourierField testModes weightedCoefficient
    (∑ velocityCoordinate : Coordinate,
      ∑ vorticityCoordinate : Coordinate,
        scaledProjectedTensorBCF timeLength spatialRadius scale start center
            testModes testCoefficient temporalWeight temporalContinuous
            velocityCoordinate vorticityCoordinate point *
          (scale • velocity) velocityCoordinate *
          ((scale ^ 2 : Real) • vorticity) vorticityCoordinate) =
      scale ^ 4 *
        ∑ velocityCoordinate : Coordinate,
          ∑ vorticityCoordinate : Coordinate,
            (fderiv ℝ weightedTest actualPoint
                  (EuclideanSpace.single velocityCoordinate 1)
                  vorticityCoordinate -
              fderiv ℝ weightedTest actualPoint
                  (EuclideanSpace.single vorticityCoordinate 1)
                  velocityCoordinate) *
              velocity velocityCoordinate *
              vorticity vorticityCoordinate := by
  dsimp only
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro velocityCoordinate _velocityCoordinateMem
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro vorticityCoordinate _vorticityCoordinateMem
  rw [scaledProjectedTensorBCF_apply]
  unfold scaledProjectedTensorTest
  unfold scaledProjectedTensorTestRaw
  simp only [PiLp.smul_apply]
  ring

private noncomputable instance cylinder_isFiniteMeasure
    (timeLength spatialRadius : Real) :
    IsFiniteMeasure
      (volume : Measure (Cylinder timeLength spatialRadius)) := by
  letI : IsFiniteMeasure (volume : Measure (Icc (0 : Real) timeLength)) :=
    ⟨by
      rw [Measure.Subtype.volume_univ
        isCompact_Icc.measurableSet.nullMeasurableSet]
      exact isCompact_Icc.measure_lt_top⟩
  letI : IsFiniteMeasure
      (volume : Measure
        (Metric.closedBall (0 : PhysicalSpace) spatialRadius)) :=
    ⟨by
      rw [Measure.Subtype.volume_univ
        (isCompact_closedBall _ _).measurableSet.nullMeasurableSet]
      exact (isCompact_closedBall _ _).measure_lt_top⟩
  infer_instance

private theorem cylinder_bcf_integral_eq_subtype
    (timeLength spatialRadius : Real)
    (density : BoundedContinuousFunction
      (Cylinder timeLength spatialRadius) Real) :
    (∫ point : Cylinder timeLength spatialRadius, density point) =
      ∫ time : Icc (0 : Real) timeLength,
        ∫ x : Metric.closedBall (0 : PhysicalSpace) spatialRadius,
          density ⟨time, x⟩ := by
  letI : IsFiniteMeasure (volume : Measure (Icc (0 : Real) timeLength)) :=
    ⟨by
      rw [Measure.Subtype.volume_univ
        isCompact_Icc.measurableSet.nullMeasurableSet]
      exact isCompact_Icc.measure_lt_top⟩
  letI : IsFiniteMeasure
      (volume : Measure
        (Metric.closedBall (0 : PhysicalSpace) spatialRadius)) :=
    ⟨by
      rw [Measure.Subtype.volume_univ
        (isCompact_closedBall _ _).measurableSet.nullMeasurableSet]
      exact (isCompact_closedBall _ _).measure_lt_top⟩
  have densityIntegrable : Integrable
      (density : Cylinder timeLength spatialRadius → Real)
      ((volume : Measure (Icc (0 : Real) timeLength)).prod
        (volume : Measure
          (Metric.closedBall (0 : PhysicalSpace) spatialRadius))) :=
    BoundedContinuousFunction.integrable _ density
  rw [Measure.volume_eq_prod]
  exact integral_prod _ densityIntegrable

private theorem cylinder_integral_eq_interval_setIntegral
    (timeLength spatialRadius : Real)
    (timeLengthNonneg : 0 ≤ timeLength)
    (g : Real → PhysicalSpace → Real)
    (gContinuous : Continuous
      (fun point : Cylinder timeLength spatialRadius =>
        g point.1.1 point.2.1)) :
    (∫ point : Cylinder timeLength spatialRadius,
        g point.1.1 point.2.1) =
      ∫ time in (0 : Real)..timeLength,
        ∫ x in Metric.closedBall (0 : PhysicalSpace) spatialRadius,
          g time x := by
  letI : IsFiniteMeasure (volume : Measure (Icc (0 : Real) timeLength)) :=
    ⟨by
      rw [Measure.Subtype.volume_univ
        isCompact_Icc.measurableSet.nullMeasurableSet]
      exact isCompact_Icc.measure_lt_top⟩
  letI : IsFiniteMeasure
      (volume : Measure
        (Metric.closedBall (0 : PhysicalSpace) spatialRadius)) :=
    ⟨by
      rw [Measure.Subtype.volume_univ
        (isCompact_closedBall _ _).measurableSet.nullMeasurableSet]
      exact (isCompact_closedBall _ _).measure_lt_top⟩
  let cylinderFunction : Cylinder timeLength spatialRadius → Real :=
    fun point => g point.1.1 point.2.1
  have cylinderContinuous : Continuous cylinderFunction := by
    exact gContinuous
  let bounded : BoundedContinuousFunction
      (Cylinder timeLength spatialRadius) Real :=
    BoundedContinuousFunction.mkOfCompact
      ⟨cylinderFunction, cylinderContinuous⟩
  have cylinderIntegrable : Integrable cylinderFunction
      ((volume : Measure (Icc (0 : Real) timeLength)).prod
        (volume : Measure
          (Metric.closedBall (0 : PhysicalSpace) spatialRadius))) := by
    change Integrable
      (bounded : Cylinder timeLength spatialRadius → Real)
      ((volume : Measure (Icc (0 : Real) timeLength)).prod
        (volume : Measure
          (Metric.closedBall (0 : PhysicalSpace) spatialRadius)))
    exact BoundedContinuousFunction.integrable _ bounded
  change (∫ point : Cylinder timeLength spatialRadius,
    cylinderFunction point) = _
  rw [Measure.volume_eq_prod]
  rw [integral_prod _ cylinderIntegrable]
  simp only [cylinderFunction]
  have inner (time : Icc (0 : Real) timeLength) :
      (∫ x : Metric.closedBall (0 : PhysicalSpace) spatialRadius,
          g time.1 x.1) =
        ∫ x in Metric.closedBall (0 : PhysicalSpace) spatialRadius,
          g time.1 x := by
    rw [MeasureTheory.integral_subtype
      (isCompact_closedBall _ _).measurableSet]
  simp_rw [inner]
  rw [MeasureTheory.integral_subtype measurableSet_Icc
    (fun time =>
      ∫ x in Metric.closedBall (0 : PhysicalSpace) spatialRadius,
        g time x)]
  rw [intervalIntegral.integral_of_le timeLengthNonneg]
  exact MeasureTheory.integral_Icc_eq_integral_Ioc

private def scaledProjectedTensorPairedDensityBCF
    (timeLength spatialRadius scale start : Real)
    (center : PhysicalSpace)
    (testModes : Finset
      ThreeDimensionalPeriodicIntegerCharacterCoarseFilter.IntegerWavevector)
    (testCoefficient :
      ThreeDimensionalPeriodicIntegerCharacterCoarseFilter.IntegerWavevector →
        ComplexCoordinateVector)
    (temporalWeight : Real → Complex)
    (temporalContinuous : Continuous temporalWeight)
    (velocity vorticity : BoundedContinuousFunction
      (Cylinder timeLength spatialRadius) PhysicalSpace) :
    BoundedContinuousFunction (Cylinder timeLength spatialRadius) Real :=
  BoundedContinuousFunction.mkOfCompact
    ⟨fun point =>
      ∑ velocityCoordinate : Coordinate,
        ∑ vorticityCoordinate : Coordinate,
          scaledProjectedTensorBCF timeLength spatialRadius scale start center
              testModes testCoefficient temporalWeight temporalContinuous
              velocityCoordinate vorticityCoordinate point *
            velocity point velocityCoordinate *
            vorticity point vorticityCoordinate,
      by
        apply continuous_finsetSum
        intro velocityCoordinate _velocityCoordinateMem
        apply continuous_finsetSum
        intro vorticityCoordinate _vorticityCoordinateMem
        exact
          ((scaledProjectedTensorBCF timeLength spatialRadius scale start
              center testModes testCoefficient temporalWeight
              temporalContinuous velocityCoordinate vorticityCoordinate).continuous.mul
            ((PiLp.continuous_apply 2 (fun _ : Coordinate => Real)
              velocityCoordinate).comp velocity.continuous)).mul
            ((PiLp.continuous_apply 2 (fun _ : Coordinate => Real)
              vorticityCoordinate).comp vorticity.continuous)⟩

private theorem scaledProjectedTensorPairedDensityBCF_apply
    (timeLength spatialRadius scale start : Real)
    (center : PhysicalSpace)
    (testModes : Finset
      ThreeDimensionalPeriodicIntegerCharacterCoarseFilter.IntegerWavevector)
    (testCoefficient :
      ThreeDimensionalPeriodicIntegerCharacterCoarseFilter.IntegerWavevector →
        ComplexCoordinateVector)
    (temporalWeight : Real → Complex)
    (temporalContinuous : Continuous temporalWeight)
    (velocity vorticity : BoundedContinuousFunction
      (Cylinder timeLength spatialRadius) PhysicalSpace)
    (point : Cylinder timeLength spatialRadius) :
    scaledProjectedTensorPairedDensityBCF timeLength spatialRadius scale start
        center testModes testCoefficient temporalWeight temporalContinuous
        velocity vorticity point =
      ∑ velocityCoordinate : Coordinate,
        ∑ vorticityCoordinate : Coordinate,
          scaledProjectedTensorBCF timeLength spatialRadius scale start center
              testModes testCoefficient temporalWeight temporalContinuous
              velocityCoordinate vorticityCoordinate point *
            velocity point velocityCoordinate *
            vorticity point vorticityCoordinate := rfl

private theorem scaledProjectedTensorPairedDensity_integral_eq_scaleFour
    (timeLength spatialRadius scale start : Real)
    (center : PhysicalSpace)
    (testModes : Finset
      ThreeDimensionalPeriodicIntegerCharacterCoarseFilter.IntegerWavevector)
    (testCoefficient :
      ThreeDimensionalPeriodicIntegerCharacterCoarseFilter.IntegerWavevector →
        ComplexCoordinateVector)
    (temporalWeight : Real → Complex)
    (temporalContinuous : Continuous temporalWeight)
    (velocityProfile vorticityProfile : BoundedContinuousFunction
      (Cylinder timeLength spatialRadius) PhysicalSpace)
    (rawVelocity rawVorticity : Real → PhysicalSpace → PhysicalSpace)
    (velocityProfileEq : ∀ point,
      velocityProfile point = scale •
        rawVelocity (start + scale ^ 2 * point.1.1)
          (center + scale • point.2.1))
    (vorticityProfileEq : ∀ point,
      vorticityProfile point = (scale ^ 2 : Real) •
        rawVorticity (start + scale ^ 2 * point.1.1)
          (center + scale • point.2.1)) :
    (∫ point : Cylinder timeLength spatialRadius,
      ∑ velocityCoordinate : Coordinate,
        ∑ vorticityCoordinate : Coordinate,
          scaledProjectedTensorBCF timeLength spatialRadius scale start center
              testModes testCoefficient temporalWeight temporalContinuous
              velocityCoordinate vorticityCoordinate point *
            velocityProfile point velocityCoordinate *
            vorticityProfile point vorticityCoordinate) =
      scale ^ 4 *
        ∫ point : Cylinder timeLength spatialRadius,
          let actualTime := start + scale ^ 2 * point.1.1
          let actualPoint := center + scale • point.2.1
          let weightedCoefficient :
              ThreeDimensionalPeriodicIntegerCharacterCoarseFilter.IntegerWavevector →
                ComplexCoordinateVector := fun wave =>
            star (temporalWeight actualTime) • testCoefficient wave
          let weightedTest :=
            finiteRealComplexFourierField testModes weightedCoefficient
          ∑ velocityCoordinate : Coordinate,
            ∑ vorticityCoordinate : Coordinate,
              (fderiv ℝ weightedTest actualPoint
                    (EuclideanSpace.single velocityCoordinate 1)
                    vorticityCoordinate -
                fderiv ℝ weightedTest actualPoint
                    (EuclideanSpace.single vorticityCoordinate 1)
                    velocityCoordinate) *
                rawVelocity actualTime actualPoint velocityCoordinate *
                rawVorticity actualTime actualPoint vorticityCoordinate := by
  rw [← MeasureTheory.integral_const_mul]
  apply integral_congr_ae
  filter_upwards with point
  rw [velocityProfileEq point, vorticityProfileEq point]
  exact scaledProjectedTensorBCF_density_eq_scaleFour timeLength spatialRadius
    scale start center testModes testCoefficient temporalWeight
    temporalContinuous
    (rawVelocity (start + scale ^ 2 * point.1.1)
      (center + scale • point.2.1))
    (rawVorticity (start + scale ^ 2 * point.1.1)
      (center + scale • point.2.1)) point

private theorem parabolic_interval_change_start
    (value : Real → Real)
    (scale start timeLength : Real) :
    scale ^ 2 *
        (∫ scaledTime in (0 : Real)..timeLength,
          value (start + scale ^ 2 * scaledTime)) =
      ∫ actualTime in start..start + scale ^ 2 * timeLength,
        value actualTime := by
  have changed := intervalIntegral.smul_integral_comp_add_mul
    (f := value) (a := (0 : Real)) (b := timeLength)
    (c := scale ^ 2) start
  simpa only [smul_eq_mul, mul_zero, add_zero, add_comm] using changed

private theorem centeredBall_parabolic_change
    (value : PhysicalSpace → Real)
    (scale spatialRadius : Real)
    (scalePos : 0 < scale)
    (center : PhysicalSpace) :
    scale ^ 3 *
        (∫ scaledPoint in Metric.closedBall (0 : PhysicalSpace) spatialRadius,
          value (center + scale • scaledPoint)) =
      ∫ displacement in
          scale • Metric.closedBall (0 : PhysicalSpace) spatialRadius,
        value (center + displacement) := by
  have changed := Measure.setIntegral_comp_smul_of_pos
    (volume : Measure PhysicalSpace) (fun displacement =>
      value (center + displacement))
      (Metric.closedBall (0 : PhysicalSpace) spatialRadius) scalePos
  have dimension : Module.finrank Real PhysicalSpace = 3 := by
    simp [PhysicalSpace, Coordinate]
  have changed' :
      (∫ scaledPoint in Metric.closedBall (0 : PhysicalSpace) spatialRadius,
          value (center + scale • scaledPoint)) =
        (scale ^ 3)⁻¹ *
          ∫ displacement in
              scale • Metric.closedBall (0 : PhysicalSpace) spatialRadius,
            value (center + displacement) := by
    rw [dimension] at changed
    simpa only [smul_eq_mul] using changed
  calc
    scale ^ 3 *
        (∫ scaledPoint in Metric.closedBall (0 : PhysicalSpace) spatialRadius,
          value (center + scale • scaledPoint)) =
      scale ^ 3 * ((scale ^ 3)⁻¹ *
          ∫ displacement in
              scale • Metric.closedBall (0 : PhysicalSpace) spatialRadius,
            value (center + displacement)) := by rw [changed']
    _ = _ := by
      rw [← mul_assoc, mul_inv_cancel₀ (pow_ne_zero 3 scalePos.ne'), one_mul]

private theorem centeredBall_parabolic_change_actualSet
    (value : PhysicalSpace → Real)
    (scale spatialRadius : Real)
    (scalePos : 0 < scale)
    (center : PhysicalSpace) :
    scale ^ 3 *
        (∫ scaledPoint in Metric.closedBall (0 : PhysicalSpace) spatialRadius,
          value (center + scale • scaledPoint)) =
      ∫ actualPoint in
          (fun x : PhysicalSpace => x - center) ⁻¹'
            (scale • Metric.closedBall (0 : PhysicalSpace) spatialRadius),
        value actualPoint := by
  rw [centeredBall_parabolic_change value scale spatialRadius scalePos center]
  let translate : PhysicalSpace ≃ᵐ PhysicalSpace :=
    MeasurableEquiv.addRight center
  have translatePreserving : MeasurePreserving
      (translate : PhysicalSpace → PhysicalSpace) volume volume := by
    simpa [translate] using measurePreserving_add_right volume center
  have translated := translatePreserving.setIntegral_preimage_emb
    translate.measurableEmbedding value
    ((translate.symm : PhysicalSpace → PhysicalSpace) ⁻¹'
      (scale • Metric.closedBall (0 : PhysicalSpace) spatialRadius))
  have sourceSet :
      translate ⁻¹'
          ((translate.symm : PhysicalSpace → PhysicalSpace) ⁻¹'
            (scale • Metric.closedBall (0 : PhysicalSpace) spatialRadius)) =
        scale • Metric.closedBall (0 : PhysicalSpace) spatialRadius := by
    ext x
    simp [translate]
  rw [sourceSet] at translated
  simpa [translate, sub_eq_add_neg, add_comm] using translated

private theorem parabolicTensorAction_ball_change
    (value : Real → PhysicalSpace → Real)
    (scale start timeLength spatialRadius : Real)
    (scalePos : 0 < scale)
    (center : PhysicalSpace) :
    (∫ scaledTime in (0 : Real)..timeLength,
      scale ^ 4 *
        ∫ scaledPoint in
            Metric.closedBall (0 : PhysicalSpace) spatialRadius,
          value (start + scale ^ 2 * scaledTime)
            (center + scale • scaledPoint)) =
      scale⁻¹ *
        ∫ actualTime in start..start + scale ^ 2 * timeLength,
          ∫ actualPoint in
              (fun x : PhysicalSpace => x - center) ⁻¹'
                (scale • Metric.closedBall
                  (0 : PhysicalSpace) spatialRadius),
            value actualTime actualPoint := by
  let actualSpatialIntegral : Real → Real := fun actualTime =>
    ∫ actualPoint in
        (fun x : PhysicalSpace => x - center) ⁻¹'
          (scale • Metric.closedBall (0 : PhysicalSpace) spatialRadius),
      value actualTime actualPoint
  have spatialChange (scaledTime : Real) :
      scale ^ 4 *
          (∫ scaledPoint in
              Metric.closedBall (0 : PhysicalSpace) spatialRadius,
            value (start + scale ^ 2 * scaledTime)
              (center + scale • scaledPoint)) =
        scale * actualSpatialIntegral
          (start + scale ^ 2 * scaledTime) := by
    calc
      _ = scale *
          (scale ^ 3 *
            ∫ scaledPoint in
                Metric.closedBall (0 : PhysicalSpace) spatialRadius,
              value (start + scale ^ 2 * scaledTime)
                (center + scale • scaledPoint)) := by ring
      _ = _ := by
        rw [centeredBall_parabolic_change_actualSet
          (value (start + scale ^ 2 * scaledTime)) scale spatialRadius
          scalePos center]
  have timeChange := parabolic_interval_change_start
    actualSpatialIntegral scale start timeLength
  calc
    (∫ scaledTime in (0 : Real)..timeLength,
      scale ^ 4 *
        ∫ scaledPoint in
            Metric.closedBall (0 : PhysicalSpace) spatialRadius,
          value (start + scale ^ 2 * scaledTime)
            (center + scale • scaledPoint)) =
      ∫ scaledTime in (0 : Real)..timeLength,
        scale * actualSpatialIntegral
          (start + scale ^ 2 * scaledTime) := by
        apply intervalIntegral.integral_congr
        intro scaledTime _scaledTimeMem
        exact spatialChange scaledTime
    _ = scale *
        ∫ scaledTime in (0 : Real)..timeLength,
          actualSpatialIntegral
            (start + scale ^ 2 * scaledTime) := by
      rw [intervalIntegral.integral_const_mul]
    _ = scale⁻¹ *
        (scale ^ 2 *
          ∫ scaledTime in (0 : Real)..timeLength,
            actualSpatialIntegral
              (start + scale ^ 2 * scaledTime)) := by
      field_simp [scalePos.ne']
    _ = scale⁻¹ *
        ∫ actualTime in start..start + scale ^ 2 * timeLength,
          actualSpatialIntegral actualTime := by rw [timeChange]
    _ = _ := by rfl

private theorem scaledProjectedTensor_cylinder_eq_restrictedActual
    (timeLength spatialRadius scale start : Real)
    (timeLengthNonneg : 0 ≤ timeLength)
    (scalePos : 0 < scale)
    (center : PhysicalSpace)
    (testModes : Finset
      ThreeDimensionalPeriodicIntegerCharacterCoarseFilter.IntegerWavevector)
    (testCoefficient :
      ThreeDimensionalPeriodicIntegerCharacterCoarseFilter.IntegerWavevector →
        ComplexCoordinateVector)
    (temporalWeight : Real → Complex)
    (temporalContinuous : Continuous temporalWeight)
    (velocityProfile vorticityProfile : BoundedContinuousFunction
      (Cylinder timeLength spatialRadius) PhysicalSpace)
    (rawVelocity rawVorticity : Real → PhysicalSpace → PhysicalSpace)
    (velocityProfileEq : ∀ point,
      velocityProfile point = scale •
        rawVelocity (start + scale ^ 2 * point.1.1)
          (center + scale • point.2.1))
    (vorticityProfileEq : ∀ point,
      vorticityProfile point = (scale ^ 2 : Real) •
        rawVorticity (start + scale ^ 2 * point.1.1)
          (center + scale • point.2.1)) :
    (∫ point : Cylinder timeLength spatialRadius,
      ∑ velocityCoordinate : Coordinate,
        ∑ vorticityCoordinate : Coordinate,
          scaledProjectedTensorBCF timeLength spatialRadius scale start center
              testModes testCoefficient temporalWeight temporalContinuous
              velocityCoordinate vorticityCoordinate point *
            velocityProfile point velocityCoordinate *
            vorticityProfile point vorticityCoordinate) =
      scale⁻¹ *
        ∫ actualTime in start..start + scale ^ 2 * timeLength,
          ∫ actualPoint in
              (fun x : PhysicalSpace => x - center) ⁻¹'
                (scale • Metric.closedBall
                  (0 : PhysicalSpace) spatialRadius),
            projectedTensorRawDensity testModes testCoefficient
              temporalWeight rawVelocity rawVorticity actualTime
                actualPoint := by
  have scaledFactor :=
    scaledProjectedTensorPairedDensity_integral_eq_scaleFour timeLength
      spatialRadius scale start center testModes testCoefficient
      temporalWeight temporalContinuous velocityProfile vorticityProfile
      rawVelocity rawVorticity velocityProfileEq vorticityProfileEq
  let pairedDensity := scaledProjectedTensorPairedDensityBCF timeLength
    spatialRadius scale start center testModes testCoefficient temporalWeight
      temporalContinuous velocityProfile vorticityProfile
  have rawDensityContinuous : Continuous
      (fun point : Cylinder timeLength spatialRadius =>
        projectedTensorRawDensity testModes testCoefficient temporalWeight
          rawVelocity rawVorticity
          (start + scale ^ 2 * point.1.1)
          (center + scale • point.2.1)) := by
    have pointwise (point : Cylinder timeLength spatialRadius) :
        projectedTensorRawDensity testModes testCoefficient temporalWeight
            rawVelocity rawVorticity
            (start + scale ^ 2 * point.1.1)
            (center + scale • point.2.1) =
          (scale ^ 4)⁻¹ * pairedDensity point := by
      have factor := scaledProjectedTensorBCF_density_eq_scaleFour
        timeLength spatialRadius scale start center testModes testCoefficient
        temporalWeight temporalContinuous
        (rawVelocity (start + scale ^ 2 * point.1.1)
          (center + scale • point.2.1))
        (rawVorticity (start + scale ^ 2 * point.1.1)
          (center + scale • point.2.1)) point
      have pairedEq : pairedDensity point =
          scale ^ 4 *
            projectedTensorRawDensity testModes testCoefficient
              temporalWeight rawVelocity rawVorticity
              (start + scale ^ 2 * point.1.1)
              (center + scale • point.2.1) := by
        dsimp only [pairedDensity]
        rw [scaledProjectedTensorPairedDensityBCF_apply,
          velocityProfileEq point, vorticityProfileEq point]
        simpa only [projectedTensorRawDensity] using factor
      rw [pairedEq]
      field_simp [scalePos.ne']
    rw [show (fun point : Cylinder timeLength spatialRadius =>
        projectedTensorRawDensity testModes testCoefficient temporalWeight
          rawVelocity rawVorticity
          (start + scale ^ 2 * point.1.1)
          (center + scale • point.2.1)) =
        fun point => (scale ^ 4)⁻¹ * pairedDensity point by
      funext point
      exact pointwise point]
    exact continuous_const.mul pairedDensity.continuous
  have cylinderChange := cylinder_integral_eq_interval_setIntegral
    timeLength spatialRadius timeLengthNonneg
    (fun scaledTime scaledPoint =>
      projectedTensorRawDensity testModes testCoefficient temporalWeight
        rawVelocity rawVorticity
        (start + scale ^ 2 * scaledTime) (center + scale • scaledPoint))
    rawDensityContinuous
  calc
    _ = scale ^ 4 *
        ∫ point : Cylinder timeLength spatialRadius,
          projectedTensorRawDensity testModes testCoefficient temporalWeight
            rawVelocity rawVorticity
            (start + scale ^ 2 * point.1.1)
            (center + scale • point.2.1) := by
      simpa only [projectedTensorRawDensity] using scaledFactor
    _ = ∫ scaledTime in (0 : Real)..timeLength,
        scale ^ 4 *
          ∫ scaledPoint in
              Metric.closedBall (0 : PhysicalSpace) spatialRadius,
            projectedTensorRawDensity testModes testCoefficient
              temporalWeight rawVelocity rawVorticity
              (start + scale ^ 2 * scaledTime)
              (center + scale • scaledPoint) := by
      rw [cylinderChange]
      rw [intervalIntegral.integral_const_mul]
    _ = _ := parabolicTensorAction_ball_change
      (projectedTensorRawDensity testModes testCoefficient temporalWeight
        rawVelocity rawVorticity)
      scale start timeLength spatialRadius scalePos center

private theorem f3RecenteredTensorCylinder_integral_eq_restricted985RHS
    (timeLength spatialRadius scale start timeCenter : Real)
    (timeLengthNonneg : 0 ≤ timeLength)
    (scalePos : 0 < scale)
    (center : PhysicalSpace)
    (inputRadius testRadius : Nat)
    (path : Real → ComplexVorticityHilbertState)
    (spatialTest : Coordinate → SchwartzMap Real Complex)
    (temporalTest : SchwartzMap Real Complex)
    (testCoordinate : Coordinate)
    (velocityProfile vorticityProfile : BoundedContinuousFunction
      (Cylinder timeLength spatialRadius) PhysicalSpace)
    (velocityProfileEq : ∀ point,
      let actualTime := start + scale ^ 2 * point.1.1
      let projected := complexSharpSupportProjection
        (integerWaveFrequencyCube inputRadius) (path actualTime)
      let source := rawSourceOfFiniteVorticityState
        (puncturedIntegerWaveFrequencyCube inputRadius) projected
      velocityProfile point = scale •
        physicalVelocity source (center + scale • point.2.1))
    (vorticityProfileEq : ∀ point,
      let actualTime := start + scale ^ 2 * point.1.1
      let projected := complexSharpSupportProjection
        (integerWaveFrequencyCube inputRadius) (path actualTime)
      vorticityProfile point = (scale ^ 2 : Real) •
        finiteRealComplexFourierField
          (puncturedIntegerWaveFrequencyCube inputRadius) projected
          (center + scale • point.2.1)) :
    let testModes := puncturedIntegerWaveFrequencyCube testRadius
    let testCoefficient :
        ThreeDimensionalPeriodicIntegerCharacterCoarseFilter.IntegerWavevector →
          ComplexCoordinateVector := fun wave =>
      Pi.single testCoordinate
        (recenteredTensorSchwartzFourierCoefficient spatialTest scale
          scalePos.ne' center wave)
    let temporalWeight : Real → Complex := fun time =>
      temporalTest ((time - timeCenter) / scale ^ 2)
    let projected : Real → ComplexVorticityHilbertState := fun time =>
      complexSharpSupportProjection
        (integerWaveFrequencyCube inputRadius) (path time)
    let rawVelocity : Real → PhysicalSpace → PhysicalSpace := fun time =>
      physicalVelocity (rawSourceOfFiniteVorticityState
        (puncturedIntegerWaveFrequencyCube inputRadius) (projected time))
    let rawVorticity : Real → PhysicalSpace → PhysicalSpace := fun time =>
      finiteRealComplexFourierField
        (puncturedIntegerWaveFrequencyCube inputRadius) (projected time)
    let temporalContinuous : Continuous temporalWeight := by
      dsimp only [temporalWeight]
      fun_prop
    (∫ point : Cylinder timeLength spatialRadius,
      ∑ velocityCoordinate : Coordinate,
        ∑ vorticityCoordinate : Coordinate,
          scaledProjectedTensorBCF timeLength spatialRadius scale start center
              testModes testCoefficient temporalWeight temporalContinuous
              velocityCoordinate vorticityCoordinate point *
            velocityProfile point velocityCoordinate *
            vorticityProfile point vorticityCoordinate) =
      scale⁻¹ *
        ∫ actualTime in start..start + scale ^ 2 * timeLength,
          ∫ actualPoint in
              (fun x : PhysicalSpace => x - center) ⁻¹'
                (scale • Metric.closedBall
                  (0 : PhysicalSpace) spatialRadius),
            projectedTensorRawDensity testModes testCoefficient
              temporalWeight rawVelocity rawVorticity actualTime
                actualPoint := by
  dsimp only
  apply scaledProjectedTensor_cylinder_eq_restrictedActual timeLength
    spatialRadius scale start timeLengthNonneg scalePos center
      (puncturedIntegerWaveFrequencyCube testRadius)
      (fun wave => Pi.single testCoordinate
        (recenteredTensorSchwartzFourierCoefficient spatialTest scale
          scalePos.ne' center wave))
      (fun time => temporalTest ((time - timeCenter) / scale ^ 2))
      (by fun_prop) velocityProfile vorticityProfile
      (fun time =>
        physicalVelocity (rawSourceOfFiniteVorticityState
          (puncturedIntegerWaveFrequencyCube inputRadius)
          (complexSharpSupportProjection
            (integerWaveFrequencyCube inputRadius) (path time))))
      (fun time =>
        finiteRealComplexFourierField
          (puncturedIntegerWaveFrequencyCube inputRadius)
          (complexSharpSupportProjection
            (integerWaveFrequencyCube inputRadius) (path time)))
  · intro point
    simpa only using velocityProfileEq point
  · intro point
    simpa only using vorticityProfileEq point

private theorem puncturedProjection_reality
    (radius : Nat)
    (state : ComplexVorticityHilbertState)
    (reality : FiniteStateFourierReality state) :
    FiniteStateFourierReality
      (complexSharpSupportProjection
        (puncturedIntegerWaveFrequencyCube radius) state) := by
  intro wave
  by_cases waveMem : wave ∈ puncturedIntegerWaveFrequencyCube radius
  · have negMem :=
      puncturedIntegerWaveFrequencyCube_waveNeg_mem radius waveMem
    simp only [complexSharpSupportProjection_apply, waveMem, negMem]
    exact reality wave
  · have negNotMem :
        waveNeg wave ∉ puncturedIntegerWaveFrequencyCube radius := by
      intro negMem
      have reflected :=
        puncturedIntegerWaveFrequencyCube_waveNeg_mem radius negMem
      exact waveMem (by simpa using reflected)
    simp [complexSharpSupportProjection_apply, waveMem, negNotMem]

private theorem rawPuncturedProjection_physicalVelocity_eq_finiteField
    (radius : Nat)
    (state : ComplexVorticityHilbertState)
    (stateTransverse : WholeStateTransverse state)
    (reality : FiniteStateFourierReality state) :
    let modes := puncturedIntegerWaveFrequencyCube radius
    let projected := complexSharpSupportProjection modes state
    physicalVelocity (rawSourceOfFiniteVorticityState modes projected) =
      finiteRealComplexFourierField modes
        (finiteStateVelocityCoefficient state) := by
  dsimp only
  let modes := puncturedIntegerWaveFrequencyCube radius
  let projected := complexSharpSupportProjection modes state
  let source := rawSourceOfFiniteVorticityState modes projected
  have zeroNotMem : (0 : IntegerWavevector) ∉ modes := by
    exact zero_not_mem_puncturedIntegerWaveFrequencyCube radius
  have negClosed : ∀ wave ∈ modes, waveNeg wave ∈ modes := by
    intro wave waveMem
    exact puncturedIntegerWaveFrequencyCube_waveNeg_mem radius waveMem
  have supported : ∀ wave, wave ∉ modes → projected wave = 0 := by
    intro wave waveNotMem
    simp [projected, complexSharpSupportProjection_apply, waveNotMem]
  have transverse : ∀ wave ∈ modes,
      complexWavevector wave ⬝ᵥ projected wave = 0 := by
    intro wave waveMem
    simp only [projected, complexSharpSupportProjection_apply, waveMem]
    exact stateTransverse wave
  have projectedReality : FiniteStateFourierReality projected := by
    simpa only [projected, modes] using
      puncturedProjection_reality radius state reality
  have supportEq : generatedSupport source = modes := by
    simpa only [source] using
      rawSourceOfFiniteVorticityState_generatedSupport
        modes zeroNotMem negClosed projected
  have compiledEq :
      generatedComplexVorticityState source (generatedSupport source) =
        projected := by
    simpa only [source] using
      generatedComplexVorticityState_rawSourceOfFinitePhysicalState
        modes zeroNotMem negClosed projected supported transverse
          projectedReality
  have generatedVorticityEq (wave : IntegerWavevector) :
      generatedVorticityCoefficient source wave = projected wave := by
    by_cases waveMem : wave ∈ modes
    · have supportMem : wave ∈ generatedSupport source := by
        simpa only [supportEq] using waveMem
      have applied := congrArg
        (fun compiled : ComplexVorticityHilbertState => compiled wave)
        compiledEq
      simpa only [generatedComplexVorticityState_apply,
        if_pos supportMem] using applied
    · rw [generatedVorticityCoefficient_eq_zero_of_not_mem]
      · exact (supported wave waveMem).symm
      · simpa only [supportEq] using waveMem
  funext x
  unfold physicalVelocity finiteRealComplexFourierField
  rw [supportEq]
  apply Finset.sum_congr rfl
  intro wave waveMem
  congr 1
  unfold generatedVelocityCoefficient finiteStateVelocityCoefficient
  rw [generatedVorticityEq]
  rw [show projected wave = state wave by
    simp [projected, complexSharpSupportProjection_apply, waveMem]]

private theorem finiteVelocityField_cube_eq_punctured
    (radius : Nat)
    (state : ComplexVorticityHilbertState) :
    finiteRealComplexFourierField (integerWaveFrequencyCube radius)
        (finiteStateVelocityCoefficient state) =
      finiteRealComplexFourierField
        (puncturedIntegerWaveFrequencyCube radius)
        (finiteStateVelocityCoefficient state) := by
  funext x
  unfold puncturedIntegerWaveFrequencyCube
  unfold finiteRealComplexFourierField
  have zeroMem : (0 : IntegerWavevector) ∈
      integerWaveFrequencyCube radius := by
    simp [integerWaveFrequencyCube]
  have zeroTerm :
      realComplexFourierMode (0 : IntegerWavevector)
          (finiteStateVelocityCoefficient state 0) x = 0 := by
    simp [finiteStateVelocityCoefficient, realComplexFourierMode]
  calc
    (∑ wave ∈ integerWaveFrequencyCube radius,
        realComplexFourierMode wave
          (finiteStateVelocityCoefficient state wave) x) =
      (∑ wave ∈ (integerWaveFrequencyCube radius).erase 0,
          realComplexFourierMode wave
            (finiteStateVelocityCoefficient state wave) x) +
        realComplexFourierMode 0
          (finiteStateVelocityCoefficient state 0) x := by
      exact (Finset.sum_erase_add
        (integerWaveFrequencyCube radius)
        (fun wave => realComplexFourierMode wave
          (finiteStateVelocityCoefficient state wave) x) zeroMem).symm
    _ = _ := by rw [zeroTerm, add_zero]

private theorem rawFullCubeProjection_physicalVelocity_eq_cubeFiniteField
    (radius : Nat)
    (state : ComplexVorticityHilbertState)
    (zeroRow : state 0 = 0)
    (stateTransverse : WholeStateTransverse state)
    (reality : FiniteStateFourierReality state) :
    let fullModes := integerWaveFrequencyCube radius
    let inputModes := puncturedIntegerWaveFrequencyCube radius
    let projected := complexSharpSupportProjection fullModes state
    physicalVelocity
        (rawSourceOfFiniteVorticityState inputModes projected) =
      finiteRealComplexFourierField fullModes
        (finiteStateVelocityCoefficient state) := by
  dsimp only
  have projectionEq :
      complexSharpSupportProjection
          (puncturedIntegerWaveFrequencyCube radius) state =
        complexSharpSupportProjection
          (integerWaveFrequencyCube radius) state := by
    apply lp.ext
    funext wave
    by_cases waveZero : wave = 0
    · subst wave
      simp [puncturedIntegerWaveFrequencyCube,
        complexSharpSupportProjection_apply, zeroRow]
    · by_cases waveMem : wave ∈ integerWaveFrequencyCube radius <;>
        simp [puncturedIntegerWaveFrequencyCube,
          complexSharpSupportProjection_apply, waveZero, waveMem]
  have rawEq := rawPuncturedProjection_physicalVelocity_eq_finiteField
    radius state stateTransverse reality
  dsimp only at rawEq
  rw [projectionEq] at rawEq
  calc
    physicalVelocity
        (rawSourceOfFiniteVorticityState
          (puncturedIntegerWaveFrequencyCube radius)
          (complexSharpSupportProjection
            (integerWaveFrequencyCube radius) state)) =
      finiteRealComplexFourierField
        (puncturedIntegerWaveFrequencyCube radius)
        (finiteStateVelocityCoefficient state) := rawEq
    _ = finiteRealComplexFourierField
        (integerWaveFrequencyCube radius)
        (finiteStateVelocityCoefficient state) :=
      (finiteVelocityField_cube_eq_punctured radius state).symm

private theorem finiteVorticityField_cube_eq_punctured_of_zero
    (radius : Nat)
    (state : ComplexVorticityHilbertState)
    (zeroRow : state 0 = 0) :
    finiteRealComplexFourierField (integerWaveFrequencyCube radius) state =
      finiteRealComplexFourierField
        (puncturedIntegerWaveFrequencyCube radius) state := by
  funext x
  unfold puncturedIntegerWaveFrequencyCube
  unfold finiteRealComplexFourierField
  have zeroMem : (0 : IntegerWavevector) ∈
      integerWaveFrequencyCube radius := by
    simp [integerWaveFrequencyCube]
  have zeroTerm :
      realComplexFourierMode (0 : IntegerWavevector) (state 0) x = 0 := by
    rw [zeroRow]
    simp [realComplexFourierMode]
  calc
    (∑ wave ∈ integerWaveFrequencyCube radius,
        realComplexFourierMode wave (state wave) x) =
      (∑ wave ∈ (integerWaveFrequencyCube radius).erase 0,
          realComplexFourierMode wave (state wave) x) +
        realComplexFourierMode 0 (state 0) x := by
      exact (Finset.sum_erase_add
        (integerWaveFrequencyCube radius)
        (fun wave => realComplexFourierMode wave (state wave) x)
        zeroMem).symm
    _ = _ := by rw [zeroTerm, add_zero]

private theorem puncturedProjection_vorticityField_eq_fullCubeField
    (radius : Nat)
    (state : ComplexVorticityHilbertState)
    (zeroRow : state 0 = 0) :
    finiteRealComplexFourierField
        (puncturedIntegerWaveFrequencyCube radius)
        (complexSharpSupportProjection
          (integerWaveFrequencyCube radius) state) =
      finiteRealComplexFourierField
        (integerWaveFrequencyCube radius) state := by
  calc
    finiteRealComplexFourierField
        (puncturedIntegerWaveFrequencyCube radius)
        (complexSharpSupportProjection
          (integerWaveFrequencyCube radius) state) =
      finiteRealComplexFourierField
        (puncturedIntegerWaveFrequencyCube radius) state := by
      funext x
      unfold finiteRealComplexFourierField
      apply Finset.sum_congr rfl
      intro wave waveMem
      congr 1
      have fullMem : wave ∈ integerWaveFrequencyCube radius := by
        exact Finset.mem_of_mem_erase waveMem
      simp [complexSharpSupportProjection_apply, fullMem]
    _ = finiteRealComplexFourierField
        (integerWaveFrequencyCube radius) state :=
      (finiteVorticityField_cube_eq_punctured_of_zero
        radius state zeroRow).symm

set_option maxHeartbeats 1000000 in
private theorem f3RecenteredTensorFullCubeProfiles_integral_eq_restricted985RHS
    (timeLength spatialRadius scale start timeCenter : Real)
    (timeLengthNonneg : 0 ≤ timeLength)
    (scalePos : 0 < scale)
    (center : PhysicalSpace)
    (inputRadius testRadius : Nat)
    (path : Real → ComplexVorticityHilbertState)
    (zeroRow : ∀ time, path time 0 = 0)
    (stateTransverse : ∀ time, WholeStateTransverse (path time))
    (realityAE : ∀ᵐ time ∂volume,
      time ∈ Ioc start (start + scale ^ 2 * timeLength) →
        FiniteStateFourierReality (path time))
    (spatialTest : Coordinate → SchwartzMap Real Complex)
    (temporalTest : SchwartzMap Real Complex)
    (testCoordinate : Coordinate)
    (velocityProfile vorticityProfile : BoundedContinuousFunction
      (Cylinder timeLength spatialRadius) PhysicalSpace)
    (velocityProfileEq : ∀ point,
      let actualTime := start + scale ^ 2 * point.1.1
      velocityProfile point = scale •
        finiteRealComplexFourierField
          (integerWaveFrequencyCube inputRadius)
          (finiteStateVelocityCoefficient (path actualTime))
          (center + scale • point.2.1))
    (vorticityProfileEq : ∀ point,
      let actualTime := start + scale ^ 2 * point.1.1
      vorticityProfile point = (scale ^ 2 : Real) •
        finiteRealComplexFourierField
          (integerWaveFrequencyCube inputRadius) (path actualTime)
          (center + scale • point.2.1)) :
    let testModes := puncturedIntegerWaveFrequencyCube testRadius
    let testCoefficient :
        ThreeDimensionalPeriodicIntegerCharacterCoarseFilter.IntegerWavevector →
          ComplexCoordinateVector := fun wave =>
      Pi.single testCoordinate
        (recenteredTensorSchwartzFourierCoefficient spatialTest scale
          scalePos.ne' center wave)
    let temporalWeight : Real → Complex := fun time =>
      temporalTest ((time - timeCenter) / scale ^ 2)
    let projected : Real → ComplexVorticityHilbertState := fun time =>
      complexSharpSupportProjection
        (integerWaveFrequencyCube inputRadius) (path time)
    let rawVelocity : Real → PhysicalSpace → PhysicalSpace := fun time =>
      physicalVelocity (rawSourceOfFiniteVorticityState
        (puncturedIntegerWaveFrequencyCube inputRadius) (projected time))
    let rawVorticity : Real → PhysicalSpace → PhysicalSpace := fun time =>
      finiteRealComplexFourierField
        (puncturedIntegerWaveFrequencyCube inputRadius) (projected time)
    let temporalContinuous : Continuous temporalWeight := by
      dsimp only [temporalWeight]
      fun_prop
    (∫ point : Cylinder timeLength spatialRadius,
      ∑ velocityCoordinate : Coordinate,
        ∑ vorticityCoordinate : Coordinate,
          scaledProjectedTensorBCF timeLength spatialRadius scale start center
              testModes testCoefficient temporalWeight temporalContinuous
              velocityCoordinate vorticityCoordinate point *
            velocityProfile point velocityCoordinate *
            vorticityProfile point vorticityCoordinate) =
      scale⁻¹ *
        ∫ actualTime in start..start + scale ^ 2 * timeLength,
          ∫ actualPoint in
              (fun x : PhysicalSpace => x - center) ⁻¹'
                (scale • Metric.closedBall
                  (0 : PhysicalSpace) spatialRadius),
            projectedTensorRawDensity testModes testCoefficient
              temporalWeight rawVelocity rawVorticity actualTime
                actualPoint := by
  dsimp only
  let cubeVelocity : Real → PhysicalSpace → PhysicalSpace := fun time =>
    finiteRealComplexFourierField
      (integerWaveFrequencyCube inputRadius)
      (finiteStateVelocityCoefficient (path time))
  let cubeVorticity : Real → PhysicalSpace → PhysicalSpace := fun time =>
    finiteRealComplexFourierField
      (integerWaveFrequencyCube inputRadius) (path time)
  have finiteFieldIdentity :
      (∫ point : Cylinder timeLength spatialRadius,
        ∑ velocityCoordinate : Coordinate,
          ∑ vorticityCoordinate : Coordinate,
            scaledProjectedTensorBCF timeLength spatialRadius scale start
                center (puncturedIntegerWaveFrequencyCube testRadius)
                (fun wave => Pi.single testCoordinate
                  (recenteredTensorSchwartzFourierCoefficient spatialTest
                    scale scalePos.ne' center wave))
                (fun time => temporalTest
                  ((time - timeCenter) / scale ^ 2))
                (by fun_prop) velocityCoordinate vorticityCoordinate point *
              velocityProfile point velocityCoordinate *
              vorticityProfile point vorticityCoordinate) =
        scale⁻¹ *
          ∫ actualTime in start..start + scale ^ 2 * timeLength,
            ∫ actualPoint in
                (fun x : PhysicalSpace => x - center) ⁻¹'
                  (scale • Metric.closedBall
                    (0 : PhysicalSpace) spatialRadius),
              projectedTensorRawDensity
                (puncturedIntegerWaveFrequencyCube testRadius)
                (fun wave => Pi.single testCoordinate
                  (recenteredTensorSchwartzFourierCoefficient spatialTest
                    scale scalePos.ne' center wave))
                (fun time => temporalTest
                  ((time - timeCenter) / scale ^ 2))
                cubeVelocity cubeVorticity actualTime actualPoint := by
    apply scaledProjectedTensor_cylinder_eq_restrictedActual timeLength
      spatialRadius scale start timeLengthNonneg scalePos center
      (puncturedIntegerWaveFrequencyCube testRadius)
      (fun wave => Pi.single testCoordinate
        (recenteredTensorSchwartzFourierCoefficient spatialTest scale
          scalePos.ne' center wave))
      (fun time => temporalTest ((time - timeCenter) / scale ^ 2))
      (by fun_prop) velocityProfile vorticityProfile cubeVelocity
        cubeVorticity
    · intro point
      simpa only [cubeVelocity] using velocityProfileEq point
    · intro point
      simpa only [cubeVorticity] using vorticityProfileEq point
  rw [finiteFieldIdentity]
  apply congrArg (fun value : Real => scale⁻¹ * value)
  have startLeFinish :
      start ≤ start + scale ^ 2 * timeLength := by
    exact le_add_of_nonneg_right
      (mul_nonneg (sq_nonneg scale) timeLengthNonneg)
  apply intervalIntegral.integral_congr_ae
  filter_upwards [realityAE] with actualTime realityAt
  intro actualTimeMem
  have actualTimeIoc :
      actualTime ∈ Ioc start (start + scale ^ 2 * timeLength) := by
    rwa [uIoc_of_le startLeFinish] at actualTimeMem
  have rawEq := rawFullCubeProjection_physicalVelocity_eq_cubeFiniteField
    inputRadius (path actualTime) (zeroRow actualTime)
      (stateTransverse actualTime) (realityAt actualTimeIoc)
  have fieldEq := puncturedProjection_vorticityField_eq_fullCubeField
    inputRadius (path actualTime) (zeroRow actualTime)
  dsimp only at rawEq
  dsimp only [cubeVelocity, cubeVorticity]
  unfold projectedTensorRawDensity
  simp only
  rw [← rawEq, ← fieldEq]

private theorem realComplexFourierMode_single_norm_le
    (wave : IntegerWavevector)
    (coefficient : Complex)
    (testCoordinate : Coordinate)
    (x : PhysicalSpace) :
    ‖realComplexFourierMode wave
        (Pi.single testCoordinate coefficient) x‖ ≤ ‖coefficient‖ := by
  rw [← sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)]
  calc
    ‖realComplexFourierMode wave
        (Pi.single testCoordinate coefficient) x‖ ^ 2 ≤
      complexCoordinateAmplitudeSq (Pi.single testCoordinate coefficient) :=
        ThreeDimensionalVorticityCoefficientGeneratedShellSerrinGeometry.realComplexFourierMode_norm_sq_le_coefficientAmplitudeSq
          wave (Pi.single testCoordinate coefficient) x
    _ = ‖coefficient‖ ^ 2 := by
      unfold complexCoordinateAmplitudeSq
      rw [Finset.sum_eq_single testCoordinate]
      · simp [Complex.sq_norm]
      · intro coordinate _ coordinateNe
        simp [coordinateNe]
      · simp

private theorem realComplexFourierMode_single_scaledLine_coordinate_hasDerivAt
    (wave : IntegerWavevector)
    (coefficient : Complex)
    (testCoordinate direction outputCoordinate : Coordinate)
    (scale : Real)
    (center point : PhysicalSpace)
    (lineTime : Real) :
    HasDerivAt
      (fun z : Real =>
        realComplexFourierMode wave
          (Pi.single testCoordinate coefficient)
          (center + scale • point +
            z • (scale • EuclideanSpace.single direction 1))
          outputCoordinate)
      (scale *
        realComplexFourierMode wave
          (angularDerivativeCoefficient
            (fun _ => Pi.single testCoordinate coefficient) direction wave)
          (center + scale • point +
            lineTime • (scale • EuclideanSpace.single direction 1))
          outputCoordinate)
      lineTime := by
  by_cases outputEq : outputCoordinate = testCoordinate
  · subst outputCoordinate
    let basePoint := center + scale • point
    let phase : Real → Real := fun z =>
      integerWavePhase wave
        (basePoint + z • (scale • EuclideanSpace.single direction 1))
    have phaseEq : phase = fun z =>
        integerWavePhase wave basePoint +
          z * (scale * integerAngularCoefficient wave direction) := by
      funext z
      dsimp only [phase]
      rw [integerWavePhase_eq_linear]
      rw [map_add, map_smul, map_smul]
      rw [integerWavePhaseLinear_single]
      ring
    have phaseDerivative : HasDerivAt phase
        (scale * integerAngularCoefficient wave direction) lineTime := by
      rw [phaseEq]
      simpa only [id_eq, one_mul, mul_one, zero_add, mul_comm] using
        ((hasDerivAt_id lineTime).const_mul
          (scale * integerAngularCoefficient wave direction)).const_add
            (integerWavePhase wave basePoint)
    have cosineDerivative := phaseDerivative.cos
    have sineDerivative := phaseDerivative.sin
    have modeEq :
        (fun z : Real =>
          realComplexFourierMode wave
            (Pi.single testCoordinate coefficient)
            (center + scale • point +
              z • (scale • EuclideanSpace.single direction 1))
            testCoordinate) =
          fun z => coefficient.re * Real.cos (phase z) -
            coefficient.im * Real.sin (phase z) := by
      funext z
      simp [realComplexFourierMode, coefficientReal, coefficientImag,
        integerCosine, integerSine, phase, basePoint]
      ring
    have derivativeEq :
        scale *
          realComplexFourierMode wave
            (angularDerivativeCoefficient
              (fun _ => Pi.single testCoordinate coefficient) direction wave)
            (center + scale • point +
              lineTime • (scale • EuclideanSpace.single direction 1))
            testCoordinate =
          coefficient.re *
              (-Real.sin (phase lineTime) *
                (scale * integerAngularCoefficient wave direction)) -
            coefficient.im *
              (Real.cos (phase lineTime) *
                (scale * integerAngularCoefficient wave direction)) := by
      simp [angularDerivativeCoefficient, realComplexFourierMode,
        coefficientReal, coefficientImag, integerCosine, integerSine,
        phase, basePoint, Complex.mul_re, Complex.mul_im]
      ring
    rw [modeEq, derivativeEq]
    exact
      (cosineDerivative.const_mul coefficient.re).sub
        (sineDerivative.const_mul coefficient.im)
  · have componentZero (z : Real) :
        realComplexFourierMode wave
          (Pi.single testCoordinate coefficient)
          (center + scale • point +
            z • (scale • EuclideanSpace.single direction 1))
          outputCoordinate = 0 := by
      simp [realComplexFourierMode, coefficientReal, coefficientImag,
        outputEq]
    have derivativeComponentZero :
        realComplexFourierMode wave
          (angularDerivativeCoefficient
            (fun _ => Pi.single testCoordinate coefficient) direction wave)
          (center + scale • point +
            lineTime • (scale • EuclideanSpace.single direction 1))
          outputCoordinate = 0 := by
      simp [angularDerivativeCoefficient, realComplexFourierMode,
        coefficientReal, coefficientImag, outputEq]
    simp_rw [componentZero]
    rw [derivativeComponentZero, mul_zero]
    exact hasDerivAt_const lineTime 0

private theorem scale_mul_abs_integerAngularCoefficient_le_c2Weight
    (wave : IntegerWavevector)
    (direction : Coordinate)
    (scale : Real)
    (scaleLeOne : scale ≤ 1) :
    scale * |integerAngularCoefficient wave direction| ≤
      (2 * Real.pi) * (1 + integerWaveNormSq wave) := by
  have coordinateSqLe :
      (wave direction : Real) ^ 2 ≤ integerWaveNormSq wave := by
    unfold integerWaveNormSq
    exact Finset.single_le_sum
      (fun coordinate _ => sq_nonneg (wave coordinate : Real))
      (Finset.mem_univ direction)
  have coordinateAbsLe :
      |(wave direction : Real)| ≤ 1 + integerWaveNormSq wave := by
    have squareControl :
        |(wave direction : Real)| ≤ 1 + (wave direction : Real) ^ 2 := by
      nlinarith [sq_nonneg (|(wave direction : Real)| - (1 / 2 : Real)),
        sq_abs (wave direction : Real)]
    exact squareControl.trans (by linarith)
  have angularAbs :
      |integerAngularCoefficient wave direction| =
        (2 * Real.pi) * |(wave direction : Real)| := by
    unfold integerAngularCoefficient
    rw [abs_mul, abs_of_pos (by positivity : 0 < 2 * Real.pi)]
  calc
    scale * |integerAngularCoefficient wave direction| ≤
        |integerAngularCoefficient wave direction| := by
      exact mul_le_of_le_one_left (abs_nonneg _) scaleLeOne
    _ = (2 * Real.pi) * |(wave direction : Real)| := angularAbs
    _ ≤ (2 * Real.pi) * (1 + integerWaveNormSq wave) :=
      mul_le_mul_of_nonneg_left coordinateAbsLe (by positivity)

private theorem scaledLineDerivative_single_abs_le_c2Weight
    (wave : IntegerWavevector)
    (coefficient : Complex)
    (testCoordinate direction outputCoordinate : Coordinate)
    (scale : Real)
    (scaleNonneg : 0 ≤ scale)
    (scaleLeOne : scale ≤ 1)
    (x : PhysicalSpace) :
    |scale *
        realComplexFourierMode wave
          (angularDerivativeCoefficient
            (fun _ => Pi.single testCoordinate coefficient) direction wave)
          x outputCoordinate| ≤
      (2 * Real.pi) * (1 + integerWaveNormSq wave) * ‖coefficient‖ := by
  let angularScalar : Complex :=
    Complex.I * (integerAngularCoefficient wave direction : Complex) *
      coefficient
  have angularVectorEq :
      angularDerivativeCoefficient
          (fun _ => Pi.single testCoordinate coefficient) direction wave =
        Pi.single testCoordinate angularScalar := by
    funext coordinate
    by_cases coordinateEq : coordinate = testCoordinate
    · subst coordinate
      simp [angularDerivativeCoefficient, angularScalar]
    · simp [angularDerivativeCoefficient, angularScalar, coordinateEq]
  let field := realComplexFourierMode wave
    (Pi.single testCoordinate angularScalar) x
  have componentLe : |field outputCoordinate| ≤ ‖field‖ := by
    simpa only [Real.norm_eq_abs] using
      (PiLp.norm_apply_le field outputCoordinate)
  have fieldLe : ‖field‖ ≤ ‖angularScalar‖ := by
    exact realComplexFourierMode_single_norm_le wave angularScalar
      testCoordinate x
  have angularScalarNorm :
      ‖angularScalar‖ =
        |integerAngularCoefficient wave direction| * ‖coefficient‖ := by
    dsimp only [angularScalar]
    rw [norm_mul, norm_mul, Complex.norm_I, one_mul]
    norm_cast
  rw [angularVectorEq]
  change |scale * field outputCoordinate| ≤ _
  calc
    |scale * field outputCoordinate| = scale * |field outputCoordinate| := by
      rw [abs_mul, abs_of_nonneg scaleNonneg]
    _ ≤ scale * ‖field‖ :=
      mul_le_mul_of_nonneg_left componentLe scaleNonneg
    _ ≤ scale * ‖angularScalar‖ :=
      mul_le_mul_of_nonneg_left fieldLe scaleNonneg
    _ = (scale * |integerAngularCoefficient wave direction|) *
        ‖coefficient‖ := by rw [angularScalarNorm]; ring
    _ ≤ ((2 * Real.pi) * (1 + integerWaveNormSq wave)) *
        ‖coefficient‖ :=
      mul_le_mul_of_nonneg_right
        (scale_mul_abs_integerAngularCoefficient_le_c2Weight
          wave direction scale scaleLeOne)
        (norm_nonneg _)

private theorem recenteredRealFourierSeries_scaledLine_hasDerivAt
    (coefficient : IntegerWavevector → Complex)
    (c2Summable : Summable fun wave : IntegerWavevector =>
      (1 + integerWaveNormSq wave) * ‖coefficient wave‖)
    (testCoordinate direction outputCoordinate : Coordinate)
    (scale : Real)
    (scaleNonneg : 0 ≤ scale)
    (scaleLeOne : scale ≤ 1)
    (center point : PhysicalSpace)
    (lineTime : Real) :
    HasDerivAt
      (fun z : Real =>
        ∑' wave : IntegerWavevector,
          realComplexFourierMode wave
            (Pi.single testCoordinate (coefficient wave))
            (center + scale • point +
              z • (scale • EuclideanSpace.single direction 1))
            outputCoordinate)
      (∑' wave : IntegerWavevector,
        scale *
          realComplexFourierMode wave
            (angularDerivativeCoefficient
              (fun _ => Pi.single testCoordinate (coefficient wave))
              direction wave)
            (center + scale • point +
              lineTime • (scale • EuclideanSpace.single direction 1))
            outputCoordinate)
      lineTime := by
  let term : IntegerWavevector → Real → Real := fun wave z =>
    realComplexFourierMode wave
      (Pi.single testCoordinate (coefficient wave))
      (center + scale • point +
        z • (scale • EuclideanSpace.single direction 1))
      outputCoordinate
  let termDerivative : IntegerWavevector → Real → Real := fun wave z =>
    scale *
      realComplexFourierMode wave
        (angularDerivativeCoefficient
          (fun _ => Pi.single testCoordinate (coefficient wave))
          direction wave)
        (center + scale • point +
          z • (scale • EuclideanSpace.single direction 1))
        outputCoordinate
  let c2Weight : IntegerWavevector → Real := fun wave =>
    (1 + integerWaveNormSq wave) * ‖coefficient wave‖
  let derivativeBound : IntegerWavevector → Real := fun wave =>
    (2 * Real.pi) * c2Weight wave
  have derivativeBoundSummable : Summable derivativeBound := by
    exact c2Summable.mul_left (2 * Real.pi)
  have coefficientNormSummable :
      Summable fun wave : IntegerWavevector => ‖coefficient wave‖ := by
    apply c2Summable.of_nonneg_of_le (fun wave => norm_nonneg _)
    intro wave
    have normSqNonneg := integerWaveNormSq_nonneg wave
    nlinarith [norm_nonneg (coefficient wave)]
  have termSummable : Summable fun wave : IntegerWavevector => term wave 0 := by
    apply Summable.of_norm
    apply coefficientNormSummable.of_nonneg_of_le (fun wave => norm_nonneg _)
    intro wave
    have componentLe :
        ‖realComplexFourierMode wave
            (Pi.single testCoordinate (coefficient wave))
            (center + scale • point) outputCoordinate‖ ≤
          ‖realComplexFourierMode wave
            (Pi.single testCoordinate (coefficient wave))
            (center + scale • point)‖ :=
      PiLp.norm_apply_le _ _
    simpa only [term, zero_smul, add_zero] using
      componentLe.trans
        (realComplexFourierMode_single_norm_le wave (coefficient wave)
          testCoordinate (center + scale • point))
  have termDerivativeLaw : ∀ wave z,
      HasDerivAt (term wave) (termDerivative wave z) z := by
    intro wave z
    simpa only [term, termDerivative] using
      realComplexFourierMode_single_scaledLine_coordinate_hasDerivAt
      wave (coefficient wave) testCoordinate direction outputCoordinate scale
        center point z
  have derivativeBoundLaw : ∀ wave z,
      ‖termDerivative wave z‖ ≤ derivativeBound wave := by
    intro wave z
    dsimp only [derivativeBound, c2Weight]
    simpa only [termDerivative, Real.norm_eq_abs, mul_assoc] using
      scaledLineDerivative_single_abs_le_c2Weight wave (coefficient wave)
        testCoordinate direction outputCoordinate scale scaleNonneg scaleLeOne
        (center + scale • point +
          z • (scale • EuclideanSpace.single direction 1))
  have seriesDerivative := hasDerivAt_tsum
    (g := term) (g' := termDerivative) (y₀ := 0) derivativeBoundSummable
      termDerivativeLaw derivativeBoundLaw termSummable lineTime
  simpa only [term, termDerivative] using seriesDerivative

private theorem realComplexFourierMode_single_apply_same_eq_re_exp
    (wave : IntegerWavevector)
    (coefficient : Complex)
    (testCoordinate : Coordinate)
    (x : PhysicalSpace) :
    realComplexFourierMode wave (Pi.single testCoordinate coefficient) x
        testCoordinate =
      (coefficient *
        Complex.exp (Complex.I * integerWavePhase wave x)).re := by
  simp [realComplexFourierMode, coefficientReal, coefficientImag,
    integerCosine, integerSine, Complex.exp_re, Complex.exp_im,
    Complex.mul_re, Complex.mul_im]
  ring

private theorem recenteredRealFourierSeries_apply_same_eq_re_complexSeries
    (coefficient : IntegerWavevector → Complex)
    (coefficientNormSummable : Summable fun wave : IntegerWavevector =>
      ‖coefficient wave‖)
    (testCoordinate : Coordinate)
    (x : PhysicalSpace) :
    (∑' wave : IntegerWavevector,
      realComplexFourierMode wave
        (Pi.single testCoordinate (coefficient wave)) x testCoordinate) =
      (∑' wave : IntegerWavevector,
        coefficient wave *
          Complex.exp (Complex.I * integerWavePhase wave x)).re := by
  have complexSeriesSummable : Summable fun wave : IntegerWavevector =>
      coefficient wave *
        Complex.exp (Complex.I * integerWavePhase wave x) := by
    apply Summable.of_norm
    convert coefficientNormSummable using 1
    funext wave
    rw [norm_mul, Complex.norm_exp]
    simp [Complex.mul_re]
  rw [Complex.re_tsum complexSeriesSummable]
  apply tsum_congr
  intro wave
  exact realComplexFourierMode_single_apply_same_eq_re_exp
    wave (coefficient wave) testCoordinate x

private theorem unitAddTorus_mFourier_physicalSpace
    (wave : IntegerWavevector) (x : PhysicalSpace) :
    UnitAddTorus.mFourier wave
        (fun coordinate => ((x coordinate : Real) : UnitAddCircle)) =
      Complex.exp (Complex.I * integerWavePhase wave x) := by
  rw [show UnitAddTorus.mFourier wave
        (fun coordinate => ((x coordinate : Real) : UnitAddCircle)) =
      ∏ coordinate : Coordinate,
        fourier (wave coordinate)
          ((x coordinate : Real) : UnitAddCircle) by rfl]
  rw [Fin.prod_univ_three]
  simp only [fourier_coe_apply]
  rw [← Complex.exp_add, ← Complex.exp_add]
  congr 1
  simp [integerWavePhase, Fin.sum_univ_three]
  ring

private def scaledSchwartzTest
    (test : 𝓢(ℝ, ℂ)) (period : ℝ) (periodNe : period ≠ 0) : 𝓢(ℝ, ℂ) :=
  SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
    (ContinuousLinearEquiv.smulLeft (Units.mk0 period periodNe)) test

private theorem scaledSchwartzTest_apply
    (test : 𝓢(ℝ, ℂ)) (period : ℝ) (periodNe : period ≠ 0) (x : ℝ) :
    scaledSchwartzTest test period periodNe x = test (period * x) := by
  rfl

private theorem scaledSchwartzTest_fourier_apply
    (test : 𝓢(ℝ, ℂ))
    (period frequency : ℝ)
    (periodPos : 0 < period) :
    𝓕 (scaledSchwartzTest test period periodPos.ne') frequency =
      (period⁻¹ : ℝ) • 𝓕 test (frequency / period) := by
  rw [SchwartzMap.fourier_coe, Real.fourier_real_eq]
  rw [SchwartzMap.fourier_coe, Real.fourier_real_eq]
  let integrand : ℝ → ℂ := fun y =>
    𝐞 (-(y * (frequency / period))) • test y
  have changeVariables :=
    Measure.integral_comp_smul (volume : Measure ℝ) integrand period
  have changeVariables' :
      (∫ x : ℝ, integrand (period • x)) =
        (period⁻¹ : ℝ) • ∫ y : ℝ, integrand y := by
    simpa only [Module.finrank_self, pow_one,
      abs_of_pos (inv_pos.mpr periodPos)] using changeVariables
  rw [← changeVariables']
  apply integral_congr_ae
  filter_upwards with x
  dsimp only [integrand]
  rw [scaledSchwartzTest_apply]
  congr 2
  simp only [smul_eq_mul]
  field_simp [periodPos.ne']

private theorem schwartzTest_fourier_samples_summable
    (test : 𝓢(ℝ, ℂ)) :
    Summable fun frequency : ℤ => 𝓕 test frequency := by
  exact summable_of_isBigO (Real.summable_abs_int_rpow one_lt_two)
    (((𝓕 test).isBigO_cocompact_rpow (-2)).comp_tendsto Int.tendsto_coe_cofinite)

private theorem scaledSchwartzTest_fourier_samples_summable
    (test : 𝓢(ℝ, ℂ)) (period : ℝ) (periodNe : period ≠ 0) :
    Summable fun frequency : ℤ =>
      𝓕 (scaledSchwartzTest test period periodNe) frequency :=
  schwartzTest_fourier_samples_summable _

private theorem schwartzTest_fourier_frequency_sq_mul_samples_summable
    (test : 𝓢(ℝ, ℂ)) :
    Summable fun frequency : ℤ =>
      ((2 * Real.pi * Complex.I * (frequency : ℝ)) ^ 2) *
        𝓕 test frequency := by
  have secondDerivativeSummable :=
    schwartzTest_fourier_samples_summable
      (∂_{(1 : ℝ)} (∂_{(1 : ℝ)} test))
  convert secondDerivativeSummable using 1
  funext frequency
  have firstDerivativeFourier := congrArg
    (fun transformed : 𝓢(ℝ, ℂ) => transformed (frequency : ℝ))
    (SchwartzMap.fourier_lineDerivOp_eq test (1 : ℝ))
  have secondDerivativeFourier := congrArg
    (fun transformed : 𝓢(ℝ, ℂ) => transformed (frequency : ℝ))
    (SchwartzMap.fourier_lineDerivOp_eq (∂_{(1 : ℝ)} test) (1 : ℝ))
  change (𝓕 (∂_{(1 : ℝ)} test)) (frequency : ℝ) =
    (2 * Real.pi * Complex.I) *
      (SchwartzMap.smulLeftCLM ℂ (fun x : ℝ => inner ℝ x 1)
        (𝓕 test)) (frequency : ℝ) at firstDerivativeFourier
  change (𝓕 (∂_{(1 : ℝ)} (∂_{(1 : ℝ)} test))) (frequency : ℝ) =
    (2 * Real.pi * Complex.I) *
      (SchwartzMap.smulLeftCLM ℂ (fun x : ℝ => inner ℝ x 1)
        (𝓕 (∂_{(1 : ℝ)} test))) (frequency : ℝ) at secondDerivativeFourier
  rw [SchwartzMap.smulLeftCLM_apply_apply (by fun_prop)] at firstDerivativeFourier
  rw [SchwartzMap.smulLeftCLM_apply_apply (by fun_prop)] at secondDerivativeFourier
  rw [secondDerivativeFourier, firstDerivativeFourier]
  simp
  ring

private theorem schwartzTest_fourier_frequency_sq_norm_summable
    (test : 𝓢(ℝ, ℂ)) :
    Summable fun frequency : ℤ =>
      (frequency : ℝ) ^ 2 * ‖𝓕 test frequency‖ := by
  have weighted :=
    (schwartzTest_fourier_frequency_sq_mul_samples_summable test).norm
  have rescaled := weighted.mul_left ((2 * Real.pi) ^ (-2 : ℤ))
  apply rescaled.congr
  intro frequency
  simp only [norm_mul, norm_pow, Complex.norm_ofNat, norm_real,
    Complex.norm_I, mul_one, norm_eq_abs]
  rw [abs_of_pos Real.pi_pos]
  have piNe : (Real.pi : ℝ) ≠ 0 := ne_of_gt Real.pi_pos
  field_simp [piNe]
  rw [sq_abs (frequency : ℝ)]
  ring

private theorem scaledSchwartzTest_periodization_eq
    (test : 𝓢(ℝ, ℂ)) (period : ℝ) (periodNe : period ≠ 0) (x : ℝ) :
    (∑' shift : ℤ, test (x + period * shift)) =
      ∑' frequency : ℤ,
        𝓕 (scaledSchwartzTest test period periodNe) frequency *
          fourier frequency ((x / period : ℝ) : UnitAddCircle) := by
  convert SchwartzMap.tsum_eq_tsum_fourier
      (scaledSchwartzTest test period periodNe) (x / period) using 1
  · congr 1
    funext shift
    rw [scaledSchwartzTest_apply]
    field_simp [periodNe]

private theorem scaledSchwartzTest_periodization_eq_self_of_compactSupport
    (test : 𝓢(ℝ, ℂ))
    (supportRadius observationRadius period x : ℝ)
    (periodPos : 0 < period)
    (periodLarge : supportRadius + observationRadius < period)
    (xBound : |x| ≤ observationRadius)
    (support : ∀ y : ℝ, supportRadius < |y| → test y = 0) :
    (∑' shift : ℤ, test (x + period * shift)) = test x := by
  rw [tsum_eq_single (0 : ℤ)]
  · simp
  · intro shift shiftNe
    have shiftAbsInt : (1 : ℤ) ≤ |shift| := Int.one_le_abs shiftNe
    have shiftAbs : (1 : ℝ) ≤ |(shift : ℝ)| := by
      exact_mod_cast shiftAbsInt
    have periodLe : period ≤ |period * (shift : ℝ)| := by
      rw [abs_mul, abs_of_pos periodPos]
      exact le_mul_of_one_le_right periodPos.le shiftAbs
    have triangle :
        |period * (shift : ℝ)| ≤
          |x + period * (shift : ℝ)| + |x| := by
      calc
        |period * (shift : ℝ)| =
            |(x + period * (shift : ℝ)) + (-x)| := by
          congr 1
          ring
        _ ≤ |x + period * (shift : ℝ)| + |-x| := abs_add_le _ _
        _ = |x + period * (shift : ℝ)| + |x| := by rw [abs_neg]
    apply support
    linarith

private theorem schwartzLineDeriv_eq_zero_of_compactSupport
    (test : 𝓢(ℝ, ℂ))
    (supportRadius y : ℝ)
    (support : ∀ z : ℝ, supportRadius < |z| → test z = 0)
    (outside : supportRadius < |y|) :
    (∂_{(1 : ℝ)} test) y = 0 := by
  have outsideOpen : IsOpen {z : ℝ | supportRadius < |z|} :=
    isOpen_lt continuous_const continuous_abs
  have outsideMem : {z : ℝ | supportRadius < |z|} ∈ nhds y :=
    outsideOpen.mem_nhds outside
  have eventuallyZero :
      test =ᶠ[nhds y] (fun _z : ℝ => (0 : ℂ)) := by
    filter_upwards [outsideMem] with z zOutside
    exact support z zOutside
  rw [SchwartzMap.lineDerivOp_apply_eq_fderiv]
  rw [eventuallyZero.fderiv_eq]
  simp

private theorem schwartzSecondLineDeriv_eq_zero_of_compactSupport
    (test : 𝓢(ℝ, ℂ))
    (supportRadius y : ℝ)
    (support : ∀ z : ℝ, supportRadius < |z| → test z = 0)
    (outside : supportRadius < |y|) :
    (∂_{(1 : ℝ)} (∂_{(1 : ℝ)} test)) y = 0 := by
  apply schwartzLineDeriv_eq_zero_of_compactSupport
    (∂_{(1 : ℝ)} test) supportRadius y
  · intro z zOutside
    exact schwartzLineDeriv_eq_zero_of_compactSupport
      test supportRadius z support zOutside
  · exact outside

private theorem scaledSchwartzTest_periodization_eq_self_C2_of_compactSupport
    (test : 𝓢(ℝ, ℂ))
    (supportRadius observationRadius period x : ℝ)
    (periodPos : 0 < period)
    (periodLarge : supportRadius + observationRadius < period)
    (xBound : |x| ≤ observationRadius)
    (support : ∀ y : ℝ, supportRadius < |y| → test y = 0) :
    (∑' shift : ℤ, test (x + period * shift)) = test x ∧
      (∑' shift : ℤ,
        (∂_{(1 : ℝ)} test) (x + period * shift)) =
          (∂_{(1 : ℝ)} test) x ∧
      (∑' shift : ℤ,
        (∂_{(1 : ℝ)} (∂_{(1 : ℝ)} test))
          (x + period * shift)) =
          (∂_{(1 : ℝ)} (∂_{(1 : ℝ)} test)) x := by
  refine ⟨scaledSchwartzTest_periodization_eq_self_of_compactSupport
      test supportRadius observationRadius period x periodPos periodLarge xBound support,
    ?_, ?_⟩
  · apply scaledSchwartzTest_periodization_eq_self_of_compactSupport
      (∂_{(1 : ℝ)} test) supportRadius observationRadius period x
      periodPos periodLarge xBound
    intro y yOutside
    exact schwartzLineDeriv_eq_zero_of_compactSupport
      test supportRadius y support yOutside
  · apply scaledSchwartzTest_periodization_eq_self_of_compactSupport
      (∂_{(1 : ℝ)} (∂_{(1 : ℝ)} test)) supportRadius observationRadius period x
      periodPos periodLarge xBound
    intro y yOutside
    exact schwartzSecondLineDeriv_eq_zero_of_compactSupport
      test supportRadius y support yOutside

private def scaledSchwartzPeriodicTest
    (test : 𝓢(ℝ, ℂ)) (period : ℝ) (periodNe : period ≠ 0) :
    C(UnitAddCircle, ℂ) :=
  ∑' frequency : ℤ,
    𝓕 (scaledSchwartzTest test period periodNe) frequency • fourier frequency

private theorem scaledSchwartzPeriodicTest_hasSum
    (test : 𝓢(ℝ, ℂ)) (period : ℝ) (periodNe : period ≠ 0) :
    HasSum
      (fun frequency : ℤ =>
        𝓕 (scaledSchwartzTest test period periodNe) frequency • fourier frequency)
      (scaledSchwartzPeriodicTest test period periodNe) := by
  apply Summable.hasSum
  apply Summable.of_norm
  convert (scaledSchwartzTest_fourier_samples_summable test period periodNe).norm using 1
  funext frequency
  rw [norm_smul, fourier_norm, mul_one]

private theorem scaledSchwartzPeriodicTest_apply
    (test : 𝓢(ℝ, ℂ)) (period : ℝ) (periodNe : period ≠ 0) (x : ℝ) :
    scaledSchwartzPeriodicTest test period periodNe
        ((x / period : ℝ) : UnitAddCircle) =
      ∑' shift : ℤ, test (x + period * shift) := by
  rw [scaledSchwartzPeriodicTest]
  rw [← ContinuousMap.tsum_apply
    (scaledSchwartzPeriodicTest_hasSum test period periodNe).summable]
  simpa only [ContinuousMap.smul_apply, smul_eq_mul] using
    (scaledSchwartzTest_periodization_eq test period periodNe x).symm

private def tensorSchwartzFourierCoefficient
    (test : Coordinate → 𝓢(ℝ, ℂ))
    (period : ℝ) (periodNe : period ≠ 0)
    (wave : IntegerWavevector) : ℂ :=
  𝓕 (scaledSchwartzTest (test 0) period periodNe) (wave 0) *
    𝓕 (scaledSchwartzTest (test 1) period periodNe) (wave 1) *
      𝓕 (scaledSchwartzTest (test 2) period periodNe) (wave 2)

private def integerWavevectorEquivTriple :
    IntegerWavevector ≃ (ℤ × ℤ) × ℤ :=
  (Fin.succFunEquiv ℤ 2).trans
    (Equiv.prodCongr (finTwoArrowEquiv ℤ) (Equiv.refl ℤ))

private theorem tensorSchwartzFourierCoefficient_norm_summable
    (test : Coordinate → 𝓢(ℝ, ℂ))
    (period : ℝ) (periodNe : period ≠ 0) :
    Summable fun wave : IntegerWavevector =>
      ‖tensorSchwartzFourierCoefficient test period periodNe wave‖ := by
  let coefficient : Coordinate → ℤ → ℂ := fun coordinate frequency =>
    𝓕 (scaledSchwartzTest (test coordinate) period periodNe) frequency
  have h₀ : Summable fun frequency : ℤ => ‖coefficient 0 frequency‖ :=
    (scaledSchwartzTest_fourier_samples_summable
      (test 0) period periodNe).norm
  have h₁ : Summable fun frequency : ℤ => ‖coefficient 1 frequency‖ :=
    (scaledSchwartzTest_fourier_samples_summable
      (test 1) period periodNe).norm
  have h₂ : Summable fun frequency : ℤ => ‖coefficient 2 frequency‖ :=
    (scaledSchwartzTest_fourier_samples_summable
      (test 2) period periodNe).norm
  have h₀₁₂ : Summable fun frequencies : (ℤ × ℤ) × ℤ =>
      ‖(coefficient 0 frequencies.1.1 * coefficient 1 frequencies.1.2) *
        coefficient 2 frequencies.2‖ :=
    (h₀.mul_norm h₁).mul_norm h₂
  let tripleDensity : (ℤ × ℤ) × ℤ → ℝ := fun frequencies =>
    ‖(coefficient 0 frequencies.1.1 * coefficient 1 frequencies.1.2) *
      coefficient 2 frequencies.2‖
  have transported : Summable (tripleDensity ∘ integerWavevectorEquivTriple) :=
    integerWavevectorEquivTriple.summable_iff.mpr h₀₁₂
  apply transported.congr
  intro wave
  simp [integerWavevectorEquivTriple, tensorSchwartzFourierCoefficient,
    tripleDensity, coefficient, mul_assoc]

set_option maxHeartbeats 800000 in
private theorem tensorSchwartzFourierCoefficient_normSq_mul_norm_summable
    (test : Coordinate → 𝓢(ℝ, ℂ))
    (period : ℝ) (periodNe : period ≠ 0) :
    Summable fun wave : IntegerWavevector =>
      integerWaveNormSq wave *
        ‖tensorSchwartzFourierCoefficient test period periodNe wave‖ := by
  let coefficient : Coordinate → ℤ → ℂ := fun coordinate frequency =>
    𝓕 (scaledSchwartzTest (test coordinate) period periodNe) frequency
  have h₀ : Summable fun frequency : ℤ => ‖coefficient 0 frequency‖ :=
    (scaledSchwartzTest_fourier_samples_summable
      (test 0) period periodNe).norm
  have h₁ : Summable fun frequency : ℤ => ‖coefficient 1 frequency‖ :=
    (scaledSchwartzTest_fourier_samples_summable
      (test 1) period periodNe).norm
  have h₂ : Summable fun frequency : ℤ => ‖coefficient 2 frequency‖ :=
    (scaledSchwartzTest_fourier_samples_summable
      (test 2) period periodNe).norm
  have h₀Sq : Summable fun frequency : ℤ =>
      (frequency : ℝ) ^ 2 * ‖coefficient 0 frequency‖ :=
    schwartzTest_fourier_frequency_sq_norm_summable
      (scaledSchwartzTest (test 0) period periodNe)
  have h₁Sq : Summable fun frequency : ℤ =>
      (frequency : ℝ) ^ 2 * ‖coefficient 1 frequency‖ :=
    schwartzTest_fourier_frequency_sq_norm_summable
      (scaledSchwartzTest (test 1) period periodNe)
  have h₂Sq : Summable fun frequency : ℤ =>
      (frequency : ℝ) ^ 2 * ‖coefficient 2 frequency‖ :=
    schwartzTest_fourier_frequency_sq_norm_summable
      (scaledSchwartzTest (test 2) period periodNe)
  have firstPair : Summable fun frequencies : ℤ × ℤ =>
      ((frequencies.1 : ℝ) ^ 2 * ‖coefficient 0 frequencies.1‖) *
        ‖coefficient 1 frequencies.2‖ :=
    h₀Sq.mul_of_nonneg h₁
      (fun frequency => mul_nonneg (sq_nonneg _) (norm_nonneg _))
      (fun frequency => norm_nonneg _)
  have firstWeighted : Summable fun frequencies : (ℤ × ℤ) × ℤ =>
      ((frequencies.1.1 : ℝ) ^ 2 * ‖coefficient 0 frequencies.1.1‖) *
        ‖coefficient 1 frequencies.1.2‖ *
          ‖coefficient 2 frequencies.2‖ :=
    firstPair.mul_of_nonneg h₂
      (fun frequencies =>
        mul_nonneg (mul_nonneg (sq_nonneg _) (norm_nonneg _))
          (norm_nonneg _))
      (fun frequency => norm_nonneg _)
  have secondPair : Summable fun frequencies : ℤ × ℤ =>
      ‖coefficient 0 frequencies.1‖ *
        ((frequencies.2 : ℝ) ^ 2 * ‖coefficient 1 frequencies.2‖) :=
    h₀.mul_of_nonneg h₁Sq
      (fun frequency => norm_nonneg _)
      (fun frequency => mul_nonneg (sq_nonneg _) (norm_nonneg _))
  have secondWeighted : Summable fun frequencies : (ℤ × ℤ) × ℤ =>
      ‖coefficient 0 frequencies.1.1‖ *
        ((frequencies.1.2 : ℝ) ^ 2 * ‖coefficient 1 frequencies.1.2‖) *
          ‖coefficient 2 frequencies.2‖ :=
    secondPair.mul_of_nonneg h₂
      (fun frequencies =>
        mul_nonneg (norm_nonneg _)
          (mul_nonneg (sq_nonneg _) (norm_nonneg _)))
      (fun frequency => norm_nonneg _)
  have thirdPair : Summable fun frequencies : ℤ × ℤ =>
      ‖coefficient 0 frequencies.1‖ *
        ‖coefficient 1 frequencies.2‖ :=
    h₀.mul_of_nonneg h₁
      (fun frequency => norm_nonneg _)
      (fun frequency => norm_nonneg _)
  have thirdWeighted : Summable fun frequencies : (ℤ × ℤ) × ℤ =>
      ‖coefficient 0 frequencies.1.1‖ *
        ‖coefficient 1 frequencies.1.2‖ *
          ((frequencies.2 : ℝ) ^ 2 * ‖coefficient 2 frequencies.2‖) :=
    thirdPair.mul_of_nonneg h₂Sq
      (fun frequencies => mul_nonneg (norm_nonneg _) (norm_nonneg _))
      (fun frequency => mul_nonneg (sq_nonneg _) (norm_nonneg _))
  let tripleDensity : (ℤ × ℤ) × ℤ → ℝ := fun frequencies =>
    (((frequencies.1.1 : ℝ) ^ 2 +
          (frequencies.1.2 : ℝ) ^ 2 +
          (frequencies.2 : ℝ) ^ 2) *
      ‖(coefficient 0 frequencies.1.1 * coefficient 1 frequencies.1.2) *
        coefficient 2 frequencies.2‖)
  have tripleSummable : Summable tripleDensity := by
    apply ((firstWeighted.add secondWeighted).add thirdWeighted).congr
    intro frequencies
    simp only [tripleDensity, norm_mul]
    ring
  have transported : Summable (tripleDensity ∘ integerWavevectorEquivTriple) :=
    integerWavevectorEquivTriple.summable_iff.mpr tripleSummable
  apply transported.congr
  intro wave
  simp [integerWavevectorEquivTriple, tensorSchwartzFourierCoefficient,
    tripleDensity, coefficient, integerWaveNormSq, Fin.sum_univ_three,
    mul_assoc]

private def tensorSchwartzPeriodicTest
    (test : Coordinate → 𝓢(ℝ, ℂ))
    (period : ℝ) (periodNe : period ≠ 0) :
    C(UnitAddTorus Coordinate, ℂ) :=
  ∑' wave : IntegerWavevector,
    tensorSchwartzFourierCoefficient test period periodNe wave •
      UnitAddTorus.mFourier wave

private theorem tensorSchwartzPeriodicTest_hasSum
    (test : Coordinate → 𝓢(ℝ, ℂ))
    (period : ℝ) (periodNe : period ≠ 0) :
    HasSum
      (fun wave : IntegerWavevector =>
        tensorSchwartzFourierCoefficient test period periodNe wave •
          UnitAddTorus.mFourier wave)
      (tensorSchwartzPeriodicTest test period periodNe) := by
  apply Summable.hasSum
  apply Summable.of_norm
  convert tensorSchwartzFourierCoefficient_norm_summable test period periodNe using 1
  funext wave
  rw [norm_smul, UnitAddTorus.mFourier_norm, mul_one]

private theorem tensorSchwartzPeriodicTest_apply_eq_mul
    (test : Coordinate → 𝓢(ℝ, ℂ))
    (period : ℝ) (periodNe : period ≠ 0)
    (z : UnitAddTorus Coordinate) :
    tensorSchwartzPeriodicTest test period periodNe z =
      scaledSchwartzPeriodicTest (test 0) period periodNe (z 0) *
        scaledSchwartzPeriodicTest (test 1) period periodNe (z 1) *
          scaledSchwartzPeriodicTest (test 2) period periodNe (z 2) := by
  let coefficient : Coordinate → ℤ → ℂ := fun coordinate frequency =>
    𝓕 (scaledSchwartzTest (test coordinate) period periodNe) frequency
  let term : Coordinate → ℤ → ℂ := fun coordinate frequency =>
    coefficient coordinate frequency * fourier frequency (z coordinate)
  have termNormSummable (coordinate : Coordinate) :
      Summable fun frequency : ℤ => ‖term coordinate frequency‖ := by
    convert (scaledSchwartzTest_fourier_samples_summable
      (test coordinate) period periodNe).norm using 1
    funext frequency
    simp only [term, coefficient, norm_mul]
    rw [fourier_apply, Circle.norm_coe, mul_one]
  have termTsum (coordinate : Coordinate) :
      (∑' frequency : ℤ, term coordinate frequency) =
        scaledSchwartzPeriodicTest (test coordinate) period periodNe
          (z coordinate) := by
    rw [scaledSchwartzPeriodicTest]
    rw [← ContinuousMap.tsum_apply
      (scaledSchwartzPeriodicTest_hasSum
        (test coordinate) period periodNe).summable]
    apply tsum_congr
    intro frequency
    simp [term, coefficient]
  have productTsum :
      ((∑' frequency : ℤ, term 0 frequency) *
          ∑' frequency : ℤ, term 1 frequency) *
          ∑' frequency : ℤ, term 2 frequency =
        ∑' frequencies : (ℤ × ℤ) × ℤ,
          (term 0 frequencies.1.1 * term 1 frequencies.1.2) *
            term 2 frequencies.2 := by
    rw [tsum_mul_tsum_of_summable_norm
      (termNormSummable 0) (termNormSummable 1)]
    rw [tsum_mul_tsum_of_summable_norm
      ((termNormSummable 0).mul_norm (termNormSummable 1))
      (termNormSummable 2)]
  rw [tensorSchwartzPeriodicTest]
  rw [← ContinuousMap.tsum_apply
    (tensorSchwartzPeriodicTest_hasSum test period periodNe).summable]
  rw [← termTsum 0, ← termTsum 1, ← termTsum 2, productTsum]
  rw [← integerWavevectorEquivTriple.tsum_eq]
  congr 1
  funext wave
  change
    ((𝓕 (scaledSchwartzTest (test 0) period periodNe)) (wave 0) *
        (𝓕 (scaledSchwartzTest (test 1) period periodNe)) (wave 1) *
        (𝓕 (scaledSchwartzTest (test 2) period periodNe)) (wave 2)) *
        (∏ coordinate : Coordinate,
          fourier (wave coordinate) (z coordinate)) =
      (((𝓕 (scaledSchwartzTest (test 0) period periodNe)) (wave 0) *
          fourier (wave 0) (z 0)) *
        ((𝓕 (scaledSchwartzTest (test 1) period periodNe)) (wave 1) *
          fourier (wave 1) (z 1))) *
        ((𝓕 (scaledSchwartzTest (test 2) period periodNe)) (wave 2) *
          fourier (wave 2) (z 2))
  rw [Fin.prod_univ_three]
  ring

private theorem tensorSchwartzPeriodicTest_apply
    (test : Coordinate → 𝓢(ℝ, ℂ))
    (period : ℝ) (periodNe : period ≠ 0)
    (x : Coordinate → ℝ) :
    tensorSchwartzPeriodicTest test period periodNe
        (fun coordinate =>
          ((x coordinate / period : ℝ) : UnitAddCircle)) =
      ∏ coordinate : Coordinate,
        ∑' shift : ℤ,
          test coordinate (x coordinate + period * shift) := by
  rw [tensorSchwartzPeriodicTest_apply_eq_mul]
  rw [Fin.prod_univ_three]
  rw [scaledSchwartzPeriodicTest_apply,
    scaledSchwartzPeriodicTest_apply,
    scaledSchwartzPeriodicTest_apply]

private theorem recenteredTensorSchwartzFourierCoefficient_norm
    (test : Coordinate → 𝓢(ℝ, ℂ))
    (scale : ℝ) (scaleNe : scale ≠ 0)
    (center : PhysicalSpace)
    (wave : IntegerWavevector) :
    ‖recenteredTensorSchwartzFourierCoefficient
        test scale scaleNe center wave‖ =
      ‖tensorSchwartzFourierCoefficient
        test scale⁻¹ (inv_ne_zero scaleNe) wave‖ := by
  unfold recenteredTensorSchwartzFourierCoefficient
  change ‖tensorSchwartzFourierCoefficient test scale⁻¹
      (inv_ne_zero scaleNe) wave *
        Complex.exp (-Complex.I * integerWavePhase wave center)‖ = _
  rw [norm_mul, Complex.norm_exp]
  simp

private theorem recenteredTensorSchwartzFourierCoefficient_c2_summable
    (test : Coordinate → 𝓢(ℝ, ℂ))
    (scale : ℝ) (scaleNe : scale ≠ 0)
    (center : PhysicalSpace) :
    Summable fun wave : IntegerWavevector =>
      (1 + integerWaveNormSq wave) *
        ‖recenteredTensorSchwartzFourierCoefficient
          test scale scaleNe center wave‖ := by
  have unweighted := tensorSchwartzFourierCoefficient_norm_summable
    test scale⁻¹ (inv_ne_zero scaleNe)
  have secondWeighted :=
    tensorSchwartzFourierCoefficient_normSq_mul_norm_summable
      test scale⁻¹ (inv_ne_zero scaleNe)
  apply (unweighted.add secondWeighted).congr
  intro wave
  rw [recenteredTensorSchwartzFourierCoefficient_norm]
  ring

private theorem recenteredTensorSchwartzFourierSeries_summable
    (test : Coordinate → 𝓢(ℝ, ℂ))
    (scale : ℝ) (scaleNe : scale ≠ 0)
    (center : PhysicalSpace) :
    Summable fun wave : IntegerWavevector =>
      recenteredTensorSchwartzFourierCoefficient
          test scale scaleNe center wave •
        UnitAddTorus.mFourier wave := by
  apply Summable.of_norm
  convert (tensorSchwartzFourierCoefficient_norm_summable
    test scale⁻¹ (inv_ne_zero scaleNe)) using 1
  funext wave
  rw [norm_smul, UnitAddTorus.mFourier_norm, mul_one,
    recenteredTensorSchwartzFourierCoefficient_norm]

private theorem recenteredTensorSchwartzFourierSeries_physical_eq
    (test : Coordinate → 𝓢(ℝ, ℂ))
    (scale : ℝ) (scaleNe : scale ≠ 0)
    (center x : PhysicalSpace) :
    (∑' wave : IntegerWavevector,
      recenteredTensorSchwartzFourierCoefficient
          test scale scaleNe center wave *
        UnitAddTorus.mFourier wave
          (fun coordinate => ((x coordinate : ℝ) : UnitAddCircle))) =
      ∏ coordinate : Coordinate,
        ∑' shift : ℤ,
          test coordinate
            (scale⁻¹ * (x coordinate - center coordinate + shift)) := by
  let shiftedPoint : PhysicalSpace := x - center
  have seriesEq :
      (∑' wave : IntegerWavevector,
        recenteredTensorSchwartzFourierCoefficient
            test scale scaleNe center wave *
          UnitAddTorus.mFourier wave
            (fun coordinate => ((x coordinate : ℝ) : UnitAddCircle))) =
        tensorSchwartzPeriodicTest test scale⁻¹ (inv_ne_zero scaleNe)
          (fun coordinate =>
            ((shiftedPoint coordinate : ℝ) : UnitAddCircle)) := by
    rw [tensorSchwartzPeriodicTest]
    rw [← ContinuousMap.tsum_apply
      (tensorSchwartzPeriodicTest_hasSum
        test scale⁻¹ (inv_ne_zero scaleNe)).summable]
    apply tsum_congr
    intro wave
    rw [unitAddTorus_mFourier_physicalSpace]
    change
      tensorSchwartzFourierCoefficient
            test scale⁻¹ (inv_ne_zero scaleNe) wave *
          Complex.exp (-Complex.I * integerWavePhase wave center) *
          Complex.exp (Complex.I * integerWavePhase wave x) =
        tensorSchwartzFourierCoefficient
            test scale⁻¹ (inv_ne_zero scaleNe) wave *
          UnitAddTorus.mFourier wave
            (fun coordinate =>
              ((shiftedPoint coordinate : ℝ) : UnitAddCircle))
    rw [unitAddTorus_mFourier_physicalSpace]
    rw [mul_assoc, ← Complex.exp_add]
    congr 1
    dsimp only [shiftedPoint]
    rw [integerWavePhase_sub]
    push_cast
    ring_nf
  rw [seriesEq]
  have periodized := tensorSchwartzPeriodicTest_apply
    test scale⁻¹ (inv_ne_zero scaleNe)
    (fun coordinate => scale⁻¹ * shiftedPoint coordinate)
  have pointEq :
      (fun coordinate =>
        ((scale⁻¹ * shiftedPoint coordinate / scale⁻¹ : ℝ) :
          UnitAddCircle)) =
        (fun coordinate =>
          ((shiftedPoint coordinate : ℝ) : UnitAddCircle)) := by
    funext coordinate
    congr 1
    field_simp [scaleNe]
  rw [pointEq] at periodized
  rw [periodized]
  congr 1
  funext coordinate
  congr 1
  funext shift
  simp [shiftedPoint, mul_add]

private theorem recenteredComplexFourierSeries_eq_tensorProduct_on_fixedBall
    (spatialTest : Coordinate → SchwartzMap Real Complex)
    (scale : Real)
    (scalePos : 0 < scale)
    (center : PhysicalSpace)
    (supportRadius observationRadius : Real)
    (periodLarge : supportRadius + observationRadius < scale⁻¹)
    (support : ∀ coordinate y,
      supportRadius < |y| → spatialTest coordinate y = 0)
    (point : PhysicalSpace)
    (pointNormLe : ‖point‖ ≤ observationRadius) :
    (∑' wave : IntegerWavevector,
      recenteredTensorSchwartzFourierCoefficient spatialTest scale
          scalePos.ne' center wave *
        Complex.exp
          (Complex.I *
            integerWavePhase wave (center + scale • point))) =
      ∏ coordinate : Coordinate, spatialTest coordinate (point coordinate) := by
  let coefficient : IntegerWavevector → Complex := fun wave =>
    recenteredTensorSchwartzFourierCoefficient spatialTest scale
      scalePos.ne' center wave
  have c2Summable :=
    recenteredTensorSchwartzFourierCoefficient_c2_summable
      spatialTest scale scalePos.ne' center
  have coefficientNormSummable : Summable fun wave : IntegerWavevector =>
      ‖coefficient wave‖ := by
    apply c2Summable.of_nonneg_of_le (fun wave => norm_nonneg _)
    intro wave
    have normSqNonneg := integerWaveNormSq_nonneg wave
    nlinarith [norm_nonneg (coefficient wave)]
  have seriesSummable : Summable fun wave : IntegerWavevector =>
      coefficient wave • UnitAddTorus.mFourier wave := by
    apply Summable.of_norm
    convert coefficientNormSummable using 1
    funext wave
    rw [norm_smul, UnitAddTorus.mFourier_norm, mul_one]
  have pointCoordinateLe (coordinate : Coordinate) :
      |point coordinate| ≤ observationRadius := by
    have coordinateLe : ‖point coordinate‖ ≤ ‖point‖ :=
      PiLp.norm_apply_le point coordinate
    simpa only [Real.norm_eq_abs] using coordinateLe.trans pointNormLe
  have remoteEq (coordinate : Coordinate) :
      (∑' shift : Int,
        spatialTest coordinate
          (scale⁻¹ *
            ((center + scale • point) coordinate - center coordinate +
              shift))) = spatialTest coordinate (point coordinate) := by
    have valueEq :=
      scaledSchwartzTest_periodization_eq_self_of_compactSupport
        (spatialTest coordinate) supportRadius observationRadius scale⁻¹
        (point coordinate) (inv_pos.mpr scalePos) periodLarge
        (pointCoordinateLe coordinate) (support coordinate)
    calc
      (∑' shift : Int,
          spatialTest coordinate
            (scale⁻¹ *
              ((center + scale • point) coordinate - center coordinate +
                shift))) =
        ∑' shift : Int,
          spatialTest coordinate
            (point coordinate + scale⁻¹ * shift) := by
          apply tsum_congr
          intro shift
          congr 1
          simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
          field_simp [scalePos.ne']
          ring
      _ = spatialTest coordinate (point coordinate) := valueEq
  have complexSeriesEq :
      (∑' wave : IntegerWavevector,
        coefficient wave *
          Complex.exp
            (Complex.I * integerWavePhase wave (center + scale • point))) =
        ∏ coordinate : Coordinate, spatialTest coordinate (point coordinate) := by
    calc
      (∑' wave : IntegerWavevector,
          coefficient wave *
            Complex.exp
              (Complex.I * integerWavePhase wave (center + scale • point))) =
        (∑' wave : IntegerWavevector,
          coefficient wave • UnitAddTorus.mFourier wave)
            (fun coordinate =>
              (((center + scale • point) coordinate : Real) :
                UnitAddCircle)) := by
          rw [← ContinuousMap.tsum_apply seriesSummable]
          apply tsum_congr
          intro wave
          rw [ContinuousMap.smul_apply, smul_eq_mul]
          rw [unitAddTorus_mFourier_physicalSpace]
      _ = ∏ coordinate : Coordinate,
          ∑' shift : Int,
            spatialTest coordinate
              (scale⁻¹ *
                ((center + scale • point) coordinate - center coordinate +
                  shift)) := by
        rw [← ContinuousMap.tsum_apply seriesSummable]
        simpa only [ContinuousMap.smul_apply, smul_eq_mul, coefficient] using
          recenteredTensorSchwartzFourierSeries_physical_eq spatialTest scale
            scalePos.ne' center (center + scale • point)
      _ = ∏ coordinate : Coordinate,
          spatialTest coordinate (point coordinate) := by
        apply Finset.prod_congr rfl
        intro coordinate _coordinateMem
        exact remoteEq coordinate
  exact complexSeriesEq

private theorem recenteredRealFourierSeries_eq_tensorProduct_on_fixedBall
    (spatialTest : Coordinate → SchwartzMap Real Complex)
    (scale : Real)
    (scalePos : 0 < scale)
    (center : PhysicalSpace)
    (testCoordinate : Coordinate)
    (supportRadius observationRadius : Real)
    (periodLarge : supportRadius + observationRadius < scale⁻¹)
    (support : ∀ coordinate y,
      supportRadius < |y| → spatialTest coordinate y = 0)
    (point : PhysicalSpace)
    (pointNormLe : ‖point‖ ≤ observationRadius) :
    (∑' wave : IntegerWavevector,
      realComplexFourierMode wave
        (Pi.single testCoordinate
          (recenteredTensorSchwartzFourierCoefficient spatialTest scale
            scalePos.ne' center wave))
        (center + scale • point) testCoordinate) =
      (∏ coordinate : Coordinate, spatialTest coordinate (point coordinate)).re := by
  let coefficient : IntegerWavevector → Complex := fun wave =>
    recenteredTensorSchwartzFourierCoefficient spatialTest scale
      scalePos.ne' center wave
  have c2Summable :=
    recenteredTensorSchwartzFourierCoefficient_c2_summable
      spatialTest scale scalePos.ne' center
  have coefficientNormSummable : Summable fun wave : IntegerWavevector =>
      ‖coefficient wave‖ := by
    apply c2Summable.of_nonneg_of_le (fun wave => norm_nonneg _)
    intro wave
    have normSqNonneg := integerWaveNormSq_nonneg wave
    nlinarith [norm_nonneg (coefficient wave)]
  rw [recenteredRealFourierSeries_apply_same_eq_re_complexSeries
    coefficient coefficientNormSummable testCoordinate
      (center + scale • point)]
  exact congrArg Complex.re
    (recenteredComplexFourierSeries_eq_tensorProduct_on_fixedBall
      spatialTest scale scalePos center supportRadius observationRadius
        periodLarge support point pointNormLe)

private theorem recenteredRealFourierSeries_smul_eq_tensorProduct_on_fixedBall
    (spatialTest : Coordinate → SchwartzMap Real Complex)
    (scale : Real)
    (scalePos : 0 < scale)
    (center : PhysicalSpace)
    (testCoordinate : Coordinate)
    (scalar : Complex)
    (supportRadius observationRadius : Real)
    (periodLarge : supportRadius + observationRadius < scale⁻¹)
    (support : ∀ coordinate y,
      supportRadius < |y| → spatialTest coordinate y = 0)
    (point : PhysicalSpace)
    (pointNormLe : ‖point‖ ≤ observationRadius) :
    (∑' wave : IntegerWavevector,
      realComplexFourierMode wave
        (Pi.single testCoordinate
          (scalar *
            recenteredTensorSchwartzFourierCoefficient spatialTest scale
              scalePos.ne' center wave))
        (center + scale • point) testCoordinate) =
      (scalar *
        ∏ coordinate : Coordinate,
          spatialTest coordinate (point coordinate)).re := by
  let coefficient : IntegerWavevector → Complex := fun wave =>
    recenteredTensorSchwartzFourierCoefficient spatialTest scale
      scalePos.ne' center wave
  have c2Summable :=
    recenteredTensorSchwartzFourierCoefficient_c2_summable
      spatialTest scale scalePos.ne' center
  have coefficientNormSummable : Summable fun wave : IntegerWavevector =>
      ‖coefficient wave‖ := by
    apply c2Summable.of_nonneg_of_le (fun wave => norm_nonneg _)
    intro wave
    have normSqNonneg := integerWaveNormSq_nonneg wave
    nlinarith [norm_nonneg (coefficient wave)]
  have scalarCoefficientNormSummable :
      Summable fun wave : IntegerWavevector => ‖scalar * coefficient wave‖ := by
    simpa only [norm_mul] using coefficientNormSummable.mul_left ‖scalar‖
  rw [recenteredRealFourierSeries_apply_same_eq_re_complexSeries
    (fun wave => scalar * coefficient wave) scalarCoefficientNormSummable
      testCoordinate (center + scale • point)]
  rw [show (∑' wave : IntegerWavevector,
      scalar * coefficient wave *
        Complex.exp
          (Complex.I * integerWavePhase wave (center + scale • point))) =
      scalar *
        ∑' wave : IntegerWavevector,
          coefficient wave *
            Complex.exp
              (Complex.I * integerWavePhase wave
                (center + scale • point)) by
    rw [← tsum_mul_left]
    apply tsum_congr
    intro wave
    ring]
  rw [recenteredComplexFourierSeries_eq_tensorProduct_on_fixedBall
    spatialTest scale scalePos center supportRadius observationRadius
      periodLarge support point pointNormLe]

private theorem recenteredRealFourierSeries_smul_scaledDerivative_eq_tensorLineDeriv
    (spatialTest : Coordinate → SchwartzMap Real Complex)
    (scale : Real)
    (scalePos : 0 < scale)
    (scaleLeOne : scale ≤ 1)
    (center : PhysicalSpace)
    (testCoordinate direction : Coordinate)
    (scalar : Complex)
    (supportRadius observationRadius : Real)
    (periodLarge : supportRadius + (observationRadius + 1) < scale⁻¹)
    (support : ∀ coordinate y,
      supportRadius < |y| → spatialTest coordinate y = 0)
    (point : PhysicalSpace)
    (pointNormLe : ‖point‖ ≤ observationRadius) :
    (∑' wave : IntegerWavevector,
      scale *
        realComplexFourierMode wave
          (angularDerivativeCoefficient
            (fun _ => Pi.single testCoordinate
              (scalar *
                recenteredTensorSchwartzFourierCoefficient spatialTest scale
                  scalePos.ne' center wave)) direction wave)
          (center + scale • point) testCoordinate) =
      deriv
        (fun z : Real =>
          (scalar *
            ∏ coordinate : Coordinate,
              spatialTest coordinate
                (((point + z • EuclideanSpace.single direction 1 :
                    PhysicalSpace))
                  coordinate)).re)
        0 := by
  let coefficient : IntegerWavevector → Complex := fun wave =>
    recenteredTensorSchwartzFourierCoefficient spatialTest scale
      scalePos.ne' center wave
  let scalarCoefficient : IntegerWavevector → Complex := fun wave =>
    scalar * coefficient wave
  have c2Summable :=
    recenteredTensorSchwartzFourierCoefficient_c2_summable
      spatialTest scale scalePos.ne' center
  have scalarC2Summable : Summable fun wave : IntegerWavevector =>
      (1 + integerWaveNormSq wave) * ‖scalarCoefficient wave‖ := by
    have scaled := c2Summable.mul_left ‖scalar‖
    exact scaled.congr fun wave => by
      dsimp only [scalarCoefficient]
      rw [norm_mul]
      ring
  let seriesLine : Real → Real := fun z =>
    ∑' wave : IntegerWavevector,
      realComplexFourierMode wave
        (Pi.single testCoordinate (scalarCoefficient wave))
        (center + scale • point +
          z • (scale • EuclideanSpace.single direction 1))
        testCoordinate
  let tensorLine : Real → Real := fun z =>
    (scalar *
      ∏ coordinate : Coordinate,
        spatialTest coordinate
          ((point + z • EuclideanSpace.single direction 1 : PhysicalSpace)
            coordinate)).re
  have seriesDerivative : HasDerivAt seriesLine
      (∑' wave : IntegerWavevector,
        scale *
          realComplexFourierMode wave
            (angularDerivativeCoefficient
              (fun _ => Pi.single testCoordinate (scalarCoefficient wave))
              direction wave)
            (center + scale • point) testCoordinate) 0 := by
    simpa only [seriesLine, zero_smul, add_zero] using
      recenteredRealFourierSeries_scaledLine_hasDerivAt scalarCoefficient
        scalarC2Summable testCoordinate direction testCoordinate scale
        scalePos.le scaleLeOne center point 0
  have localEq : seriesLine =ᶠ[nhds (0 : Real)] tensorLine := by
    have neighborhood : Ioo (-1 : Real) 1 ∈ nhds (0 : Real) :=
      Ioo_mem_nhds (by norm_num) (by norm_num)
    filter_upwards [neighborhood] with z zMem
    let shiftedPoint : PhysicalSpace :=
      point + z • EuclideanSpace.single direction 1
    have singleNorm :
        ‖(EuclideanSpace.single direction (1 : Real) : PhysicalSpace)‖ = 1 := by
      simp
    have shiftedNormLe : ‖shiftedPoint‖ ≤ observationRadius + 1 := by
      calc
        ‖shiftedPoint‖ ≤ ‖point‖ +
            ‖z • (EuclideanSpace.single direction (1 : Real) :
              PhysicalSpace)‖ := norm_add_le _ _
        _ = ‖point‖ + |z| := by
          rw [norm_smul, Real.norm_eq_abs, singleNorm, mul_one]
        _ ≤ observationRadius + 1 := by
          have zAbsLt : |z| < 1 := abs_lt.mpr zMem
          linarith
    have fieldEq := recenteredRealFourierSeries_smul_eq_tensorProduct_on_fixedBall
      spatialTest scale scalePos center testCoordinate scalar supportRadius
        (observationRadius + 1) periodLarge support shiftedPoint shiftedNormLe
    dsimp only [shiftedPoint, coefficient, scalarCoefficient] at fieldEq
    dsimp only [seriesLine, tensorLine, shiftedPoint]
    simpa only [smul_add, smul_smul, mul_comm, add_assoc] using fieldEq
  calc
    (∑' wave : IntegerWavevector,
        scale *
          realComplexFourierMode wave
            (angularDerivativeCoefficient
              (fun _ => Pi.single testCoordinate
                (scalar *
                  recenteredTensorSchwartzFourierCoefficient spatialTest scale
                    scalePos.ne' center wave)) direction wave)
            (center + scale • point) testCoordinate) =
      deriv seriesLine 0 := by
        simpa only [coefficient, scalarCoefficient] using
          seriesDerivative.deriv.symm
    _ = deriv tensorLine 0 := localEq.deriv_eq
    _ = _ := rfl

private def tensorSchwartzProduct
    (spatialTest : Coordinate → SchwartzMap Real Complex)
    (point : PhysicalSpace) : Complex :=
  ∏ coordinate : Coordinate, spatialTest coordinate (point coordinate)

private theorem tensorSchwartzProduct_contDiff
    (spatialTest : Coordinate → SchwartzMap Real Complex) :
    ContDiff Real ∞ (tensorSchwartzProduct spatialTest) := by
  unfold tensorSchwartzProduct
  apply contDiff_prod
  intro coordinate _coordinateMem
  have coordinateSmooth : ContDiff Real ∞
      (fun point : PhysicalSpace => point coordinate) := by
    fun_prop
  exact ((spatialTest coordinate).smooth (⊤ : ℕ∞)).comp coordinateSmooth

private theorem tensorSchwartzProduct_smul_line_hasDerivAt
    (spatialTest : Coordinate → SchwartzMap Real Complex)
    (scalar : Complex)
    (point : PhysicalSpace)
    (direction : Coordinate) :
    HasDerivAt
      (fun z : Real =>
        (scalar * tensorSchwartzProduct spatialTest
          (point + z • EuclideanSpace.single direction 1)).re)
      (scalar *
        fderiv Real (tensorSchwartzProduct spatialTest) point
          (EuclideanSpace.single direction 1)).re
      0 := by
  have lineDerivative : HasDerivAt
      (fun z : Real =>
        point + z • EuclideanSpace.single direction 1)
      (EuclideanSpace.single direction 1) 0 := by
    simpa using
      ((hasDerivAt_id (𝕜 := Real) (0 : Real)).smul_const
        (EuclideanSpace.single direction 1)).const_add point
  have spatialDifferentiable :
      Differentiable Real (tensorSchwartzProduct spatialTest) :=
    (tensorSchwartzProduct_contDiff spatialTest).differentiable (by simp)
  have spatialDerivative : HasFDerivAt
      (tensorSchwartzProduct spatialTest)
      (fderiv Real (tensorSchwartzProduct spatialTest) point) point :=
    spatialDifferentiable.differentiableAt.hasFDerivAt
  have spatialDerivativeAtLine : HasFDerivAt
      (tensorSchwartzProduct spatialTest)
      (fderiv Real (tensorSchwartzProduct spatialTest) point)
      (point + (0 : Real) • EuclideanSpace.single direction 1) := by
    simpa using spatialDerivative
  have lineSpatialDerivative := spatialDerivativeAtLine.comp_hasDerivAt 0
      lineDerivative
  have productDerivative :=
    (hasDerivAt_const (x := (0 : Real)) (c := scalar)).mul
      lineSpatialDerivative
  have realDerivative :=
    (hasDerivAt_const (x := (0 : Real)) Complex.reCLM).clm_apply
      productDerivative
  simpa only [Function.comp_apply, zero_mul, zero_add, Pi.mul_apply,
    zero_apply, Complex.reCLM_apply] using realDerivative

private def fixedTensorSchwartzTestRaw
    (spatialTest : Coordinate → SchwartzMap Real Complex)
    (temporalTest : SchwartzMap Real Complex)
    (normalizedTimeOffset : Real)
    (testCoordinate velocityCoordinate vorticityCoordinate : Coordinate)
    (scaledTime : Real) (scaledPoint : PhysicalSpace) : Real :=
  let temporalScalar := star (temporalTest (scaledTime + normalizedTimeOffset))
  let directionalValue := fun direction : Coordinate =>
    (temporalScalar *
      fderiv Real (tensorSchwartzProduct spatialTest) scaledPoint
        (EuclideanSpace.single direction 1)).re
  (Pi.single testCoordinate (directionalValue velocityCoordinate) :
      Coordinate → Real) vorticityCoordinate -
    (Pi.single testCoordinate (directionalValue vorticityCoordinate) :
      Coordinate → Real) velocityCoordinate

private def fixedTensorSchwartzTest
    (timeLength spatialRadius : Real)
    (spatialTest : Coordinate → SchwartzMap Real Complex)
    (temporalTest : SchwartzMap Real Complex)
    (normalizedTimeOffset : Real)
    (testCoordinate velocityCoordinate vorticityCoordinate : Coordinate) :
    Cylinder timeLength spatialRadius → Real := fun point =>
  fixedTensorSchwartzTestRaw spatialTest temporalTest normalizedTimeOffset
    testCoordinate velocityCoordinate vorticityCoordinate point.1.1 point.2.1

private theorem fixedTensorSchwartzTest_continuous
    (timeLength spatialRadius : Real)
    (spatialTest : Coordinate → SchwartzMap Real Complex)
    (temporalTest : SchwartzMap Real Complex)
    (normalizedTimeOffset : Real)
    (testCoordinate velocityCoordinate vorticityCoordinate : Coordinate) :
    Continuous
      (fixedTensorSchwartzTest timeLength spatialRadius spatialTest
        temporalTest normalizedTimeOffset testCoordinate velocityCoordinate
          vorticityCoordinate) := by
  have temporalContinuous : Continuous
      (fun point : Cylinder timeLength spatialRadius =>
        star (temporalTest (point.1.1 + normalizedTimeOffset))) := by
    exact Complex.continuous_conj.comp
      ((temporalTest.continuous).comp (by fun_prop))
  have spatialFDerivContinuous : Continuous
      (fderiv Real (tensorSchwartzProduct spatialTest)) :=
    (tensorSchwartzProduct_contDiff spatialTest).continuous_fderiv (by simp)
  have directionalContinuous (direction : Coordinate) : Continuous
      (fun point : Cylinder timeLength spatialRadius =>
        (star (temporalTest (point.1.1 + normalizedTimeOffset)) *
          fderiv Real (tensorSchwartzProduct spatialTest) point.2.1
            (EuclideanSpace.single direction 1)).re) := by
    have derivativeApplied : Continuous
        (fun point : Cylinder timeLength spatialRadius =>
          fderiv Real (tensorSchwartzProduct spatialTest) point.2.1
            (EuclideanSpace.single direction 1)) := by
      exact (spatialFDerivContinuous.comp (by fun_prop)).clm_apply
        continuous_const
    exact Complex.continuous_re.comp
      (temporalContinuous.mul derivativeApplied)
  unfold fixedTensorSchwartzTest fixedTensorSchwartzTestRaw
  dsimp only
  apply Continuous.sub
  · by_cases coordinateEq : vorticityCoordinate = testCoordinate
    · subst vorticityCoordinate
      simpa using directionalContinuous velocityCoordinate
    · simpa [Pi.single_apply, coordinateEq] using
        (continuous_const : Continuous
          (fun _point : Cylinder timeLength spatialRadius => (0 : Real)))
  · by_cases coordinateEq : velocityCoordinate = testCoordinate
    · subst velocityCoordinate
      simpa using directionalContinuous vorticityCoordinate
    · simpa [Pi.single_apply, coordinateEq] using
        (continuous_const : Continuous
          (fun _point : Cylinder timeLength spatialRadius => (0 : Real)))

/-- One coordinate of the limiting compact tensor-Schwartz test on the
normalized cylinder. -/
def fixedTensorSchwartzBCF
    (timeLength spatialRadius : Real)
    (spatialTest : Coordinate → SchwartzMap Real Complex)
    (temporalTest : SchwartzMap Real Complex)
    (normalizedTimeOffset : Real)
    (testCoordinate velocityCoordinate vorticityCoordinate : Coordinate) :
    BoundedContinuousFunction (Cylinder timeLength spatialRadius) Real :=
  BoundedContinuousFunction.mkOfCompact
    ⟨fixedTensorSchwartzTest timeLength spatialRadius spatialTest temporalTest
      normalizedTimeOffset testCoordinate velocityCoordinate
        vorticityCoordinate,
      fixedTensorSchwartzTest_continuous timeLength spatialRadius spatialTest
        temporalTest normalizedTimeOffset testCoordinate velocityCoordinate
          vorticityCoordinate⟩

private theorem recenteredRealFourierSeries_smul_scaledDerivative_coordinate_eq
    (spatialTest : Coordinate → SchwartzMap Real Complex)
    (scale : Real)
    (scalePos : 0 < scale)
    (scaleLeOne : scale ≤ 1)
    (center : PhysicalSpace)
    (testCoordinate direction outputCoordinate : Coordinate)
    (scalar : Complex)
    (supportRadius observationRadius : Real)
    (periodLarge : supportRadius + (observationRadius + 1) < scale⁻¹)
    (support : ∀ coordinate y,
      supportRadius < |y| → spatialTest coordinate y = 0)
    (point : PhysicalSpace)
    (pointNormLe : ‖point‖ ≤ observationRadius) :
    (∑' wave : IntegerWavevector,
      scale *
        realComplexFourierMode wave
          (angularDerivativeCoefficient
            (fun _ => Pi.single testCoordinate
              (scalar *
                recenteredTensorSchwartzFourierCoefficient spatialTest scale
                  scalePos.ne' center wave)) direction wave)
          (center + scale • point) outputCoordinate) =
      (Pi.single testCoordinate
        (scalar *
          fderiv Real (tensorSchwartzProduct spatialTest) point
            (EuclideanSpace.single direction 1)).re : Coordinate → Real)
        outputCoordinate := by
  by_cases outputEq : outputCoordinate = testCoordinate
  · subst outputCoordinate
    rw [recenteredRealFourierSeries_smul_scaledDerivative_eq_tensorLineDeriv
      spatialTest scale scalePos scaleLeOne center testCoordinate direction
        scalar supportRadius observationRadius periodLarge support point
        pointNormLe]
    change deriv
        (fun z : Real =>
          (scalar * tensorSchwartzProduct spatialTest
            (point + z • EuclideanSpace.single direction 1)).re)
        0 = _
    rw [(tensorSchwartzProduct_smul_line_hasDerivAt spatialTest scalar point
      direction).deriv]
    simp
  · have termZero (wave : IntegerWavevector) :
        scale *
          realComplexFourierMode wave
            (angularDerivativeCoefficient
              (fun _ => Pi.single testCoordinate
                (scalar *
                  recenteredTensorSchwartzFourierCoefficient spatialTest scale
                    scalePos.ne' center wave)) direction wave)
            (center + scale • point) outputCoordinate = 0 := by
      simp [angularDerivativeCoefficient, realComplexFourierMode,
        coefficientReal, coefficientImag, outputEq]
    simp_rw [termZero]
    simp [outputEq]

private def scaledProjectedTensorInfiniteTestRaw
    (scale start : Real)
    (scaleNe : scale ≠ 0)
    (center : PhysicalSpace)
    (spatialTest : Coordinate → SchwartzMap Real Complex)
    (temporalTest : SchwartzMap Real Complex)
    (timeCenter : Real)
    (testCoordinate velocityCoordinate vorticityCoordinate : Coordinate)
    (scaledTime : Real) (scaledPoint : PhysicalSpace) : Real :=
  let scalar := star
    (temporalTest ((start + scale ^ 2 * scaledTime - timeCenter) / scale ^ 2))
  let coefficient : IntegerWavevector → Complex := fun wave =>
    scalar *
      recenteredTensorSchwartzFourierCoefficient spatialTest scale
        scaleNe center wave
  (∑' wave : IntegerWavevector,
      scale *
        realComplexFourierMode wave
          (angularDerivativeCoefficient
            (fun _ => Pi.single testCoordinate (coefficient wave))
            velocityCoordinate wave)
          (center + scale • scaledPoint) vorticityCoordinate) -
    ∑' wave : IntegerWavevector,
      scale *
        realComplexFourierMode wave
          (angularDerivativeCoefficient
            (fun _ => Pi.single testCoordinate (coefficient wave))
            vorticityCoordinate wave)
          (center + scale • scaledPoint) velocityCoordinate

private def normalizedScaledDerivativeMode
    (scale : Real)
    (scaleNe : scale ≠ 0)
    (center : PhysicalSpace)
    (spatialTest : Coordinate → SchwartzMap Real Complex)
    (temporalTest : SchwartzMap Real Complex)
    (normalizedTimeOffset : Real)
    (testCoordinate direction outputCoordinate : Coordinate)
    (wave : IntegerWavevector)
    (point : Cylinder timeLength spatialRadius) : Real :=
  let scalar := star (temporalTest (point.1.1 + normalizedTimeOffset))
  scale *
    realComplexFourierMode wave
      (angularDerivativeCoefficient
        (fun _ => Pi.single testCoordinate
          (scalar *
            recenteredTensorSchwartzFourierCoefficient spatialTest scale
              scaleNe center wave)) direction wave)
      (center + scale • point.2.1) outputCoordinate

private theorem normalizedScaledDerivativeMode_abs_le_c2Weight
    (scale : Real)
    (scalePos : 0 < scale)
    (scaleLeOne : scale ≤ 1)
    (center : PhysicalSpace)
    (spatialTest : Coordinate → SchwartzMap Real Complex)
    (temporalTest : SchwartzMap Real Complex)
    (normalizedTimeOffset temporalCeiling : Real)
    (temporalBound : ∀ scaledTime : Icc (0 : Real) timeLength,
      ‖temporalTest (scaledTime.1 + normalizedTimeOffset)‖ ≤ temporalCeiling)
    (testCoordinate direction outputCoordinate : Coordinate)
    (wave : IntegerWavevector)
    (point : Cylinder timeLength spatialRadius) :
    |normalizedScaledDerivativeMode (timeLength := timeLength)
        (spatialRadius := spatialRadius) scale scalePos.ne' center spatialTest
        temporalTest
        normalizedTimeOffset testCoordinate direction outputCoordinate wave
        point| ≤
      ((2 * Real.pi) * temporalCeiling) *
        ((1 + integerWaveNormSq wave) *
          ‖recenteredTensorSchwartzFourierCoefficient spatialTest scale
            scalePos.ne' center wave‖) := by
  let scalar := star (temporalTest (point.1.1 + normalizedTimeOffset))
  let coefficient := recenteredTensorSchwartzFourierCoefficient spatialTest
    scale scalePos.ne' center wave
  have modeBound := scaledLineDerivative_single_abs_le_c2Weight wave
    (scalar * coefficient) testCoordinate direction outputCoordinate scale
    scalePos.le scaleLeOne (center + scale • point.2.1)
  have scalarNorm : ‖scalar‖ =
      ‖temporalTest (point.1.1 + normalizedTimeOffset)‖ := by
    simp [scalar]
  have scalarLe : ‖scalar‖ ≤ temporalCeiling := by
    rw [scalarNorm]
    exact temporalBound point.1
  have temporalCeilingNonneg : 0 ≤ temporalCeiling :=
    (norm_nonneg scalar).trans scalarLe
  unfold normalizedScaledDerivativeMode
  dsimp only
  change |scale *
      realComplexFourierMode wave
        (angularDerivativeCoefficient
          (fun _ => Pi.single testCoordinate (scalar * coefficient)) direction
            wave)
        (center + scale • point.2.1) outputCoordinate| ≤ _
  calc
    _ ≤ (2 * Real.pi) * (1 + integerWaveNormSq wave) *
        ‖scalar * coefficient‖ := modeBound
    _ = (2 * Real.pi) * (1 + integerWaveNormSq wave) *
        (‖scalar‖ * ‖coefficient‖) := by rw [norm_mul]
    _ ≤ (2 * Real.pi) * (1 + integerWaveNormSq wave) *
        (temporalCeiling * ‖coefficient‖) := by
      apply mul_le_mul_of_nonneg_left
      · exact mul_le_mul_of_nonneg_right scalarLe (norm_nonneg _)
      · exact mul_nonneg (by positivity) (by
          have := integerWaveNormSq_nonneg wave
          linarith)
    _ = ((2 * Real.pi) * temporalCeiling) *
        ((1 + integerWaveNormSq wave) *
          ‖recenteredTensorSchwartzFourierCoefficient spatialTest scale
            scalePos.ne' center wave‖) := by
      dsimp only [coefficient]
      ring

private def wholeCellNormalizedScaledDerivativeMode
    (scale : Real)
    (scaleNe : scale ≠ 0)
    (center : PhysicalSpace)
    (spatialTest : Coordinate → SchwartzMap Real Complex)
    (temporalTest : SchwartzMap Real Complex)
    (normalizedTimeOffset : Real)
    (testCoordinate direction outputCoordinate : Coordinate)
    (wave : IntegerWavevector)
    (point : Icc (0 : Real) timeLength × PhysicalSpace) : Real :=
  let scalar := star (temporalTest (point.1.1 + normalizedTimeOffset))
  scale *
    realComplexFourierMode wave
      (angularDerivativeCoefficient
        (fun _ => Pi.single testCoordinate
          (scalar *
            recenteredTensorSchwartzFourierCoefficient spatialTest scale
              scaleNe center wave)) direction wave)
      (center + scale • point.2) outputCoordinate

private def wholeCellRecenteredTensorMode
    (scale : Real)
    (scaleNe : scale ≠ 0)
    (center : PhysicalSpace)
    (spatialTest : Coordinate → SchwartzMap Real Complex)
    (scalar : Complex)
    (testCoordinate : Coordinate)
    (wave : IntegerWavevector)
    (point : PhysicalSpace) : PhysicalSpace :=
  realComplexFourierMode wave
    (Pi.single testCoordinate
      (scalar * recenteredTensorSchwartzFourierCoefficient spatialTest scale
        scaleNe center wave)) point

private theorem wholeCellRecenteredTensorMode_tendstoUniformly
    (scale : Real)
    (scaleNe : scale ≠ 0)
    (center : PhysicalSpace)
    (spatialTest : Coordinate → SchwartzMap Real Complex)
    (scalar : Complex)
    (testCoordinate : Coordinate) :
    TendstoUniformlyOn
      (fun radius : Nat => fun point : PhysicalSpace =>
        ∑ wave ∈ integerWaveFrequencyCube radius,
          wholeCellRecenteredTensorMode scale scaleNe center spatialTest
            scalar testCoordinate wave point)
      (fun point : PhysicalSpace =>
        ∑' wave : IntegerWavevector,
          wholeCellRecenteredTensorMode scale scaleNe center spatialTest
            scalar testCoordinate wave point)
      atTop Set.univ := by
  have c2Summable :=
    recenteredTensorSchwartzFourierCoefficient_c2_summable
      spatialTest scale scaleNe center
  have coefficientNormSummable : Summable fun wave : IntegerWavevector =>
      ‖scalar * recenteredTensorSchwartzFourierCoefficient spatialTest scale
        scaleNe center wave‖ := by
    simpa only [norm_mul] using
      (c2Summable.of_nonneg_of_le (fun wave => norm_nonneg _) (fun wave => by
        have normSqNonneg := integerWaveNormSq_nonneg wave
        nlinarith [norm_nonneg
          (recenteredTensorSchwartzFourierCoefficient spatialTest scale
            scaleNe center wave)])).mul_left ‖scalar‖
  have uniform : TendstoUniformlyOn
      (fun modes : Finset IntegerWavevector => fun point : PhysicalSpace =>
        ∑ wave ∈ modes,
          wholeCellRecenteredTensorMode scale scaleNe center spatialTest
            scalar testCoordinate wave point)
      (fun point : PhysicalSpace =>
        ∑' wave : IntegerWavevector,
          wholeCellRecenteredTensorMode scale scaleNe center spatialTest
            scalar testCoordinate wave point)
      atTop Set.univ := by
    apply tendstoUniformlyOn_tsum coefficientNormSummable
    intro wave point _pointMem
    exact realComplexFourierMode_single_norm_le wave
      (scalar * recenteredTensorSchwartzFourierCoefficient spatialTest scale
        scaleNe center wave) testCoordinate point
  rw [Metric.tendstoUniformlyOn_iff] at uniform ⊢
  intro epsilon epsilonPos
  exact integerWaveFrequencyCube_tendsto_atTop.eventually
    (uniform epsilon epsilonPos)

private theorem wholeCellRecenteredTensorMode_tsum_eq_periodized
    (scale : Real)
    (scaleNe : scale ≠ 0)
    (center : PhysicalSpace)
    (spatialTest : Coordinate → SchwartzMap Real Complex)
    (scalar : Complex)
    (testCoordinate : Coordinate)
    (point : PhysicalSpace) :
    (∑' wave : IntegerWavevector,
      wholeCellRecenteredTensorMode scale scaleNe center spatialTest scalar
        testCoordinate wave point) =
      periodizedCentralTensorVectorTest spatialTest scale center scalar
        testCoordinate point := by
  let coefficient : IntegerWavevector → Complex := fun wave =>
    recenteredTensorSchwartzFourierCoefficient spatialTest scale scaleNe
      center wave
  have c2Summable :=
    recenteredTensorSchwartzFourierCoefficient_c2_summable
      spatialTest scale scaleNe center
  have coefficientNormSummable : Summable fun wave : IntegerWavevector =>
      ‖coefficient wave‖ := by
    apply c2Summable.of_nonneg_of_le (fun wave => norm_nonneg _)
    intro wave
    have normSqNonneg := integerWaveNormSq_nonneg wave
    nlinarith [norm_nonneg (coefficient wave)]
  have scalarCoefficientNormSummable :
      Summable fun wave : IntegerWavevector => ‖scalar * coefficient wave‖ := by
    simpa only [norm_mul] using coefficientNormSummable.mul_left ‖scalar‖
  have modeSummable : Summable fun wave : IntegerWavevector =>
      wholeCellRecenteredTensorMode scale scaleNe center spatialTest scalar
        testCoordinate wave point := by
    apply Summable.of_norm
    apply scalarCoefficientNormSummable.of_nonneg_of_le
      (fun wave => norm_nonneg _)
    intro wave
    exact realComplexFourierMode_single_norm_le wave
      (scalar * coefficient wave) testCoordinate point
  ext outputCoordinate
  change (EuclideanSpace.proj outputCoordinate)
      (∑' wave : IntegerWavevector,
        wholeCellRecenteredTensorMode scale scaleNe center spatialTest scalar
          testCoordinate wave point) =
    (EuclideanSpace.proj outputCoordinate)
      (periodizedCentralTensorVectorTest spatialTest scale center scalar
        testCoordinate point)
  rw [(EuclideanSpace.proj outputCoordinate).map_tsum modeSummable]
  by_cases outputEq : outputCoordinate = testCoordinate
  · subst outputCoordinate
    change (∑' wave : IntegerWavevector,
      realComplexFourierMode wave
        (Pi.single testCoordinate (scalar * coefficient wave)) point
          testCoordinate) = _
    rw [recenteredRealFourierSeries_apply_same_eq_re_complexSeries
      (fun wave => scalar * coefficient wave) scalarCoefficientNormSummable
      testCoordinate point]
    rw [show (∑' wave : IntegerWavevector,
        scalar * coefficient wave *
          Complex.exp (Complex.I * integerWavePhase wave point)) =
        scalar *
          ∑' wave : IntegerWavevector,
            coefficient wave *
              Complex.exp (Complex.I * integerWavePhase wave point) by
      rw [← tsum_mul_left]
      apply tsum_congr
      intro wave
      ring]
    rw [show (∑' wave : IntegerWavevector,
        coefficient wave *
          Complex.exp (Complex.I * integerWavePhase wave point)) =
        ∏ coordinate : Coordinate,
          ∑' shift : Int,
            spatialTest coordinate
              (scale⁻¹ *
                (point coordinate - center coordinate + shift)) by
      have seriesEq :=
        recenteredTensorSchwartzFourierSeries_physical_eq spatialTest scale
          scaleNe center point
      rw [show (∑' wave : IntegerWavevector,
          coefficient wave *
            Complex.exp (Complex.I * integerWavePhase wave point)) =
          ∑' wave : IntegerWavevector,
            recenteredTensorSchwartzFourierCoefficient spatialTest scale
                scaleNe center wave *
              UnitAddTorus.mFourier wave
                (fun coordinate =>
                  (((point coordinate : Real)) : UnitAddCircle)) by
        apply tsum_congr
        intro wave
        dsimp only [coefficient]
        rw [unitAddTorus_mFourier_physicalSpace]]
      exact seriesEq]
    simp [periodizedCentralTensorVectorTest, EuclideanSpace.coe_proj]
  · have termZero (wave : IntegerWavevector) :
        (EuclideanSpace.proj outputCoordinate)
          (wholeCellRecenteredTensorMode scale scaleNe center spatialTest
            scalar testCoordinate wave point) = 0 := by
      simp [wholeCellRecenteredTensorMode, realComplexFourierMode,
        coefficientReal, coefficientImag, outputEq,
        EuclideanSpace.coe_proj]
    simp_rw [termZero]
    rw [tsum_zero]
    simp [periodizedCentralTensorVectorTest, outputEq,
      EuclideanSpace.coe_proj]

private theorem abs_velocityDot_apply_le_norm_mul_norm
    (left right : PhysicalSpace) :
    |∑ coordinate : Coordinate, left coordinate * right coordinate| ≤
      ‖left‖ * ‖right‖ := by
  simpa only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial,
    ofReal_mul, Complex.norm_real, Real.norm_eq_abs,
    Real.norm_of_nonneg (norm_nonneg _), mul_comm] using
      (abs_real_inner_le_norm right left)

private theorem wholeCellRecenteredTensor_pairing_tendsto_periodized
    (scale : Real)
    (scaleNe : scale ≠ 0)
    (center : PhysicalSpace)
    (spatialTest : Coordinate → SchwartzMap Real Complex)
    (scalar : Complex)
    (testCoordinate : Coordinate)
    (field : PhysicalSpace → PhysicalSpace)
    (fieldContinuous : Continuous field)
    (fieldCeiling : Real)
    (fieldBound : ∀ point ∈ physicalUnitCell,
      ‖field point‖ ≤ fieldCeiling) :
    Tendsto
      (fun radius : Nat =>
        ∫ point in physicalUnitCell,
          velocityDot
            (finiteRealComplexFourierField
              (integerWaveFrequencyCube radius)
              (fun wave => Pi.single testCoordinate
                (scalar * recenteredTensorSchwartzFourierCoefficient
                  spatialTest scale scaleNe center wave))) field point)
      atTop
      (nhds
        (∫ point in physicalUnitCell,
          velocityDot
            (periodizedCentralTensorVectorTest spatialTest scale center scalar
              testCoordinate) field point)) := by
  let coefficient : IntegerWavevector → Complex := fun wave =>
    recenteredTensorSchwartzFourierCoefficient spatialTest scale scaleNe
      center wave
  let finiteTest : Nat → PhysicalSpace → PhysicalSpace := fun radius point =>
    finiteRealComplexFourierField (integerWaveFrequencyCube radius)
      (fun wave => Pi.single testCoordinate (scalar * coefficient wave)) point
  let limitTest : PhysicalSpace → PhysicalSpace :=
    periodizedCentralTensorVectorTest spatialTest scale center scalar
      testCoordinate
  let density : Nat → PhysicalSpace → Real := fun radius point =>
    velocityDot (finiteTest radius) field point
  let limitDensity : PhysicalSpace → Real := fun point =>
    velocityDot limitTest field point
  have c2Summable :=
    recenteredTensorSchwartzFourierCoefficient_c2_summable
      spatialTest scale scaleNe center
  have coefficientNormSummable : Summable fun wave : IntegerWavevector =>
      ‖scalar * coefficient wave‖ := by
    have unscaled : Summable fun wave : IntegerWavevector =>
        ‖coefficient wave‖ := by
      apply c2Summable.of_nonneg_of_le (fun wave => norm_nonneg _)
      intro wave
      have normSqNonneg := integerWaveNormSq_nonneg wave
      nlinarith [norm_nonneg (coefficient wave)]
    simpa only [norm_mul] using unscaled.mul_left ‖scalar‖
  let testCeiling : Real := ∑' wave : IntegerWavevector,
    ‖scalar * coefficient wave‖
  have testCeilingNonneg : 0 ≤ testCeiling := tsum_nonneg fun _ => norm_nonneg _
  have finiteTestNormLe (radius : Nat) (point : PhysicalSpace) :
      ‖finiteTest radius point‖ ≤ testCeiling := by
    calc
      ‖finiteTest radius point‖ ≤
          ∑ wave ∈ integerWaveFrequencyCube radius,
            ‖scalar * coefficient wave‖ := by
        dsimp only [finiteTest]
        unfold finiteRealComplexFourierField
        apply (norm_sum_le _ _).trans
        apply Finset.sum_le_sum
        intro wave _waveMem
        exact realComplexFourierMode_single_norm_le wave
          (scalar * coefficient wave) testCoordinate point
      _ ≤ testCeiling := by
        exact Summable.sum_le_tsum (f := fun wave : IntegerWavevector =>
          ‖scalar * coefficient wave‖) (integerWaveFrequencyCube radius)
            (fun _ _ => norm_nonneg _) coefficientNormSummable
  have finiteTestContinuous (radius : Nat) : Continuous (finiteTest radius) := by
    dsimp only [finiteTest]
    exact (finiteRealComplexFourierField_contDiff
      (integerWaveFrequencyCube radius)
      (fun wave => Pi.single testCoordinate (scalar * coefficient wave)))
      |>.continuous
  have uniform := wholeCellRecenteredTensorMode_tendstoUniformly scale scaleNe
    center spatialTest scalar testCoordinate
  have finiteTestTendsto (point : PhysicalSpace) :
      Tendsto (fun radius => finiteTest radius point) atTop
        (nhds (limitTest point)) := by
    have pointTendsto := uniform.tendsto_at (Set.mem_univ point)
    rw [wholeCellRecenteredTensorMode_tsum_eq_periodized
      scale scaleNe center spatialTest scalar testCoordinate point] at pointTendsto
    simpa only [finiteTest, limitTest, wholeCellRecenteredTensorMode,
      finiteRealComplexFourierField] using pointTendsto
  let bound : PhysicalSpace → Real := fun _ => testCeiling * fieldCeiling
  apply tendsto_integral_of_dominated_convergence bound
  · intro radius
    exact (projectedPairing_velocityDot_continuous
      (finiteTest radius) field (finiteTestContinuous radius)
        fieldContinuous).aestronglyMeasurable.mono_measure
          Measure.restrict_le_self
  · change IntegrableOn
      (fun _ : PhysicalSpace => testCeiling * fieldCeiling)
      physicalUnitCell volume
    exact integrableOn_const
      physicalUnitCell_isCompact.measure_lt_top.ne
  · intro radius
    filter_upwards
      [ae_restrict_mem physicalUnitCell_isCompact.measurableSet] with
        point pointMem
    rw [Real.norm_eq_abs]
    exact (abs_velocityDot_apply_le_norm_mul_norm
      (finiteTest radius point) (field point)).trans
        (mul_le_mul (finiteTestNormLe radius point)
          (fieldBound point pointMem) (norm_nonneg _) testCeilingNonneg)
  · filter_upwards with point
    have vectorTendsto := finiteTestTendsto point
    have coordinateTendsto (coordinate : Coordinate) :
        Tendsto (fun radius => finiteTest radius point coordinate) atTop
          (nhds (limitTest point coordinate)) :=
      ((PiLp.continuous_apply 2 (fun _ : Coordinate => Real) coordinate)
        |>.continuousAt.tendsto).comp vectorTendsto
    dsimp only [density, limitDensity, velocityDot]
    apply tendsto_finsetSum Finset.univ
    intro coordinate _coordinateMem
    exact (coordinateTendsto coordinate).mul_const (field point coordinate)

/-- Finite Fourier tensor tests on the periodic cell converge to the honest
compact physical tensor action.  The compact test is periodized before the
limit, so the statement is valid for every recentering point, including
centers on the boundary of the chosen unit cell. -/
theorem fullCubeProjectedNonlinearTensor_tendsto_affineBall
    (inputRadius : Nat)
    (state : ComplexVorticityHilbertState)
    (zeroRow : state 0 = 0)
    (stateTransverse : WholeStateTransverse state)
    (reality : FiniteStateFourierReality state)
    (spatialTest : Coordinate → SchwartzMap Real Complex)
    (scale : Real) (scalePos : 0 < scale)
    (center : PhysicalSpace)
    (scalar : Complex)
    (testCoordinate : Coordinate)
    (supportRadius spatialRadius : Real)
    (supportRadiusNonneg : 0 ≤ supportRadius)
    (supportInside : 3 * supportRadius < spatialRadius)
    (support : ∀ coordinate y,
      supportRadius < |y| → spatialTest coordinate y = 0) :
    let fullModes := integerWaveFrequencyCube inputRadius
    let inputModes := puncturedIntegerWaveFrequencyCube inputRadius
    let projected := complexSharpSupportProjection fullModes state
    let source := rawSourceOfFiniteVorticityState inputModes projected
    let velocity := physicalVelocity source
    let vorticity := finiteRealComplexFourierField inputModes projected
    Tendsto
      (fun testRadius : Nat =>
        let test := finiteRealComplexFourierField
          (integerWaveFrequencyCube testRadius)
          (fun wave => Pi.single testCoordinate
            (scalar * recenteredTensorSchwartzFourierCoefficient
              spatialTest scale scalePos.ne' center wave))
        ∫ x in physicalUnitCell,
          ∑ velocityCoordinate : Coordinate,
            ∑ vorticityCoordinate : Coordinate,
              (fderiv Real test x
                    (EuclideanSpace.single velocityCoordinate 1)
                      vorticityCoordinate -
                fderiv Real test x
                    (EuclideanSpace.single vorticityCoordinate 1)
                      velocityCoordinate) *
                velocity x velocityCoordinate *
                vorticity x vorticityCoordinate)
      atTop
      (nhds
        (∫ x in
            (fun y : PhysicalSpace => y - center) ⁻¹'
              (scale • Metric.closedBall (0 : PhysicalSpace) spatialRadius),
          ∑ velocityCoordinate : Coordinate,
            ∑ vorticityCoordinate : Coordinate,
              (fderiv Real
                    (centralTensorVectorTest spatialTest scale center scalar
                      testCoordinate) x
                    (EuclideanSpace.single velocityCoordinate 1)
                      vorticityCoordinate -
                fderiv Real
                    (centralTensorVectorTest spatialTest scale center scalar
                      testCoordinate) x
                    (EuclideanSpace.single vorticityCoordinate 1)
                      velocityCoordinate) *
                velocity x velocityCoordinate *
                vorticity x vorticityCoordinate)) := by
  dsimp only
  let fullModes := integerWaveFrequencyCube inputRadius
  let inputModes := puncturedIntegerWaveFrequencyCube inputRadius
  let projected := complexSharpSupportProjection fullModes state
  let source := rawSourceOfFiniteVorticityState inputModes projected
  let velocity := physicalVelocity source
  let vorticity := finiteRealComplexFourierField inputModes projected
  let nonlinear := -vorticityAdvection velocity + vortexStretching velocity
  have projectionEq :
      complexSharpSupportProjection inputModes state = projected := by
    apply lp.ext
    funext wave
    by_cases waveZero : wave = 0
    · subst wave
      simp [inputModes, fullModes, projected,
        puncturedIntegerWaveFrequencyCube,
        complexSharpSupportProjection_apply, zeroRow]
    · by_cases waveMem : wave ∈ fullModes <;>
        simp [inputModes, fullModes, projected,
          puncturedIntegerWaveFrequencyCube,
          complexSharpSupportProjection_apply, waveZero, waveMem]
  have zeroNotMem : 0 ∉ inputModes := by
    exact zero_not_mem_puncturedIntegerWaveFrequencyCube inputRadius
  have negClosed : ∀ wave ∈ inputModes, waveNeg wave ∈ inputModes := by
    intro wave waveMem
    exact puncturedIntegerWaveFrequencyCube_waveNeg_mem inputRadius waveMem
  have supported : ∀ wave, wave ∉ inputModes → projected wave = 0 := by
    intro wave waveNotMem
    rw [← projectionEq]
    simp [complexSharpSupportProjection_apply, waveNotMem]
  have transverse : ∀ wave ∈ inputModes,
      complexWavevector wave ⬝ᵥ projected wave = 0 := by
    intro wave waveMem
    rw [← projectionEq]
    simp only [complexSharpSupportProjection_apply, waveMem, if_true]
    exact stateTransverse wave
  have projectedRealityLaw : FiniteStateFourierReality projected := by
    rw [← projectionEq]
    exact projectedReality inputRadius state reality
  have velocityContDiff : ContDiff Real 2 velocity := by
    exact (physicalVelocity_contDiff source).of_le
      (show (↑(2 : ℕ∞) : WithTop ℕ∞) ≤
          (↑(⊤ : ℕ∞) : WithTop ℕ∞) from
        WithTop.coe_le_coe.mpr le_top)
  have velocityPeriodic : LatticePeriodic velocity :=
    physicalVelocity_latticePeriodic source
  have velocityDivergenceZero : velocityDivergence velocity = 0 :=
    velocityDivergence_physicalVelocity_eq_zero source
  have vorticityEq : vorticityField velocity = vorticity := by
    dsimp only [velocity, vorticity]
    rw [vorticityField_physicalVelocity source]
    exact physicalVorticity_rawSourceOfFinitePhysicalState_eq
      inputModes zeroNotMem negClosed projected supported transverse
        projectedRealityLaw
  have nonlinearContinuous : Continuous nonlinear := by
    have velocityContDiffOne : ContDiff Real 1 velocity :=
      velocityContDiff.of_le (by norm_num)
    have vorticityContDiff : ContDiff Real 1 (vorticityField velocity) :=
      vorticityField_contDiff velocity velocityContDiff
    dsimp only [nonlinear]
    unfold vorticityAdvection vortexStretching
    exact
      ((vorticityContDiff.continuous_fderiv (by norm_num)).clm_apply
        velocityContDiffOne.continuous).neg.add
      ((velocityContDiffOne.continuous_fderiv (by norm_num)).clm_apply
        vorticityContDiff.continuous)
  obtain ⟨fieldCeiling, fieldBound⟩ :=
    physicalUnitCell_isCompact.exists_bound_of_continuousOn
      nonlinearContinuous.continuousOn
  have pairingTendsto :=
    wholeCellRecenteredTensor_pairing_tendsto_periodized scale scalePos.ne'
      center spatialTest scalar testCoordinate nonlinear nonlinearContinuous
      fieldCeiling fieldBound
  have finitePairingEq (testRadius : Nat) :
      (∫ x in physicalUnitCell,
        velocityDot
          (finiteRealComplexFourierField
            (integerWaveFrequencyCube testRadius)
            (fun wave => Pi.single testCoordinate
              (scalar * recenteredTensorSchwartzFourierCoefficient
                spatialTest scale scalePos.ne' center wave))) nonlinear x) =
        ∫ x in physicalUnitCell,
          ∑ velocityCoordinate : Coordinate,
            ∑ vorticityCoordinate : Coordinate,
              (fderiv Real
                    (finiteRealComplexFourierField
                      (integerWaveFrequencyCube testRadius)
                      (fun wave => Pi.single testCoordinate
                        (scalar * recenteredTensorSchwartzFourierCoefficient
                          spatialTest scale scalePos.ne' center wave))) x
                    (EuclideanSpace.single velocityCoordinate 1)
                      vorticityCoordinate -
                fderiv Real
                    (finiteRealComplexFourierField
                      (integerWaveFrequencyCube testRadius)
                      (fun wave => Pi.single testCoordinate
                        (scalar * recenteredTensorSchwartzFourierCoefficient
                          spatialTest scale scalePos.ne' center wave))) x
                    (EuclideanSpace.single vorticityCoordinate 1)
                      velocityCoordinate) *
                velocity x velocityCoordinate *
                vorticity x vorticityCoordinate := by
    let test := finiteRealComplexFourierField
      (integerWaveFrequencyCube testRadius)
      (fun wave => Pi.single testCoordinate
        (scalar * recenteredTensorSchwartzFourierCoefficient
          spatialTest scale scalePos.ne' center wave))
    have testContDiff : ContDiff Real 1 test :=
      (finiteRealComplexFourierField_contDiff
        (integerWaveFrequencyCube testRadius)
        (fun wave => Pi.single testCoordinate
          (scalar * recenteredTensorSchwartzFourierCoefficient
            spatialTest scale scalePos.ne' center wave))).of_le (by norm_num)
    have tensorPairing :=
      physicalUnitCell_vorticityNonlinearity_pairing_eq_tensorProduct
        velocity test velocityContDiff testContDiff velocityPeriodic
        (finiteRealComplexFourierField_latticePeriodic
          (integerWaveFrequencyCube testRadius)
          (fun wave => Pi.single testCoordinate
            (scalar * recenteredTensorSchwartzFourierCoefficient
              spatialTest scale scalePos.ne' center wave)))
        velocityDivergenceZero
    rw [vorticityEq] at tensorPairing
    simpa only [test, nonlinear] using tensorPairing
  have limitEq := periodizedCentralNonlinearity_eq_affineBallTensor
    spatialTest scale scalePos center scalar testCoordinate supportRadius
      spatialRadius supportRadiusNonneg supportInside support velocity
      velocityContDiff velocityPeriodic velocityDivergenceZero
  rw [vorticityEq] at limitEq
  rw [← limitEq]
  convert pairingTendsto using 1
  · funext testRadius
    exact (finitePairingEq testRadius).symm

private theorem wholeCellNormalizedScaledDerivativeMode_abs_le_c2Weight
    (scale : Real)
    (scalePos : 0 < scale)
    (scaleLeOne : scale ≤ 1)
    (center : PhysicalSpace)
    (spatialTest : Coordinate → SchwartzMap Real Complex)
    (temporalTest : SchwartzMap Real Complex)
    (normalizedTimeOffset temporalCeiling : Real)
    (temporalBound : ∀ scaledTime : Icc (0 : Real) timeLength,
      ‖temporalTest (scaledTime.1 + normalizedTimeOffset)‖ ≤ temporalCeiling)
    (testCoordinate direction outputCoordinate : Coordinate)
    (wave : IntegerWavevector)
    (point : Icc (0 : Real) timeLength × PhysicalSpace) :
    |wholeCellNormalizedScaledDerivativeMode (timeLength := timeLength)
        scale scalePos.ne' center spatialTest temporalTest normalizedTimeOffset
        testCoordinate direction outputCoordinate wave point| ≤
      ((2 * Real.pi) * temporalCeiling) *
        ((1 + integerWaveNormSq wave) *
          ‖recenteredTensorSchwartzFourierCoefficient spatialTest scale
            scalePos.ne' center wave‖) := by
  let scalar := star (temporalTest (point.1.1 + normalizedTimeOffset))
  let coefficient := recenteredTensorSchwartzFourierCoefficient spatialTest
    scale scalePos.ne' center wave
  have modeBound := scaledLineDerivative_single_abs_le_c2Weight wave
    (scalar * coefficient) testCoordinate direction outputCoordinate scale
    scalePos.le scaleLeOne (center + scale • point.2)
  have scalarNorm : ‖scalar‖ =
      ‖temporalTest (point.1.1 + normalizedTimeOffset)‖ := by
    simp [scalar]
  have scalarLe : ‖scalar‖ ≤ temporalCeiling := by
    rw [scalarNorm]
    exact temporalBound point.1
  have temporalCeilingNonneg : 0 ≤ temporalCeiling :=
    (norm_nonneg scalar).trans scalarLe
  unfold wholeCellNormalizedScaledDerivativeMode
  dsimp only
  change |scale *
      realComplexFourierMode wave
        (angularDerivativeCoefficient
          (fun _ => Pi.single testCoordinate (scalar * coefficient)) direction
            wave)
        (center + scale • point.2) outputCoordinate| ≤ _
  calc
    _ ≤ (2 * Real.pi) * (1 + integerWaveNormSq wave) *
        ‖scalar * coefficient‖ := modeBound
    _ = (2 * Real.pi) * (1 + integerWaveNormSq wave) *
        (‖scalar‖ * ‖coefficient‖) := by rw [norm_mul]
    _ ≤ (2 * Real.pi) * (1 + integerWaveNormSq wave) *
        (temporalCeiling * ‖coefficient‖) := by
      apply mul_le_mul_of_nonneg_left
      · exact mul_le_mul_of_nonneg_right scalarLe (norm_nonneg _)
      · exact mul_nonneg (by positivity) (by
          have := integerWaveNormSq_nonneg wave
          linarith)
    _ = ((2 * Real.pi) * temporalCeiling) *
        ((1 + integerWaveNormSq wave) *
          ‖recenteredTensorSchwartzFourierCoefficient spatialTest scale
            scalePos.ne' center wave‖) := by
      dsimp only [coefficient]
      ring

private theorem
    wholeCellNormalizedScaledDerivativeMode_cube_tendstoUniformly
    (scale : Real)
    (scalePos : 0 < scale)
    (scaleLeOne : scale ≤ 1)
    (center : PhysicalSpace)
    (spatialTest : Coordinate → SchwartzMap Real Complex)
    (temporalTest : SchwartzMap Real Complex)
    (normalizedTimeOffset temporalCeiling : Real)
    (temporalBound : ∀ scaledTime : Icc (0 : Real) timeLength,
      ‖temporalTest (scaledTime.1 + normalizedTimeOffset)‖ ≤ temporalCeiling)
    (testCoordinate direction outputCoordinate : Coordinate) :
    TendstoUniformlyOn
      (fun radius : Nat =>
        fun point : Icc (0 : Real) timeLength × PhysicalSpace =>
          ∑ wave ∈ integerWaveFrequencyCube radius,
            wholeCellNormalizedScaledDerivativeMode
              (timeLength := timeLength) scale scalePos.ne' center spatialTest
              temporalTest normalizedTimeOffset testCoordinate direction
              outputCoordinate wave point)
      (fun point : Icc (0 : Real) timeLength × PhysicalSpace =>
        ∑' wave : IntegerWavevector,
          wholeCellNormalizedScaledDerivativeMode
            (timeLength := timeLength) scale scalePos.ne' center spatialTest
            temporalTest normalizedTimeOffset testCoordinate direction
            outputCoordinate wave point)
      atTop Set.univ := by
  have c2Summable :=
    recenteredTensorSchwartzFourierCoefficient_c2_summable
      spatialTest scale scalePos.ne' center
  let bound : IntegerWavevector → Real := fun wave =>
    ((2 * Real.pi) * temporalCeiling) *
      ((1 + integerWaveNormSq wave) *
        ‖recenteredTensorSchwartzFourierCoefficient spatialTest scale
          scalePos.ne' center wave‖)
  have boundSummable : Summable bound := by
    exact c2Summable.mul_left ((2 * Real.pi) * temporalCeiling)
  have uniform : TendstoUniformlyOn
      (fun modes : Finset IntegerWavevector =>
        fun point : Icc (0 : Real) timeLength × PhysicalSpace =>
          ∑ wave ∈ modes,
            wholeCellNormalizedScaledDerivativeMode
              (timeLength := timeLength) scale scalePos.ne' center spatialTest
              temporalTest normalizedTimeOffset testCoordinate direction
              outputCoordinate wave point)
      (fun point : Icc (0 : Real) timeLength × PhysicalSpace =>
        ∑' wave : IntegerWavevector,
          wholeCellNormalizedScaledDerivativeMode
            (timeLength := timeLength) scale scalePos.ne' center spatialTest
            temporalTest normalizedTimeOffset testCoordinate direction
            outputCoordinate wave point)
      atTop Set.univ := by
    apply tendstoUniformlyOn_tsum boundSummable
    intro wave point _pointMem
    simpa only [Real.norm_eq_abs, bound] using
      wholeCellNormalizedScaledDerivativeMode_abs_le_c2Weight
        (timeLength := timeLength) scale scalePos scaleLeOne center spatialTest
        temporalTest normalizedTimeOffset temporalCeiling temporalBound
        testCoordinate direction outputCoordinate wave point
  rw [Metric.tendstoUniformlyOn_iff] at uniform ⊢
  intro epsilon epsilonPos
  exact integerWaveFrequencyCube_tendsto_atTop.eventually
    (uniform epsilon epsilonPos)

private theorem exists_testRadius_wholeCellDerivative_sq_close
    (timeLength normalizedTimeOffset : Real)
    (scale : Nat → Real)
    (center : Nat → PhysicalSpace)
    (scalePos : ∀ index, 0 < scale index)
    (scaleLeOne : ∀ index, scale index ≤ 1)
    (spatialTest : Coordinate → SchwartzMap Real Complex)
    (temporalTest : SchwartzMap Real Complex)
    (temporalCeiling : Real)
    (temporalBound : ∀ scaledTime : Icc (0 : Real) timeLength,
      ‖temporalTest (scaledTime.1 + normalizedTimeOffset)‖ ≤ temporalCeiling)
    (testCoordinate : Coordinate) :
    ∃ testRadius : Nat → Nat,
      ∀ index direction outputCoordinate
        (point : Icc (0 : Real) timeLength × PhysicalSpace),
        dist
          (∑ wave ∈ integerWaveFrequencyCube (testRadius index),
            wholeCellNormalizedScaledDerivativeMode
              (timeLength := timeLength) (scale index)
              (scalePos index).ne' (center index) spatialTest temporalTest
              normalizedTimeOffset testCoordinate direction outputCoordinate
              wave point)
          (∑' wave : IntegerWavevector,
            wholeCellNormalizedScaledDerivativeMode
              (timeLength := timeLength) (scale index)
              (scalePos index).ne' (center index) spatialTest temporalTest
              normalizedTimeOffset testCoordinate direction outputCoordinate
              wave point) < scale index ^ 2 := by
  have closeEventually (index : Nat)
      (direction outputCoordinate : Coordinate) :
      ∀ᶠ radius : Nat in atTop,
        ∀ point : Icc (0 : Real) timeLength × PhysicalSpace,
          dist
            (∑ wave ∈ integerWaveFrequencyCube radius,
              wholeCellNormalizedScaledDerivativeMode
                (timeLength := timeLength) (scale index)
                (scalePos index).ne' (center index) spatialTest temporalTest
                normalizedTimeOffset testCoordinate direction outputCoordinate
                wave point)
            (∑' wave : IntegerWavevector,
              wholeCellNormalizedScaledDerivativeMode
                (timeLength := timeLength) (scale index)
                (scalePos index).ne' (center index) spatialTest temporalTest
                normalizedTimeOffset testCoordinate direction outputCoordinate
                wave point) < scale index ^ 2 := by
    have uniform :=
      wholeCellNormalizedScaledDerivativeMode_cube_tendstoUniformly
        (timeLength := timeLength) (scale index) (scalePos index)
        (scaleLeOne index) (center index) spatialTest temporalTest
        normalizedTimeOffset temporalCeiling temporalBound testCoordinate
        direction outputCoordinate
    have close := (Metric.tendstoUniformlyOn_iff.mp uniform)
      (scale index ^ 2) (sq_pos_of_pos (scalePos index))
    filter_upwards [close] with radius radiusClose
    intro point
    simpa only [dist_comm] using
      radiusClose point (Set.mem_univ point)
  have thresholdExists (index : Nat)
      (direction outputCoordinate : Coordinate) :
      ∃ threshold : Nat, ∀ radius, threshold ≤ radius →
        ∀ point : Icc (0 : Real) timeLength × PhysicalSpace,
          dist
            (∑ wave ∈ integerWaveFrequencyCube radius,
              wholeCellNormalizedScaledDerivativeMode
                (timeLength := timeLength) (scale index)
                (scalePos index).ne' (center index) spatialTest temporalTest
                normalizedTimeOffset testCoordinate direction outputCoordinate
                wave point)
            (∑' wave : IntegerWavevector,
              wholeCellNormalizedScaledDerivativeMode
                (timeLength := timeLength) (scale index)
                (scalePos index).ne' (center index) spatialTest temporalTest
                normalizedTimeOffset testCoordinate direction outputCoordinate
                wave point) < scale index ^ 2 := by
    simpa only [eventually_atTop] using
      closeEventually index direction outputCoordinate
  choose threshold thresholdLaw using thresholdExists
  let testRadius : Nat → Nat := fun index =>
    ∑ direction : Coordinate,
      ∑ outputCoordinate : Coordinate, threshold index direction outputCoordinate
  refine ⟨testRadius, ?_⟩
  intro index direction outputCoordinate point
  apply thresholdLaw index direction outputCoordinate (testRadius index)
  have entryLeRow : threshold index direction outputCoordinate ≤
      ∑ coordinate : Coordinate, threshold index direction coordinate := by
    exact Finset.single_le_sum (fun _ _ => Nat.zero_le _)
      (Finset.mem_univ outputCoordinate)
  have rowLeTotal :
      (∑ coordinate : Coordinate, threshold index direction coordinate) ≤
        ∑ direction' : Coordinate,
          ∑ coordinate : Coordinate, threshold index direction' coordinate := by
    exact Finset.single_le_sum
      (s := (Finset.univ : Finset Coordinate))
      (f := fun direction' : Coordinate =>
        ∑ coordinate : Coordinate, threshold index direction' coordinate)
      (fun _ _ => Nat.zero_le _) (Finset.mem_univ direction)
  exact entryLeRow.trans rowLeTotal

private theorem normalizedScaledDerivativeMode_tendstoUniformlyOn_tsum
    (scale : Real)
    (scalePos : 0 < scale)
    (scaleLeOne : scale ≤ 1)
    (center : PhysicalSpace)
    (spatialTest : Coordinate → SchwartzMap Real Complex)
    (temporalTest : SchwartzMap Real Complex)
    (normalizedTimeOffset temporalCeiling : Real)
    (temporalBound : ∀ scaledTime : Icc (0 : Real) timeLength,
      ‖temporalTest (scaledTime.1 + normalizedTimeOffset)‖ ≤ temporalCeiling)
    (testCoordinate direction outputCoordinate : Coordinate) :
    TendstoUniformlyOn
      (fun modes : Finset IntegerWavevector =>
        fun point : Cylinder timeLength spatialRadius =>
          ∑ wave ∈ modes,
            normalizedScaledDerivativeMode (timeLength := timeLength)
              (spatialRadius := spatialRadius) scale scalePos.ne' center
              spatialTest temporalTest normalizedTimeOffset testCoordinate
                direction outputCoordinate wave point)
      (fun point : Cylinder timeLength spatialRadius =>
        ∑' wave : IntegerWavevector,
          normalizedScaledDerivativeMode (timeLength := timeLength)
            (spatialRadius := spatialRadius) scale scalePos.ne' center
            spatialTest temporalTest normalizedTimeOffset testCoordinate
              direction outputCoordinate wave point)
      atTop Set.univ := by
  have c2Summable :=
    recenteredTensorSchwartzFourierCoefficient_c2_summable
      spatialTest scale scalePos.ne' center
  let bound : IntegerWavevector → Real := fun wave =>
    ((2 * Real.pi) * temporalCeiling) *
      ((1 + integerWaveNormSq wave) *
        ‖recenteredTensorSchwartzFourierCoefficient spatialTest scale
          scalePos.ne' center wave‖)
  have boundSummable : Summable bound := by
    exact c2Summable.mul_left ((2 * Real.pi) * temporalCeiling)
  apply tendstoUniformlyOn_tsum boundSummable
  intro wave point _pointMem
  simpa only [Real.norm_eq_abs, bound] using
    normalizedScaledDerivativeMode_abs_le_c2Weight
      (timeLength := timeLength) (spatialRadius := spatialRadius) scale
      scalePos scaleLeOne center spatialTest temporalTest normalizedTimeOffset
      temporalCeiling temporalBound testCoordinate direction outputCoordinate
      wave point

private theorem normalizedScaledDerivativeMode_cube_tendstoUniformly
    (scale : Real)
    (scalePos : 0 < scale)
    (scaleLeOne : scale ≤ 1)
    (center : PhysicalSpace)
    (spatialTest : Coordinate → SchwartzMap Real Complex)
    (temporalTest : SchwartzMap Real Complex)
    (normalizedTimeOffset temporalCeiling : Real)
    (temporalBound : ∀ scaledTime : Icc (0 : Real) timeLength,
      ‖temporalTest (scaledTime.1 + normalizedTimeOffset)‖ ≤ temporalCeiling)
    (testCoordinate direction outputCoordinate : Coordinate) :
    TendstoUniformlyOn
      (fun radius : Nat =>
        fun point : Cylinder timeLength spatialRadius =>
          ∑ wave ∈ integerWaveFrequencyCube radius,
            normalizedScaledDerivativeMode (timeLength := timeLength)
              (spatialRadius := spatialRadius) scale scalePos.ne' center
              spatialTest temporalTest normalizedTimeOffset testCoordinate
                direction outputCoordinate wave point)
      (fun point : Cylinder timeLength spatialRadius =>
        ∑' wave : IntegerWavevector,
          normalizedScaledDerivativeMode (timeLength := timeLength)
            (spatialRadius := spatialRadius) scale scalePos.ne' center
            spatialTest temporalTest normalizedTimeOffset testCoordinate
              direction outputCoordinate wave point)
      atTop Set.univ := by
  have uniform := normalizedScaledDerivativeMode_tendstoUniformlyOn_tsum
    (timeLength := timeLength) (spatialRadius := spatialRadius) scale
      scalePos scaleLeOne center spatialTest temporalTest normalizedTimeOffset
      temporalCeiling temporalBound testCoordinate direction outputCoordinate
  rw [Metric.tendstoUniformlyOn_iff] at uniform ⊢
  intro epsilon epsilonPos
  exact integerWaveFrequencyCube_tendsto_atTop.eventually
    (uniform epsilon epsilonPos)

private theorem normalizedScaledDerivativeMode_zero
    (scale : Real)
    (scaleNe : scale ≠ 0)
    (center : PhysicalSpace)
    (spatialTest : Coordinate → SchwartzMap Real Complex)
    (temporalTest : SchwartzMap Real Complex)
    (normalizedTimeOffset : Real)
    (testCoordinate direction outputCoordinate : Coordinate)
    (point : Cylinder timeLength spatialRadius) :
    normalizedScaledDerivativeMode (timeLength := timeLength)
        (spatialRadius := spatialRadius) scale scaleNe center spatialTest
        temporalTest normalizedTimeOffset testCoordinate direction
          outputCoordinate 0 point = 0 := by
  unfold normalizedScaledDerivativeMode
  simp [angularDerivativeCoefficient, integerAngularCoefficient,
    realComplexFourierMode, coefficientReal, coefficientImag]

private theorem normalizedScaledDerivativeMode_punctured_sum_eq_cube
    (radius : Nat)
    (scale : Real)
    (scaleNe : scale ≠ 0)
    (center : PhysicalSpace)
    (spatialTest : Coordinate → SchwartzMap Real Complex)
    (temporalTest : SchwartzMap Real Complex)
    (normalizedTimeOffset : Real)
    (testCoordinate direction outputCoordinate : Coordinate)
    (point : Cylinder timeLength spatialRadius) :
    (∑ wave ∈ puncturedIntegerWaveFrequencyCube radius,
      normalizedScaledDerivativeMode (timeLength := timeLength)
        (spatialRadius := spatialRadius) scale scaleNe center spatialTest
        temporalTest normalizedTimeOffset testCoordinate direction
          outputCoordinate wave point) =
      ∑ wave ∈ integerWaveFrequencyCube radius,
        normalizedScaledDerivativeMode (timeLength := timeLength)
          (spatialRadius := spatialRadius) scale scaleNe center spatialTest
          temporalTest normalizedTimeOffset testCoordinate direction
            outputCoordinate wave point := by
  rw [puncturedIntegerWaveFrequencyCube]
  rw [Finset.sum_erase]
  rw [normalizedScaledDerivativeMode_zero]

private theorem scaledProjectedTensorBCF_apply_eq_normalizedCubeDerivative
    (timeLength spatialRadius scale start timeCenter normalizedTimeOffset : Real)
    (scalePos : 0 < scale)
    (timeChart : start - timeCenter = scale ^ 2 * normalizedTimeOffset)
    (center : PhysicalSpace)
    (testRadius : Nat)
    (spatialTest : Coordinate → SchwartzMap Real Complex)
    (temporalTest : SchwartzMap Real Complex)
    (testCoordinate velocityCoordinate vorticityCoordinate : Coordinate)
    (point : Cylinder timeLength spatialRadius) :
    scaledProjectedTensorBCF timeLength spatialRadius scale start center
        (puncturedIntegerWaveFrequencyCube testRadius)
        (fun wave => Pi.single testCoordinate
          (recenteredTensorSchwartzFourierCoefficient spatialTest scale
            scalePos.ne' center wave))
        (fun time => temporalTest ((time - timeCenter) / scale ^ 2))
        (by fun_prop) velocityCoordinate vorticityCoordinate point =
      (∑ wave ∈ integerWaveFrequencyCube testRadius,
        normalizedScaledDerivativeMode (timeLength := timeLength)
          (spatialRadius := spatialRadius) scale scalePos.ne' center spatialTest
          temporalTest normalizedTimeOffset testCoordinate velocityCoordinate
            vorticityCoordinate wave point) -
      ∑ wave ∈ integerWaveFrequencyCube testRadius,
        normalizedScaledDerivativeMode (timeLength := timeLength)
          (spatialRadius := spatialRadius) scale scalePos.ne' center spatialTest
          temporalTest normalizedTimeOffset testCoordinate
            vorticityCoordinate velocityCoordinate wave point := by
  have normalizedTimeEq :
      (start + scale ^ 2 * point.1.1 - timeCenter) / scale ^ 2 =
        point.1.1 + normalizedTimeOffset := by
    field_simp [scalePos.ne']
    nlinarith
  rw [scaledProjectedTensorBCF_apply]
  unfold scaledProjectedTensorTest scaledProjectedTensorTestRaw
  dsimp only
  rw [normalizedTimeEq]
  have weightedCoefficientEq :
      (fun wave : IntegerWavevector =>
        star (temporalTest (point.1.1 + normalizedTimeOffset)) •
          Pi.single testCoordinate
            (recenteredTensorSchwartzFourierCoefficient spatialTest scale
              scalePos.ne' center wave)) =
        (fun wave : IntegerWavevector =>
          Pi.single testCoordinate
            (star (temporalTest (point.1.1 + normalizedTimeOffset)) *
              recenteredTensorSchwartzFourierCoefficient spatialTest scale
                scalePos.ne' center wave)) := by
    funext wave coordinate
    by_cases coordinateEq : coordinate = testCoordinate
    · subst coordinate
      simp
    · simp [coordinateEq]
  rw [weightedCoefficientEq]
  simp_rw [finiteRealComplexFourierField_coordinateDerivative]
  unfold finiteRealComplexFourierField
  simp only [WithLp.ofLp_sum, Finset.sum_apply]
  rw [mul_sub, Finset.mul_sum, Finset.mul_sum]
  change
    (∑ wave ∈ puncturedIntegerWaveFrequencyCube testRadius,
      normalizedScaledDerivativeMode (timeLength := timeLength)
        (spatialRadius := spatialRadius) scale scalePos.ne' center spatialTest
        temporalTest normalizedTimeOffset testCoordinate velocityCoordinate
          vorticityCoordinate wave point) -
      (∑ wave ∈ puncturedIntegerWaveFrequencyCube testRadius,
        normalizedScaledDerivativeMode (timeLength := timeLength)
          (spatialRadius := spatialRadius) scale scalePos.ne' center spatialTest
          temporalTest normalizedTimeOffset testCoordinate
            vorticityCoordinate velocityCoordinate wave point) = _
  rw [normalizedScaledDerivativeMode_punctured_sum_eq_cube]
  rw [normalizedScaledDerivativeMode_punctured_sum_eq_cube]

private theorem fixedTensorSchwartzBCF_apply_eq_normalizedTsumDerivative
    (timeLength spatialRadius scale normalizedTimeOffset : Real)
    (scalePos : 0 < scale)
    (scaleLeOne : scale ≤ 1)
    (center : PhysicalSpace)
    (spatialTest : Coordinate → SchwartzMap Real Complex)
    (temporalTest : SchwartzMap Real Complex)
    (testCoordinate velocityCoordinate vorticityCoordinate : Coordinate)
    (supportRadius : Real)
    (periodLarge : supportRadius + (spatialRadius + 1) < scale⁻¹)
    (support : ∀ coordinate y,
      supportRadius < |y| → spatialTest coordinate y = 0)
    (point : Cylinder timeLength spatialRadius) :
    fixedTensorSchwartzBCF timeLength spatialRadius spatialTest temporalTest
        normalizedTimeOffset testCoordinate velocityCoordinate
          vorticityCoordinate point =
      (∑' wave : IntegerWavevector,
        normalizedScaledDerivativeMode (timeLength := timeLength)
          (spatialRadius := spatialRadius) scale scalePos.ne' center spatialTest
          temporalTest normalizedTimeOffset testCoordinate velocityCoordinate
            vorticityCoordinate wave point) -
      ∑' wave : IntegerWavevector,
        normalizedScaledDerivativeMode (timeLength := timeLength)
          (spatialRadius := spatialRadius) scale scalePos.ne' center spatialTest
          temporalTest normalizedTimeOffset testCoordinate
            vorticityCoordinate velocityCoordinate wave point := by
  have pointNormLe : ‖point.2.1‖ ≤ spatialRadius := by
    simpa only [Metric.mem_closedBall, dist_zero_right] using point.2.2
  rw [show fixedTensorSchwartzBCF timeLength spatialRadius spatialTest
        temporalTest normalizedTimeOffset testCoordinate velocityCoordinate
          vorticityCoordinate point =
      fixedTensorSchwartzTestRaw spatialTest temporalTest
        normalizedTimeOffset testCoordinate velocityCoordinate
          vorticityCoordinate point.1.1 point.2.1 by rfl]
  unfold normalizedScaledDerivativeMode
  dsimp only
  rw [recenteredRealFourierSeries_smul_scaledDerivative_coordinate_eq
    spatialTest scale scalePos scaleLeOne center testCoordinate
      velocityCoordinate vorticityCoordinate
      (star (temporalTest (point.1.1 + normalizedTimeOffset))) supportRadius
      spatialRadius periodLarge support point.2.1 pointNormLe]
  rw [recenteredRealFourierSeries_smul_scaledDerivative_coordinate_eq
    spatialTest scale scalePos scaleLeOne center testCoordinate
      vorticityCoordinate velocityCoordinate
      (star (temporalTest (point.1.1 + normalizedTimeOffset))) supportRadius
      spatialRadius periodLarge support point.2.1 pointNormLe]
  rfl

private theorem scaledProjectedTensorBCF_tendsto_fixedTensorSchwartzBCF
    (timeLength spatialRadius scale start timeCenter normalizedTimeOffset : Real)
    (scalePos : 0 < scale)
    (scaleLeOne : scale ≤ 1)
    (timeChart : start - timeCenter = scale ^ 2 * normalizedTimeOffset)
    (center : PhysicalSpace)
    (spatialTest : Coordinate → SchwartzMap Real Complex)
    (temporalTest : SchwartzMap Real Complex)
    (temporalCeiling : Real)
    (temporalBound : ∀ scaledTime : Icc (0 : Real) timeLength,
      ‖temporalTest (scaledTime.1 + normalizedTimeOffset)‖ ≤ temporalCeiling)
    (testCoordinate velocityCoordinate vorticityCoordinate : Coordinate)
    (supportRadius : Real)
    (periodLarge : supportRadius + (spatialRadius + 1) < scale⁻¹)
    (support : ∀ coordinate y,
      supportRadius < |y| → spatialTest coordinate y = 0) :
    Tendsto
      (fun testRadius : Nat =>
        scaledProjectedTensorBCF timeLength spatialRadius scale start center
          (puncturedIntegerWaveFrequencyCube testRadius)
          (fun wave => Pi.single testCoordinate
            (recenteredTensorSchwartzFourierCoefficient spatialTest scale
              scalePos.ne' center wave))
          (fun time => temporalTest ((time - timeCenter) / scale ^ 2))
          (by fun_prop) velocityCoordinate vorticityCoordinate)
      atTop
      (nhds
        (fixedTensorSchwartzBCF timeLength spatialRadius spatialTest
          temporalTest normalizedTimeOffset testCoordinate velocityCoordinate
            vorticityCoordinate)) := by
  have firstUniform := normalizedScaledDerivativeMode_cube_tendstoUniformly
    (timeLength := timeLength) (spatialRadius := spatialRadius) scale
      scalePos scaleLeOne center spatialTest temporalTest normalizedTimeOffset
      temporalCeiling temporalBound testCoordinate velocityCoordinate
      vorticityCoordinate
  have secondUniform := normalizedScaledDerivativeMode_cube_tendstoUniformly
    (timeLength := timeLength) (spatialRadius := spatialRadius) scale
      scalePos scaleLeOne center spatialTest temporalTest normalizedTimeOffset
      temporalCeiling temporalBound testCoordinate vorticityCoordinate
      velocityCoordinate
  rw [Metric.tendsto_nhds]
  intro epsilon epsilonPos
  have firstEventually :=
    (Metric.tendstoUniformlyOn_iff.mp firstUniform) (epsilon / 2)
      (by linarith)
  have secondEventually :=
    (Metric.tendstoUniformlyOn_iff.mp secondUniform) (epsilon / 2)
      (by linarith)
  filter_upwards [firstEventually, secondEventually] with testRadius
      firstClose secondClose
  rw [dist_eq_norm]
  apply (BoundedContinuousFunction.norm_lt_iff_of_compact epsilonPos).2
  intro point
  have firstPoint := firstClose point (Set.mem_univ point)
  have secondPoint := secondClose point (Set.mem_univ point)
  simp only [BoundedContinuousFunction.sub_apply]
  rw [scaledProjectedTensorBCF_apply_eq_normalizedCubeDerivative
    timeLength spatialRadius scale start timeCenter normalizedTimeOffset
      scalePos timeChart center testRadius spatialTest temporalTest
      testCoordinate velocityCoordinate vorticityCoordinate point]
  rw [fixedTensorSchwartzBCF_apply_eq_normalizedTsumDerivative
    timeLength spatialRadius scale normalizedTimeOffset
      scalePos scaleLeOne center spatialTest temporalTest testCoordinate
      velocityCoordinate vorticityCoordinate supportRadius periodLarge support
      point]
  simp only [Real.norm_eq_abs]
  let finiteFirst : Real :=
    ∑ wave ∈ integerWaveFrequencyCube testRadius,
      normalizedScaledDerivativeMode (timeLength := timeLength)
        (spatialRadius := spatialRadius) scale scalePos.ne' center spatialTest
        temporalTest normalizedTimeOffset testCoordinate velocityCoordinate
          vorticityCoordinate wave point
  let finiteSecond : Real :=
    ∑ wave ∈ integerWaveFrequencyCube testRadius,
      normalizedScaledDerivativeMode (timeLength := timeLength)
        (spatialRadius := spatialRadius) scale scalePos.ne' center spatialTest
        temporalTest normalizedTimeOffset testCoordinate vorticityCoordinate
          velocityCoordinate wave point
  let infiniteFirst : Real :=
    ∑' wave : IntegerWavevector,
      normalizedScaledDerivativeMode (timeLength := timeLength)
        (spatialRadius := spatialRadius) scale scalePos.ne' center spatialTest
        temporalTest normalizedTimeOffset testCoordinate velocityCoordinate
          vorticityCoordinate wave point
  let infiniteSecond : Real :=
    ∑' wave : IntegerWavevector,
      normalizedScaledDerivativeMode (timeLength := timeLength)
        (spatialRadius := spatialRadius) scale scalePos.ne' center spatialTest
        temporalTest normalizedTimeOffset testCoordinate vorticityCoordinate
          velocityCoordinate wave point
  change |(finiteFirst - finiteSecond) -
    (infiniteFirst - infiniteSecond)| < epsilon
  have firstAbs : |finiteFirst - infiniteFirst| < epsilon / 2 := by
    simpa only [Real.dist_eq, abs_sub_comm, finiteFirst, infiniteFirst] using
      firstPoint
  have secondAbs : |finiteSecond - infiniteSecond| < epsilon / 2 := by
    simpa only [Real.dist_eq, abs_sub_comm, finiteSecond, infiniteSecond] using
      secondPoint
  calc
    |(finiteFirst - finiteSecond) -
        (infiniteFirst - infiniteSecond)| =
      |(finiteFirst - infiniteFirst) -
        (finiteSecond - infiniteSecond)| := by
      congr 1
      ring
    _ ≤ |finiteFirst - infiniteFirst| +
        |finiteSecond - infiniteSecond| := abs_sub _ _
    _ < epsilon := by linarith

private theorem exists_testRadius_scaledProjectedTensorBCF_tendsto_fixed
    (timeLength spatialRadius normalizedTimeOffset : Real)
    (scale start timeCenter : Nat → Real)
    (center : Nat → PhysicalSpace)
    (scalePos : ∀ index, 0 < scale index)
    (scaleLeOne : ∀ index, scale index ≤ 1)
    (timeChart : ∀ index,
      start index - timeCenter index =
        scale index ^ 2 * normalizedTimeOffset)
    (spatialTest : Coordinate → SchwartzMap Real Complex)
    (temporalTest : SchwartzMap Real Complex)
    (temporalCeiling : Real)
    (temporalBound : ∀ scaledTime : Icc (0 : Real) timeLength,
      ‖temporalTest (scaledTime.1 + normalizedTimeOffset)‖ ≤ temporalCeiling)
    (testCoordinate : Coordinate)
    (supportRadius : Real)
    (periodLarge : ∀ index,
      supportRadius + (spatialRadius + 1) < (scale index)⁻¹)
    (support : ∀ coordinate y,
      supportRadius < |y| → spatialTest coordinate y = 0) :
    ∃ testRadius : Nat → Nat,
      ∀ velocityCoordinate vorticityCoordinate : Coordinate,
        Tendsto
          (fun index =>
            scaledProjectedTensorBCF timeLength spatialRadius (scale index)
              (start index) (center index)
              (puncturedIntegerWaveFrequencyCube (testRadius index))
              (fun wave => Pi.single testCoordinate
                (recenteredTensorSchwartzFourierCoefficient spatialTest
                  (scale index) (scalePos index).ne' (center index) wave))
              (fun time => temporalTest
                ((time - timeCenter index) / scale index ^ 2))
              (by fun_prop) velocityCoordinate vorticityCoordinate)
          atTop
          (nhds
            (fixedTensorSchwartzBCF timeLength spatialRadius spatialTest
              temporalTest normalizedTimeOffset testCoordinate
                velocityCoordinate vorticityCoordinate)) := by
  let finiteFamily : Nat → Nat → Coordinate → Coordinate →
      BoundedContinuousFunction (Cylinder timeLength spatialRadius) Real :=
    fun index testRadius velocityCoordinate vorticityCoordinate =>
      scaledProjectedTensorBCF timeLength spatialRadius (scale index)
        (start index) (center index)
        (puncturedIntegerWaveFrequencyCube testRadius)
        (fun wave => Pi.single testCoordinate
          (recenteredTensorSchwartzFourierCoefficient spatialTest
            (scale index) (scalePos index).ne' (center index) wave))
        (fun time => temporalTest
          ((time - timeCenter index) / scale index ^ 2))
        (by fun_prop) velocityCoordinate vorticityCoordinate
  let fixedFamily : Coordinate → Coordinate →
      BoundedContinuousFunction (Cylinder timeLength spatialRadius) Real :=
    fun velocityCoordinate vorticityCoordinate =>
      fixedTensorSchwartzBCF timeLength spatialRadius spatialTest temporalTest
        normalizedTimeOffset testCoordinate velocityCoordinate
          vorticityCoordinate
  have familyTendsto (index : Nat) :
      Tendsto (finiteFamily index) atTop (nhds fixedFamily) := by
    apply tendsto_pi_nhds.mpr
    intro velocityCoordinate
    apply tendsto_pi_nhds.mpr
    intro vorticityCoordinate
    exact scaledProjectedTensorBCF_tendsto_fixedTensorSchwartzBCF
      timeLength spatialRadius (scale index) (start index) (timeCenter index)
      normalizedTimeOffset (scalePos index) (scaleLeOne index)
      (timeChart index) (center index) spatialTest temporalTest temporalCeiling
      temporalBound testCoordinate velocityCoordinate vorticityCoordinate
      supportRadius (periodLarge index) support
  let approximationRate : Nat → Real := fun index =>
    1 / ((index : Real) + 1)
  have approximationRatePos (index : Nat) : 0 < approximationRate index := by
    dsimp only [approximationRate]
    positivity
  have radiusExists (index : Nat) : ∃ testRadius : Nat,
      dist (finiteFamily index testRadius) fixedFamily <
        approximationRate index := by
    obtain ⟨threshold, thresholdLaw⟩ :=
      (Metric.tendsto_atTop.mp (familyTendsto index))
        (approximationRate index) (approximationRatePos index)
    exact ⟨threshold, thresholdLaw threshold le_rfl⟩
  choose testRadius testRadiusClose using radiusExists
  have approximationRateTendsto :
      Tendsto approximationRate atTop (nhds 0) := by
    simpa only [approximationRate, Nat.cast_add, Nat.cast_one] using
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := Real))
  have selectedFamilyTendsto :
      Tendsto (fun index => finiteFamily index (testRadius index)) atTop
        (nhds fixedFamily) := by
    rw [Metric.tendsto_nhds]
    intro epsilon epsilonPos
    have rateEventually : ∀ᶠ index : Nat in atTop,
        approximationRate index < epsilon := by
      have nearZero :=
        (Metric.tendsto_nhds.mp approximationRateTendsto) epsilon epsilonPos
      filter_upwards [nearZero] with index indexClose
      simpa only [Real.dist_eq, sub_zero,
        abs_of_pos (approximationRatePos index)] using indexClose
    filter_upwards [rateEventually] with index rateSmall
    exact (testRadiusClose index).trans rateSmall
  refine ⟨testRadius, ?_⟩
  intro velocityCoordinate vorticityCoordinate
  have firstCoordinate :=
    tendsto_pi_nhds.mp selectedFamilyTendsto velocityCoordinate
  have secondCoordinate :=
    tendsto_pi_nhds.mp firstCoordinate vorticityCoordinate
  simpa only [finiteFamily, fixedFamily] using secondCoordinate

private def tensorTestProductDensityBCF
    {X : Type*}
    [TopologicalSpace X]
    [CompactSpace X]
    (test : Coordinate → Coordinate → BoundedContinuousFunction X Real)
    (velocity vorticity : BoundedContinuousFunction X PhysicalSpace) :
    BoundedContinuousFunction X Real :=
  BoundedContinuousFunction.mkOfCompact
    ⟨fun point =>
      ∑ velocityCoordinate : Coordinate,
        ∑ vorticityCoordinate : Coordinate,
          test velocityCoordinate vorticityCoordinate point *
            velocity point velocityCoordinate *
            vorticity point vorticityCoordinate,
      by fun_prop⟩

private theorem tensorTestProductDensityBCF_sub_norm_le
    {X : Type*}
    [TopologicalSpace X]
    [CompactSpace X]
    (firstTest secondTest :
      Coordinate → Coordinate → BoundedContinuousFunction X Real)
    (velocity vorticity : BoundedContinuousFunction X PhysicalSpace)
    (velocityCeiling vorticityCeiling : Real)
    (velocityCeilingNonneg : 0 ≤ velocityCeiling)
    (vorticityCeilingNonneg : 0 ≤ vorticityCeiling)
    (velocityBound : ∀ point, ‖velocity point‖ ≤ velocityCeiling)
    (vorticityBound : ∀ point, ‖vorticity point‖ ≤ vorticityCeiling) :
    ‖tensorTestProductDensityBCF firstTest velocity vorticity -
        tensorTestProductDensityBCF secondTest velocity vorticity‖ ≤
      (∑ velocityCoordinate : Coordinate,
        ∑ vorticityCoordinate : Coordinate,
          ‖firstTest velocityCoordinate vorticityCoordinate -
            secondTest velocityCoordinate vorticityCoordinate‖) *
        velocityCeiling * vorticityCeiling := by
  let testError : Real :=
    ∑ velocityCoordinate : Coordinate,
      ∑ vorticityCoordinate : Coordinate,
        ‖firstTest velocityCoordinate vorticityCoordinate -
          secondTest velocityCoordinate vorticityCoordinate‖
  have testErrorNonneg : 0 ≤ testError := by
    dsimp only [testError]
    positivity
  apply (BoundedContinuousFunction.norm_le
    (mul_nonneg (mul_nonneg testErrorNonneg velocityCeilingNonneg)
      vorticityCeilingNonneg)).2
  intro point
  simp only [BoundedContinuousFunction.sub_apply, Real.norm_eq_abs]
  change
    |(∑ velocityCoordinate : Coordinate,
        ∑ vorticityCoordinate : Coordinate,
          firstTest velocityCoordinate vorticityCoordinate point *
            velocity point velocityCoordinate *
            vorticity point vorticityCoordinate) -
      ∑ velocityCoordinate : Coordinate,
        ∑ vorticityCoordinate : Coordinate,
          secondTest velocityCoordinate vorticityCoordinate point *
            velocity point velocityCoordinate *
            vorticity point vorticityCoordinate| ≤ _
  rw [← Finset.sum_sub_distrib]
  simp_rw [← Finset.sum_sub_distrib]
  have coordinateTermBound
      (velocityCoordinate vorticityCoordinate : Coordinate) :
      |(firstTest velocityCoordinate vorticityCoordinate point -
          secondTest velocityCoordinate vorticityCoordinate point) *
          velocity point velocityCoordinate *
          vorticity point vorticityCoordinate| ≤
        ‖firstTest velocityCoordinate vorticityCoordinate -
          secondTest velocityCoordinate vorticityCoordinate‖ *
          velocityCeiling * vorticityCeiling := by
    have testPointBound :
        |firstTest velocityCoordinate vorticityCoordinate point -
          secondTest velocityCoordinate vorticityCoordinate point| ≤
          ‖firstTest velocityCoordinate vorticityCoordinate -
            secondTest velocityCoordinate vorticityCoordinate‖ := by
      simpa only [BoundedContinuousFunction.sub_apply, Real.norm_eq_abs] using
        BoundedContinuousFunction.norm_coe_le_norm
          (firstTest velocityCoordinate vorticityCoordinate -
            secondTest velocityCoordinate vorticityCoordinate) point
    have velocityCoordinateBound :
        |velocity point velocityCoordinate| ≤ velocityCeiling := by
      have coordinateLe :
          ‖velocity point velocityCoordinate‖ ≤ ‖velocity point‖ :=
        PiLp.norm_apply_le _ _
      simpa only [Real.norm_eq_abs] using
        coordinateLe.trans (velocityBound point)
    have vorticityCoordinateBound :
        |vorticity point vorticityCoordinate| ≤ vorticityCeiling := by
      have coordinateLe :
          ‖vorticity point vorticityCoordinate‖ ≤ ‖vorticity point‖ :=
        PiLp.norm_apply_le _ _
      simpa only [Real.norm_eq_abs] using
        coordinateLe.trans (vorticityBound point)
    rw [abs_mul, abs_mul]
    exact mul_le_mul
      (mul_le_mul testPointBound velocityCoordinateBound
        (abs_nonneg _) (norm_nonneg _))
      vorticityCoordinateBound (abs_nonneg _)
      (mul_nonneg (norm_nonneg _) velocityCeilingNonneg)
  have sumFactor :
      (∑ velocityCoordinate : Coordinate,
        ∑ vorticityCoordinate : Coordinate,
          (firstTest velocityCoordinate vorticityCoordinate point *
                velocity point velocityCoordinate *
                vorticity point vorticityCoordinate -
            secondTest velocityCoordinate vorticityCoordinate point *
                velocity point velocityCoordinate *
                vorticity point vorticityCoordinate)) =
        ∑ velocityCoordinate : Coordinate,
          ∑ vorticityCoordinate : Coordinate,
            ((firstTest velocityCoordinate vorticityCoordinate point -
                secondTest velocityCoordinate vorticityCoordinate point) *
              velocity point velocityCoordinate *
              vorticity point vorticityCoordinate) := by
    apply Finset.sum_congr rfl
    intro velocityCoordinate _velocityCoordinateMem
    apply Finset.sum_congr rfl
    intro vorticityCoordinate _vorticityCoordinateMem
    ring
  rw [sumFactor]
  calc
    |∑ velocityCoordinate : Coordinate,
        ∑ vorticityCoordinate : Coordinate,
          ((firstTest velocityCoordinate vorticityCoordinate point -
              secondTest velocityCoordinate vorticityCoordinate point) *
            velocity point velocityCoordinate *
            vorticity point vorticityCoordinate)| ≤
      ∑ velocityCoordinate : Coordinate,
        |∑ vorticityCoordinate : Coordinate,
          ((firstTest velocityCoordinate vorticityCoordinate point -
              secondTest velocityCoordinate vorticityCoordinate point) *
            velocity point velocityCoordinate *
            vorticity point vorticityCoordinate)| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ velocityCoordinate : Coordinate,
        ∑ vorticityCoordinate : Coordinate,
          |(firstTest velocityCoordinate vorticityCoordinate point -
              secondTest velocityCoordinate vorticityCoordinate point) *
            velocity point velocityCoordinate *
            vorticity point vorticityCoordinate| := by
      apply Finset.sum_le_sum
      intro velocityCoordinate _velocityCoordinateMem
      exact Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ velocityCoordinate : Coordinate,
        ∑ vorticityCoordinate : Coordinate,
          ‖firstTest velocityCoordinate vorticityCoordinate -
              secondTest velocityCoordinate vorticityCoordinate‖ *
            velocityCeiling * vorticityCeiling := by
      apply Finset.sum_le_sum
      intro velocityCoordinate _velocityCoordinateMem
      apply Finset.sum_le_sum
      intro vorticityCoordinate _vorticityCoordinateMem
      exact coordinateTermBound velocityCoordinate vorticityCoordinate
    _ = testError * velocityCeiling * vorticityCeiling := by
      dsimp only [testError]
      rw [Finset.sum_mul, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro velocityCoordinate _velocityCoordinateMem
      rw [Finset.sum_mul, Finset.sum_mul]
    _ = _ := rfl

private theorem varyingTensorTestProduct_integral_tendsto_of_fixed
    {X : Type*}
    [TopologicalSpace X]
    [CompactSpace X]
    [MeasurableSpace X]
    [BorelSpace X]
    (μ : Measure X)
    [IsFiniteMeasure μ]
    (test : Nat → Coordinate → Coordinate →
      BoundedContinuousFunction X Real)
    (fixedTest : Coordinate → Coordinate →
      BoundedContinuousFunction X Real)
    (velocity vorticity : Nat → BoundedContinuousFunction X PhysicalSpace)
    (velocityLimit vorticityLimit : BoundedContinuousFunction X PhysicalSpace)
    (velocityCeiling vorticityCeiling : Real)
    (velocityCeilingNonneg : 0 ≤ velocityCeiling)
    (vorticityCeilingNonneg : 0 ≤ vorticityCeiling)
    (testTendsto : ∀ velocityCoordinate vorticityCoordinate,
      Tendsto (fun index => test index velocityCoordinate vorticityCoordinate)
        atTop (nhds (fixedTest velocityCoordinate vorticityCoordinate)))
    (velocityBound : ∀ index point,
      ‖velocity index point‖ ≤ velocityCeiling)
    (vorticityBound : ∀ index point,
      ‖vorticity index point‖ ≤ vorticityCeiling)
    (fixedProductTendsto :
      Tendsto
        (fun index =>
          ∫ point,
            ∑ velocityCoordinate : Coordinate,
              ∑ vorticityCoordinate : Coordinate,
                fixedTest velocityCoordinate vorticityCoordinate point *
                  velocity index point velocityCoordinate *
                  vorticity index point vorticityCoordinate ∂μ)
        atTop
        (nhds
          (∫ point,
            ∑ velocityCoordinate : Coordinate,
              ∑ vorticityCoordinate : Coordinate,
                fixedTest velocityCoordinate vorticityCoordinate point *
                  velocityLimit point velocityCoordinate *
                  vorticityLimit point vorticityCoordinate ∂μ))) :
    Tendsto
      (fun index =>
        ∫ point,
          ∑ velocityCoordinate : Coordinate,
            ∑ vorticityCoordinate : Coordinate,
              test index velocityCoordinate vorticityCoordinate point *
                velocity index point velocityCoordinate *
                vorticity index point vorticityCoordinate ∂μ)
      atTop
      (nhds
        (∫ point,
          ∑ velocityCoordinate : Coordinate,
            ∑ vorticityCoordinate : Coordinate,
              fixedTest velocityCoordinate vorticityCoordinate point *
                velocityLimit point velocityCoordinate *
                vorticityLimit point vorticityCoordinate ∂μ)) := by
  let testError : Nat → Real := fun index =>
    ∑ velocityCoordinate : Coordinate,
      ∑ vorticityCoordinate : Coordinate,
        ‖test index velocityCoordinate vorticityCoordinate -
          fixedTest velocityCoordinate vorticityCoordinate‖
  have testErrorTendsto : Tendsto testError atTop (nhds 0) := by
    dsimp only [testError]
    have testErrorTendstoRaw :=
      tendsto_finsetSum Finset.univ (fun velocityCoordinate _ =>
        tendsto_finsetSum Finset.univ (fun vorticityCoordinate _ => by
          have differenceTendstoRaw :=
            (testTendsto velocityCoordinate vorticityCoordinate).sub
              (tendsto_const_nhds : Tendsto
                (fun _index : Nat =>
                  fixedTest velocityCoordinate vorticityCoordinate)
                atTop
                (nhds (fixedTest velocityCoordinate vorticityCoordinate)))
          have differenceTendsto : Tendsto
              (fun index =>
                test index velocityCoordinate vorticityCoordinate -
                  fixedTest velocityCoordinate vorticityCoordinate)
              atTop (nhds 0) := by
            simpa only [sub_self] using differenceTendstoRaw
          simpa only [norm_zero] using differenceTendsto.norm))
    simpa using testErrorTendstoRaw
  let densityError : Nat → BoundedContinuousFunction X Real := fun index =>
    tensorTestProductDensityBCF (test index) (velocity index)
        (vorticity index) -
      tensorTestProductDensityBCF fixedTest (velocity index)
        (vorticity index)
  have densityErrorBound (index : Nat) :
      ‖densityError index‖ ≤
        testError index * velocityCeiling * vorticityCeiling := by
    exact tensorTestProductDensityBCF_sub_norm_le (test index) fixedTest
      (velocity index) (vorticity index) velocityCeiling vorticityCeiling
      velocityCeilingNonneg vorticityCeilingNonneg (velocityBound index)
      (vorticityBound index)
  have densityErrorRateTendsto :
      Tendsto
        (fun index => testError index * velocityCeiling * vorticityCeiling)
        atTop (nhds 0) := by
    simpa only [zero_mul] using
      (testErrorTendsto.mul_const velocityCeiling).mul_const vorticityCeiling
  have densityErrorTendsto : Tendsto densityError atTop (nhds 0) :=
    squeeze_zero_norm densityErrorBound densityErrorRateTendsto
  have densityErrorIntegralTendsto :
      Tendsto (fun index => ∫ point, densityError index point ∂μ)
        atTop (nhds 0) := by
    apply squeeze_zero_norm
      (a := fun index => μ.real Set.univ * ‖densityError index‖)
    · intro index
      exact BoundedContinuousFunction.norm_integral_le_mul_norm μ
        (densityError index)
    · have measureConst :
          Tendsto (fun index => μ.real Set.univ * ‖densityError index‖)
            atTop (nhds (μ.real Set.univ * ‖(0 :
              BoundedContinuousFunction X Real)‖)) := by
          exact tendsto_const_nhds.mul densityErrorTendsto.norm
      simpa only [norm_zero, mul_zero] using measureConst
  have summedTendsto := fixedProductTendsto.add densityErrorIntegralTendsto
  convert summedTendsto using 1
  · funext index
    have fixedIntegrable :=
      (tensorTestProductDensityBCF fixedTest (velocity index)
        (vorticity index)).integrable μ
    have errorIntegrable := (densityError index).integrable μ
    change
      (∫ point,
        tensorTestProductDensityBCF (test index) (velocity index)
          (vorticity index) point ∂μ) =
        (∫ point,
          tensorTestProductDensityBCF fixedTest (velocity index)
            (vorticity index) point ∂μ) +
          ∫ point, densityError index point ∂μ
    rw [← integral_add fixedIntegrable errorIntegrable]
    apply integral_congr_ae
    filter_upwards [] with point
    simp only [densityError, tensorTestProductDensityBCF,
      BoundedContinuousFunction.sub_apply]
    ring
  · simp

private theorem coordinatePairBCF_abs_le_sum_norm
    {X : Type*}
    [TopologicalSpace X]
    [CompactSpace X]
    (test : Coordinate → Coordinate → BoundedContinuousFunction X Real)
    (velocityCoordinate vorticityCoordinate : Coordinate)
    (point : X) :
    |test velocityCoordinate vorticityCoordinate point| ≤
      ∑ firstCoordinate : Coordinate,
        ∑ secondCoordinate : Coordinate,
          ‖test firstCoordinate secondCoordinate‖ := by
  calc
    |test velocityCoordinate vorticityCoordinate point| ≤
        ‖test velocityCoordinate vorticityCoordinate‖ := by
      simpa only [Real.norm_eq_abs] using
        BoundedContinuousFunction.norm_coe_le_norm
          (test velocityCoordinate vorticityCoordinate) point
    _ ≤ ∑ secondCoordinate : Coordinate,
        ‖test velocityCoordinate secondCoordinate‖ := by
      exact Finset.single_le_sum
        (fun coordinate _ => norm_nonneg (test velocityCoordinate coordinate))
        (Finset.mem_univ vorticityCoordinate)
    _ ≤ ∑ firstCoordinate : Coordinate,
        ∑ secondCoordinate : Coordinate,
          ‖test firstCoordinate secondCoordinate‖ := by
      exact Finset.single_le_sum
        (fun coordinate _ => Finset.sum_nonneg fun _ _ => norm_nonneg _)
        (Finset.mem_univ velocityCoordinate)

/--
A uniformly controlled finite Fourier band admits one velocity subsequence
that preserves the supplied vorticity limit and simultaneously compiles a
single sequence of recentered tensor-Schwartz trigonometric tests.  All nine
coordinate tests converge to the same fixed physical test, their velocity-
vorticity products converge on the cylinder, and every approximating product
is exactly the recentered physical projected action after parabolic scaling.
-/
theorem finiteBandVelocity_recenteredTensorSchwartz_paired_tendsto_subseq
    (timeLength spatialRadius bandRadius massCeiling timeCeiling
      normalizedTimeOffset : Real)
    (scale start timeCenter : Nat → Real)
    (radius : Nat → Nat)
    (center : Nat → PhysicalSpace)
    (actualPath : Nat → Real → ComplexVorticityHilbertState)
    (timeLengthNonneg : 0 ≤ timeLength)
    (bandRadiusNonneg : 0 ≤ bandRadius)
    (massCeilingNonneg : 0 ≤ massCeiling)
    (timeCeilingNonneg : 0 ≤ timeCeiling)
    (scalePos : ∀ index, 0 < scale index)
    (scaleLeOne : ∀ index, scale index ≤ 1)
    (radiusLe : ∀ index,
      scale index * (radius index : Real) ≤ bandRadius)
    (massLe : ∀ index (time : Icc (0 : Real) timeLength),
      scale index * finiteStateVorticityCoefficientEnstrophy
        (integerWaveFrequencyCube (radius index))
        (actualPath index
          (start index + scale index ^ 2 * time.1)) ≤ massCeiling)
    (timeIncrement : ∀ index
      (first second : Icc (0 : Real) timeLength),
      scale index * finiteStateVorticityCoefficientEnstrophy
        (integerWaveFrequencyCube (radius index))
        (actualPath index
            (start index + scale index ^ 2 * first.1) -
          actualPath index
            (start index + scale index ^ 2 * second.1)) ≤
        timeCeiling * dist first second)
    (zeroRow : ∀ index time, actualPath index time 0 = 0)
    (stateTransverse : ∀ index time,
      WholeStateTransverse (actualPath index time))
    (realityAE : ∀ index, ∀ᵐ time ∂volume,
      time ∈ Ioc (start index)
          (start index + scale index ^ 2 * timeLength) →
        FiniteStateFourierReality (actualPath index time))
    (μ : Measure (Cylinder timeLength spatialRadius))
    [IsFiniteMeasure μ]
    (vorticityProfile : Nat → BoundedContinuousFunction
      (Cylinder timeLength spatialRadius) PhysicalSpace)
    (vorticityLimit : BoundedContinuousFunction
      (Cylinder timeLength spatialRadius) PhysicalSpace)
    (vorticityCeiling : Real)
    (vorticityCeilingNonneg : 0 ≤ vorticityCeiling)
    (vorticityProfileEq : ∀ index point,
      vorticityProfile index point = (scale index ^ 2 : Real) •
        finiteRealComplexFourierField
          (integerWaveFrequencyCube (radius index))
          (actualPath index
            (start index + scale index ^ 2 * point.1.1))
          (center index + scale index • point.2.1))
    (vorticityBound : ∀ index point,
      ‖vorticityProfile index point‖ ≤ vorticityCeiling)
    (vorticityTendsto : Tendsto vorticityProfile atTop
      (nhds vorticityLimit))
    (timeChart : ∀ index,
      start index - timeCenter index =
        scale index ^ 2 * normalizedTimeOffset)
    (spatialTest : Coordinate → SchwartzMap Real Complex)
    (temporalTest : SchwartzMap Real Complex)
    (temporalCeiling : Real)
    (temporalBound : ∀ scaledTime : Icc (0 : Real) timeLength,
      ‖temporalTest (scaledTime.1 + normalizedTimeOffset)‖ ≤
        temporalCeiling)
    (testCoordinate : Coordinate)
    (supportRadius : Real)
    (periodLarge : ∀ index,
      supportRadius + (spatialRadius + 1) < (scale index)⁻¹)
    (support : ∀ coordinate y,
      supportRadius < |y| → spatialTest coordinate y = 0) :
    ∃ velocityProfile : Nat → BoundedContinuousFunction
        (Cylinder timeLength spatialRadius) PhysicalSpace,
    ∃ velocityLimit : BoundedContinuousFunction
        (Cylinder timeLength spatialRadius) PhysicalSpace,
    ∃ subsequence testRadius : Nat → Nat,
      StrictMono subsequence ∧
      (∀ index point,
        velocityProfile index point = scale index •
          finiteRealComplexFourierField
            (integerWaveFrequencyCube (radius index))
            (finiteStateVelocityCoefficient
              (actualPath index
                (start index + scale index ^ 2 * point.1.1)))
            (center index + scale index • point.2.1)) ∧
      Tendsto (fun index => velocityProfile (subsequence index)) atTop
        (nhds velocityLimit) ∧
      Tendsto (fun index => vorticityProfile (subsequence index)) atTop
        (nhds vorticityLimit) ∧
      (∀ velocityCoordinate vorticityCoordinate : Coordinate,
        Tendsto
          (fun index =>
            scaledProjectedTensorBCF timeLength spatialRadius
              (scale (subsequence index)) (start (subsequence index))
              (center (subsequence index))
              (puncturedIntegerWaveFrequencyCube (testRadius index))
              (fun wave => Pi.single testCoordinate
                (recenteredTensorSchwartzFourierCoefficient spatialTest
                  (scale (subsequence index))
                  (scalePos (subsequence index)).ne'
                  (center (subsequence index)) wave))
              (fun time => temporalTest
                ((time - timeCenter (subsequence index)) /
                  scale (subsequence index) ^ 2))
              (by fun_prop) velocityCoordinate vorticityCoordinate)
          atTop
          (nhds
            (fixedTensorSchwartzBCF timeLength spatialRadius spatialTest
              temporalTest normalizedTimeOffset testCoordinate
              velocityCoordinate vorticityCoordinate))) ∧
      Tendsto
        (fun index =>
          ∫ point,
            ∑ velocityCoordinate : Coordinate,
              ∑ vorticityCoordinate : Coordinate,
                scaledProjectedTensorBCF timeLength spatialRadius
                    (scale (subsequence index))
                    (start (subsequence index))
                    (center (subsequence index))
                    (puncturedIntegerWaveFrequencyCube (testRadius index))
                    (fun wave => Pi.single testCoordinate
                      (recenteredTensorSchwartzFourierCoefficient spatialTest
                        (scale (subsequence index))
                        (scalePos (subsequence index)).ne'
                        (center (subsequence index)) wave))
                    (fun time => temporalTest
                      ((time - timeCenter (subsequence index)) /
                        scale (subsequence index) ^ 2))
                    (by fun_prop) velocityCoordinate vorticityCoordinate point *
                  velocityProfile (subsequence index) point
                    velocityCoordinate *
                  vorticityProfile (subsequence index) point
                    vorticityCoordinate ∂μ)
        atTop
        (nhds
          (∫ point,
            ∑ velocityCoordinate : Coordinate,
              ∑ vorticityCoordinate : Coordinate,
                fixedTensorSchwartzBCF timeLength spatialRadius spatialTest
                    temporalTest normalizedTimeOffset testCoordinate
                    velocityCoordinate vorticityCoordinate point *
                  velocityLimit point velocityCoordinate *
                  vorticityLimit point vorticityCoordinate ∂μ)) ∧
      ∀ index,
        let originalIndex := subsequence index
        let testModes :=
          puncturedIntegerWaveFrequencyCube (testRadius index)
        let testCoefficient : IntegerWavevector → ComplexCoordinateVector :=
          fun wave => Pi.single testCoordinate
            (recenteredTensorSchwartzFourierCoefficient spatialTest
              (scale originalIndex) (scalePos originalIndex).ne'
              (center originalIndex) wave)
        let temporalWeight : Real → Complex := fun time =>
          temporalTest
            ((time - timeCenter originalIndex) / scale originalIndex ^ 2)
        let projected : Real → ComplexVorticityHilbertState := fun time =>
          complexSharpSupportProjection
            (integerWaveFrequencyCube (radius originalIndex))
            (actualPath originalIndex time)
        let rawVelocity : Real → PhysicalSpace → PhysicalSpace := fun time =>
          physicalVelocity (rawSourceOfFiniteVorticityState
            (puncturedIntegerWaveFrequencyCube (radius originalIndex))
            (projected time))
        let rawVorticity : Real → PhysicalSpace → PhysicalSpace := fun time =>
          finiteRealComplexFourierField
            (puncturedIntegerWaveFrequencyCube (radius originalIndex))
            (projected time)
        (∫ point : Cylinder timeLength spatialRadius,
          ∑ velocityCoordinate : Coordinate,
            ∑ vorticityCoordinate : Coordinate,
              scaledProjectedTensorBCF timeLength spatialRadius
                  (scale originalIndex) (start originalIndex)
                  (center originalIndex) testModes testCoefficient
                  temporalWeight (by fun_prop)
                  velocityCoordinate vorticityCoordinate point *
                velocityProfile originalIndex point velocityCoordinate *
                vorticityProfile originalIndex point vorticityCoordinate) =
          (scale originalIndex)⁻¹ *
            ∫ actualTime in start originalIndex..
                start originalIndex + scale originalIndex ^ 2 * timeLength,
              ∫ actualPoint in
                  (fun x : PhysicalSpace => x - center originalIndex) ⁻¹'
                    (scale originalIndex •
                      Metric.closedBall (0 : PhysicalSpace) spatialRadius),
                projectedTensorRawDensity testModes testCoefficient
                  temporalWeight rawVelocity rawVorticity actualTime
                    actualPoint := by
  let normalizedPath : Nat → Icc (0 : Real) timeLength →
      ComplexVorticityHilbertState := fun index time =>
    actualPath index (start index + scale index ^ 2 * time.1)
  have normalizedMassLe : ∀ index time,
      scale index * finiteStateVorticityCoefficientEnstrophy
        (integerWaveFrequencyCube (radius index))
        (normalizedPath index time) ≤ massCeiling := by
    intro index time
    simpa only [normalizedPath] using massLe index time
  have normalizedTimeIncrement : ∀ index first second,
      scale index * finiteStateVorticityCoefficientEnstrophy
        (integerWaveFrequencyCube (radius index))
        (normalizedPath index first - normalizedPath index second) ≤
          timeCeiling * dist first second := by
    intro index first second
    simpa only [normalizedPath] using timeIncrement index first second
  obtain ⟨velocityProfile, velocityLimit, subsequence, subsequenceMono,
      velocityProfileEq, velocityTendsto, vorticitySubsequenceTendsto,
      fixedProductTendsto⟩ :=
    finiteBandVelocity_parabolicScale_pairedTensorTest_tendsto_subseq
      timeLength spatialRadius bandRadius massCeiling timeCeiling scale radius
      center normalizedPath bandRadiusNonneg massCeilingNonneg
      timeCeilingNonneg scalePos scaleLeOne radiusLe normalizedMassLe
      normalizedTimeIncrement μ vorticityProfile vorticityLimit
      vorticityCeiling vorticityCeilingNonneg vorticityBound
      vorticityTendsto
  obtain ⟨testRadius, testTendsto⟩ :=
    exists_testRadius_scaledProjectedTensorBCF_tendsto_fixed
      timeLength spatialRadius normalizedTimeOffset
      (fun index => scale (subsequence index))
      (fun index => start (subsequence index))
      (fun index => timeCenter (subsequence index))
      (fun index => center (subsequence index))
      (fun index => scalePos (subsequence index))
      (fun index => scaleLeOne (subsequence index))
      (fun index => timeChart (subsequence index)) spatialTest temporalTest
      temporalCeiling temporalBound testCoordinate supportRadius
      (fun index => periodLarge (subsequence index)) support
  let fixedTest : Coordinate → Coordinate → BoundedContinuousFunction
      (Cylinder timeLength spatialRadius) Real := fun velocityCoordinate
        vorticityCoordinate =>
    fixedTensorSchwartzBCF timeLength spatialRadius spatialTest temporalTest
      normalizedTimeOffset testCoordinate velocityCoordinate
        vorticityCoordinate
  let fixedTestCeiling : Real :=
    ∑ velocityCoordinate : Coordinate,
      ∑ vorticityCoordinate : Coordinate,
        ‖fixedTest velocityCoordinate vorticityCoordinate‖
  have fixedTestCeilingNonneg : 0 ≤ fixedTestCeiling := by
    dsimp only [fixedTestCeiling]
    positivity
  have fixedTestBound (velocityCoordinate vorticityCoordinate : Coordinate)
      (point : Cylinder timeLength spatialRadius) :
      |fixedTest velocityCoordinate vorticityCoordinate point| ≤
        fixedTestCeiling := by
    exact coordinatePairBCF_abs_le_sum_norm fixedTest velocityCoordinate
      vorticityCoordinate point
  have fixedProductTendsto' :=
    fixedProductTendsto fixedTest fixedTestCeiling fixedTestCeilingNonneg
      fixedTestBound
  let velocityCeiling : Real := Real.sqrt
    (26 * biotSavartSerrinConstant * bandRadius * massCeiling)
  have velocityCeilingNonneg : 0 ≤ velocityCeiling := Real.sqrt_nonneg _
  have velocityCeilingArgumentNonneg :
      0 ≤ 26 * biotSavartSerrinConstant * bandRadius * massCeiling := by
    exact mul_nonneg
      (mul_nonneg
        (mul_nonneg (by norm_num) biotSavartSerrinConstant_nonneg)
        bandRadiusNonneg)
      massCeilingNonneg
  have velocityBound' (index : Nat)
      (point : Cylinder timeLength spatialRadius) :
      ‖velocityProfile (subsequence index) point‖ ≤ velocityCeiling := by
    rw [← sq_le_sq₀ (norm_nonneg _) velocityCeilingNonneg]
    rw [Real.sq_sqrt velocityCeilingArgumentNonneg]
    rw [velocityProfileEq]
    refine (finiteRealComplexFourierVelocityField_parabolicScale_norm_sq_le
      (radius (subsequence index))
      (normalizedPath (subsequence index) point.1)
      (scale (subsequence index))
      (le_of_lt (scalePos (subsequence index)))
      (center (subsequence index)) point.2.1).trans ?_
    have scaledMassNonneg : 0 ≤
        scale (subsequence index) *
          finiteStateVorticityCoefficientEnstrophy
            (integerWaveFrequencyCube (radius (subsequence index)))
            (normalizedPath (subsequence index) point.1) := by
      apply mul_nonneg (le_of_lt (scalePos _))
      unfold finiteStateVorticityCoefficientEnstrophy
      exact Finset.sum_nonneg fun _ _ => complexCoordinateAmplitudeSq_nonneg _
    have productLe :
        (scale (subsequence index) * (radius (subsequence index) : Real)) *
            (scale (subsequence index) *
              finiteStateVorticityCoefficientEnstrophy
                (integerWaveFrequencyCube (radius (subsequence index)))
                (normalizedPath (subsequence index) point.1)) ≤
          bandRadius * massCeiling := by
      exact mul_le_mul (radiusLe _) (normalizedMassLe _ _)
        scaledMassNonneg bandRadiusNonneg
    have coefficientNonneg :
        0 ≤ 26 * biotSavartSerrinConstant :=
      mul_nonneg (by norm_num) biotSavartSerrinConstant_nonneg
    calc
      26 * biotSavartSerrinConstant *
          (scale (subsequence index) *
            (radius (subsequence index) : Real)) *
          (scale (subsequence index) *
            finiteStateVorticityCoefficientEnstrophy
              (integerWaveFrequencyCube (radius (subsequence index)))
              (normalizedPath (subsequence index) point.1)) =
        (26 * biotSavartSerrinConstant) *
          ((scale (subsequence index) *
              (radius (subsequence index) : Real)) *
            (scale (subsequence index) *
              finiteStateVorticityCoefficientEnstrophy
                (integerWaveFrequencyCube (radius (subsequence index)))
                (normalizedPath (subsequence index) point.1))) := by ring
      _ ≤ (26 * biotSavartSerrinConstant) *
          (bandRadius * massCeiling) :=
        mul_le_mul_of_nonneg_left productLe coefficientNonneg
      _ = 26 * biotSavartSerrinConstant * bandRadius * massCeiling := by ring
  let varyingTest : Nat → Coordinate → Coordinate →
      BoundedContinuousFunction (Cylinder timeLength spatialRadius) Real :=
    fun index velocityCoordinate vorticityCoordinate =>
      scaledProjectedTensorBCF timeLength spatialRadius
        (scale (subsequence index)) (start (subsequence index))
        (center (subsequence index))
        (puncturedIntegerWaveFrequencyCube (testRadius index))
        (fun wave => Pi.single testCoordinate
          (recenteredTensorSchwartzFourierCoefficient spatialTest
            (scale (subsequence index))
            (scalePos (subsequence index)).ne'
            (center (subsequence index)) wave))
        (fun time => temporalTest
          ((time - timeCenter (subsequence index)) /
            scale (subsequence index) ^ 2))
        (by fun_prop) velocityCoordinate vorticityCoordinate
  have varyingProductTendsto :=
    varyingTensorTestProduct_integral_tendsto_of_fixed μ varyingTest fixedTest
      (fun index => velocityProfile (subsequence index))
      (fun index => vorticityProfile (subsequence index)) velocityLimit
      vorticityLimit velocityCeiling vorticityCeiling
      velocityCeilingNonneg vorticityCeilingNonneg testTendsto velocityBound'
      (fun index point => vorticityBound (subsequence index) point)
      (by simpa only [fixedTest] using fixedProductTendsto')
  refine ⟨velocityProfile, velocityLimit, subsequence, testRadius,
    subsequenceMono, ?_, velocityTendsto, vorticitySubsequenceTendsto,
    testTendsto, ?_, ?_⟩
  · intro index point
    simpa only [normalizedPath] using velocityProfileEq index point
  · simpa only [varyingTest, fixedTest] using varyingProductTendsto
  · intro index
    dsimp only
    apply f3RecenteredTensorFullCubeProfiles_integral_eq_restricted985RHS
      timeLength spatialRadius (scale (subsequence index))
      (start (subsequence index)) (timeCenter (subsequence index))
      timeLengthNonneg (scalePos (subsequence index))
      (center (subsequence index)) (radius (subsequence index))
      (testRadius index) (actualPath (subsequence index))
      (zeroRow (subsequence index)) (stateTransverse (subsequence index))
      (realityAE (subsequence index)) spatialTest temporalTest testCoordinate
      (velocityProfile (subsequence index))
      (vorticityProfile (subsequence index))
    · intro point
      simpa only [normalizedPath] using
        velocityProfileEq (subsequence index) point
    · exact vorticityProfileEq (subsequence index)


end

end
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartCrossingFrequencySupportExhaustion
end NavierStokes
end SaturationMonoid
