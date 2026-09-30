import H0mework.NavierStokes.EndpointSettlement.ReceiptSquareCascade

/-!
# Annular responsibility of the reduced-core scale lineage

The least crossing radius does more than label the cofinal branch.  At every
generated scale node, the previous requested cube is still below the fixed
half-critical threshold while the internally selected least core is above it.
Their exact finite-sum difference is therefore a positive annular coefficient
mass in the same actual whole state.

Consequently the source itself generates a nonzero physical Fourier mode
strictly beyond the requested radius at every scale node.  No mode, cutoff,
gap, lower amplitude, or nonzero witness is accepted from a caller.
-/

namespace SaturationMonoid
namespace NavierStokes
namespace
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointRecursiveMacroRuntime

open ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientStretchingPairTable
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open ThreeDimensionalVorticityCoefficientFiniteGalerkinEnstrophyBalance
open ThreeDimensionalVorticityCoefficientGeneratedShellSerrinGeometry
open
  ThreeDimensionalVorticityCoefficientFiniteGalerkinCriticalEnstrophyBarrier
open ThreeDimensionalVorticityCoefficientInfiniteFixedOutputNonlinearRow
open ThreeDimensionalVorticityCoefficientPuncturedCanonicalGalerkinTarget
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartCanonicalReplay
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion.GeneratedWholeRestartCurrent
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartCrossingFiniteCore
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartCrossingFrequencySupportExhaustion

noncomputable section

namespace GeneratedInfiniteWholeRestartEndpointMacroLineage

/-- The exact new frequency band between the requested cube and the least
crossing core generated at one scale node. -/
def WholeRestartReducedCoreScaleLineage.annularModes
    {ν : Viscosity}
    {initial : GeneratedWholeRestartCurrent ν}
    (scale : WholeRestartReducedCoreScaleLineage initial)
    (step : ℕ) : Finset IntegerWavevector :=
  wholeRestartCrossingFiniteCoreModes
      (run initial (scale.start step))
      (scale.relativeIndex step) (scale.crossed step) \
    wholeRestartModes (scale.requestedRadius step)

/-- The physical coefficient mass carried by the same generated annulus at
the same actual occurrence. -/
def WholeRestartReducedCoreScaleLineage.annularCoefficientMass
    {ν : Viscosity}
    {initial : GeneratedWholeRestartCurrent ν}
    (scale : WholeRestartReducedCoreScaleLineage initial)
    (step : ℕ) : ℝ :=
  finiteStateVorticityCoefficientEnstrophy
    (scale.annularModes step)
    (run initial (scale.absoluteOccurrence step)).contact.physicalState

private theorem WholeRestartReducedCoreScaleLineage.requestedModes_subset_coreModes
    {ν : Viscosity}
    {initial : GeneratedWholeRestartCurrent ν}
    (scale : WholeRestartReducedCoreScaleLineage initial)
    (step : ℕ) :
    wholeRestartModes (scale.requestedRadius step) ⊆
    wholeRestartCrossingFiniteCoreModes
        (run initial (scale.start step))
        (scale.relativeIndex step) (scale.crossed step) := by
  intro wave waveMem
  unfold wholeRestartModes at waveMem
  unfold wholeRestartCrossingFiniteCoreModes wholeRestartModes
  rw [puncturedIntegerWaveFrequencyCube, Finset.mem_erase] at waveMem ⊢
  exact
    ⟨waveMem.1,
      integerWaveFrequencyCube_mono
        (Nat.le_of_lt (scale.coreEscapes step)) waveMem.2⟩

/-- Exact disjoint finite-sum split of the least crossing core into its newly
exposed annulus and the previously requested finite cube. -/
theorem WholeRestartReducedCoreScaleLineage.coreMass_eq_annular_add_requested
    {ν : Viscosity}
    {initial : GeneratedWholeRestartCurrent ν}
    (scale : WholeRestartReducedCoreScaleLineage initial)
    (step : ℕ) :
    finiteStateVorticityCoefficientEnstrophy
          (wholeRestartCrossingFiniteCoreModes
            (run initial (scale.start step))
            (scale.relativeIndex step) (scale.crossed step))
          (run initial (scale.absoluteOccurrence step)).contact.physicalState =
      scale.annularCoefficientMass step +
        finiteStateVorticityCoefficientEnstrophy
          (wholeRestartModes (scale.requestedRadius step))
          (run initial (scale.absoluteOccurrence step)).contact.physicalState := by
  unfold WholeRestartReducedCoreScaleLineage.annularCoefficientMass
    WholeRestartReducedCoreScaleLineage.annularModes
    finiteStateVorticityCoefficientEnstrophy
  rw [Finset.sum_sdiff (scale.requestedModes_subset_coreModes step)]

/-- The newly exposed annular physical responsibility is strictly positive.
Its positivity is generated by `Nat.find` minimality and the same actual
crossing, rather than stored as a certificate. -/
theorem WholeRestartReducedCoreScaleLineage.annularCoefficientMass_pos
    {ν : Viscosity}
    {initial : GeneratedWholeRestartCurrent ν}
    (scale : WholeRestartReducedCoreScaleLineage initial)
    (step : ℕ) :
    0 < scale.annularCoefficientMass step := by
  have requestedBelow :=
    wholeRestartCrossingFiniteCoreRadius_minimal
      (run initial (scale.start step))
      (scale.relativeIndex step) (scale.crossed step)
      (scale.coreEscapes step)
  have coreAbove :=
    wholeRestartCrossingFiniteCoreRadius_crossed
      (run initial (scale.start step))
      (scale.relativeIndex step) (scale.crossed step)
  rw [scale.actualCurrent step] at requestedBelow coreAbove
  have scaledMassLt :
      criticalEnstrophyLatticeConstant *
            finiteStateVorticityCoefficientEnstrophy
              (wholeRestartModes (scale.requestedRadius step))
              (run initial
                (scale.absoluteOccurrence step)).contact.physicalState <
        criticalEnstrophyLatticeConstant *
            finiteStateVorticityCoefficientEnstrophy
              (wholeRestartCrossingFiniteCoreModes
                (run initial (scale.start step))
                (scale.relativeIndex step) (scale.crossed step))
              (run initial
                (scale.absoluteOccurrence step)).contact.physicalState :=
    requestedBelow.trans_lt coreAbove
  have requestedMassLtCore :
      finiteStateVorticityCoefficientEnstrophy
            (wholeRestartModes (scale.requestedRadius step))
            (run initial
              (scale.absoluteOccurrence step)).contact.physicalState <
        finiteStateVorticityCoefficientEnstrophy
            (wholeRestartCrossingFiniteCoreModes
              (run initial (scale.start step))
              (scale.relativeIndex step) (scale.crossed step))
            (run initial
              (scale.absoluteOccurrence step)).contact.physicalState :=
    by
      nlinarith [criticalEnstrophyLatticeConstant_pos]
  rw [scale.coreMass_eq_annular_add_requested step] at requestedMassLtCore
  linarith

/-- Positive annular mass exposes one concrete nonzero physical row before
any coefficient or occurrence quotient can merge it away. -/
theorem WholeRestartReducedCoreScaleLineage.annular_generates_nonzero_mode
    {ν : Viscosity}
    {initial : GeneratedWholeRestartCurrent ν}
    (scale : WholeRestartReducedCoreScaleLineage initial)
    (step : ℕ) :
    ∃ output : IntegerWavevector,
      output ∈ scale.annularModes step ∧
        (run initial
          (scale.absoluteOccurrence step)).contact.physicalState output ≠ 0 := by
  by_contra noOutput
  have allZero :
      ∀ output ∈ scale.annularModes step,
        (run initial
          (scale.absoluteOccurrence step)).contact.physicalState output = 0 := by
    intro output outputMem
    by_contra outputNonzero
    exact noOutput ⟨output, outputMem, outputNonzero⟩
  have massZero : scale.annularCoefficientMass step = 0 := by
    unfold WholeRestartReducedCoreScaleLineage.annularCoefficientMass
      finiteStateVorticityCoefficientEnstrophy
    apply Finset.sum_eq_zero
    intro output outputMem
    rw [allZero output outputMem]
    exact (complexCoordinateVectorNormSq_eq_zero_iff 0).2 rfl
  exact
    (ne_of_gt (scale.annularCoefficientMass_pos step)) massZero

/-- Every row in the generated annulus is a genuine nonzero Fourier mode. -/
theorem WholeRestartReducedCoreScaleLineage.annularMode_ne_zero
    {ν : Viscosity}
    {initial : GeneratedWholeRestartCurrent ν}
    (scale : WholeRestartReducedCoreScaleLineage initial)
    (step : ℕ)
    {output : IntegerWavevector}
    (outputMem : output ∈ scale.annularModes step) :
    output ≠ 0 := by
  have outputCoreMem := (Finset.mem_sdiff.mp outputMem).1
  unfold wholeRestartCrossingFiniteCoreModes wholeRestartModes at outputCoreMem
  exact (Finset.mem_erase.mp outputCoreMem).1

/-- The annular carrier is pointwise beyond the source-owned requested
radius, not merely nonempty there. -/
theorem WholeRestartReducedCoreScaleLineage.annularMode_frequency_gt
    {ν : Viscosity}
    {initial : GeneratedWholeRestartCurrent ν}
    (scale : WholeRestartReducedCoreScaleLineage initial)
    (step : ℕ)
    {output : IntegerWavevector}
    (outputMem : output ∈ scale.annularModes step) :
    scale.requestedRadius step < integerWaveCoordinateRadius output := by
  apply lt_of_not_ge
  intro outputRadiusLe
  have outputInRequested :
      output ∈ wholeRestartModes (scale.requestedRadius step) := by
    unfold wholeRestartModes puncturedIntegerWaveFrequencyCube
    exact
      Finset.mem_erase.mpr
        ⟨scale.annularMode_ne_zero step outputMem,
          integerWave_mem_frequencyCube_of_radius_le
            output (scale.requestedRadius step) outputRadiusLe⟩
  exact (Finset.mem_sdiff.mp outputMem).2 outputInRequested

/-- Escaping a coordinate cube forces the literal Euclidean frequency square
to pay at least the next integer radius. -/
theorem integerWaveCoordinateRadius_succ_sq_le_normSq
    (radius : ℕ)
    (output : IntegerWavevector)
    (radiusLarge : radius < integerWaveCoordinateRadius output) :
    ((radius + 1 : ℕ) : ℝ) ^ 2 ≤ integerWaveNormSq output := by
  unfold integerWaveCoordinateRadius at radiusLarge
  obtain ⟨coordinate, _coordinateMem, coordinateLarge⟩ :=
    Finset.lt_sup_iff.mp radiusLarge
  have radiusSuccLe :
      radius + 1 ≤ Int.natAbs (output coordinate) :=
    Nat.succ_le_iff.mpr coordinateLarge
  have radiusSuccCastLe :
      ((radius + 1 : ℕ) : ℝ) ≤
        ((Int.natAbs (output coordinate) : ℕ) : ℝ) := by
    exact_mod_cast radiusSuccLe
  have natAbsCast :
      ((Int.natAbs (output coordinate) : ℕ) : ℝ) =
        |(output coordinate : ℝ)| := by
    rw [← Int.cast_natCast]
    rw [Int.natCast_natAbs]
    norm_cast
  rw [natAbsCast] at radiusSuccCastLe
  have coordinateSqLe :
      ((radius + 1 : ℕ) : ℝ) ^ 2 ≤
        (output coordinate : ℝ) ^ 2 := by
    calc
      ((radius + 1 : ℕ) : ℝ) ^ 2 ≤
          |(output coordinate : ℝ)| ^ 2 :=
        (sq_le_sq₀ (by positivity) (abs_nonneg _)).2 radiusSuccCastLe
      _ = (output coordinate : ℝ) ^ 2 := sq_abs _
  exact coordinateSqLe.trans (by
    unfold integerWaveNormSq
    exact Finset.single_le_sum
      (fun other _otherMem => sq_nonneg (output other : ℝ))
      (Finset.mem_univ coordinate))

/-- The whole annular mass therefore carries an exact source-generated
frequency-square factor before the kinetic consumer is applied. -/
theorem
    WholeRestartReducedCoreScaleLineage.requestedFrequencySq_mul_annularMass_le_weighted
    {ν : Viscosity}
    {initial : GeneratedWholeRestartCurrent ν}
    (scale : WholeRestartReducedCoreScaleLineage initial)
    (step : ℕ) :
    (2 * Real.pi) ^ 2 *
          ((scale.requestedRadius step + 1 : ℕ) : ℝ) ^ 2 *
          scale.annularCoefficientMass step ≤
      ∑ output ∈ scale.annularModes step,
        integerWaveViscousMultiplier output *
          complexCoordinateAmplitudeSq
            ((run initial
              (scale.absoluteOccurrence step)).contact.physicalState
                output) := by
  unfold WholeRestartReducedCoreScaleLineage.annularCoefficientMass
    finiteStateVorticityCoefficientEnstrophy
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro output outputMem
  apply mul_le_mul_of_nonneg_right
  · unfold integerWaveViscousMultiplier
    exact mul_le_mul_of_nonneg_left
      (integerWaveCoordinateRadius_succ_sq_le_normSq
        (scale.requestedRadius step) output
        (scale.annularMode_frequency_gt step outputMem))
      (sq_nonneg _)
  · exact complexCoordinateAmplitudeSq_nonneg _

/-- Every generated scale node therefore produces a concrete nonzero physical
Fourier responsibility strictly beyond its source-owned requested radius. -/
theorem WholeRestartReducedCoreScaleLineage.annular_generates_highFrequency_mode
    {ν : Viscosity}
    {initial : GeneratedWholeRestartCurrent ν}
    (scale : WholeRestartReducedCoreScaleLineage initial)
    (step : ℕ) :
    ∃ output : IntegerWavevector,
      scale.requestedRadius step < integerWaveCoordinateRadius output ∧
        output ∈ scale.annularModes step ∧
        (run initial
          (scale.absoluteOccurrence step)).contact.physicalState output ≠ 0 := by
  obtain ⟨output, outputMem, outputNonzero⟩ :=
    scale.annular_generates_nonzero_mode step
  exact
    ⟨output, scale.annularMode_frequency_gt step outputMem,
      outputMem, outputNonzero⟩

end GeneratedInfiniteWholeRestartEndpointMacroLineage

end

end
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointRecursiveMacroRuntime
end NavierStokes
end SaturationMonoid
