import H0mework.NavierStokes.ShellSources.StrongContinuationEnergyLedger

/-!
# Exact source-receipt write-back in the whole PDE energy ledger

The source-generated integer-shell lineage already carries an exact
nonnegative receipt quantum at every native scale update.  This module
identifies the complete receipt series with the Euclidean Fourier mass of
the actual infinite mild initial state, then substitutes that identity into
the all-wave nonlinear-minus-viscous work ledger.

The final theorem is an equality on the same whole carrier:

```text
all-wave actual energy work
  = terminal punctured Euclidean mass
      - (seed carrier mass + complete source receipt series).
```

No finite cutoff, tail-silence certificate, endpoint state, frequency
cover, or target obstruction is accepted as input.  This is an exact
write-back seam; separating the nonlinear work from the frequency-weighted
viscous dissipation and feeding the resulting estimate to a continuation
criterion remain downstream analytic obligations.
-/

namespace SaturationMonoid
namespace NavierStokes
namespace ThreeDimensionalVorticityCoefficientGeneratedIntegerShellWholeReceiptEnergyWriteBack

open scoped BigOperators ENNReal Topology

open Filter
open ThreeDimensionalPeriodicCoarseFilterCore
open ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open ThreeDimensionalVorticityCoefficientGeneratedIntegerShellSource
open ThreeDimensionalVorticityCoefficientGeneratedIntegerShellTraceCumulative
open ThreeDimensionalVorticityCoefficientGeneratedShellSerrinGeometry
open ThreeDimensionalVorticityCoefficientFixedOutputNonlinearContinuity
open ThreeDimensionalVorticityCoefficientInfiniteFixedOutputNonlinearRow
open ThreeDimensionalVorticityCoefficientPuncturedCanonicalGalerkinTarget
open ThreeDimensionalVorticityCoefficientGeneratedPathInfiniteNonlinearNegativeOneTimeBudget
open ThreeDimensionalVorticityCoefficientGeneratedIntegerShellInfiniteLineageReceiptSquare
open ThreeDimensionalVorticityCoefficientGeneratedIntegerShellInfiniteLineageReceiptSquare.GeneratedIntegerShellInfiniteLineage
open ThreeDimensionalVorticityCoefficientGeneratedIntegerShellInfiniteLineageCarrierCompletion
open ThreeDimensionalVorticityCoefficientGeneratedIntegerShellInfiniteLineageCarrierCompletion.GeneratedIntegerShellInfiniteLineage
open ThreeDimensionalVorticityCoefficientGeneratedIntegerShellInfiniteLineageHilbertCompletion
open ThreeDimensionalVorticityCoefficientGeneratedIntegerShellInfiniteLineageHilbertCompletion.GeneratedIntegerShellInfiniteLineage
open ThreeDimensionalVorticityCoefficientGeneratedIntegerShellInfiniteMildDuhamel
open ThreeDimensionalVorticityCoefficientGeneratedIntegerShellStrongContinuation
open ThreeDimensionalVorticityCoefficientGeneratedIntegerShellStrongContinuationEnergyLedger

noncomputable section

/--
The continuous linear observation of one physical coordinate across every
integer Fourier row.
-/
def wholeStateCoordinateSliceCLM
    (coordinate : Coordinate) :
    ComplexVorticityHilbertState →L[ℂ]
      lp (fun _ : IntegerWavevector => ℂ) 2 :=
  lp.mapCLM 2
    (fun _wave =>
      (ContinuousLinearMap.proj coordinate :
        ComplexCoordinateVector →L[ℂ] ℂ))
    zero_le_one
    (fun _wave => by
      apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
      intro vector
      simpa only [one_mul, ContinuousLinearMap.proj_apply] using
        norm_le_pi_norm vector coordinate)

@[simp] theorem wholeStateCoordinateSliceCLM_apply
    (coordinate : Coordinate)
    (state : ComplexVorticityHilbertState)
    (wave : IntegerWavevector) :
    wholeStateCoordinateSliceCLM coordinate state wave =
      state wave coordinate :=
  rfl

/--
The whole Euclidean Fourier mass is exactly the finite sum of the squared
`ℓ²` norms of its three coordinate slices.
-/
theorem wholeVorticityEuclideanMass_eq_coordinateSlices
    (state : ComplexVorticityHilbertState) :
    wholeVorticityEuclideanMass state =
      ∑ coordinate : Coordinate,
        ‖wholeStateCoordinateSliceCLM coordinate state‖ ^ 2 := by
  unfold wholeVorticityEuclideanMass
  rw [show
    (fun wave : IntegerWavevector =>
      vorticityRowAmplitude state wave ^ 2) =
        (fun wave : IntegerWavevector =>
          complexCoordinateAmplitudeSq (state wave)) by
      funext wave
      exact vorticityRowAmplitude_sq state wave]
  unfold complexCoordinateAmplitudeSq
  simp_rw [Complex.normSq_eq_norm_sq]
  have coordinateSummable :
      ∀ coordinate : Coordinate,
        Summable fun wave : IntegerWavevector =>
          ‖state wave coordinate‖ ^ 2 := by
    intro coordinate
    have summableSlice :=
      (lp.hasSum_norm
        (p := (2 : ℝ≥0∞)) (by norm_num)
        (wholeStateCoordinateSliceCLM coordinate state)).summable
    convert summableSlice using 1
    all_goals
      norm_num [wholeStateCoordinateSliceCLM_apply]
  rw [Summable.tsum_finsetSum
    (fun coordinate _coordinateMem =>
      coordinateSummable coordinate)]
  apply Finset.sum_congr rfl
  intro coordinate coordinateMem
  have normIdentity :=
    lp.norm_rpow_eq_tsum
      (p := (2 : ℝ≥0∞)) (by norm_num)
      (wholeStateCoordinateSliceCLM coordinate state)
  norm_num at normIdentity
  rw [normIdentity]

/--
Strong convergence in the whole Fourier Hilbert carrier preserves the exact
Euclidean coordinate mass.
-/
theorem tendsto_wholeVorticityEuclideanMass
    {α : Type*}
    {filter : Filter α}
    {states : α → ComplexVorticityHilbertState}
    {limit : ComplexVorticityHilbertState}
    (statesTendsto : Tendsto states filter (𝓝 limit)) :
    Tendsto
      (fun index =>
        wholeVorticityEuclideanMass (states index))
      filter
      (𝓝 (wholeVorticityEuclideanMass limit)) := by
  rw [show
      (fun index =>
        wholeVorticityEuclideanMass (states index)) =
        (fun index =>
          ∑ coordinate : Coordinate,
            ‖wholeStateCoordinateSliceCLM coordinate
              (states index)‖ ^ 2) by
        funext index
        exact wholeVorticityEuclideanMass_eq_coordinateSlices
          (states index)]
  rw [wholeVorticityEuclideanMass_eq_coordinateSlices limit]
  apply tendsto_finsetSum Finset.univ
  intro coordinate coordinateMem
  exact
    (((wholeStateCoordinateSliceCLM coordinate).continuous.tendsto
      limit).comp statesTendsto).norm.pow 2

/--
Embedding a finite source coefficient carrier into the whole Hilbert state
preserves its exact Euclidean mass.
-/
theorem wholeVorticityEuclideanMass_coefficientCarrierComplexState
    (carrier : IntegerShellCoefficientCarrier) :
    wholeVorticityEuclideanMass
        (coefficientCarrierComplexState carrier) =
      coefficientCarrierNormSq carrier := by
  rw [
    wholeVorticityEuclideanMass_eq_finite_of_supported
      (coefficientWaveSupport carrier)
      (coefficientCarrierComplexState carrier)
      (by
        intro wave waveNotMem
        rw [
          coefficientCarrierComplexState,
          finiteComplexVorticityState_apply,
          if_neg waveNotMem])]
  exact
    (coefficientCarrierNormSq_eq_coefficientEnstrophy carrier).symm

/--
At every finite source prefix, the endpoint Hilbert mass is the seed mass
plus the exact accumulated receipt quantum.
-/
theorem endpointHilbertState_euclideanMass_eq_seed_add_sum_range
    (lineage : GeneratedIntegerShellInfiniteLineage)
    (length : ℕ) :
    wholeVorticityEuclideanMass
        (endpointHilbertState lineage length) =
      coefficientCarrierNormSq
          (generatedCoefficientCarrier
            (lineage.current 0)) +
        ∑ index ∈ Finset.range length,
          lineage.receiptQuantum index := by
  rw [endpointHilbertState_eq_carrierComplexState,
    wholeVorticityEuclideanMass_coefficientCarrierComplexState,
    generatedCoefficientCarrier_normSq_current_eq_seed_add_sum_range]

section InfiniteReceipt

variable
    {lineage : GeneratedIntegerShellInfiniteLineage}
    {ν : Viscosity}
    {θ requestedTime : ℝ}
    {θLtOne : θ < 1}
    {criticalMargin :
      ∀ length : ℕ,
        ThreeDimensionalVorticityCoefficientFiniteGalerkinCriticalEnstrophyBarrier.criticalEnstrophyLatticeConstant *
            ThreeDimensionalVorticityCoefficientFiniteGalerkinEnstrophyBalance.finiteStateVorticityCoefficientEnstrophy
              (generatedSupport (lineage.current length))
              (generatedComplexVorticityState
                (lineage.current length)
                (generatedSupport (lineage.current length))) ≤
          θ * ν.coeff ^ 2 * (2 * Real.pi) ^ 2}
    {requestedTimePos : 0 < requestedTime}

/--
The actual finite source endpoints converge to the initial whole state of
the same generated mild receipt.
-/
theorem endpointHilbertState_tendsto_initialState
    (receipt :
      InfiniteMildDuhamelForcingReceipt
        lineage ν θ requestedTime θLtOne criticalMargin
        requestedTimePos) :
    Tendsto (endpointHilbertState lineage)
      atTop (𝓝 receipt.initialState) := by
  rcases
      endpointHilbertState_puncturedFrequencyCube_tendsto_limit
        lineage ν θ criticalMargin with
    ⟨limit, endpointTendsto, projectedTendsto⟩
  have projectedTendsto' :
      Tendsto
        (puncturedCanonicalInitialState lineage)
        atTop (𝓝 limit) := by
    change
      Tendsto
        (fun radius =>
          complexSharpSupportProjection
            (puncturedIntegerWaveFrequencyCube radius)
            (endpointHilbertState lineage radius))
        atTop (𝓝 limit)
    exact projectedTendsto
  have limitEq :
      limit = receipt.initialState :=
    tendsto_nhds_unique projectedTendsto'
      receipt.initial_tendsto
  rw [limitEq] at endpointTendsto
  exact endpointTendsto

/--
The Euclidean mass of the actual whole initial state is exactly the source
seed mass plus the complete source-generated receipt quantum series.
-/
theorem initialState_euclideanMass_eq_seed_add_receiptQuantum_tsum
    (receipt :
      InfiniteMildDuhamelForcingReceipt
        lineage ν θ requestedTime θLtOne criticalMargin
        requestedTimePos) :
    wholeVorticityEuclideanMass receipt.initialState =
      coefficientCarrierNormSq
          (generatedCoefficientCarrier
            (lineage.current 0)) +
        ∑' index : ℕ, lineage.receiptQuantum index := by
  have massTendsto :
      Tendsto
        (fun length =>
          wholeVorticityEuclideanMass
            (endpointHilbertState lineage length))
        atTop
        (𝓝
          (wholeVorticityEuclideanMass
            receipt.initialState)) :=
    tendsto_wholeVorticityEuclideanMass
      (endpointHilbertState_tendsto_initialState receipt)
  have quantumTendsto :
      Tendsto
        (fun length =>
          ∑ index ∈ Finset.range length,
            lineage.receiptQuantum index)
        atTop
        (𝓝 (∑' index : ℕ,
          lineage.receiptQuantum index)) :=
    (ThreeDimensionalVorticityCoefficientGeneratedIntegerShellInfiniteLineageCarrierCompletion.GeneratedIntegerShellInfiniteLineage.receiptQuantum_summable
      lineage ν θ criticalMargin).hasSum.tendsto_sum_nat
  have sourceTendsto :
      Tendsto
        (fun length =>
          wholeVorticityEuclideanMass
            (endpointHilbertState lineage length))
        atTop
        (𝓝
          (coefficientCarrierNormSq
              (generatedCoefficientCarrier
                (lineage.current 0)) +
            ∑' index : ℕ,
              lineage.receiptQuantum index)) := by
    rw [show
      (fun length =>
        wholeVorticityEuclideanMass
          (endpointHilbertState lineage length)) =
        (fun length =>
          coefficientCarrierNormSq
              (generatedCoefficientCarrier
                (lineage.current 0)) +
            ∑ index ∈ Finset.range length,
              lineage.receiptQuantum index) by
        funext length
        exact
          endpointHilbertState_euclideanMass_eq_seed_add_sum_range
            lineage length]
    exact tendsto_const_nhds.add quantumTendsto
  exact tendsto_nhds_unique massTendsto sourceTendsto

/--
Removing the zero Fourier row does not change Euclidean mass when that row
is actually zero.
-/
theorem puncturedWholeVorticityEuclideanMass_eq_whole_of_zero_row
    (state : ComplexVorticityHilbertState)
    (zeroRow : state 0 = 0) :
    puncturedWholeVorticityEuclideanMass state =
      wholeVorticityEuclideanMass state := by
  let mass : IntegerWavevector → ℝ :=
    fun wave =>
      complexCoordinateAmplitudeSq (state wave)
  have massSummable : Summable mass := by
    exact
      (summable_vorticityRowAmplitude_sq state).congr
        (fun wave =>
          vorticityRowAmplitude_sq state wave)
  have complementZero :
      (∑' wave :
          ↥({ wave : IntegerWavevector | wave ≠ 0 }ᶜ :
            Set IntegerWavevector),
        mass wave.1) =
        0 := by
    have pointwiseZero :
        ∀ wave :
            ↥({ wave : IntegerWavevector | wave ≠ 0 }ᶜ :
              Set IntegerWavevector),
          mass wave.1 = 0 := by
      intro wave
      have waveZero : wave.1 = 0 := by
        simpa using wave.2
      rw [waveZero]
      unfold mass
      rw [zeroRow]
      simp [complexCoordinateAmplitudeSq]
    rw [show
      (fun wave :
          ↥({ wave : IntegerWavevector | wave ≠ 0 }ᶜ :
            Set IntegerWavevector) =>
        mass wave.1) =
        0 by
      funext wave
      exact pointwiseZero wave]
    exact tsum_zero
  have split :=
    massSummable.tsum_subtype_add_tsum_subtype_compl
      { wave : IntegerWavevector | wave ≠ 0 }
  unfold puncturedWholeVorticityEuclideanMass
  unfold wholeVorticityEuclideanMass
  rw [show
      (fun wave : IntegerWavevector =>
        vorticityRowAmplitude state wave ^ 2) =
        mass by
      funext wave
      exact vorticityRowAmplitude_sq state wave]
  simpa only [mass, complementZero, add_zero] using split

/--
The exact source receipt series is the punctured Euclidean mass of the
actual infinite mild initial state.
-/
theorem initialState_puncturedEuclideanMass_eq_seed_add_receiptQuantum_tsum
    (receipt :
      InfiniteMildDuhamelForcingReceipt
        lineage ν θ requestedTime θLtOne criticalMargin
        requestedTimePos) :
    puncturedWholeVorticityEuclideanMass receipt.initialState =
      coefficientCarrierNormSq
          (generatedCoefficientCarrier
            (lineage.current 0)) +
        ∑' index : ℕ, lineage.receiptQuantum index := by
  rw [
    puncturedWholeVorticityEuclideanMass_eq_whole_of_zero_row
      receipt.initialState
      (ThreeDimensionalVorticityCoefficientGeneratedIntegerShellInfiniteMildPhysicalLimit.InfiniteMildDuhamelForcingReceipt.initialState_zero_row
        receipt),
    initialState_euclideanMass_eq_seed_add_receiptQuantum_tsum receipt]

/--
Every finite source receipt prefix is paid for by the exact Euclidean mass
of the actual whole initial state.
-/
theorem prefixReceiptQuantumMass_le_initialState
    (receipt :
      InfiniteMildDuhamelForcingReceipt
        lineage ν θ requestedTime θLtOne criticalMargin
        requestedTimePos)
    (length : ℕ) :
    coefficientCarrierNormSq
          (generatedCoefficientCarrier
            (lineage.current 0)) +
        ∑ index ∈ Finset.range length,
          lineage.receiptQuantum index ≤
      puncturedWholeVorticityEuclideanMass
        receipt.initialState := by
  rw [
    initialState_puncturedEuclideanMass_eq_seed_add_receiptQuantum_tsum
      receipt]
  gcongr
  exact
    (ThreeDimensionalVorticityCoefficientGeneratedIntegerShellInfiniteLineageCarrierCompletion.GeneratedIntegerShellInfiniteLineage.receiptQuantum_summable
      lineage ν θ criticalMargin).sum_le_tsum
        (Finset.range length)
        (fun index _indexMem =>
          lineage.receiptQuantum_nonneg index)

/--
Exact whole-carrier source/PDE write-back.

The complete source receipt quantum series is not merely compared with an
analytic budget: it is the initial-mass term in the same equality whose
left side is the actual all-wave nonlinear-minus-viscous work.
-/
theorem tsum_actualWaveEnergyWork_eq_terminal_sub_seed_add_receiptQuantum_tsum
    (receipt :
      StrongContinuationReceipt
        lineage ν θ requestedTime θLtOne criticalMargin
        requestedTimePos) :
    (∑' wave : NonzeroIntegerWavevector,
        actualWaveEnergyWork receipt wave) =
      puncturedWholeVorticityEuclideanMass
          (receipt.wholePath
            ⟨requestedTime,
              ⟨requestedTimePos.le, le_rfl⟩⟩) -
        (coefficientCarrierNormSq
            (generatedCoefficientCarrier
              (lineage.current 0)) +
          ∑' index : ℕ,
            lineage.receiptQuantum index) := by
  rw [tsum_actualWaveEnergyWork_eq]
  rw [
    initialState_puncturedEuclideanMass_eq_seed_add_receiptQuantum_tsum
      receipt.toInfiniteMildDuhamelForcingReceipt]

end InfiniteReceipt

end

end ThreeDimensionalVorticityCoefficientGeneratedIntegerShellWholeReceiptEnergyWriteBack
end NavierStokes
end SaturationMonoid
