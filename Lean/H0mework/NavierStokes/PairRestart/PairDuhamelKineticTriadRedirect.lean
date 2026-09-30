import H0mework.NavierStokes.PairRestart.PairDuhamelOccurrence
import H0mework.NavierStokes.Energy.FiniteKineticDifferenceCancellation

/-!
# Same-event kinetic triad compiler for whole-restart pair Duhamel rows

The complete pair-Duhamel table is a vorticity carrier.  The native
three-slot skew relation, however, is generated on the velocity-convection
carrier before fixed-output aggregation.  This module proves the missing
same-event compiler:

```text
actual continuous whole path
  -> two ordered velocity occurrences of one input pair
  -> causal heat integration
  -> physical curl
  = the two existing vorticity pair-Duhamel occurrences.
```

The two ordered occurrences, the receipt, the physical time, the heat
multiplier and the output wave are identical on both sides.  No cutoff,
target path, pair coverage, nonzero witness or coercive estimate is supplied.
-/

namespace SaturationMonoid
namespace NavierStokes
namespace
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartPairDuhamelKineticTriadRedirect

open scoped BigOperators ENNReal Interval

open Set Filter MeasureTheory
open ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientStretchingPairTable
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open ThreeDimensionalVorticityCoefficientFiniteSupportRealityTrajectory
open ThreeDimensionalVorticityCoefficientFiniteGalerkinMildDuhamel
open ThreeDimensionalVorticityCoefficientFiniteGalerkinKineticEnergyLedger
open ThreeDimensionalVorticityCoefficientFixedOutputNonlinearContinuity
open ThreeDimensionalVorticityCoefficientInfiniteFixedOutputNonlinearRow
open ThreeDimensionalVorticityCoefficientGeneratedPathStrongSpaceTimeCompactness
open ThreeDimensionalVorticityCoefficientWholeContinuousMildSerrinUniqueness
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartSourcePairOccurrence
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartPairOccurrenceWork
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion.GeneratedWholeRestartCurrent
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartPairDuhamelOccurrence
open
  ThreeDimensionalVorticityCoefficientFiniteKineticDifferenceCancellation

noncomputable section

/-! ## Physical curl as the exact integral compiler -/

/-- The Fourier curl at one physical wave, with its exact complex-linear
structure exposed. -/
def fourierCurlCoefficientLinearMap
    (wave : IntegerWavevector) :
    ComplexCoordinateVector →ₗ[ℂ] ComplexCoordinateVector where
  toFun := fourierCurlCoefficient wave
  map_add' left right := by
    ext coordinate
    fin_cases coordinate <;>
      simp [fourierCurlCoefficient, cross_apply] <;> ring
  map_smul' scalar value := by
    ext coordinate
    fin_cases coordinate <;>
      simp [fourierCurlCoefficient, cross_apply] <;> ring

/-- The same physical curl as a continuous linear map on the finite
coordinate carrier. -/
def fourierCurlCoefficientContinuousLinearMap
    (wave : IntegerWavevector) :
    ComplexCoordinateVector →L[ℂ] ComplexCoordinateVector :=
  LinearMap.toContinuousLinearMap
    (fourierCurlCoefficientLinearMap wave)

@[simp] theorem fourierCurlCoefficientContinuousLinearMap_apply
    (wave : IntegerWavevector)
    (value : ComplexCoordinateVector) :
    fourierCurlCoefficientContinuousLinearMap wave value =
      fourierCurlCoefficient wave value := by
  rfl

/-- Physical curl commutes with every integrable Bochner row. -/
theorem fourierCurlCoefficient_integral
    {α : Type*}
    [MeasurableSpace α]
    (μ : Measure α)
    (wave : IntegerWavevector)
    (row : α → ComplexCoordinateVector)
    (rowIntegrable : Integrable row μ) :
    fourierCurlCoefficient wave (∫ point, row point ∂μ) =
      ∫ point, fourierCurlCoefficient wave (row point) ∂μ := by
  symm
  exact
    (fourierCurlCoefficientContinuousLinearMap wave).integral_comp_comm
      rowIntegrable

/-! ## Same-receipt velocity occurrences -/

/-- One ordered velocity-convection occurrence on the receipt's actual
continuous whole path.  Its output is generated as `first + second`. -/
def actualWholeContinuousVelocityPairVector
    {ν : Viscosity}
    {initialState : ComplexVorticityHilbertState}
    {requestedTime : ℝ}
    (receipt :
      WholeContinuousMildSerrinReceipt ν initialState requestedTime)
    (first second : IntegerWavevector)
    (time : Icc (0 : ℝ) requestedTime) :
    ComplexCoordinateVector :=
  finiteStateVelocityBilinearPairContribution
    (receipt.wholePath time) (receipt.wholePath time) (first, second)

theorem actualWholeContinuousVelocityPairVector_continuous
    {ν : Viscosity}
    {initialState : ComplexVorticityHilbertState}
    {requestedTime : ℝ}
    (receipt :
      WholeContinuousMildSerrinReceipt ν initialState requestedTime)
    (first second : IntegerWavevector) :
    Continuous fun time : Icc (0 : ℝ) requestedTime =>
      actualWholeContinuousVelocityPairVector
        receipt first second time := by
  have velocityFirstContinuous :
      Continuous fun time : Icc (0 : ℝ) requestedTime =>
        finiteStateVelocityCoefficient
          (receipt.wholePath time) first :=
    (finiteStateVelocityCoefficient_contDiff first).continuous.comp
      receipt.wholePath.continuous
  have velocitySecondContinuous :
      Continuous fun time : Icc (0 : ℝ) requestedTime =>
        finiteStateVelocityCoefficient
          (receipt.wholePath time) second :=
    (finiteStateVelocityCoefficient_contDiff second).continuous.comp
      receipt.wholePath.continuous
  have derivativeContinuous :
      Continuous fun time : Icc (0 : ℝ) requestedTime =>
        complexWavevector second ⬝ᵥ
          finiteStateVelocityCoefficient
            (receipt.wholePath time) first :=
    continuous_const.dotProduct velocityFirstContinuous
  unfold actualWholeContinuousVelocityPairVector
    finiteStateVelocityBilinearPairContribution
  exact
    (continuous_const.mul derivativeContinuous).neg.smul
      velocitySecondContinuous

/-- Before time integration, the physical curl of the two ordered velocity
occurrences is exactly the two existing vorticity pair occurrences. -/
theorem
    actualWholeContinuousVelocityPair_add_swap_curl_eq_pairVector
    {ν : Viscosity}
    {initialState : ComplexVorticityHilbertState}
    {requestedTime : ℝ}
    (receipt :
      WholeContinuousMildSerrinReceipt ν initialState requestedTime)
    (first second : IntegerWavevector)
    (time : Icc (0 : ℝ) requestedTime) :
    fourierCurlCoefficient (first + second)
        (actualWholeContinuousVelocityPairVector
            receipt first second time +
          actualWholeContinuousVelocityPairVector
            receipt second first time) =
      actualWholeContinuousPairVector
          receipt (first + second) first time +
        actualWholeContinuousPairVector
          receipt (first + second) second time := by
  unfold actualWholeContinuousVelocityPairVector
  rw [fourierCurlCoefficient_velocityBilinearPair_add_swap_of_zero
    (receipt.wholePath time) (receipt.wholePath time)
    (receipt.wholePath_zero_row time) (receipt.wholePath_zero_row time)
    (wholePath_transverse receipt time) (wholePath_transverse receipt time)
    first second]
  simp only [bilinearPair_self_eq_nonlinearPair]
  unfold actualWholeContinuousPairVector
  congr 1 <;> congr 1 <;> ext coordinate <;> simp

/-! ## Causal compiler before pair aggregation -/

/-- The two ordered velocity occurrences integrated under the actual heat
kernel at their generated output. -/
def actualWholeSymmetricVelocityPairDuhamelOccurrence
    {ν : Viscosity}
    {initialState : ComplexVorticityHilbertState}
    {requestedTime : ℝ}
    (receipt :
      WholeContinuousMildSerrinReceipt ν initialState requestedTime)
    (first second : IntegerWavevector)
    (endpoint : Icc (0 : ℝ) requestedTime) :
    ComplexCoordinateVector :=
  ∫ earlier in Iic endpoint,
    finiteStateVorticityHeatMultiplier
        ν.coeff (endpoint.1 - earlier.1) (first + second) •
      (actualWholeContinuousVelocityPairVector
          receipt first second earlier +
        actualWholeContinuousVelocityPairVector
          receipt second first earlier)
    ∂(commonTimeMeasure requestedTime)

/-- The causal velocity occurrence and the existing pair-Duhamel carrier are
the same actual event through the physical curl. -/
theorem
    actualWholeSymmetricVelocityPairDuhamelOccurrence_curl_eq_pairDuhamel
    {ν : Viscosity}
    {initialState : ComplexVorticityHilbertState}
    {requestedTime : ℝ}
    (receipt :
      WholeContinuousMildSerrinReceipt ν initialState requestedTime)
    (first second : IntegerWavevector)
    (endpoint : Icc (0 : ℝ) requestedTime) :
    fourierCurlCoefficient (first + second)
        (actualWholeSymmetricVelocityPairDuhamelOccurrence
          receipt first second endpoint) =
      actualWholePairDuhamelOccurrence
          receipt (first + second) first endpoint +
        actualWholePairDuhamelOccurrence
          receipt (first + second) second endpoint := by
  let μ :=
    (commonTimeMeasure requestedTime).restrict (Iic endpoint)
  let heat : Icc (0 : ℝ) requestedTime → ℂ := fun earlier =>
    (finiteStateVorticityHeatMultiplier
      ν.coeff (endpoint.1 - earlier.1) (first + second) : ℂ)
  let velocityPair :
      Icc (0 : ℝ) requestedTime → ComplexCoordinateVector :=
    fun earlier =>
      actualWholeContinuousVelocityPairVector
          receipt first second earlier +
        actualWholeContinuousVelocityPairVector
          receipt second first earlier
  have heatContinuous : Continuous heat := by
    unfold heat finiteStateVorticityHeatMultiplier
    fun_prop
  have velocityPairContinuous : Continuous velocityPair := by
    exact
      (actualWholeContinuousVelocityPairVector_continuous
        receipt first second).add
      (actualWholeContinuousVelocityPairVector_continuous
        receipt second first)
  have velocityIntegrable :
      Integrable (fun earlier => heat earlier • velocityPair earlier) μ := by
    exact
      ((heatContinuous.smul velocityPairContinuous)
        |>.integrable_of_hasCompactSupport
          (HasCompactSupport.of_compactSpace _)).integrableOn
  have firstIntegrable :
      Integrable
        (fun earlier =>
          actualWholeCausalPairVector
            receipt (first + second) first endpoint earlier) μ := by
    exact
      ((actualWholeCausalPairVector_continuous
          receipt (first + second) first endpoint)
        |>.integrable_of_hasCompactSupport
          (HasCompactSupport.of_compactSpace _)).integrableOn
  have secondIntegrable :
      Integrable
        (fun earlier =>
          actualWholeCausalPairVector
            receipt (first + second) second endpoint earlier) μ := by
    exact
      ((actualWholeCausalPairVector_continuous
          receipt (first + second) second endpoint)
        |>.integrable_of_hasCompactSupport
          (HasCompactSupport.of_compactSpace _)).integrableOn
  unfold actualWholeSymmetricVelocityPairDuhamelOccurrence
    actualWholePairDuhamelOccurrence
  change
    fourierCurlCoefficient (first + second)
        (∫ earlier, heat earlier • velocityPair earlier ∂μ) =
      (∫ earlier,
        actualWholeCausalPairVector
          receipt (first + second) first endpoint earlier ∂μ) +
      ∫ earlier,
        actualWholeCausalPairVector
          receipt (first + second) second endpoint earlier ∂μ
  rw [fourierCurlCoefficient_integral μ (first + second)
    (fun earlier => heat earlier • velocityPair earlier)
    velocityIntegrable]
  rw [← integral_add firstIntegrable secondIntegrable]
  apply integral_congr_ae
  filter_upwards with earlier
  change
    fourierCurlCoefficient (first + second)
        (heat earlier • velocityPair earlier) =
      actualWholeCausalPairVector
          receipt (first + second) first endpoint earlier +
        actualWholeCausalPairVector
          receipt (first + second) second endpoint earlier
  rw [← fourierCurlCoefficientContinuousLinearMap_apply,
    map_smul, fourierCurlCoefficientContinuousLinearMap_apply,
    actualWholeContinuousVelocityPair_add_swap_curl_eq_pairVector
      receipt first second earlier]
  unfold actualWholeCausalPairVector heat
  simp only [smul_add]
  ext coordinate
  simp

/-! ## Native reflected triad relation under the causal heat kernel -/

/-- Real kinetic work of one ordered velocity occurrence, before output or
pair aggregation.  All three slots are read from the same actual whole path
at the same physical time. -/
def actualWholeVelocityBilinearEnergyOccurrence
    {ν : Viscosity}
    {initialState : ComplexVorticityHilbertState}
    {requestedTime : ℝ}
    (receipt :
      WholeContinuousMildSerrinReceipt ν initialState requestedTime)
    (first second : IntegerWavevector)
    (time : Icc (0 : ℝ) requestedTime) : ℝ :=
  finiteStateVelocityBilinearEnergyOccurrence
    (receipt.wholePath time)
    (receipt.wholePath time)
    (receipt.wholePath time)
    first second

theorem actualWholeVelocityBilinearEnergyOccurrence_continuous
    {ν : Viscosity}
    {initialState : ComplexVorticityHilbertState}
    {requestedTime : ℝ}
    (receipt :
      WholeContinuousMildSerrinReceipt ν initialState requestedTime)
    (first second : IntegerWavevector) :
    Continuous
      (actualWholeVelocityBilinearEnergyOccurrence
        receipt first second) := by
  have testContinuous :
      Continuous fun time : Icc (0 : ℝ) requestedTime =>
        finiteStateVelocityCoefficient
          (receipt.wholePath time) (first + second) :=
    (finiteStateVelocityCoefficient_contDiff
      (first + second)).continuous.comp receipt.wholePath.continuous
  have occurrenceContinuous :=
    actualWholeContinuousVelocityPairVector_continuous
      receipt first second
  unfold actualWholeContinuousVelocityPairVector at occurrenceContinuous
  unfold actualWholeVelocityBilinearEnergyOccurrence
    finiteStateVelocityBilinearEnergyOccurrence
  exact
    complexCoordinateRealInner_prod_continuous.comp
      (testContinuous.prodMk occurrenceContinuous)

/-- Fourier reality of the actual continuous whole path is inherited almost
everywhere from its receipt-owned transverse representative. -/
theorem wholePath_fourierReality_ae
    {ν : Viscosity}
    {initialState : ComplexVorticityHilbertState}
    {requestedTime : ℝ}
    (receipt :
      WholeContinuousMildSerrinReceipt ν initialState requestedTime) :
    ∀ᵐ time ∂(commonTimeMeasure requestedTime),
      FiniteStateFourierReality (receipt.wholePath time) := by
  filter_upwards [receipt.wholePath_eq_transverse_ae,
    receipt.transverse_fourierReality_ae] with time pathEq reality
  simpa only [pathEq] using reality

/-- The source-free three-slot involution acts on the actual receipt before
any fixed-output quotient.  The reflected second input is generated by the
same first input and swaps the testing/transported roles; because all three
roles belong to the same actual state, its occurrence is the exact negative. -/
theorem actualWholeVelocityBilinearEnergyOccurrence_reflect_ae
    {ν : Viscosity}
    {initialState : ComplexVorticityHilbertState}
    {requestedTime : ℝ}
    (receipt :
      WholeContinuousMildSerrinReceipt ν initialState requestedTime)
    (first second : IntegerWavevector) :
    ∀ᵐ time ∂(commonTimeMeasure requestedTime),
      actualWholeVelocityBilinearEnergyOccurrence
          receipt first (outputNegSecondEquiv first second) time =
        -actualWholeVelocityBilinearEnergyOccurrence
          receipt first second time := by
  filter_upwards [wholePath_fourierReality_ae receipt] with time reality
  exact
    finiteStateVelocityBilinearEnergyOccurrence_reflect_swap
      (receipt.wholePath time)
      (receipt.wholePath time)
      (receipt.wholePath time)
      reality reality first second

/-- One ordered kinetic occurrence under the actual causal heat multiplier
of its generated output wave. -/
def actualWholeCausalVelocityBilinearEnergyOccurrence
    {ν : Viscosity}
    {initialState : ComplexVorticityHilbertState}
    {requestedTime : ℝ}
    (receipt :
      WholeContinuousMildSerrinReceipt ν initialState requestedTime)
    (first second : IntegerWavevector)
    (endpoint earlier : Icc (0 : ℝ) requestedTime) : ℝ :=
  finiteStateVorticityHeatMultiplier
      ν.coeff (endpoint.1 - earlier.1) (first + second) *
    actualWholeVelocityBilinearEnergyOccurrence
      receipt first second earlier

theorem actualWholeCausalVelocityBilinearEnergyOccurrence_continuous
    {ν : Viscosity}
    {initialState : ComplexVorticityHilbertState}
    {requestedTime : ℝ}
    (receipt :
      WholeContinuousMildSerrinReceipt ν initialState requestedTime)
    (first second : IntegerWavevector)
    (endpoint : Icc (0 : ℝ) requestedTime) :
    Continuous fun earlier : Icc (0 : ℝ) requestedTime =>
      actualWholeCausalVelocityBilinearEnergyOccurrence
        receipt first second endpoint earlier := by
  have heatContinuous :
      Continuous fun earlier : Icc (0 : ℝ) requestedTime =>
        finiteStateVorticityHeatMultiplier
          ν.coeff (endpoint.1 - earlier.1) (first + second) := by
    unfold finiteStateVorticityHeatMultiplier
    fun_prop
  exact heatContinuous.mul
    (actualWholeVelocityBilinearEnergyOccurrence_continuous
      receipt first second)

/-- Causal kinetic work of one ordered occurrence while its complete triad
incidence is still present. -/
def actualWholeVelocityBilinearEnergyDuhamelWork
    {ν : Viscosity}
    {initialState : ComplexVorticityHilbertState}
    {requestedTime : ℝ}
    (receipt :
      WholeContinuousMildSerrinReceipt ν initialState requestedTime)
    (first second : IntegerWavevector)
    (endpoint : Icc (0 : ℝ) requestedTime) : ℝ :=
  ∫ earlier in Iic endpoint,
    actualWholeCausalVelocityBilinearEnergyOccurrence
      receipt first second endpoint earlier
    ∂(commonTimeMeasure requestedTime)

/-- The exact trace left when the reflected native relation is transported
through output-dependent viscous heat.  It is forced by the difference of
the two actual output multipliers; no scalar debt is chosen by a caller. -/
def actualWholeVelocityTriadHeatCommutatorTrace
    {ν : Viscosity}
    {initialState : ComplexVorticityHilbertState}
    {requestedTime : ℝ}
    (receipt :
      WholeContinuousMildSerrinReceipt ν initialState requestedTime)
    (first second : IntegerWavevector)
    (endpoint : Icc (0 : ℝ) requestedTime) : ℝ :=
  ∫ earlier in Iic endpoint,
    (finiteStateVorticityHeatMultiplier
          ν.coeff (endpoint.1 - earlier.1) (first + second) -
        finiteStateVorticityHeatMultiplier
          ν.coeff (endpoint.1 - earlier.1)
            (first + outputNegSecondEquiv first second)) *
      actualWholeVelocityBilinearEnergyOccurrence
        receipt first second earlier
    ∂(commonTimeMeasure requestedTime)

/-- Transporting the native reflected triad relation through the actual
causal heat kernel yields exactly the generated heat commutator trace.

When the two output multipliers happen to agree the relation closes; in
general the mismatch is retained on this same occurrence carrier instead of
being erased by output aggregation. -/
theorem
    actualWholeVelocityBilinearEnergyDuhamelWork_add_reflect_eq_heatCommutator
    {ν : Viscosity}
    {initialState : ComplexVorticityHilbertState}
    {requestedTime : ℝ}
    (receipt :
      WholeContinuousMildSerrinReceipt ν initialState requestedTime)
    (first second : IntegerWavevector)
    (endpoint : Icc (0 : ℝ) requestedTime) :
    actualWholeVelocityBilinearEnergyDuhamelWork
        receipt first second endpoint +
      actualWholeVelocityBilinearEnergyDuhamelWork
        receipt first (outputNegSecondEquiv first second) endpoint =
      actualWholeVelocityTriadHeatCommutatorTrace
        receipt first second endpoint := by
  let μ :=
    (commonTimeMeasure requestedTime).restrict (Iic endpoint)
  let direct := fun earlier : Icc (0 : ℝ) requestedTime =>
    actualWholeCausalVelocityBilinearEnergyOccurrence
      receipt first second endpoint earlier
  let reflected := fun earlier : Icc (0 : ℝ) requestedTime =>
    actualWholeCausalVelocityBilinearEnergyOccurrence
      receipt first (outputNegSecondEquiv first second) endpoint earlier
  have directIntegrable : Integrable direct μ := by
    exact
      ((actualWholeCausalVelocityBilinearEnergyOccurrence_continuous
          receipt first second endpoint)
        |>.integrable_of_hasCompactSupport
          (HasCompactSupport.of_compactSpace _)).integrableOn
  have reflectedIntegrable : Integrable reflected μ := by
    exact
      ((actualWholeCausalVelocityBilinearEnergyOccurrence_continuous
          receipt first (outputNegSecondEquiv first second) endpoint)
        |>.integrable_of_hasCompactSupport
          (HasCompactSupport.of_compactSpace _)).integrableOn
  unfold actualWholeVelocityBilinearEnergyDuhamelWork
    actualWholeVelocityTriadHeatCommutatorTrace
  change (∫ earlier, direct earlier ∂μ) +
      (∫ earlier, reflected earlier ∂μ) = _
  rw [← integral_add directIntegrable reflectedIntegrable]
  apply integral_congr_ae
  have reflectedAE :=
    (actualWholeVelocityBilinearEnergyOccurrence_reflect_ae
      receipt first second).filter_mono
        (ae_restrict_le (s := Iic endpoint))
  filter_upwards [reflectedAE] with earlier reflectedEq
  unfold direct reflected
    actualWholeCausalVelocityBilinearEnergyOccurrence
  rw [reflectedEq]
  ring

/-! ## Source-owned whole-restart specialization -/

/-- The symmetric velocity occurrence carried by one actual whole-restart
receipt at its source-generated contact time. -/
def wholeRestartSymmetricVelocityPairDuhamelOccurrence
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (index : ℕ)
    (first second : IntegerWavevector) : ComplexCoordinateVector :=
  actualWholeSymmetricVelocityPairDuhamelOccurrence
    (run initial index).nextContact.prefixReceipt
    first second
    ⟨(run initial index).nextContact.time.1,
      ⟨(run initial index).nextContact.time_pos.le, le_rfl⟩⟩

/-- On every actual restart edge, the physical curl compiler lands in the
existing pair-Duhamel table before its input-pair quotient. -/
theorem wholeRestartSymmetricVelocityPairDuhamelOccurrence_curl_eq
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (index : ℕ)
    (first second : IntegerWavevector) :
    fourierCurlCoefficient (first + second)
        (wholeRestartSymmetricVelocityPairDuhamelOccurrence
          initial index first second) =
      wholeRestartPairDuhamelOccurrence
          initial index (first + second) first +
        wholeRestartPairDuhamelOccurrence
          initial index (first + second) second := by
  exact
    actualWholeSymmetricVelocityPairDuhamelOccurrence_curl_eq_pairDuhamel
      (run initial index).nextContact.prefixReceipt
      first second
      ⟨(run initial index).nextContact.time.1,
        ⟨(run initial index).nextContact.time_pos.le, le_rfl⟩⟩

/-- Input-pair form aligned with the current `output × first` carrier.  The
second input and its swapped companion are generated by the actual incidence
equation `first + second = output`; no companion is supplied separately. -/
theorem wholeRestartPairDuhamelOccurrence_add_swap_eq_velocityPair_curl
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (index : ℕ)
    (output first : IntegerWavevector) :
    wholeRestartPairDuhamelOccurrence initial index output first +
        wholeRestartPairDuhamelOccurrence
          initial index output (output - first) =
      fourierCurlCoefficient output
        (wholeRestartSymmetricVelocityPairDuhamelOccurrence
          initial index first (output - first)) := by
  symm
  simpa using
    wholeRestartSymmetricVelocityPairDuhamelOccurrence_curl_eq
      initial index first (output - first)

/-- The reflected heat-commutator trace generated by the same actual restart
receipt and its source-owned contact time. -/
def wholeRestartVelocityTriadHeatCommutatorTrace
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (index : ℕ)
    (first second : IntegerWavevector) : ℝ :=
  actualWholeVelocityTriadHeatCommutatorTrace
    (run initial index).nextContact.prefixReceipt
    first second
    ⟨(run initial index).nextContact.time.1,
      ⟨(run initial index).nextContact.time_pos.le, le_rfl⟩⟩

/-- The actual restart's reflected source relation closes only up to its
source-generated causal commutator trace. -/
theorem wholeRestartVelocityBilinearEnergyWork_add_reflect_eq_heatCommutator
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (index : ℕ)
    (first second : IntegerWavevector) :
    actualWholeVelocityBilinearEnergyDuhamelWork
        (run initial index).nextContact.prefixReceipt
        first second
        ⟨(run initial index).nextContact.time.1,
          ⟨(run initial index).nextContact.time_pos.le, le_rfl⟩⟩ +
      actualWholeVelocityBilinearEnergyDuhamelWork
        (run initial index).nextContact.prefixReceipt
        first (outputNegSecondEquiv first second)
        ⟨(run initial index).nextContact.time.1,
          ⟨(run initial index).nextContact.time_pos.le, le_rfl⟩⟩ =
      wholeRestartVelocityTriadHeatCommutatorTrace
        initial index first second := by
  exact
    actualWholeVelocityBilinearEnergyDuhamelWork_add_reflect_eq_heatCommutator
      (run initial index).nextContact.prefixReceipt
      first second
      ⟨(run initial index).nextContact.time.1,
        ⟨(run initial index).nextContact.time_pos.le, le_rfl⟩⟩

end
end ThreeDimensionalVorticityCoefficientGeneratedWholeRestartPairDuhamelKineticTriadRedirect
end NavierStokes
end SaturationMonoid
