import H0mework.Versions.X.NavierStokes.PhysicalJets.CorrectionPhysical
import H0mework.Versions.X.NavierStokes.CorrectionControl.Consumer

set_option autoImplicit false
open scoped BigOperators ENNReal Topology

namespace SaturationMonoid.NavierStokes.NativeFixedFilterGlobalControl

open Set Filter MeasureTheory
open ThreeDimensionalPeriodicCoarseFilterCore
open ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientStretchingPairTable
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open ThreeDimensionalVorticityCoefficientGeneratedShellSerrinGeometry
open ThreeDimensionalVorticityCoefficientFixedOutputNonlinearContinuity
open ThreeDimensionalVorticityCoefficientInfiniteFixedOutputNonlinearRow
open ThreeDimensionalVorticityCoefficientWholeContinuousMildSerrinUniqueness
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartSourcePairOccurrence
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion.GeneratedWholeRestartCurrent
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityWeakEndpoint
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeAccumulationBoundaryDisposition
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeAccumulationNativeTurbulenceLaw
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointRecursiveMacroRuntime
open NativeFullOrderAction NativeFullOrderSynthesis NativeCorrectionPhysical NativeTurbulenceControl

noncomputable section

def outputInventory (modes : Finset IntegerWavevector) : Finset IntegerWavevector :=
  modes ∪ (modes.product modes).image (fun pair => pair.1 + pair.2)

theorem correction_supported (modes : Finset IntegerWavevector) (state : ComplexVorticityHilbertState)
    (wave : IntegerWavevector) (outside : wave ∉ outputInventory modes) :
    nativeTurbulenceCorrectionAt modes state wave = 0 := by
  have outsideFirst : wave ∉ modes := fun inside => outside (Finset.mem_union_left _ inside)
  rw [nativeTurbulenceCorrectionAt, projectedWholeNonlinearCoefficientAt, if_neg outsideFirst,
    wholeStateVorticityNonlinearCoefficientAt_projection_eq_finite]
  unfold finiteStateVorticityNonlinearCoefficientAt
  have allZero : (∑ first ∈ modes, ∑ second ∈ modes,
      if first + second = wave then finiteStateVorticityNonlinearPairContribution state (first, second) else 0) = 0 := by
    apply Finset.sum_eq_zero
    intro first firstIn
    apply Finset.sum_eq_zero
    intro second secondIn
    have notOutput : first + second ≠ wave := by
      intro same
      apply outside
      apply Finset.mem_union_right
      exact Finset.mem_image.mpr ⟨(first, second), Finset.mem_product.mpr ⟨firstIn, secondIn⟩, same⟩
    rw [if_neg notOutput]
  rw [allZero, sub_self]

theorem correctionState_supported (modes : Finset IntegerWavevector) (state : ComplexVorticityHilbertState)
    (zero : state 0 = 0) (wave : IntegerWavevector) (outside : wave ∉ outputInventory modes) :
    correctionState modes state wave = 0 := by
  rw [correctionState_apply modes state zero, correction_supported modes state wave outside]

theorem amplitude_le_three_norm (state : ComplexVorticityHilbertState) (wave : IntegerWavevector) :
    amplitude state wave ≤ 3 * ‖state wave‖ := by
  change vorticityRowAmplitude state wave ≤ _
  have square := complexCoordinateAmplitudeSq_le_three_mul_norm_sq (state wave)
  rw [complexCoordinateAmplitudeSq_eq_complexCoordinateVectorNormSq] at square
  nlinarith [vorticityRowAmplitude_sq state wave, vorticityRowAmplitude_nonneg state wave, norm_nonneg (state wave)]

theorem correction_moments (modes : Finset IntegerWavevector) (state : ComplexVorticityHilbertState)
    (zero : state 0 = 0) (order : ℕ) :
    Summable fun wave => frequencySize wave ^ order * amplitude (correctionState modes state) wave := by
  apply summable_of_ne_finset_zero (s := outputInventory modes)
  intro wave outside
  change frequencySize wave ^ order * Real.sqrt (complexCoordinateVectorNormSq (correctionState modes state wave)) = 0
  rw [correctionState_supported modes state zero wave outside]
  simp [complexCoordinateVectorNormSq]

def spatialBudget (modes : Finset IntegerWavevector) (radius : ℝ) (order : ℕ) : ℝ :=
  (2 * Real.pi) ^ order * ∑ wave ∈ outputInventory modes,
    frequencySize wave ^ order * (6 * curlWeight wave ^ 2 * radius ^ 2)

theorem spatial_control (modes : Finset IntegerWavevector) (state : ComplexVorticityHilbertState)
    (zero : state 0 = 0) (radius : ℝ)
    (bounded : ∀ wave, ‖nativeTurbulenceCorrectionAt modes state wave‖ ≤ 2 * curlWeight wave ^ 2 * radius ^ 2) :
    ContDiff ℝ (↑(⊤ : ℕ∞)) (nativeTurbulenceCorrectionField modes state) ∧
      ∀ order point, ‖iteratedFDeriv ℝ order (nativeTurbulenceCorrectionField modes state) point‖ ≤
        spatialBudget modes radius order := by
  rw [← correctionState_physical_eq_original]
  refine ⟨spatialField_smooth _ (correction_moments modes state zero), ?_⟩
  intro order point
  apply (spatialField_iterated_bound _ (correction_moments modes state zero) order point).trans
  apply mul_le_mul_of_nonneg_left _ (by positivity : 0 ≤ (2 * Real.pi) ^ order)
  rw [tsum_eq_sum (s := outputInventory modes)]
  · apply Finset.sum_le_sum
    intro wave _
    apply mul_le_mul_of_nonneg_left _ (pow_nonneg (frequencySize_nonneg wave) _)
    have coefficient := amplitude_le_three_norm (correctionState modes state) wave
    rw [correctionState_apply modes state zero] at coefficient
    nlinarith [bounded wave]
  · intro wave outside
    change frequencySize wave ^ order * Real.sqrt (complexCoordinateVectorNormSq (correctionState modes state wave)) = 0
    rw [correctionState_supported modes state zero wave outside]
    simp [complexCoordinateVectorNormSq]

theorem spatial_Lp (modes : Finset IntegerWavevector) (state : ComplexVorticityHilbertState)
    (zero : state 0 = 0) (radius : ℝ)
    (bounded : ∀ wave, ‖nativeTurbulenceCorrectionAt modes state wave‖ ≤ 2 * curlWeight wave ^ 2 * radius ^ 2)
    (order : ℕ) (exponent : ℝ≥0∞) {domain : Set PhysicalSpace} (compact : IsCompact domain) :
    MemLp (iteratedFDeriv ℝ order (nativeTurbulenceCorrectionField modes state)) exponent (volume.restrict domain) ∧
      eLpNorm (iteratedFDeriv ℝ order (nativeTurbulenceCorrectionField modes state)) exponent (volume.restrict domain) ≤
        ENNReal.ofReal (spatialBudget modes radius order) * volume domain ^ (1 / exponent.toReal) := by
  let : IsFiniteMeasure (volume.restrict domain) := ⟨by simpa using compact.measure_lt_top (μ := volume)⟩
  have source := spatial_control modes state zero radius bounded
  have continuous := ContDiff.continuous_iteratedFDeriv (WithTop.coe_le_coe.mpr le_top) source.1 (m := order)
  have aeBound : ∀ᵐ point ∂volume.restrict domain,
      ‖iteratedFDeriv ℝ order (nativeTurbulenceCorrectionField modes state) point‖ ≤ spatialBudget modes radius order :=
    Eventually.of_forall (source.2 order)
  exact ⟨MemLp.of_bound continuous.aestronglyMeasurable _ aeBound,
    by simpa [mul_comm] using eLpNorm_le_of_ae_bound (p := exponent) aeBound⟩

def finiteBudget (inventory : Finset IntegerWavevector) (cap : IntegerWavevector → ℝ) (order : ℕ) : ℝ :=
  (2 * Real.pi) ^ order * ∑ wave ∈ inventory, frequencySize wave ^ order * (3 * cap wave)

theorem finite_field_control (inventory : Finset IntegerWavevector) (rows : IntegerWavevector → ComplexCoordinateVector)
    (cap : IntegerWavevector → ℝ) (bounded : ∀ wave, ‖rows wave‖ ≤ cap wave) :
    ContDiff ℝ (↑(⊤ : ℕ∞)) (spatialField (finiteComplexVorticityState inventory rows)) ∧
      ∀ order point, ‖iteratedFDeriv ℝ order (spatialField (finiteComplexVorticityState inventory rows)) point‖ ≤
        finiteBudget inventory cap order := by
  have paid order : Summable fun wave => frequencySize wave ^ order * amplitude (finiteComplexVorticityState inventory rows) wave := by
    apply summable_of_ne_finset_zero (s := inventory)
    intro wave outside
    simp [amplitude, vorticityRowAmplitude, finiteComplexVorticityState_apply, outside, complexCoordinateVectorNormSq]
  refine ⟨spatialField_smooth _ paid, ?_⟩
  intro order point
  apply (spatialField_iterated_bound _ paid order point).trans
  apply mul_le_mul_of_nonneg_left _ (by positivity : 0 ≤ (2 * Real.pi) ^ order)
  rw [tsum_eq_sum (s := inventory)]
  · apply Finset.sum_le_sum
    intro wave inside
    apply mul_le_mul_of_nonneg_left _ (pow_nonneg (frequencySize_nonneg wave) _)
    have row := amplitude_le_three_norm (finiteComplexVorticityState inventory rows) wave
    rw [finiteComplexVorticityState_apply, if_pos inside] at row
    exact row.trans (mul_le_mul_of_nonneg_left (bounded wave) (by norm_num))
  · intro wave outside
    simp [amplitude, vorticityRowAmplitude, finiteComplexVorticityState_apply, outside, complexCoordinateVectorNormSq]

theorem finite_field_Lp (inventory : Finset IntegerWavevector) (rows : IntegerWavevector → ComplexCoordinateVector)
    (cap : IntegerWavevector → ℝ) (bounded : ∀ wave, ‖rows wave‖ ≤ cap wave)
    (order : ℕ) (exponent : ℝ≥0∞) {domain : Set PhysicalSpace} (compact : IsCompact domain) :
    MemLp (iteratedFDeriv ℝ order (spatialField (finiteComplexVorticityState inventory rows))) exponent (volume.restrict domain) ∧
      eLpNorm (iteratedFDeriv ℝ order (spatialField (finiteComplexVorticityState inventory rows))) exponent (volume.restrict domain) ≤
        ENNReal.ofReal (finiteBudget inventory cap order) * volume domain ^ (1 / exponent.toReal) := by
  let : IsFiniteMeasure (volume.restrict domain) := ⟨by simpa using compact.measure_lt_top (μ := volume)⟩
  have source := finite_field_control inventory rows cap bounded
  have continuous := ContDiff.continuous_iteratedFDeriv (WithTop.coe_le_coe.mpr le_top) source.1 (m := order)
  have aeBound : ∀ᵐ point ∂volume.restrict domain,
      ‖iteratedFDeriv ℝ order (spatialField (finiteComplexVorticityState inventory rows)) point‖ ≤ finiteBudget inventory cap order :=
    Eventually.of_forall (source.2 order)
  exact ⟨MemLp.of_bound continuous.aestronglyMeasurable _ aeBound,
    by simpa [mul_comm] using eLpNorm_le_of_ae_bound (p := exponent) aeBound⟩

theorem original_spatial_control {nu : Viscosity} (initial : GeneratedWholeRestartCurrent nu)
    (index : ℕ) (modes : Finset IntegerWavevector)
    (time : Icc (0 : ℝ) (run initial index).nextContact.time.1) :
    ContDiff ℝ (↑(⊤ : ℕ∞))
      (nativeTurbulenceCorrectionField modes ((run initial index).nextContact.prefixReceipt.wholePath time)) ∧
      ∀ order point, ‖iteratedFDeriv ℝ order
        (nativeTurbulenceCorrectionField modes ((run initial index).nextContact.prefixReceipt.wholePath time)) point‖ ≤
          spatialBudget modes ‖puncturedWholeVelocityEuclideanState initial.initialState‖ order :=
  spatial_control modes _ ((run initial index).nextContact.prefixReceipt.wholePath_zero_row time) _
    (fun wave => original_correction_norm_le initial index modes wave time)

theorem recovery_spatial_control {nu : Viscosity} {initial : GeneratedWholeRestartCurrent nu}
    {inquiry : SourceGeneratedBoundaryRevisedInquiryAt initial} (law : SourceGeneratedNativeTurbulenceLawAt initial inquiry)
    (modes : Finset IntegerWavevector) (time : Icc (0 : ℝ) law.recovery.next.duration) :
    ContDiff ℝ (↑(⊤ : ℕ∞)) (nativeTurbulenceCorrectionField modes (law.recovery.next.receipt.wholePath time)) ∧
      ∀ order point, ‖iteratedFDeriv ℝ order (nativeTurbulenceCorrectionField modes (law.recovery.next.receipt.wholePath time)) point‖ ≤
        spatialBudget modes ‖puncturedWholeVelocityEuclideanState initial.initialState‖ order :=
  spatial_control modes _ (law.recovery.next.receipt.wholePath_zero_row time) _
    (fun wave => recovery_correction_norm_le law modes wave time)

theorem original_spatial_Lp {nu : Viscosity} (initial : GeneratedWholeRestartCurrent nu)
    (index : ℕ) (modes : Finset IntegerWavevector)
    (time : Icc (0 : ℝ) (run initial index).nextContact.time.1)
    (order : ℕ) (exponent : ℝ≥0∞) {domain : Set PhysicalSpace} (compact : IsCompact domain) :
    MemLp (iteratedFDeriv ℝ order (nativeTurbulenceCorrectionField modes ((run initial index).nextContact.prefixReceipt.wholePath time)))
      exponent (volume.restrict domain) ∧
      eLpNorm (iteratedFDeriv ℝ order (nativeTurbulenceCorrectionField modes ((run initial index).nextContact.prefixReceipt.wholePath time)))
        exponent (volume.restrict domain) ≤ ENNReal.ofReal (spatialBudget modes ‖puncturedWholeVelocityEuclideanState initial.initialState‖ order) *
          volume domain ^ (1 / exponent.toReal) :=
  spatial_Lp modes _ ((run initial index).nextContact.prefixReceipt.wholePath_zero_row time) _
    (fun wave => original_correction_norm_le initial index modes wave time) order exponent compact

theorem recovery_spatial_Lp {nu : Viscosity} {initial : GeneratedWholeRestartCurrent nu}
    {inquiry : SourceGeneratedBoundaryRevisedInquiryAt initial} (law : SourceGeneratedNativeTurbulenceLawAt initial inquiry)
    (modes : Finset IntegerWavevector) (time : Icc (0 : ℝ) law.recovery.next.duration)
    (order : ℕ) (exponent : ℝ≥0∞) {domain : Set PhysicalSpace} (compact : IsCompact domain) :
    MemLp (iteratedFDeriv ℝ order (nativeTurbulenceCorrectionField modes (law.recovery.next.receipt.wholePath time))) exponent (volume.restrict domain) ∧
      eLpNorm (iteratedFDeriv ℝ order (nativeTurbulenceCorrectionField modes (law.recovery.next.receipt.wholePath time))) exponent (volume.restrict domain) ≤
        ENNReal.ofReal (spatialBudget modes ‖puncturedWholeVelocityEuclideanState initial.initialState‖ order) * volume domain ^ (1 / exponent.toReal) :=
  spatial_Lp modes _ (law.recovery.next.receipt.wholePath_zero_row time) _
    (fun wave => recovery_correction_norm_le law modes wave time) order exponent compact

theorem macro_spatial_control {nu : Viscosity} (lineage : GeneratedInfiniteWholeRestartEndpointMacroLineage nu)
    (macroIndex micro : ℕ) (modes : Finset IntegerWavevector)
    (time : Icc (0 : ℝ) (run (lineage.current macroIndex) micro).nextContact.time.1) :
    ContDiff ℝ (↑(⊤ : ℕ∞))
      (nativeTurbulenceCorrectionField modes ((run (lineage.current macroIndex) micro).nextContact.prefixReceipt.wholePath time)) ∧
      ∀ order point, ‖iteratedFDeriv ℝ order
        (nativeTurbulenceCorrectionField modes ((run (lineage.current macroIndex) micro).nextContact.prefixReceipt.wholePath time)) point‖ ≤
          spatialBudget modes ‖puncturedWholeVelocityEuclideanState (lineage.current 0).initialState‖ order :=
  spatial_control modes _ ((run (lineage.current macroIndex) micro).nextContact.prefixReceipt.wholePath_zero_row time) _
    (fun wave => macro_correction_norm_le lineage macroIndex micro modes wave time)

theorem macro_spatial_Lp {nu : Viscosity} (lineage : GeneratedInfiniteWholeRestartEndpointMacroLineage nu)
    (macroIndex micro : ℕ) (modes : Finset IntegerWavevector)
    (time : Icc (0 : ℝ) (run (lineage.current macroIndex) micro).nextContact.time.1)
    (order : ℕ) (exponent : ℝ≥0∞) {domain : Set PhysicalSpace} (compact : IsCompact domain) :
    MemLp (iteratedFDeriv ℝ order
      (nativeTurbulenceCorrectionField modes ((run (lineage.current macroIndex) micro).nextContact.prefixReceipt.wholePath time)))
      exponent (volume.restrict domain) ∧
      eLpNorm (iteratedFDeriv ℝ order
        (nativeTurbulenceCorrectionField modes ((run (lineage.current macroIndex) micro).nextContact.prefixReceipt.wholePath time)))
        exponent (volume.restrict domain) ≤ ENNReal.ofReal
          (spatialBudget modes ‖puncturedWholeVelocityEuclideanState (lineage.current 0).initialState‖ order) *
            volume domain ^ (1 / exponent.toReal) :=
  spatial_Lp modes _ ((run (lineage.current macroIndex) micro).nextContact.prefixReceipt.wholePath_zero_row time) _
    (fun wave => macro_correction_norm_le lineage macroIndex micro modes wave time) order exponent compact

end
end SaturationMonoid.NavierStokes.NativeFixedFilterGlobalControl
