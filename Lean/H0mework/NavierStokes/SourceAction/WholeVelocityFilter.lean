import H0mework.NavierStokes.SourceAction.FixedFilterGlobal
import H0mework.NavierStokes.PhysicalReadout.EndpointVelocity
import H0mework.NavierStokes.NormControl.Observations

set_option autoImplicit false
open scoped BigOperators ENNReal Topology

namespace SaturationMonoid.NavierStokes.NativeWholeVelocityFilterControl

open Set Filter MeasureTheory
open ThreeDimensionalPeriodicCoarseFilterCore
open ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open ThreeDimensionalVorticityCoefficientInfiniteFixedOutputNonlinearRow
open ThreeDimensionalVorticityCoefficientWholeVelocityPairDiagonalBudget
open ThreeDimensionalVorticityCoefficientWholeKineticDifferenceCancellation
open ThreeDimensionalVorticityCoefficientNativeFluidMedium
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartPairDuhamelKineticTriadRedirect
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion.GeneratedWholeRestartCurrent
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityWeakEndpoint
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeAccumulationNativeTurbulenceLaw
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointRecursiveMacroRuntime
open NativeStressSource NativeStressCurlAlgebra NativeEndpointVelocityCarrier NativeCorrectionPhysical
open NativeFullOrderSynthesis NativeFixedFilterGlobalControl

noncomputable section

def stress (modes : Finset IntegerWavevector) (velocity : ComplexVorticityHilbertState) : NativeFluidStressFourierState :=
  (fun wave => if wave ∈ modes then quadraticFlux velocity wave else 0) -
    quadraticFlux (complexSharpSupportProjection modes velocity)

def rowAction (wave : IntegerWavevector) : NativeFluidStressCoefficient →L[ℂ] ComplexCoordinateVector :=
  (fourierCurlCoefficientContinuousLinearMap wave).comp (stressDivergenceCLM wave)

def coefficient (modes : Finset IntegerWavevector) (velocity : ComplexVorticityHilbertState) (wave : IntegerWavevector) :
    ComplexCoordinateVector := nativeFluidConstitutiveVorticityAction (stress modes velocity) wave

theorem projected_flux_zero (modes : Finset IntegerWavevector) (velocity : ComplexVorticityHilbertState)
    (wave : IntegerWavevector) (outside : wave ∉ outputInventory modes) :
    quadraticFlux (complexSharpSupportProjection modes velocity) wave = 0 := by
  funext output input
  unfold quadraticFlux
  have allZero (first : IntegerWavevector) :
      complexSharpSupportProjection modes velocity first input *
        complexSharpSupportProjection modes velocity (wave - first) output = 0 := by
    by_cases firstIn : first ∈ modes
    · have secondOut : wave - first ∉ modes := by
        intro secondIn
        apply outside
        apply Finset.mem_union_right
        refine Finset.mem_image.mpr ⟨(first, wave - first), Finset.mem_product.mpr ⟨firstIn, secondIn⟩, ?_⟩
        dsimp only
        abel
      simp [complexSharpSupportProjection_apply, secondOut]
    · simp [complexSharpSupportProjection_apply, firstIn]
  simp only [allZero, tsum_zero, neg_zero, Pi.zero_apply]

theorem coefficient_supported (modes : Finset IntegerWavevector) (velocity : ComplexVorticityHilbertState)
    (wave : IntegerWavevector) (outside : wave ∉ outputInventory modes) : coefficient modes velocity wave = 0 := by
  have outsideFirst : wave ∉ modes := fun inside => outside (Finset.mem_union_left _ inside)
  change rowAction wave (stress modes velocity wave) = 0
  have rowZero : stress modes velocity wave = 0 := by
    simp only [stress, Pi.sub_apply, if_neg outsideFirst, projected_flux_zero modes velocity wave outside, sub_self]
  rw [rowZero, map_zero]

theorem stress_norm_le (modes : Finset IntegerWavevector) (velocity : ComplexVorticityHilbertState) (wave : IntegerWavevector) :
    ‖stress modes velocity wave‖ ≤ 2 * wholeVorticityEuclideanMass velocity := by
  have massNonnegative : 0 ≤ wholeVorticityEuclideanMass velocity := tsum_nonneg fun _ => sq_nonneg _
  have projectionMass : wholeVorticityEuclideanMass (complexSharpSupportProjection modes velocity) ≤
      wholeVorticityEuclideanMass velocity := by
    have split := wholeVorticityEuclideanMass_eq_projection_add_complement modes velocity
    have complementNonnegative : 0 ≤ wholeVorticityEuclideanMass (complexSharpSupportProjection modes velocity - velocity) :=
      tsum_nonneg fun _ => sq_nonneg _
    linarith
  apply (pi_norm_le_iff_of_nonneg (by positivity : 0 ≤ 2 * wholeVorticityEuclideanMass velocity)).mpr
  intro output
  apply (pi_norm_le_iff_of_nonneg (by positivity : 0 ≤ 2 * wholeVorticityEuclideanMass velocity)).mpr
  intro input
  have full : ‖(if wave ∈ modes then quadraticFlux velocity wave else 0) output input‖ ≤ wholeVorticityEuclideanMass velocity := by
    split_ifs
    · exact quadraticFlux_norm_le_mass velocity wave output input
    · simpa only [Pi.zero_apply, norm_zero] using massNonnegative
  have resolved := (quadraticFlux_norm_le_mass (complexSharpSupportProjection modes velocity) wave output input).trans projectionMass
  exact (norm_sub_le _ _).trans ((add_le_add full resolved).trans_eq (by ring))

theorem coefficient_norm_le (modes : Finset IntegerWavevector) (velocity : ComplexVorticityHilbertState) (wave : IntegerWavevector) :
    ‖coefficient modes velocity wave‖ ≤ 2 * ‖rowAction wave‖ * wholeVorticityEuclideanMass velocity := by
  have action := (rowAction wave).le_opNorm (stress modes velocity wave)
  exact action.trans ((mul_le_mul_of_nonneg_left (stress_norm_le modes velocity wave) (norm_nonneg _)).trans_eq (by ring))

def state (modes : Finset IntegerWavevector) (velocity : ComplexVorticityHilbertState) : ComplexVorticityHilbertState :=
  finiteComplexVorticityState (outputInventory modes) (coefficient modes velocity)

theorem state_apply (modes : Finset IntegerWavevector) (velocity : ComplexVorticityHilbertState) (wave : IntegerWavevector) :
    state modes velocity wave = coefficient modes velocity wave := by
  rw [state, finiteComplexVorticityState_apply]
  split_ifs with inside
  · rfl
  · exact (coefficient_supported modes velocity wave inside).symm

theorem coefficient_eq_original (modes : Finset IntegerWavevector) (vorticity : ComplexVorticityHilbertState)
    (zero : vorticity 0 = 0) (transverse : WholeStateTransverse vorticity) (wave : IntegerWavevector) :
    coefficient modes (wholeBiotSavartVelocityState vorticity) wave = nativeTurbulenceCorrectionAt modes vorticity wave := by
  have same : stress modes (wholeBiotSavartVelocityState vorticity) = correctionStress modes vorticity := by
    funext k output input
    simp only [stress, correctionStress, NativeTurbulenceControl.velocity_projection, Pi.sub_apply]
    split_ifs <;> rfl
  rw [coefficient, same, correctionStress_action modes vorticity zero transverse]

theorem state_eq_original (modes : Finset IntegerWavevector) (vorticity : ComplexVorticityHilbertState)
    (zero : vorticity 0 = 0) (transverse : WholeStateTransverse vorticity) :
    state modes (wholeBiotSavartVelocityState vorticity) = correctionState modes vorticity := by
  apply lp.ext
  funext wave
  rw [state_apply, coefficient_eq_original modes vorticity zero transverse, correctionState_apply modes vorticity zero]

def physicalField (modes : Finset IntegerWavevector) (velocity : ComplexVorticityHilbertState) : PhysicalSpace → PhysicalSpace :=
  spatialField (state modes velocity)

theorem physicalField_eq_finite (modes : Finset IntegerWavevector) (velocity : ComplexVorticityHilbertState) :
    physicalField modes velocity =
      ThreeDimensionalVorticityCoefficientPhysicalCompiler.finiteRealComplexFourierField
        (outputInventory modes) (coefficient modes velocity) :=
  spatialField_finite_compiler _ _

theorem physicalField_eq_original (modes : Finset IntegerWavevector) (vorticity : ComplexVorticityHilbertState)
    (zero : vorticity 0 = 0) (transverse : WholeStateTransverse vorticity) :
    physicalField modes (wholeBiotSavartVelocityState vorticity) = nativeTurbulenceCorrectionField modes vorticity := by
  rw [physicalField, state_eq_original modes vorticity zero transverse, correctionState_physical_eq_original]

def globalField {nu : Viscosity} (lineage : GeneratedInfiniteWholeRestartEndpointMacroLineage nu)
    (modes : Finset IntegerWavevector) (actual : ℝ) : PhysicalSpace → PhysicalSpace :=
  physicalField modes (wholeVelocity (lineage.globalAbsoluteVelocityTrajectory actual))

def globalBudget (modes : Finset IntegerWavevector) (radius : ℝ) (order : ℕ) : ℝ :=
  finiteBudget (outputInventory modes) (fun wave => 2 * ‖rowAction wave‖ * radius ^ 2) order

theorem global_coefficient_norm_le {nu : Viscosity} (lineage : GeneratedInfiniteWholeRestartEndpointMacroLineage nu)
    (modes : Finset IntegerWavevector) (actual : ℝ) (wave : IntegerWavevector) :
    ‖coefficient modes (wholeVelocity (lineage.globalAbsoluteVelocityTrajectory actual)) wave‖ ≤
      2 * ‖rowAction wave‖ * ‖puncturedWholeVelocityEuclideanState (lineage.current 0).initialState‖ ^ 2 := by
  have source := coefficient_norm_le modes (wholeVelocity (lineage.globalAbsoluteVelocityTrajectory actual)) wave
  rw [wholeVelocity_mass] at source
  exact source.trans (mul_le_mul_of_nonneg_left
    ((sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr (NativeNormControl.global_velocity_norm_le lineage actual)) (by positivity))

theorem global_spatial_control {nu : Viscosity} (lineage : GeneratedInfiniteWholeRestartEndpointMacroLineage nu)
    (modes : Finset IntegerWavevector) (actual : ℝ) :
    ContDiff ℝ (↑(⊤ : ℕ∞)) (globalField lineage modes actual) ∧
      ∀ order point, ‖iteratedFDeriv ℝ order (globalField lineage modes actual) point‖ ≤
        globalBudget modes ‖puncturedWholeVelocityEuclideanState (lineage.current 0).initialState‖ order :=
  finite_field_control (outputInventory modes) _ _ (global_coefficient_norm_le lineage modes actual)

theorem global_spatial_Lp {nu : Viscosity} (lineage : GeneratedInfiniteWholeRestartEndpointMacroLineage nu)
    (modes : Finset IntegerWavevector) (actual : ℝ) (order : ℕ) (exponent : ℝ≥0∞)
    {domain : Set PhysicalSpace} (compact : IsCompact domain) :
    MemLp (iteratedFDeriv ℝ order (globalField lineage modes actual)) exponent (volume.restrict domain) ∧
      eLpNorm (iteratedFDeriv ℝ order (globalField lineage modes actual)) exponent (volume.restrict domain) ≤
        ENNReal.ofReal (globalBudget modes ‖puncturedWholeVelocityEuclideanState (lineage.current 0).initialState‖ order) *
          volume domain ^ (1 / exponent.toReal) :=
  finite_field_Lp (outputInventory modes) _ _ (global_coefficient_norm_le lineage modes actual) order exponent compact

end
end SaturationMonoid.NavierStokes.NativeWholeVelocityFilterControl
