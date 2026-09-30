import H0mework.Versions.X.NavierStokes.SourceAction.WholeVelocityFilter
import H0mework.Versions.X.NavierStokes.EscapeAction.EscapeCorrection

set_option autoImplicit false
open scoped BigOperators ENNReal Topology

namespace SaturationMonoid.NavierStokes.NativeJointStressFilterControl

open Set Filter MeasureTheory
open ThreeDimensionalPeriodicCoarseFilterCore
open ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open ThreeDimensionalVorticityCoefficientInfiniteFixedOutputNonlinearRow
open ThreeDimensionalVorticityCoefficientWholeVelocityPairDiagonalBudget
open ThreeDimensionalVorticityCoefficientWholeKineticDifferenceCancellation
open ThreeDimensionalVorticityCoefficientNativeFluidMedium
open NativeStressSource NativeStressCurlAlgebra NativeFullOrderSynthesis NativeCorrectionPhysical
open NativeFixedFilterGlobalControl
open NativeRecoveryEscapeCorrection (projectStress)

noncomputable section

def stress (modes : Finset IntegerWavevector) (velocity : ComplexVorticityHilbertState)
    (total : NativeFluidStressFourierState) : NativeFluidStressFourierState :=
  projectStress modes total - quadraticFlux (complexSharpSupportProjection modes velocity)

def coefficient (modes : Finset IntegerWavevector) (velocity : ComplexVorticityHilbertState)
    (total : NativeFluidStressFourierState) (wave : IntegerWavevector) : ComplexCoordinateVector :=
  NativeWholeVelocityFilterControl.rowAction wave (stress modes velocity total wave)

theorem coefficient_supported (modes : Finset IntegerWavevector) (velocity : ComplexVorticityHilbertState)
    (total : NativeFluidStressFourierState) (wave : IntegerWavevector) (outside : wave ∉ outputInventory modes) :
    coefficient modes velocity total wave = 0 := by
  have outsideFirst : wave ∉ modes := fun inside => outside (Finset.mem_union_left _ inside)
  have rowZero : stress modes velocity total wave = 0 := by
    simp only [stress, projectStress, Pi.sub_apply, if_neg outsideFirst,
      NativeWholeVelocityFilterControl.projected_flux_zero modes velocity wave outside, sub_self]
  rw [coefficient, rowZero, map_zero]

theorem projected_mass_le (modes : Finset IntegerWavevector) (velocity : ComplexVorticityHilbertState) :
    wholeVorticityEuclideanMass (complexSharpSupportProjection modes velocity) ≤ wholeVorticityEuclideanMass velocity := by
  have split := wholeVorticityEuclideanMass_eq_projection_add_complement modes velocity
  have nonnegative : 0 ≤ wholeVorticityEuclideanMass (complexSharpSupportProjection modes velocity - velocity) :=
    tsum_nonneg fun _ => sq_nonneg _
  linarith

theorem stress_norm_le (modes : Finset IntegerWavevector) (velocity : ComplexVorticityHilbertState)
    (total : NativeFluidStressFourierState) (budget : ℝ) (nonnegative : 0 ≤ budget)
    (totalBound : ∀ wave output input, ‖total wave output input‖ ≤ budget)
    (velocityBound : wholeVorticityEuclideanMass velocity ≤ budget) (wave : IntegerWavevector) :
    ‖stress modes velocity total wave‖ ≤ 2 * budget := by
  apply (pi_norm_le_iff_of_nonneg (by positivity : 0 ≤ 2 * budget)).mpr
  intro output
  apply (pi_norm_le_iff_of_nonneg (by positivity : 0 ≤ 2 * budget)).mpr
  intro input
  have first : ‖projectStress modes total wave output input‖ ≤ budget := by
    by_cases inside : wave ∈ modes
    · simpa only [projectStress, if_pos inside] using totalBound wave output input
    · simpa only [projectStress, if_neg inside, Pi.zero_apply, norm_zero] using nonnegative
  have second := (quadraticFlux_norm_le_mass (complexSharpSupportProjection modes velocity) wave output input).trans
    ((projected_mass_le modes velocity).trans velocityBound)
  exact (norm_sub_le _ _).trans ((add_le_add first second).trans_eq (by ring))

theorem coefficient_norm_le (modes : Finset IntegerWavevector) (velocity : ComplexVorticityHilbertState)
    (total : NativeFluidStressFourierState) (budget : ℝ) (nonnegative : 0 ≤ budget)
    (totalBound : ∀ wave output input, ‖total wave output input‖ ≤ budget)
    (velocityBound : wholeVorticityEuclideanMass velocity ≤ budget) (wave : IntegerWavevector) :
    ‖coefficient modes velocity total wave‖ ≤ 2 * ‖NativeWholeVelocityFilterControl.rowAction wave‖ * budget :=
  (NativeWholeVelocityFilterControl.rowAction wave).le_opNorm _ |>.trans
    ((mul_le_mul_of_nonneg_left (stress_norm_le modes velocity total budget nonnegative totalBound velocityBound wave)
      (norm_nonneg _)).trans_eq (by ring))

def state (modes : Finset IntegerWavevector) (velocity : ComplexVorticityHilbertState)
    (total : NativeFluidStressFourierState) : ComplexVorticityHilbertState :=
  finiteComplexVorticityState (outputInventory modes) (coefficient modes velocity total)

theorem state_apply (modes : Finset IntegerWavevector) (velocity : ComplexVorticityHilbertState)
    (total : NativeFluidStressFourierState) (wave : IntegerWavevector) :
    state modes velocity total wave = coefficient modes velocity total wave := by
  rw [state, finiteComplexVorticityState_apply]
  split_ifs with inside
  · rfl
  · exact (coefficient_supported modes velocity total wave inside).symm

def physicalField (modes : Finset IntegerWavevector) (velocity : ComplexVorticityHilbertState)
    (total : NativeFluidStressFourierState) : PhysicalSpace → PhysicalSpace := spatialField (state modes velocity total)

theorem physicalField_eq_finite (modes : Finset IntegerWavevector) (velocity : ComplexVorticityHilbertState)
    (total : NativeFluidStressFourierState) : physicalField modes velocity total =
      ThreeDimensionalVorticityCoefficientPhysicalCompiler.finiteRealComplexFourierField
        (outputInventory modes) (coefficient modes velocity total) := spatialField_finite_compiler _ _

theorem resolved_coefficient (modes : Finset IntegerWavevector) (velocity : ComplexVorticityHilbertState) :
    coefficient modes velocity (quadraticFlux velocity) = NativeWholeVelocityFilterControl.coefficient modes velocity := rfl

theorem coefficient_decomposition (modes : Finset IntegerWavevector) (velocity : ComplexVorticityHilbertState)
    (total : NativeFluidStressFourierState) (wave : IntegerWavevector) :
    coefficient modes velocity total wave = NativeWholeVelocityFilterControl.coefficient modes velocity wave +
      NativeWholeVelocityFilterControl.rowAction wave (projectStress modes (total - quadraticFlux velocity) wave) := by
  have tensor : stress modes velocity total wave =
      NativeWholeVelocityFilterControl.stress modes velocity wave + projectStress modes (total - quadraticFlux velocity) wave := by
    simp only [stress, NativeWholeVelocityFilterControl.stress, projectStress, Pi.sub_apply]
    by_cases inside : wave ∈ modes <;> simp [inside]
  rw [coefficient, tensor, map_add]
  rfl

theorem coefficient_tendsto (modes : Finset IntegerWavevector) (sequence : ℕ → ComplexVorticityHilbertState)
    (limit : ComplexVorticityHilbertState) (total : NativeFluidStressFourierState)
    (rows : ∀ wave, Tendsto (fun index => sequence index wave) atTop (𝓝 (limit wave)))
    (stressLimit : Tendsto (fun index => quadraticFlux (sequence index)) atTop (𝓝 total)) :
    Tendsto (fun index => coefficient modes (sequence index) (quadraticFlux (sequence index))) atTop
      (𝓝 (coefficient modes limit total)) := by
  have filtered : Tendsto (fun index => projectStress modes (quadraticFlux (sequence index))) atTop
      (𝓝 (projectStress modes total)) := by
    apply tendsto_pi_nhds.mpr
    intro wave
    by_cases inside : wave ∈ modes
    · simpa only [projectStress, if_pos inside] using tendsto_pi_nhds.mp stressLimit wave
    · simpa only [projectStress, if_neg inside] using tendsto_const_nhds (x := (0 : NativeFluidStressCoefficient))
  have resolved := NativeRecoveryEscapeCorrection.projected_flux_tendsto modes sequence limit rows
  apply tendsto_pi_nhds.mpr
  intro wave
  exact (NativeWholeVelocityFilterControl.rowAction wave).continuous.tendsto (stress modes limit total wave) |>.comp
    (tendsto_pi_nhds.mp (filtered.sub resolved) wave)

def spatialBudget (modes : Finset IntegerWavevector) (budget : ℝ) (order : ℕ) : ℝ :=
  finiteBudget (outputInventory modes) (fun wave => 2 * ‖NativeWholeVelocityFilterControl.rowAction wave‖ * budget) order

theorem spatial_control (modes : Finset IntegerWavevector) (velocity : ComplexVorticityHilbertState)
    (total : NativeFluidStressFourierState) (budget : ℝ) (nonnegative : 0 ≤ budget)
    (totalBound : ∀ wave output input, ‖total wave output input‖ ≤ budget)
    (velocityBound : wholeVorticityEuclideanMass velocity ≤ budget) :
    ContDiff ℝ (↑(⊤ : ℕ∞)) (physicalField modes velocity total) ∧
      ∀ order point, ‖iteratedFDeriv ℝ order (physicalField modes velocity total) point‖ ≤ spatialBudget modes budget order :=
  finite_field_control (outputInventory modes) _ _ (coefficient_norm_le modes velocity total budget nonnegative totalBound velocityBound)

theorem spatial_Lp (modes : Finset IntegerWavevector) (velocity : ComplexVorticityHilbertState)
    (total : NativeFluidStressFourierState) (budget : ℝ) (nonnegative : 0 ≤ budget)
    (totalBound : ∀ wave output input, ‖total wave output input‖ ≤ budget)
    (velocityBound : wholeVorticityEuclideanMass velocity ≤ budget)
    (order : ℕ) (exponent : ℝ≥0∞) {domain : Set PhysicalSpace} (compact : IsCompact domain) :
    MemLp (iteratedFDeriv ℝ order (physicalField modes velocity total)) exponent (volume.restrict domain) ∧
      eLpNorm (iteratedFDeriv ℝ order (physicalField modes velocity total)) exponent (volume.restrict domain) ≤
        ENNReal.ofReal (spatialBudget modes budget order) * volume domain ^ (1 / exponent.toReal) :=
  finite_field_Lp (outputInventory modes) _ _ (coefficient_norm_le modes velocity total budget nonnegative totalBound velocityBound)
    order exponent compact

end
end SaturationMonoid.NavierStokes.NativeJointStressFilterControl
