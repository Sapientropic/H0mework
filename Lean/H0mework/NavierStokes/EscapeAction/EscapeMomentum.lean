import H0mework.NavierStokes.EscapeAction.EscapeStress
import H0mework.NavierStokes.CofinalAction.CofinalMomentum

set_option autoImplicit false
open scoped BigOperators Topology ENNReal

namespace SaturationMonoid.NavierStokes.NativeRecoveryEscapeMomentum

open Set Filter
open ThreeDimensionalPeriodicCoarseFilterCore
open ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientStretchingPairTable
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open ThreeDimensionalVorticityCoefficientFiniteSupportPhysicalInvariantTrajectory
open ThreeDimensionalVorticityCoefficientFiniteGalerkinKineticEnergyLedger
open ThreeDimensionalVorticityCoefficientFixedOutputNonlinearContinuity
open ThreeDimensionalVorticityCoefficientInfiniteFixedOutputNonlinearRow
open ThreeDimensionalVorticityCoefficientWholeVelocityPairDiagonalBudget
open ThreeDimensionalVorticityCoefficientPuncturedCanonicalGalerkinTarget
open ThreeDimensionalVorticityCoefficientCanonicalExhaustiveGalerkinTarget
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityWeakEndpoint
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointGalerkinUniformKineticLedger
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointWholeMildReadWrite
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeAccumulationRoot
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointPositiveTimeH1Reentry
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeAccumulationNativeTurbulenceLaw
open ThreeDimensionalVorticityCoefficientNativeFluidMedium
open NativeRecoveryCoverage NativeRecoveryEscapeCarrier NativeRecoveryEscapeStress
open NativeStressSource NativeStressCurlAlgebra NativeCofinalStress NativeTimeJetCarrier
open NativeEndpointVelocityCarrier

noncomputable section

variable {nu : Viscosity} {ledger : GeneratedWholeRestartVelocityEndpointUniformKineticViscousLedgerCore nu}
  {receipt : GeneratedWholeRestartVelocityEndpointWholeMildReadWriteReceipt ledger} {point : ℝ}
  {escape : SourceActionEscape receipt point}

theorem state_momentum_eq_stress (viscosity : ℝ) (vorticity : ComplexVorticityHilbertState)
    (zero : vorticity 0 = 0) (transverse : WholeStateTransverse vorticity) (wave : IntegerWavevector) :
    biotSavartVelocityCoefficient wave (wholeLatticeVorticityFourierTangentAt viscosity vorticity wave) =
      projectedDivergenceCLM wave (quadraticFlux (wholeBiotSavartVelocityState vorticity) wave) -
        (viscosity * integerWaveViscousMultiplier wave) • wholeBiotSavartVelocityState vorticity wave := by
  by_cases nonzero : wave ≠ 0
  · unfold wholeLatticeVorticityFourierTangentAt
    change (biotSavartVelocityCLM wave) (_ - _ • vorticity wave) = _
    rw [map_sub, map_smul, biotSavartVelocityCLM_apply,
      ← quadraticFlux_biotSavart_action vorticity zero transverse wave,
      nativeFluidConstitutiveVorticityAction,
      biotSavartVelocityCoefficient_fourierCurlCoefficient wave _ nonzero]
    rfl
  · have atZero : wave = 0 := not_ne_iff.mp nonzero
    subst wave
    simp [projectedDivergenceCLM_apply, transverseProjection, integerWaveViscousMultiplier]

def actualMomentum (escape : SourceActionEscape receipt point) (index : ℕ) : NativeFluidVorticityTangent :=
  fun wave => biotSavartVelocityCoefficient wave
    (wholeLatticeVorticityFourierTangentAt nu.coeff (state escape index) wave)

theorem actualStress_eq (escape : SourceActionEscape receipt point) (index : ℕ) :
    actualStress escape index = quadraticFlux (wholeBiotSavartVelocityState (state escape index)) := by
  unfold actualStress velocity
  rw [wholeVelocity_punctured]

theorem actualMomentum_eq_stress (escape : SourceActionEscape receipt point) (pointLe : point ≤ 1)
    (index : ℕ) (wave : IntegerWavevector) :
    actualMomentum escape index wave = projectedDivergenceCLM wave (actualStress escape index wave) -
      (nu.coeff * integerWaveViscousMultiplier wave) • finiteStateVelocityCoefficient (state escape index) wave := by
  have physical := (ledger.family.stage (radius escape index)).physical _ (sampleTime escape pointLe index).2
  rw [actualStress_eq]
  exact state_momentum_eq_stress nu.coeff (state escape index)
    (physical.2.1 0 (zero_not_mem_puncturedIntegerWaveFrequencyCube _)) physical.2.2.1 wave

def momentum (stress : StressAt escape) (pointLe : point ≤ 1) : NativeFluidVorticityTangent :=
  fun wave => projectedDivergenceCLM wave (stress.stress wave) -
    (nu.coeff * integerWaveViscousMultiplier wave) • wholeVelocity (fixedEndpoint escape pointLe) wave

def resolvedMomentum (escape : SourceActionEscape receipt point) (pointLe : point ≤ 1) : NativeFluidVorticityTangent :=
  fun wave => projectedDivergenceCLM wave (quadraticFlux (wholeVelocity (fixedEndpoint escape pointLe)) wave) -
    (nu.coeff * integerWaveViscousMultiplier wave) • wholeVelocity (fixedEndpoint escape pointLe) wave

def internalMomentum (stress : StressAt escape) (pointLe : point ≤ 1) : NativeFluidVorticityTangent :=
  fun wave => projectedDivergenceCLM wave (defect stress pointLe wave)

theorem momentum_tendsto (stress : StressAt escape) (pointLe : point ≤ 1) :
    Tendsto (fun index => actualMomentum escape (stress.refinement index)) atTop (𝓝 (momentum stress pointLe)) := by
  apply tendsto_pi_nhds.mpr
  intro wave
  have flux := (projectedDivergenceCLM wave).continuous.tendsto (stress.stress wave) |>.comp
    (tendsto_pi_nhds.mp stress.stress_tendsto wave)
  have velocity := (velocity_row_tendsto escape pointLe wave).comp stress.refinement_strict.tendsto_atTop
  rw [← fixedEndpoint_reads_original escape pointLe] at velocity
  exact (flux.sub (velocity.const_smul (nu.coeff * integerWaveViscousMultiplier wave))).congr'
    (Eventually.of_forall fun index => (actualMomentum_eq_stress escape pointLe (stress.refinement index) wave).symm)

theorem momentum_decomposition (stress : StressAt escape) (pointLe : point ≤ 1) :
    momentum stress pointLe = resolvedMomentum escape pointLe + internalMomentum stress pointLe := by
  funext wave
  have tensor : stress.stress wave = quadraticFlux (wholeVelocity (fixedEndpoint escape pointLe)) wave +
      defect stress pointLe wave := by
    unfold defect
    change stress.stress wave = _ + (stress.stress wave - _)
    abel
  rw [momentum, tensor, map_add]
  change _ = resolvedMomentum escape pointLe wave + internalMomentum stress pointLe wave
  unfold resolvedMomentum internalMomentum
  abel

theorem pressure_tendsto (stress : StressAt escape) :
    Tendsto (fun index wave => sourcePressure (state escape (stress.refinement index)) wave) atTop
      (𝓝 fun wave => stressPressureCoefficient wave (stress.stress wave)) := by
  apply tendsto_pi_nhds.mpr
  intro wave
  have source := (stressPressureCLM wave).continuous.tendsto (stress.stress wave) |>.comp
    (tendsto_pi_nhds.mp stress.stress_tendsto wave)
  simpa only [Function.comp_def, stressPressureCLM_apply, actualStress_eq, sourcePressure] using source

theorem pressure_decomposition (stress : StressAt escape) (pointLe : point ≤ 1) (wave : IntegerWavevector) :
    stressPressureCoefficient wave (stress.stress wave) =
      stressPressureCoefficient wave (quadraticFlux (wholeVelocity (fixedEndpoint escape pointLe)) wave) +
        stressPressureCoefficient wave (defect stress pointLe wave) := by
  have tensor : stress.stress wave = quadraticFlux (wholeVelocity (fixedEndpoint escape pointLe)) wave +
      defect stress pointLe wave := by
    unfold defect
    change stress.stress wave = _ + (stress.stress wave - _)
    abel
  change stressPressureCLM wave (stress.stress wave) = _
  rw [tensor, map_add]
  rfl

theorem momentum_pressure_identity (stress : StressAt escape) (pointLe : point ≤ 1) (wave : IntegerWavevector) :
    momentum stress pointLe wave = nativeFluidStressDivergenceCoefficient stress.stress wave -
      ((Complex.I * (((2 * Real.pi : ℝ) : ℂ))) * stressPressureCoefficient wave (stress.stress wave)) •
        complexWavevector wave - (nu.coeff * integerWaveViscousMultiplier wave) •
          wholeVelocity (fixedEndpoint escape pointLe) wave := by
  have pressure := nativeFluidStressDivergenceCoefficient_eq_leray_add_pressure wave (stress.stress wave)
  have decomposed : projectedDivergenceCLM wave (stress.stress wave) =
      nativeFluidStressDivergenceCoefficient stress.stress wave -
        ((Complex.I * (((2 * Real.pi : ℝ) : ℂ))) * stressPressureCoefficient wave (stress.stress wave)) •
          complexWavevector wave := eq_sub_of_add_eq pressure.symm
  rw [momentum, decomposed]

end
end SaturationMonoid.NavierStokes.NativeRecoveryEscapeMomentum
