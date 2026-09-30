import H0mework.NavierStokes.CofinalReadout.StressDefect
import H0mework.NavierStokes.TimeJets.TimeCarrier

set_option autoImplicit false
open scoped BigOperators ENNReal Topology

namespace SaturationMonoid.NavierStokes.NativeCofinalMomentumAction

open Set Filter
open ThreeDimensionalPeriodicCoarseFilterCore
open ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open ThreeDimensionalVorticityCoefficientFiniteSupportPhysicalInvariantTrajectory
open ThreeDimensionalVorticityCoefficientFiniteGalerkinKineticEnergyLedger
open ThreeDimensionalVorticityCoefficientCanonicalExhaustiveGalerkinTarget
open ThreeDimensionalVorticityCoefficientInfiniteFixedOutputNonlinearRow
open ThreeDimensionalVorticityCoefficientWholeVelocityPairDiagonalBudget
open ThreeDimensionalVorticityCoefficientNativeFluidMedium
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion.GeneratedWholeRestartCurrent
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityWeakEndpoint
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeAccumulationRoot
open NativeStressSource NativeStressCurlAlgebra NativeCofinalStress NativeCofinalStressDefect
open NativeEndpointVelocityCarrier NativeTimeJetCarrier

noncomputable section

variable {nu : Viscosity}

def endpointVelocity (initial : GeneratedWholeRestartCurrent nu) : ComplexVorticityHilbertState :=
  wholeVelocity (sourceGeneratedWholeRestartCanonicalWeakCofinalReceipt initial).velocityEndpoint

def actualMomentum (initial : GeneratedWholeRestartCurrent nu) (stage : ℕ) : NativeFluidVorticityTangent :=
  fun wave => biotSavartVelocityCoefficient wave
    (wholeLatticeVorticityFourierTangentAt nu.coeff (run initial stage).contact.physicalState wave)

theorem actualMomentum_eq_stress (initial : GeneratedWholeRestartCurrent nu) (stage : ℕ) (wave : IntegerWavevector) :
    actualMomentum initial stage wave = projectedDivergenceCLM wave (contactStress initial stage wave) -
      (nu.coeff * integerWaveViscousMultiplier wave) • wholeBiotSavartVelocityState (run initial stage).contact.physicalState wave := by
  by_cases nonzero : wave ≠ 0
  · unfold actualMomentum wholeLatticeVorticityFourierTangentAt
    change (biotSavartVelocityCLM wave) (_ - _ • (run initial stage).contact.physicalState wave) = _
    rw [map_sub, map_smul, biotSavartVelocityCLM_apply]
    rw [← quadraticFlux_biotSavart_action _ (run initial stage).contact.physicalState_zero
      (run initial stage).contact.transverse wave, nativeFluidConstitutiveVorticityAction,
      biotSavartVelocityCoefficient_fourierCurlCoefficient wave _ nonzero]
    rfl
  · have zero : wave = 0 := not_ne_iff.mp nonzero
    subst wave
    simp [actualMomentum, projectedDivergenceCLM_apply, transverseProjection, integerWaveViscousMultiplier]

theorem velocity_row_tendsto {initial : GeneratedWholeRestartCurrent nu} (receipt : CofinalStressAt initial)
    (wave : IntegerWavevector) :
    Tendsto (fun index => wholeBiotSavartVelocityState (run initial (receipt.stage index)).contact.physicalState wave)
      atTop (𝓝 (endpointVelocity initial wave)) := by
  by_cases nonzero : wave ≠ 0
  · apply tendsto_pi_nhds.mpr
    intro coordinate
    have source := velocityWeakTendsto_coordinate
      (fun index => wholeRestartContactVelocityState initial (receipt.stage index))
      (sourceGeneratedWholeRestartCanonicalWeakCofinalReceipt initial).velocityEndpoint
      receipt.velocityWeak_tendsto ⟨wave, nonzero⟩ coordinate
    change Tendsto _ atTop (𝓝 (wholeVelocity
      (sourceGeneratedWholeRestartCanonicalWeakCofinalReceipt initial).velocityEndpoint wave coordinate))
    rw [wholeVelocity_nonzero _ ⟨wave, nonzero⟩]
    exact source
  · have zero : wave = 0 := not_ne_iff.mp nonzero
    subst wave
    simpa only [wholeBiotSavartVelocityState_apply, finiteStateVelocityCoefficient, biotSavartVelocityCoefficient_zero,
      endpointVelocity, wholeVelocity_zero] using tendsto_const_nhds (x := (0 : ComplexCoordinateVector))

theorem velocity_tendsto {initial : GeneratedWholeRestartCurrent nu} (receipt : CofinalStressAt initial) :
    Tendsto (fun index wave => wholeBiotSavartVelocityState (run initial (receipt.stage index)).contact.physicalState wave)
      atTop (𝓝 fun wave => endpointVelocity initial wave) :=
  tendsto_pi_nhds.mpr (velocity_row_tendsto receipt)

def momentum {initial : GeneratedWholeRestartCurrent nu} (receipt : CofinalStressAt initial) : NativeFluidVorticityTangent :=
  fun wave => projectedDivergenceCLM wave (receipt.stress wave) -
    (nu.coeff * integerWaveViscousMultiplier wave) • endpointVelocity initial wave

def resolvedMomentum (initial : GeneratedWholeRestartCurrent nu) : NativeFluidVorticityTangent :=
  fun wave => projectedDivergenceCLM wave (quadraticFlux (endpointVelocity initial) wave) -
    (nu.coeff * integerWaveViscousMultiplier wave) • endpointVelocity initial wave

def internalMomentum {initial : GeneratedWholeRestartCurrent nu} (receipt : CofinalStressAt initial) : NativeFluidVorticityTangent :=
  fun wave => projectedDivergenceCLM wave (stressDefect receipt wave)

theorem momentum_tendsto {initial : GeneratedWholeRestartCurrent nu} (receipt : CofinalStressAt initial) :
    Tendsto (fun index => actualMomentum initial (receipt.stage index)) atTop (𝓝 (momentum receipt)) := by
  apply tendsto_pi_nhds.mpr
  intro wave
  have flux : Tendsto (fun index => projectedDivergenceCLM wave (contactStress initial (receipt.stage index) wave))
      atTop (𝓝 (projectedDivergenceCLM wave (receipt.stress wave))) :=
    (projectedDivergenceCLM wave).continuous.tendsto (receipt.stress wave) |>.comp
      (tendsto_pi_nhds.mp receipt.stress_tendsto wave)
  have viscous := (velocity_row_tendsto receipt wave).const_smul (nu.coeff * integerWaveViscousMultiplier wave)
  exact (flux.sub viscous).congr'
    (Eventually.of_forall fun index => (actualMomentum_eq_stress initial (receipt.stage index) wave).symm)

theorem momentum_decomposition {initial : GeneratedWholeRestartCurrent nu} (receipt : CofinalStressAt initial) :
    momentum receipt = resolvedMomentum initial + internalMomentum receipt := by
  funext wave
  have tensor : receipt.stress wave = quadraticFlux (endpointVelocity initial) wave + stressDefect receipt wave := by
    unfold endpointVelocity stressDefect
    change receipt.stress wave = _ + (receipt.stress wave - _)
    abel
  rw [momentum, tensor, map_add]
  change _ = resolvedMomentum initial wave + internalMomentum receipt wave
  unfold resolvedMomentum internalMomentum
  abel

theorem momentum_pressure_identity {initial : GeneratedWholeRestartCurrent nu} (receipt : CofinalStressAt initial)
    (wave : IntegerWavevector) :
    momentum receipt wave = nativeFluidStressDivergenceCoefficient receipt.stress wave -
      ((Complex.I * (((2 * Real.pi : ℝ) : ℂ))) * stressPressureCoefficient wave (receipt.stress wave)) •
        complexWavevector wave - (nu.coeff * integerWaveViscousMultiplier wave) • endpointVelocity initial wave := by
  have pressure := nativeFluidStressDivergenceCoefficient_eq_leray_add_pressure wave (receipt.stress wave)
  have decomposed : projectedDivergenceCLM wave (receipt.stress wave) =
      nativeFluidStressDivergenceCoefficient receipt.stress wave -
        ((Complex.I * (((2 * Real.pi : ℝ) : ℂ))) * stressPressureCoefficient wave (receipt.stress wave)) • complexWavevector wave :=
    eq_sub_of_add_eq pressure.symm
  rw [momentum, decomposed]

theorem source_generated_momentum_tendsto (initial : GeneratedWholeRestartCurrent nu) :
    Tendsto (fun index => actualMomentum initial ((sourceGeneratedCofinalStress initial).stage index))
      atTop (𝓝 (resolvedMomentum initial + internalMomentum (sourceGeneratedCofinalStress initial))) := by
  rw [← momentum_decomposition]
  exact momentum_tendsto (sourceGeneratedCofinalStress initial)

theorem source_generated_joint_tendsto (initial : GeneratedWholeRestartCurrent nu) :
    Tendsto (fun index =>
      ( (fun wave => wholeBiotSavartVelocityState
          (run initial ((sourceGeneratedCofinalStress initial).stage index)).contact.physicalState wave),
        contactStress initial ((sourceGeneratedCofinalStress initial).stage index),
        actualMomentum initial ((sourceGeneratedCofinalStress initial).stage index)))
      atTop (𝓝 ( (fun wave => endpointVelocity initial wave),
        (sourceGeneratedCofinalStress initial).stress,
        resolvedMomentum initial + internalMomentum (sourceGeneratedCofinalStress initial))) :=
  (velocity_tendsto (sourceGeneratedCofinalStress initial)).prodMk_nhds
    ((sourceGeneratedCofinalStress initial).stress_tendsto.prodMk_nhds (source_generated_momentum_tendsto initial))

end
end SaturationMonoid.NavierStokes.NativeCofinalMomentumAction
