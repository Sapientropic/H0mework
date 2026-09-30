import H0mework.NavierStokes.SourceReadout.StressEnergy
import H0mework.NavierStokes.KineticRestart.KineticVelocityWholeCarrierMorphism

set_option autoImplicit false
open scoped ENNReal BigOperators

namespace SaturationMonoid.NavierStokes.NativeCofinalKineticIdentity

open Filter Set Matrix
open ThreeDimensionalPeriodicCoarseFilterCore
open ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientStretchingPairTable
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open ThreeDimensionalVorticityCoefficientGeneratedShellSerrinGeometry
open ThreeDimensionalVorticityCoefficientGeneratedShellViscousParseval
open ThreeDimensionalVorticityCoefficientStrongContinuationDifferenceKineticEnergy
open ThreeDimensionalVorticityCoefficientGeneratedIntegerShellStrongContinuationEnergyLedger
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartCrossingTangentCoercivity
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion.GeneratedWholeRestartCurrent
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartKineticWeakEndpoint
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityWeakEndpoint
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeAccumulationRoot
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointRecursiveMacroRuntime
open NativeCofinalStress

noncomputable section

theorem row_map_norm_sq (wave : NonzeroIntegerWavevector) (row : ComplexCoordinateEuclidean)
    (transverse : complexWavevector wave.1 ⬝ᵥ WithLp.ofLp row = 0) :
    ‖wholeRestartKineticToVelocityRowCLM wave row‖ ^ 2 = ‖row‖ ^ 2 := by
  have positive : 0 < integerWaveViscousMultiplier wave.1 := integerWaveViscousMultiplier_pos wave
  have scaled : complexWavevector wave.1 ⬝ᵥ
      ((Real.sqrt (integerWaveViscousMultiplier wave.1) : ℂ) • WithLp.ofLp row) = 0 := by
    rw [dotProduct_smul, transverse, smul_zero]
  rw [wholeRestartKineticToVelocityRowCLM_apply, euclideanCoordinateRow_norm_sq,
    complexCoordinateAmplitudeSq_eq_complexCoordinateVectorNormSq,
    biotSavartVelocityCoefficient_normSq_of_transverse _ _ wave.2 scaled,
    complexCoordinateVectorNormSq_smul, Complex.normSq_ofReal, Real.mul_self_sqrt positive.le]
  have sourceNorm : complexCoordinateVectorNormSq (WithLp.ofLp row) = ‖row‖ ^ 2 := by
    simpa only [euclideanCoordinateRow,
      complexCoordinateAmplitudeSq_eq_complexCoordinateVectorNormSq] using
      (euclideanCoordinateRow_norm_sq (WithLp.ofLp row)).symm
  rw [sourceNorm, ← integerWaveViscousMultiplier]
  field_simp

theorem whole_map_norm_sq (state : WholeRestartKineticEndpointState)
    (transverse : WholeRestartVelocityEndpointTransverse state) :
    ‖wholeRestartKineticToVelocityCLM state‖ ^ 2 = ‖state‖ ^ 2 := by
  have left := lp.norm_rpow_eq_tsum (p := (2 : ℝ≥0∞)) (by norm_num)
    (wholeRestartKineticToVelocityCLM state)
  have right := lp.norm_rpow_eq_tsum (p := (2 : ℝ≥0∞)) (by norm_num) state
  simp only [ENNReal.toReal_ofNat, Real.rpow_two] at left right
  rw [left, right]
  exact tsum_congr (fun wave => row_map_norm_sq wave (state wave) (transverse wave))

theorem contact_kinetic_transverse {nu : Viscosity} (initial : GeneratedWholeRestartCurrent nu)
    (index : ℕ) : WholeRestartVelocityEndpointTransverse (wholeRestartContactKineticState initial index) := by
  intro wave
  change complexWavevector wave.1 ⬝ᵥ
    ((Real.sqrt (integerWaveViscousMultiplier wave.1))⁻¹ • (run initial index).contact.physicalState wave.1) = 0
  have sourceTransverse : complexWavevector wave.1 ⬝ᵥ (run initial index).contact.physicalState wave.1 = 0 :=
    (run initial index).contact.transverse wave.1
  rw [dotProduct_smul, sourceTransverse, smul_zero]

theorem canonical_kinetic_transverse {nu : Viscosity} (initial : GeneratedWholeRestartCurrent nu) :
    WholeRestartVelocityEndpointTransverse
      (sourceGeneratedWholeRestartCanonicalWeakCofinalReceipt initial).kineticEndpoint :=
  velocityWeakLimit_transverse _ _
    (sourceGeneratedWholeRestartCanonicalWeakCofinalReceipt initial).kineticWeak_tendsto
    (fun _ => contact_kinetic_transverse initial _)

theorem canonical_endpoint_map {nu : Viscosity} (initial : GeneratedWholeRestartCurrent nu) :
    wholeRestartKineticToVelocityCLM
      (sourceGeneratedWholeRestartCanonicalWeakCofinalReceipt initial).kineticEndpoint =
        (sourceGeneratedWholeRestartCanonicalWeakCofinalReceipt initial).velocityEndpoint := by
  apply ext_inner_right ℂ
  intro test
  have mapped := (sourceGeneratedWholeRestartCanonicalWeakCofinalReceipt initial).kineticWeak_tendsto
    (wholeRestartKineticToVelocityCLM.adjoint test)
  simp only [ContinuousLinearMap.adjoint_inner_right, wholeRestartKineticToVelocityCLM_contact] at mapped
  exact tendsto_nhds_unique mapped
    ((sourceGeneratedWholeRestartCanonicalWeakCofinalReceipt initial).velocityWeak_tendsto test)

/-- Both original endpoint readouts retain the same physical kinetic norm. -/
theorem canonical_endpoint_norm_sq {nu : Viscosity} (initial : GeneratedWholeRestartCurrent nu) :
    ‖(sourceGeneratedWholeRestartCanonicalWeakCofinalReceipt initial).velocityEndpoint‖ ^ 2 =
      ‖(sourceGeneratedWholeRestartCanonicalWeakCofinalReceipt initial).kineticEndpoint‖ ^ 2 := by
  rw [← canonical_endpoint_map]
  exact whole_map_norm_sq _ (canonical_kinetic_transverse initial)

/-- The fluctuation energy on this exact cofinal refinement tends to the original kinetic defect. -/
theorem cofinal_fluctuation_mass_tendsto {nu : Viscosity} {initial : GeneratedWholeRestartCurrent nu}
    (receipt : CofinalStressAt initial) :
    Tendsto (fun index => ‖wholeRestartContactVelocityState initial (receipt.stage index) -
      (sourceGeneratedWholeRestartCanonicalWeakCofinalReceipt initial).velocityEndpoint‖ ^ 2) atTop
      (nhds (wholeRestartKineticWeakEndpointDefect initial
        (sourceGeneratedWholeRestartCanonicalWeakCofinalReceipt initial).kineticEndpoint)) := by
  have mass := (wholeRestartContactKineticMass_tendsto_limit initial).comp
    receipt.stage_strictMono.tendsto_atTop
  have originalMass (index : ℕ) : ‖wholeRestartContactVelocityState initial index‖ ^ 2 =
      wholeRestartContactKineticMass initial index := by
    rw [wholeRestartContactVelocityState_norm_sq, wholeRestartContactKineticMass,
      wholeRestartContactKineticState, puncturedWholeVorticityKineticEuclideanState_norm_sq]
  have cross := Complex.continuous_re.continuousAt.tendsto.comp
    (receipt.velocityWeak_tendsto
      (sourceGeneratedWholeRestartCanonicalWeakCofinalReceipt initial).velocityEndpoint)
  have difference := (mass.sub ((tendsto_const_nhds (x := (2 : ℝ))).mul cross)).add
    (tendsto_const_nhds (x :=
      ‖(sourceGeneratedWholeRestartCanonicalWeakCofinalReceipt initial).velocityEndpoint‖ ^ 2))
  have limitEq : wholeRestartKineticMassLimit initial -
      2 * (inner ℂ (sourceGeneratedWholeRestartCanonicalWeakCofinalReceipt initial).velocityEndpoint
        (sourceGeneratedWholeRestartCanonicalWeakCofinalReceipt initial).velocityEndpoint).re +
      ‖(sourceGeneratedWholeRestartCanonicalWeakCofinalReceipt initial).velocityEndpoint‖ ^ 2 =
      wholeRestartKineticWeakEndpointDefect initial
        (sourceGeneratedWholeRestartCanonicalWeakCofinalReceipt initial).kineticEndpoint := by
    rw [← RCLike.re_eq_complex_re, inner_self_eq_norm_sq (𝕜 := ℂ), canonical_endpoint_norm_sq]
    unfold wholeRestartKineticWeakEndpointDefect
    ring
  rw [limitEq] at difference
  simpa only [norm_sub_sq (𝕜 := ℂ), RCLike.re_eq_complex_re, originalMass, Function.comp_def] using difference

end
end SaturationMonoid.NavierStokes.NativeCofinalKineticIdentity
