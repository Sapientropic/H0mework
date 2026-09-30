import H0mework.NavierStokes.SourceReadout.CofinalStress

/-!
# The original kinetic account is the trace of its complete source stress

The full zero-frequency stress trace recovers the original kinetic mass.
The same cofinal refinement preserves its mass limit and original canonical
kinetic endpoint defect; no separate velocity-endpoint receipt is substituted.
-/

set_option autoImplicit false

namespace SaturationMonoid.NavierStokes.NativeStressKineticTrace

open scoped BigOperators
open Filter
open ThreeDimensionalPeriodicCoarseFilterCore
open ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open ThreeDimensionalVorticityCoefficientFiniteSupportRealityTrajectory
open ThreeDimensionalVorticityCoefficientGeneratedShellSerrinGeometry
open ThreeDimensionalVorticityCoefficientFixedOutputNonlinearContinuity
open ThreeDimensionalVorticityCoefficientInfiniteFixedOutputNonlinearRow
open ThreeDimensionalVorticityCoefficientWholeVelocityPairDiagonalBudget
open ThreeDimensionalVorticityCoefficientStrongContinuationDifferenceKineticEnergy
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartCrossingTangentCoercivity
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion.GeneratedWholeRestartCurrent
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartKineticWeakEndpoint
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityWeakEndpoint
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeAccumulationRoot
open NativeStressSource NativeCofinalStress

noncomputable section

/-- The original physical kinetic scalar is the negative real zero-frequency stress trace. -/
theorem quadraticFlux_zero_trace_eq_neg_kinetic (state : ComplexVorticityHilbertState)
    (transverse : WholeStateTransverse state) (reality : FiniteStateFourierReality state) :
    (∑ i : Coordinate, (quadraticFlux (wholeBiotSavartVelocityState state) 0 i i).re) =
      -puncturedWholeVorticityKineticMass state := by
  let velocity := wholeBiotSavartVelocityState state
  have velocityReality (wave : IntegerWavevector) :
      velocity (0 - wave) = vectorConj (velocity wave) := by
    change biotSavartVelocityCoefficient (0 - wave) (state (0 - wave)) =
      vectorConj (biotSavartVelocityCoefficient wave (state wave))
    have negEq : 0 - wave = waveNeg wave := by
      funext coordinate
      simp [waveNeg]
    rw [negEq, reality wave, biotSavartVelocityCoefficient_waveNeg_vectorConj]
  have productRe (wave : IntegerWavevector) (i : Coordinate) :
      (velocity wave i * velocity (0 - wave) i).re = Complex.normSq (velocity wave i) := by
    rw [velocityReality]
    simp [vectorConj, Complex.mul_re, Complex.normSq_apply]
  have normSummable (i : Coordinate) :
      Summable (fun wave : IntegerWavevector => Complex.normSq (velocity wave i)) :=
    (Complex.hasSum_re (flux_pair_summable velocity 0 i i).hasSum).summable.congr
      (fun wave => productRe wave i)
  have diagonal (i : Coordinate) :
      (quadraticFlux velocity 0 i i).re =
        -∑' wave : IntegerWavevector, Complex.normSq (velocity wave i) := by
    rw [quadraticFlux, Complex.neg_re, Complex.re_tsum (flux_pair_summable velocity 0 i i)]
    exact congrArg Neg.neg (tsum_congr fun wave => productRe wave i)
  change (∑ i : Coordinate, (quadraticFlux velocity 0 i i).re) = _
  simp_rw [diagonal]
  rw [Finset.sum_neg_distrib]
  have exchange := Summable.tsum_finsetSum
    (s := Finset.univ) (fun i _ => normSummable i)
  rw [← exchange]
  have massEq : (∑' wave : IntegerWavevector,
      ∑ i : Coordinate, Complex.normSq (velocity wave i)) = wholeVorticityEuclideanMass velocity := by
    unfold wholeVorticityEuclideanMass
    apply tsum_congr
    intro wave
    exact (vorticityRowAmplitude_sq velocity wave).symm
  rw [massEq, wholeVorticityEuclideanMass_wholeBiotSavartVelocityState state transverse]

/-- The cofinal limit keeps the exact scalar from the same original contact ledger. -/
theorem cofinal_zero_trace_eq_neg_massLimit {nu : Viscosity}
    {initial : GeneratedWholeRestartCurrent nu} (receipt : CofinalStressAt initial) :
    (∑ i : Coordinate, (receipt.stress 0 i i).re) = -wholeRestartKineticMassLimit initial := by
  have coordinate (i : Coordinate) :
      Tendsto (fun index => (contactStress initial (receipt.stage index) 0 i i).re) atTop
        (nhds (receipt.stress 0 i i).re) := by
    have tensor := tendsto_pi_nhds.mp receipt.stress_tendsto 0
    have row := tendsto_pi_nhds.mp tensor i
    have scalar := tendsto_pi_nhds.mp row i
    exact Complex.continuous_re.continuousAt.tendsto.comp scalar
  have traceTendsto := tendsto_finsetSum Finset.univ (fun i _ => coordinate i)
  have massTendsto := ((wholeRestartContactKineticMass_tendsto_limit initial).comp
    receipt.stage_strictMono.tendsto_atTop).neg
  have sourceEq (index : ℕ) :
      (∑ i : Coordinate, (contactStress initial (receipt.stage index) 0 i i).re) =
        -wholeRestartContactKineticMass initial (receipt.stage index) := by
    rw [contactStress, quadraticFlux_zero_trace_eq_neg_kinetic
      (run initial (receipt.stage index)).contact.physicalState
      (run initial (receipt.stage index)).contact.transverse
      (run initial (receipt.stage index)).contact.reality]
    rw [wholeRestartContactKineticMass, wholeRestartContactKineticState,
      puncturedWholeVorticityKineticEuclideanState_norm_sq]
  have sameSequence : (fun index => ∑ i : Coordinate,
      (contactStress initial (receipt.stage index) 0 i i).re) =
      (fun index => -wholeRestartContactKineticMass initial (receipt.stage index)) :=
    funext sourceEq
  rw [sameSequence] at traceTendsto
  exact tendsto_nhds_unique traceTendsto massTendsto

/-- The existing kinetic endpoint defect is the unresolved part of this same stress trace. -/
theorem cofinal_trace_residual_eq_kinetic_defect {nu : Viscosity}
    {initial : GeneratedWholeRestartCurrent nu} (receipt : CofinalStressAt initial) :
    -(∑ i : Coordinate, (receipt.stress 0 i i).re) -
        ‖(sourceGeneratedWholeRestartCanonicalWeakCofinalReceipt initial).kineticEndpoint‖ ^ 2 =
      wholeRestartKineticWeakEndpointDefect initial
        (sourceGeneratedWholeRestartCanonicalWeakCofinalReceipt initial).kineticEndpoint := by
  rw [cofinal_zero_trace_eq_neg_massLimit, neg_neg]
  rfl

end
end SaturationMonoid.NavierStokes.NativeStressKineticTrace
