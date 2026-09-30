import H0mework.NavierStokes.RecoveryAction.RecoveryJointTimeKernel

set_option autoImplicit false
open scoped Topology

namespace SaturationMonoid.NavierStokes.NativeRecoveryTimeGramReadout

open Set Filter
open ThreeDimensionalPeriodicCoarseFilterCore ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open ThreeDimensionalVorticityCoefficientWholeVelocityPairDiagonalBudget
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityWeakEndpoint
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointGalerkinUniformKineticLedger
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointWholeMildReadWrite
open NativeRecoveryCoverage NativeRecoveryEscapeStress NativeRecoveryTimeGramRaw NativeRecoveryJointTimeKernel
open NativeEndpointVelocityCarrier NativeCofinalStressPositivity NativePhysicalFourier

noncomputable section

variable {nu : Viscosity} {ledger : GeneratedWholeRestartVelocityEndpointUniformKineticViscousLedgerCore nu}
  {receipt : GeneratedWholeRestartVelocityEndpointWholeMildReadWriteReceipt ledger} {point : ℝ}
  {escape : SourceActionEscape receipt point}

theorem background_gram (escape : SourceActionEscape receipt point) (pointLe : point ≤ 1) (index : ℕ)
    (wave : IntegerWavevector) (node : TimeNode) (shift : IntegerWavevector) (coordinate : Coordinate) :
    gram escape pointLe index (.inl wave) (.inr (node, shift, coordinate)) =
      wholeVelocity (NativeRecoveryTimeGramRaw.velocity escape pointLe index node) (wave - shift) coordinate := by
  change inner ℂ (lp.single 2 wave (1 : ℂ) : ScalarSequence)
    (shiftedComponent (NativeRecoveryTimeGramRaw.velocity escape pointLe index node) (shift, coordinate)) = _
  rw [lp.inner_single_left]
  simp [RCLike.inner_apply, shiftedComponent]

theorem fixed_velocity_tendsto (stress : StressAt escape) (pointLe : point ≤ 1)
    (time : Icc (0 : ℝ) 1) (wave : IntegerWavevector) :
    Tendsto (fun index => wholeVelocity (NativeRecoveryTimeGramRaw.velocity escape pointLe (stress.refinement index) (.fixed time)) wave)
      atTop (𝓝 (receipt.wholePath time wave)) := by
  have original := NativeRecoveryControlProducer.endpoint_velocity_row_tendsto ledger receipt.core time wave
  rw [← receipt.wholePath_apply] at original
  have extraction := escape.extraction_strict.tendsto_atTop.comp (tendsto_atTop_mono escape.index_ge tendsto_id)
  have refined := (original.comp extraction).comp stress.refinement_strict.tendsto_atTop
  apply refined.congr'
  exact Eventually.of_forall fun index => by
    change finiteStateVelocityCoefficient _ wave = wholeVelocity (puncturedWholeVelocityEuclideanState _) wave
    rw [wholeVelocity_punctured]
    rfl

def physicalTime (escape : SourceActionEscape receipt point) (pointLe : point ≤ 1) : TimeNode → Icc (0 : ℝ) 1
  | .anchor => ⟨point, NativeRecoveryEscapeCarrier.point_nonnegative escape, pointLe⟩
  | .fixed time => time

theorem velocity_tendsto (stress : StressAt escape) (pointLe : point ≤ 1) (node : TimeNode) (wave : IntegerWavevector) :
    Tendsto (fun index => wholeVelocity (NativeRecoveryTimeGramRaw.velocity escape pointLe (stress.refinement index) node) wave)
      atTop (𝓝 (receipt.wholePath (physicalTime escape pointLe node) wave)) := by
  cases node with
  | fixed time => exact fixed_velocity_tendsto stress pointLe time wave
  | anchor =>
    have original := (NativeRecoveryEscapeCarrier.velocity_row_tendsto escape pointLe wave).comp stress.refinement_strict.tendsto_atTop
    apply original.congr'
    exact Eventually.of_forall fun index => by
      change finiteStateVelocityCoefficient _ wave = wholeVelocity (puncturedWholeVelocityEuclideanState _) wave
      rw [wholeVelocity_punctured]
      rfl

def velocityRead (stress : StressAt escape) (pointLe : point ≤ 1) (node : TimeNode)
    (wave : IntegerWavevector) (coordinate : Coordinate) : ℂ :=
  inner ℂ (NativeRecoveryJointTimeKernel.vector stress pointLe (.inl wave))
    (NativeRecoveryJointTimeKernel.vector stress pointLe (.inr (node, 0, coordinate)))

theorem source_velocity (stress : StressAt escape) (pointLe : point ≤ 1) (node : TimeNode)
    (wave : IntegerWavevector) (coordinate : Coordinate) :
    velocityRead stress pointLe node wave coordinate = receipt.wholePath (physicalTime escape pointLe node) wave coordinate := by
  have selected := pairing_tendsto stress pointLe (.inl wave) (.inr (node, 0, coordinate))
  simp only [background_gram, sub_zero] at selected
  have original := ((continuous_apply coordinate).tendsto _ |>.comp (velocity_tendsto stress pointLe node wave)).mono_left
    (generated stress pointLe).cofinal
  exact tendsto_nhds_unique selected original

def stressRead (stress : StressAt escape) (pointLe : point ≤ 1) (node : TimeNode)
    (wave : IntegerWavevector) (output input : Coordinate) : ℂ :=
  -inner ℂ (NativeRecoveryJointTimeKernel.vector stress pointLe (.inr (node, wave, output)))
    (NativeRecoveryJointTimeKernel.vector stress pointLe (.inr (node, 0, input)))

theorem source_anchor_stress (stress : StressAt escape) (pointLe : point ≤ 1)
    (wave : IntegerWavevector) (output input : Coordinate) : stressRead stress pointLe .anchor wave output input = stress.stress wave output input := by
  rw [stressRead, anchor_stress, sub_zero, neg_neg]

end
end SaturationMonoid.NavierStokes.NativeRecoveryTimeGramReadout
