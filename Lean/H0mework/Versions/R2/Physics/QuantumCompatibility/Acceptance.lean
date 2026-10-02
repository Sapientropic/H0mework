import H0mework.Versions.R2.Physics.QuantumCompatibility.Hermitian
import H0mework.Versions.R2.Physics.QuantumCompatibility.Mass
import H0mework.Versions.R2.Physics.QuantumCompatibility.ConnectionJet
import H0mework.Versions.R2.Physics.QuantumCompatibility.ExteriorRemainder
import H0mework.Versions.R2.Physics.QuantumState.SourceFrame
import H0mework.Versions.R2.Physics.QuantumState.SourceReparametrization

/-! One common-carrier compatibility output. The source's full mass map and
vacuum coexist with the occupied Yukawa kernel; current, stress and the
actual connection are consumed at their original physical scope. -/

set_option autoImplicit false

namespace SaturationMonoid.PhysicsCore.Stage9DEF.Compatibility

open ProofFreeRicherAnholonomicSource StageNineHolonomicField StageNineEnrichedProofFreeSource
open Stage9C.Material.SpinPair SU7MotherLieAlgebra SU7ExteriorMatterRepresentation
open SU7ExteriorMatterRestriction
open StageNineP286GaugeConnectionVariationDensity StageNineP286GaugeConnectionActionVariation
open StageNineP286GaugeConnectionVariation SU7ExteriorYukawaMassSpectrum
open StageNineConnectionSectorSourceBalance
open DiracExteriorMatterLocalGaugeLink
open scoped Matrix Matrix.Norms.L2Operator

noncomputable section

structure PhysicalCompatibility : Prop where
  current : ∀ point variation, currentResponse point variation =
    p286MatterCurrentCoefficient positiveSmoothUnifiedSource actual variation point
  currentSelfAdjoint : ∀ direction data, (physicalCurrent direction data).IsHermitian
  currentEvaluation : ∀ point direction data,
    State.evaluation point (physicalCurrent direction data) =
      (vectorRead point (currentObservable direction data)).re
  stress : ∀ point, kineticLoad point = actualKineticLoad point
  stressSelfAdjoint : ∀ internal direction, (physicalKinetic internal direction).IsHermitian
  stressEvaluation : ∀ point internal direction,
    State.evaluation point (physicalKinetic internal direction) =
      (vectorRead point (kineticObservable internal direction)).re
  vacuum : ∀ point, actualVacuum point = finiteGenerationJointBreakingScalar
  fullMass : ∀ point, fullMass point ≠ 0
  massEntries : ∀ point output input, massMatrix point output input ≠ 0
  occupiedMass : ∀ point, yukawaAction point (actual.matter point) = 0 ∧
    vectorRead point (responseMatrix (yukawaAction point)) = 0
  massCovariant : ∀ point frame matter,
    SU7ExteriorBreakingYukawa.exteriorYukawaMassMap
        (SU7ExteriorBreakingYukawa.exteriorBreakingScalarRepresentation frame (actualVacuum point))
        (su7ExteriorPowerRepresentation 2 frame matter) =
      su7ExteriorPowerRepresentation 6 frame (Compatibility.fullMass point matter)
  connectionIsActual : ∀ point direction,
    actualPotential point direction = p286LieBlockEmbed (actual.gaugeConnection point direction)
  smoothFirstJet : ∀ point direction,
    HasDerivAt (connectionTransport point direction) (connectionGenerator point direction) 0
  finiteUnitary : ∀ point direction duration,
    connectionTransport point direction duration ∈ Matrix.unitaryGroup SU7MotherIndex ℂ
  stageEight : ∀ point direction duration,
    exteriorSpinorLinkAction (connectionJet point direction duration) =
      SU7ExteriorMatterGaugeCovariantJet.exteriorSpinorMotherTransport
        (duration • actualPotential point direction)
  quantitativeRemainder : ∀ point direction duration, 0 ≤ duration →
    ‖connectionTransport point direction duration - connectionJet point direction duration‖ ≤
      ‖connectionGenerator point direction‖ ^ 2 * duration ^ 2
  exteriorFirstJet : ∀ point direction degree
      (matter : ⋀[ℂ]^degree SU7FundamentalCarrier) coordinate,
    HasDerivAt (fun duration : ℝ => (su7ExteriorBasis degree).repr
      (exteriorLinkAction degree (connectionTransport point direction duration) matter) coordinate)
      ((su7ExteriorBasis degree).repr
        (exteriorMotherLieAction degree (actualPotential point direction) matter) coordinate) 0
  exteriorRemainder : ∀ point direction degree
      (matter : ⋀[ℂ]^degree SU7FundamentalCarrier) coordinate duration, 0 ≤ duration →
    ‖(su7ExteriorBasis degree).repr
        (exteriorLinkAction degree (connectionTransport point direction duration) matter) coordinate -
      (su7ExteriorBasis degree).repr
        (exteriorLinkAction degree (connectionJet point direction duration) matter) coordinate‖ ≤
      exteriorErrorScale point direction degree matter coordinate duration * duration ^ 2
  commonFrame : ∀ (frame : Source.Frame.Action) point reference,
    State.vectorEvaluation (Source.Frame.prepare frame (frame (actual.matter point)))
      (Source.Frame.effect frame reference).matrix =
        State.evaluation point (State.sourceEffect reference).matrix
  fullSpinGauge : ∀ element point reference,
    State.vectorEvaluation
      (Source.Frame.prepare (Source.Frame.totalFrame element)
        (StageNineSpinMatterBundle.totalDiracExteriorMatterRepresentation element (actual.matter point)))
      (Source.Frame.effect (Source.Frame.totalFrame element) reference).matrix =
        State.evaluation point (State.sourceEffect reference).matrix
  ambientAction : ∀ (frame : Source.Frame.Action) observable matter,
    Source.Frame.observableAction frame observable (frame matter) =
      frame (Source.Frame.observableAction (LinearEquiv.refl ℂ _) observable matter)
  coordinateInvariant : ∀ (reparam : BasePoint ≃ BasePoint)
      (localFrame : BasePoint → Source.Frame.Action) point reference,
    Source.Reparametrization.weight reparam localFrame
        (reparam.symm point) (reparam.symm reference) =
      State.effectWeight point (State.sourceEffect reference)

theorem physicalCompatibility : PhysicalCompatibility where
  current := currentResponse_eq_classical
  currentSelfAdjoint := physicalCurrent_isHermitian
  currentEvaluation := physicalCurrent_readout
  stress := kineticLoad_eq_actual
  stressSelfAdjoint := physicalKinetic_isHermitian
  stressEvaluation := physicalKinetic_readout
  vacuum := actualVacuum_stageEight
  fullMass := fullMass_nonzero
  massEntries := massMatrix_entry_nonzero
  occupiedMass := fun point => ⟨occupied_yukawa_zero point, occupied_yukawa_quantum_zero point⟩
  massCovariant := fullMass_su7_covariant
  connectionIsActual := fun _ _ => rfl
  smoothFirstJet := connectionTransport_firstJet
  finiteUnitary := connectionTransport_unitary
  stageEight := connectionJet_stageEight
  quantitativeRemainder := connectionTransport_remainder
  exteriorFirstJet := exteriorTransport_hasDerivAt
  exteriorRemainder := exteriorTransport_remainder
  commonFrame := Source.Frame.quantum_evaluation
  fullSpinGauge := Source.Frame.total_spin_SU7_quantum_evaluation
  ambientAction := Source.Frame.observableAction_transformed
  coordinateInvariant := Source.Reparametrization.same_physical_points_weight

end
end SaturationMonoid.PhysicsCore.Stage9DEF.Compatibility
