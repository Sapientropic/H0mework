import H0mework.Versions.Rdf421ff6.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.PhysicalN3NormalizedOutputPole
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.PhysicalN3CausalResponseWindow
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualRestLightCausalWindow

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.GaussComposite.PhysicalN3SourceEnergy
open GaussCoreHilbert CanonicalGradedSpatialSource ActualCompositeFieldCurrent
open PreparationVacuumMixedFieldReturn PreparationVacuumJointFieldResponse
open PreparationVacuumUncutYukawa PreparationVacuumSourcePreparedResponse
open GaussComposite.SourceGraph
open ActualDressedUniformMaterialCoefficients ActualElectronPhysicalJointInverse
open SourcePropagationAlgebraicResponse SourcePropagationCommonMomentum
open LowEnergy.ActualDressedVisiblePole
open PreparationVacuumActionFieldLift PreparationVacuumPhysicalFeedback
open PreparationVacuumRawJointFeedback PreparationVacuumNoetherOrdinaryWard
open PreparationVacuumNoetherChart PreparationVacuumGaugeSourceInjection
open PreparationVacuumFieldPerturbation.Blocks PreparationVacuumFullPoleContinuation
open ActualEMJointCurrentMomentum ActualElectronWholeChargeSoft
open ActualElectronWholeNoetherObserver ActualDressedFullCoulomb ActualDressedNoether
open ActualElectronFullNoetherMixedSoft SourceFamilyHilbert SourceFamilyOperator
open SourcePropagationTimeDependentFeedback
open PhysicalN3CausalWindow ActualSourceLightCircuit
open Filter
open scoped InnerProductSpace Topology

attribute [local irreducible] actualElectronPhysicalSeed actualElectronPhysicalResponse
  materialJointNumerator jointGenerator jointResolvent jointPolynomial compressionPolynomial
  physicalN3InputEnergyRead physicalN3InputEnergyNumerator
  physicalN3OutputEnergyNumerator physicalN3OutputEnergyGerm actualElectronPhysicalUnit
  physicalN3OutputPoleLeading physicalN3OutputPoleUnit actualFullNoetherVariation
  sourceRestLightMap sourceRestRemainderMap sourceProjectedVariation
  physicalN3ResponseWindowOperator sourceProjectedWindowOperator laplaceWeight
  prepared sourceProfile

/-- The external-energy frame read: the same five-term window pairing as the original
`physicalN3FrameRead`, with the normalized source state `actualElectronPhysicalUnit`
evaluated at the variable external energy `z`. The response-window operator stays the
event's fixed original operator and the background stays the original `sourceProfile`
preparation; `z` changes only the prepared physical state, never the operator. -/
def physicalN3ExternalEnergyFrameRead (event : DressedEvent) (leg : CompositeLeg)
    (k : PhysicalMomentum) (lambda : ℂ) (T : ℝ) (reader force : Field289)
    (F : GaussUnitaryHistory.Index) (z : ℂ) : ℂ:=
  let psi:=actualElectronPhysicalUnit event.momentum F z leg
  let A:=physicalN3ResponseWindowOperator event k lambda T reader force
  let b:=prepared (sourceProfile event.epsilon event.precision);
  -inner ℂ psi (A psi)+inner ℂ b (A b)

/-- The pole frame read: the identical window pairing evaluated on the normalized
whole-output pole vector `physicalN3OutputPoleUnit`. -/
def physicalN3PoleFrameRead (event : DressedEvent) (leg : CompositeLeg)
    (k : PhysicalMomentum) (lambda : ℂ) (T : ℝ) (reader force : Field289)
    (F : GaussUnitaryHistory.Index) (pole : N3SourceEnergyPole event.momentum F leg) : ℂ:=
  let psi:=physicalN3OutputPoleUnit event.momentum F leg pole
  let A:=physicalN3ResponseWindowOperator event k lambda T reader force
  let b:=prepared (sourceProfile event.epsilon event.precision);
  -inner ℂ psi (A psi)+inner ℂ b (A b)

/-- At the event's own energy the external read is exactly the original frame read:
the same normalized state, operator and background are recovered verbatim. -/
theorem physical_n3_external_energy_frame_original (event : DressedEvent)
    (leg : CompositeLeg) (k : PhysicalMomentum) (lambda : ℂ) (T : ℝ)
    (reader force : Field289) (F : GaussUnitaryHistory.Index) :
    physicalN3ExternalEnergyFrameRead event leg k lambda T reader force F event.energy=
      physicalN3FrameRead event leg k lambda T reader force F:=rfl

/-- The external preparation-energy boundary: along nonreal `z → pole.val`, the external
frame read converges to the pole frame read. The detector pairing converges by
`physical_n3_normalized_output_pole_read`; the fixed operator and background terms are
constant along the boundary. -/
theorem physical_n3_pole_window_boundary (event : DressedEvent)
    (leg : CompositeLeg) (k : PhysicalMomentum) (lambda : ℂ) (T : ℝ)
    (reader force : Field289) (F : GaussUnitaryHistory.Index)
    (pole : N3SourceEnergyPole event.momentum F leg) :
    Tendsto (fun z : ℂ =>
        physicalN3ExternalEnergyFrameRead event leg k lambda T reader force F z)
      (nhdsWithin pole.val {z : ℂ | z.im ≠ 0})
      (𝓝 (physicalN3PoleFrameRead event leg k lambda T reader force F pole)) := by
  show Tendsto (fun z : ℂ =>
      -inner ℂ (actualElectronPhysicalUnit event.momentum F z leg)
        (physicalN3ResponseWindowOperator event k lambda T reader force
          (actualElectronPhysicalUnit event.momentum F z leg))+
      inner ℂ (prepared (sourceProfile event.epsilon event.precision))
        (physicalN3ResponseWindowOperator event k lambda T reader force
          (prepared (sourceProfile event.epsilon event.precision))))
    (nhdsWithin pole.val {z : ℂ | z.im ≠ 0})
    (𝓝 (-inner ℂ (physicalN3OutputPoleUnit event.momentum F leg pole)
        (physicalN3ResponseWindowOperator event k lambda T reader force
          (physicalN3OutputPoleUnit event.momentum F leg pole))+
      inner ℂ (prepared (sourceProfile event.epsilon event.precision))
        (physicalN3ResponseWindowOperator event k lambda T reader force
          (prepared (sourceProfile event.epsilon event.precision)))))
  exact (physical_n3_normalized_output_pole_read event.momentum F leg pole
      (physicalN3ResponseWindowOperator event k lambda T reader force)).neg.add
    tendsto_const_nhds

/-- The pole frame read inherits the already generated rest-light/remainder operator
split; the original `sourceProfile` background is the same vector in both channels. -/
theorem physical_n3_pole_window_light_partition (event : DressedEvent)
    (leg : CompositeLeg) (k : PhysicalMomentum) (lambda : ℂ) (T : ℝ)
    (reader force : Field289) (F : GaussUnitaryHistory.Index)
    (pole : N3SourceEnergyPole event.momentum F leg) :
    physicalN3PoleFrameRead event leg k lambda T reader force F pole=
      (-inner ℂ (physicalN3OutputPoleUnit event.momentum F leg pole)
        (sourceProjectedWindowOperator sourceRestLightMap event k lambda T reader force
          (physicalN3OutputPoleUnit event.momentum F leg pole))+
      inner ℂ (prepared (sourceProfile event.epsilon event.precision))
        (sourceProjectedWindowOperator sourceRestLightMap event k lambda T reader force
          (prepared (sourceProfile event.epsilon event.precision))))+
      (-inner ℂ (physicalN3OutputPoleUnit event.momentum F leg pole)
        (sourceProjectedWindowOperator sourceRestRemainderMap event k lambda T
          reader force (physicalN3OutputPoleUnit event.momentum F leg pole))+
      inner ℂ (prepared (sourceProfile event.epsilon event.precision))
        (sourceProjectedWindowOperator sourceRestRemainderMap event k lambda T
          reader force
          (prepared (sourceProfile event.epsilon event.precision)))) := by
  have hsplit := actual_physical_n3_window_operator_source_rest_light_partition
    event k lambda T reader force
  calc physicalN3PoleFrameRead event leg k lambda T reader force F pole
      = -inner ℂ (physicalN3OutputPoleUnit event.momentum F leg pole)
          (physicalN3ResponseWindowOperator event k lambda T reader force
            (physicalN3OutputPoleUnit event.momentum F leg pole))+
        inner ℂ (prepared (sourceProfile event.epsilon event.precision))
          (physicalN3ResponseWindowOperator event k lambda T reader force
            (prepared (sourceProfile event.epsilon event.precision))) := rfl
    _ = -inner ℂ (physicalN3OutputPoleUnit event.momentum F leg pole)
        ((sourceProjectedWindowOperator sourceRestLightMap event k lambda T
          reader force+sourceProjectedWindowOperator sourceRestRemainderMap event
            k lambda T reader force)
          (physicalN3OutputPoleUnit event.momentum F leg pole))+
        inner ℂ (prepared (sourceProfile event.epsilon event.precision))
          ((sourceProjectedWindowOperator sourceRestLightMap event k lambda T
            reader force+sourceProjectedWindowOperator sourceRestRemainderMap
              event k lambda T reader force)
          (prepared (sourceProfile event.epsilon event.precision))) :=
      congrArg (fun W : H→L[ℂ]H =>
        -inner ℂ (physicalN3OutputPoleUnit event.momentum F leg pole) (W
          (physicalN3OutputPoleUnit event.momentum F leg pole))+
        inner ℂ (prepared (sourceProfile event.epsilon event.precision)) (W
          (prepared (sourceProfile event.epsilon event.precision)))) hsplit
    _ = (-inner ℂ (physicalN3OutputPoleUnit event.momentum F leg pole)
        (sourceProjectedWindowOperator sourceRestLightMap event k lambda T
          reader force (physicalN3OutputPoleUnit event.momentum F leg pole))+
        inner ℂ (prepared (sourceProfile event.epsilon event.precision))
          (sourceProjectedWindowOperator sourceRestLightMap event k lambda T
            reader force
            (prepared (sourceProfile event.epsilon event.precision))))+
      (-inner ℂ (physicalN3OutputPoleUnit event.momentum F leg pole)
        (sourceProjectedWindowOperator sourceRestRemainderMap event k lambda T
          reader force (physicalN3OutputPoleUnit event.momentum F leg pole))+
        inner ℂ (prepared (sourceProfile event.epsilon event.precision))
          (sourceProjectedWindowOperator sourceRestRemainderMap event k lambda T
            reader force
            (prepared (sourceProfile event.epsilon event.precision)))) := by
      simp only [add_apply, inner_add_right]
      ring

/-- The complete `289×289` reader/force square converges coordinatewise to the
pole-frame square along the nonreal boundary; every `fieldUnit` slot gets its own
boundary limit, no averaging. -/
theorem physical_n3_pole_window_square_boundary (event : DressedEvent)
    (leg : CompositeLeg) (k : PhysicalMomentum) (lambda : ℂ) (T : ℝ)
    (F : GaussUnitaryHistory.Index) (pole : N3SourceEnergyPole event.momentum F leg) :
    Tendsto (fun z : ℂ => fun (i j : Fin 289) =>
        physicalN3ExternalEnergyFrameRead event leg k lambda T
          (fieldUnit i) (fieldUnit j) F z)
      (nhdsWithin pole.val {z : ℂ | z.im ≠ 0})
      (𝓝 (fun (i j : Fin 289) =>
        physicalN3PoleFrameRead event leg k lambda T
          (fieldUnit i) (fieldUnit j) F pole)) := by
  apply tendsto_pi_nhds.mpr
  intro i
  apply tendsto_pi_nhds.mpr
  intro j
  exact physical_n3_pole_window_boundary event leg k lambda T
    (fieldUnit i) (fieldUnit j) F pole

end LowEnergy.GaussComposite.PhysicalN3SourceEnergy
