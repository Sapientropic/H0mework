import H0mework.Versions.Rdf421ff6.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.PhysicalN3PoleEMActionRead
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualElectronNoetherDensity
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.SourceSignedVolumeObservation

/-! The raw Noether h-normalized EM action density calibrated against the
canonical pole action read: the raw reader decomposes as the canonical action
plus the explicit finite-reader density core. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.GaussComposite.PhysicalN3SourceEnergy
open SaturationMonoid.PhysicsCore SaturationMonoid.PhysicsCore.LowEnergy
open GaussCoreHilbert GaussCoreDifferential GaussFockPair CanonicalGradedSpatialSource
open ActualCompositeFieldCurrent
open PreparationVacuumMixedFieldReturn PreparationVacuumJointFieldResponse
open PreparationVacuumUncutYukawa PreparationVacuumSourcePreparedResponse
open GaussComposite.SourceGraph
open ActualDressedUniformMaterialCoefficients ActualElectronPhysicalJointInverse
open ActualElectronWholeChargeSoft CanonicalGradedCharge PreparationPhysicalPhaseGaugeRealization
open SourceFamilyHilbert SourceFamilyOperator
open SourcePropagationAlgebraicResponse SourcePropagationCommonMomentum
open LowEnergy.ActualDressedVisiblePole
open PreparationVacuumFieldConstraintResponse
open ActualDressedTemporalForm SourceQuantumGaugeSliceCoordinates GaussHistoryHilbert
open PreparationVacuumRawJointFeedback PreparationPhysicalFirstTemporalChargeReturn
open PreparationPhysicalSignedVolumeWeightReturn ActualElectronNoetherDensity
open PhysicalEMGaugeRealization PhysicalEMVoltage
open MeasureTheory Filter
open scoped InnerProductSpace Topology

attribute [local irreducible] actualElectronPhysicalSeed actualElectronPhysicalResponse
  materialJointNumerator jointGenerator jointResolvent jointPolynomial compressionPolynomial
  physicalN3InputEnergyRead physicalN3InputEnergyNumerator
  physicalN3OutputEnergyNumerator physicalN3OutputEnergyGerm actualElectronPhysicalUnit
  physicalN3OutputPoleOrder physicalN3OutputPoleLeading physicalN3OutputPoleUnit
  actualElectronPhysicalChargeCorrection chargeReader actualElectronPhysicalState
  actualElectronPhysicalChargeVertex actualElectronPhysicalChargeRead
  physicalN3PolePhase physicalN3PoleEnergyRadius
  physicalN3PoleEnergyScale physicalN3PoleApproachEnergy physicalN3PoleApproachUnit
  prepared sourceProfile

/-- The explicit finite-reader density core: `-(h)⁻¹` times the actual
independent-dual temporal matrix core minus the source charge action. Scalar
smul and scalar inverse, matching `actualDensityCorrection`'s source formula. -/
def physicalN3PoleEMDensityCore (b : QuantumTest) : QuantumTest :=
  (-(Stage10.ActionNormalization.phaseMomentum : ℂ)⁻¹) •
    sourceTemporalMatrixCore emGaugeChargeMatrix b -
    chargeAction sourcePhaseGaugeLie b

/-- The literal original h-normalized raw EM action read on the two actual
approach tests. -/
def physicalN3PoleRawEMActionFrameRead (pL pR : PhysicalMomentum)
    (left right : CompositeLeg)
    (polesL : N3SourceEnergyPoleSection pL left)
    (polesR : N3SourceEnergyPoleSection pR right)
    (m : ℕ) (F : GaussUnitaryHistory.Index) (G : GaussUnitaryHistory.Index) : ℂ :=
  -(Stage10.ActionNormalization.phaseMomentum : ℂ)⁻¹ *
    rawForm (emGaugeField 0) pR
      (sourceTestApprox G (physicalN3PoleApproachUnit pL F left (polesL F) m))
      (sourceTestApprox G (physicalN3PoleApproachUnit pR F right (polesR F) m)) 0

/-- The density-core pairing read on the same actual tests. -/
def physicalN3PoleEMDensityFrameRead (pL pR : PhysicalMomentum)
    (left right : CompositeLeg)
    (polesL : N3SourceEnergyPoleSection pL left)
    (polesR : N3SourceEnergyPoleSection pR right)
    (m : ℕ) (F : GaussUnitaryHistory.Index) (G : GaussUnitaryHistory.Index) : ℂ :=
  sourcePair (sourceTestApprox G (physicalN3PoleApproachUnit pL F left (polesL F) m))
    (physicalN3PoleEMDensityCore
      (sourceTestApprox G (physicalN3PoleApproachUnit pR F right (polesR F) m)))

/-- The raw h-normalized action decomposes as the canonical action plus the
explicit density core pairing, on arbitrary complete source tests: the signed
coframe volume and independent-dual terms are preserved throughout. -/
theorem physical_n3_pole_em_raw_density_core (p : PhysicalMomentum)
    (a b : QuantumTest) :
    -(Stage10.ActionNormalization.phaseMomentum : ℂ)⁻¹ *
        rawForm (emGaugeField 0) p a b 0 =
      emActionForm p a b +
        sourcePair a (physicalN3PoleEMDensityCore b) := by
  rw [actual_em_signed_density_form, sourceSignedVolumeForm_actual, em_action_form]
  unfold physicalN3PoleEMDensityCore
  have e : GaussCoreHilbert.embed
        ((-(Stage10.ActionNormalization.phaseMomentum : ℂ)⁻¹) •
          sourceTemporalMatrixCore emGaugeChargeMatrix b -
        chargeAction sourcePhaseGaugeLie b) =
      (-(Stage10.ActionNormalization.phaseMomentum : ℂ)⁻¹) •
        embed (sourceTemporalMatrixCore emGaugeChargeMatrix b) -
        embed (chargeAction sourcePhaseGaugeLie b) := by
    rw [map_sub, map_smul]
  have hsub : sourcePair a
        ((-(Stage10.ActionNormalization.phaseMomentum : ℂ)⁻¹) •
          sourceTemporalMatrixCore emGaugeChargeMatrix b -
        chargeAction sourcePhaseGaugeLie b) =
      -(Stage10.ActionNormalization.phaseMomentum : ℂ)⁻¹ *
        sourcePair a (sourceTemporalMatrixCore emGaugeChargeMatrix b) -
      sourcePair a (chargeAction sourcePhaseGaugeLie b) := by
    calc sourcePair a
          ((-(Stage10.ActionNormalization.phaseMomentum : ℂ)⁻¹) •
            sourceTemporalMatrixCore emGaugeChargeMatrix b -
          chargeAction sourcePhaseGaugeLie b)
        = inner ℂ (embed a) ((-(Stage10.ActionNormalization.phaseMomentum : ℂ)⁻¹) •
            embed (sourceTemporalMatrixCore emGaugeChargeMatrix b) -
          embed (chargeAction sourcePhaseGaugeLie b)) :=
          congrArg (inner ℂ (embed a)) e
      _ = inner ℂ (embed a) ((-(Stage10.ActionNormalization.phaseMomentum : ℂ)⁻¹) •
            embed (sourceTemporalMatrixCore emGaugeChargeMatrix b)) -
          inner ℂ (embed a) (embed (chargeAction sourcePhaseGaugeLie b)) :=
          inner_sub_right _ _ _
      _ = (-(Stage10.ActionNormalization.phaseMomentum : ℂ)⁻¹) *
            inner ℂ (embed a) (embed (sourceTemporalMatrixCore emGaugeChargeMatrix b)) -
          inner ℂ (embed a) (embed (chargeAction sourcePhaseGaugeLie b)) :=
          congrArg (fun t : ℂ => t -
            inner ℂ (embed a) (embed (chargeAction sourcePhaseGaugeLie b)))
            (inner_smul_right (embed a)
              (embed (sourceTemporalMatrixCore emGaugeChargeMatrix b))
              (-(Stage10.ActionNormalization.phaseMomentum : ℂ)⁻¹))
      _ = _ := rfl
  rw [hsub]
  ring

/-- The actual raw frame read equals the canonical pole action frame read plus
the explicit density-core read on exactly the same `F`, `G`, `m`, legs and
sections. -/
theorem physical_n3_pole_em_raw_frame_calibration (pL pR : PhysicalMomentum)
    (left right : CompositeLeg)
    (polesL : N3SourceEnergyPoleSection pL left)
    (polesR : N3SourceEnergyPoleSection pR right)
    (m : ℕ) (F : GaussUnitaryHistory.Index) (G : GaussUnitaryHistory.Index) :
    physicalN3PoleRawEMActionFrameRead pL pR left right polesL polesR m F G =
      physicalN3PoleEMActionFrameRead pL pR left right polesL polesR m F G +
        physicalN3PoleEMDensityFrameRead pL pR left right polesL polesR m F G := by
  unfold physicalN3PoleRawEMActionFrameRead physicalN3PoleEMDensityFrameRead
    physicalN3PoleEMActionFrameRead
  exact physical_n3_pole_em_raw_density_core pR _ _

end LowEnergy.GaussComposite.PhysicalN3SourceEnergy
