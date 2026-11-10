import H0mework.Versions.Rdf421ff6.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.PhysicalN3PoleAmputatedChargeRead
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualDressedTemporalForm
import H0mework.Versions.R3bbcbd59.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.CanonicalPreparationFieldFormConsumer

/-! The original EM action form evaluated on the generated source-pole approach
units through the independent original core-approximation index: preparation `F`
supplies the units, `G` supplies the test approximations; they are never identified. -/
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
open GaussQuantumMultiplier PreparationVacuumSourceActionJets
open PreparationVacuumSourceFieldFamily PreparationVacuumActionFieldLift
open PreparationVacuumFullElectricWard ActualDressedActionPhase PhysicalEMGaugeRealization
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

/-- The original literal EM action configuration integral on the two actual
approach tests: `F` prepares the pole-approach units, `G` is the independent
original core approximation index. -/
def physicalN3PoleEMActionFrameRead (pL pR : PhysicalMomentum)
    (left right : CompositeLeg)
    (polesL : N3SourceEnergyPoleSection pL left)
    (polesR : N3SourceEnergyPoleSection pR right)
    (m : ℕ) (F : GaussUnitaryHistory.Index) (G : GaussUnitaryHistory.Index) : ℂ :=
  emActionForm pR
    (sourceTestApprox G (physicalN3PoleApproachUnit pL F left (polesL F) m))
    (sourceTestApprox G (physicalN3PoleApproachUnit pR F right (polesR F) m))

/-- The exact underlying configuration integrand on the two actual tests is
integrable under the original configuration measure; the full field-dependent
matrix normalizer and the full pair term are retained. -/
theorem physical_n3_pole_em_action_integrable (pL pR : PhysicalMomentum)
    (left right : CompositeLeg)
    (polesL : N3SourceEnergyPoleSection pL left)
    (polesR : N3SourceEnergyPoleSection pR right)
    (m : ℕ) (F : GaussUnitaryHistory.Index) (G : GaussUnitaryHistory.Index) :
    Integrable (fun z : SourceCoordinateSlice => pairSample z
        (sourceTestApprox G (physicalN3PoleApproachUnit pL F left (polesL F) m) z)
        (quantized (canonicalPhaseNormalizer (sourceState z))
          (quantized ((Stage10.ActionNormalization.actionScale : ℂ) •
            rawActionSymbol (emGaugeField 0) pR (sourceState z))
            (sourceTestApprox G (physicalN3PoleApproachUnit pR F right (polesR F) m) z)) -
          pairFiber (canonicalPhaseNormalizer (sourceState z))
            ((Stage10.ActionNormalization.actionScale : ℂ) •
              rawActionSymbol (emGaugeField 0) pR (sourceState z))
            (sourceTestApprox G (physicalN3PoleApproachUnit pR F right (polesR F) m) z)))
      GaussHistoryHilbert.configurationMeasure :=
  em_action_integrable pR _ _

/-- The frame action read pays the original source pairing against the charge
action of the right approximate test. -/
theorem physical_n3_pole_em_action_source_pair (pL pR : PhysicalMomentum)
    (left right : CompositeLeg)
    (polesL : N3SourceEnergyPoleSection pL left)
    (polesR : N3SourceEnergyPoleSection pR right)
    (m : ℕ) (F : GaussUnitaryHistory.Index) (G : GaussUnitaryHistory.Index) :
    physicalN3PoleEMActionFrameRead pL pR left right polesL polesR m F G =
      sourcePair (sourceTestApprox G (physicalN3PoleApproachUnit pL F left (polesL F) m))
        (chargeAction sourcePhaseGaugeLie
          (sourceTestApprox G (physicalN3PoleApproachUnit pR F right (polesR F) m))) :=
  em_action_form pR _ _

/-- For each fixed `m` and `F`, the independent core-approximation index `G`
returns the frame action read to the exact amputated two-Green charge read,
through `same_source_approximation` on both fixed units and the bounded charge
reader. -/
theorem physical_n3_pole_em_action_core_return (pL pR : PhysicalMomentum)
    (left right : CompositeLeg)
    (polesL : N3SourceEnergyPoleSection pL left)
    (polesR : N3SourceEnergyPoleSection pR right)
    (m : ℕ) (F : GaussUnitaryHistory.Index) :
    Tendsto (fun G : GaussUnitaryHistory.Index =>
        physicalN3PoleEMActionFrameRead pL pR left right polesL polesR m F G)
      GaussUnitaryHistory.sourceFilter
      (𝓝 (physicalN3PoleAmputatedChargeFrameRead pL pR left right polesL polesR m F)) := by
  have hlim : Tendsto (fun G : GaussUnitaryHistory.Index =>
        inner ℂ (embed (sourceTestApprox G
          (physicalN3PoleApproachUnit pL F left (polesL F) m)))
          (chargeReader sourcePhaseGaugeLie (embed (sourceTestApprox G
            (physicalN3PoleApproachUnit pR F right (polesR F) m)))))
      GaussUnitaryHistory.sourceFilter
      (𝓝 (inner ℂ (physicalN3PoleApproachUnit pL F left (polesL F) m)
        (chargeReader sourcePhaseGaugeLie
          (physicalN3PoleApproachUnit pR F right (polesR F) m)))) :=
    (same_source_approximation (physicalN3PoleApproachUnit pL F left (polesL F) m)).inner
      (((chargeReader sourcePhaseGaugeLie).continuous.tendsto _).comp
        (same_source_approximation (physicalN3PoleApproachUnit pR F right (polesR F) m)))
  have heq : (fun G : GaussUnitaryHistory.Index =>
        inner ℂ (embed (sourceTestApprox G
          (physicalN3PoleApproachUnit pL F left (polesL F) m)))
          (chargeReader sourcePhaseGaugeLie (embed (sourceTestApprox G
            (physicalN3PoleApproachUnit pR F right (polesR F) m))))) =ᶠ[GaussUnitaryHistory.sourceFilter]
      (fun G : GaussUnitaryHistory.Index =>
        physicalN3PoleEMActionFrameRead pL pR left right polesL polesR m F G) :=
    Eventually.of_forall fun G : GaussUnitaryHistory.Index => by
      show inner ℂ (embed (sourceTestApprox G
            (physicalN3PoleApproachUnit pL F left (polesL F) m)))
          (chargeReader sourcePhaseGaugeLie (embed (sourceTestApprox G
            (physicalN3PoleApproachUnit pR F right (polesR F) m)))) =
        physicalN3PoleEMActionFrameRead pL pR left right polesL polesR m F G
      unfold physicalN3PoleEMActionFrameRead
      rw [em_action_form]
      unfold GaussFockPair.sourcePair
      rw [← chargeReader_core]
  have h := hlim.congr' heq
  rwa [← physical_n3_pole_amputated_charge_value pL pR left right polesL polesR m F] at h

/-- The ordered three-clause contract: the `G`-core return to the exact amputated
frame read, the `F`-sourceFilter return to the completed history read, and the
`atTop` energy return to sign-weighted pole overlap plus the retained right
correction. Ordered consumption, not a product or simultaneous limit. -/
theorem physical_n3_pole_em_action_staged_return (pL pR : PhysicalMomentum)
    (left right : CompositeLeg)
    (polesL : N3SourceEnergyPoleSection pL left)
    (polesR : N3SourceEnergyPoleSection pR right) :
    (∀ (m : ℕ) (F : GaussUnitaryHistory.Index),
      Tendsto (fun G : GaussUnitaryHistory.Index =>
          physicalN3PoleEMActionFrameRead pL pR left right polesL polesR m F G)
        GaussUnitaryHistory.sourceFilter
        (𝓝 (physicalN3PoleAmputatedChargeFrameRead pL pR left right polesL polesR m F)))
      ∧
    (∀ m : ℕ,
      Tendsto (fun F : GaussUnitaryHistory.Index =>
          physicalN3PoleAmputatedChargeFrameRead pL pR left right polesL polesR m F)
        GaussUnitaryHistory.sourceFilter
        (𝓝 (physicalN3PoleAmputatedChargeHistoryRead pL pR left right polesL polesR m)))
      ∧
    Tendsto (fun m : ℕ =>
        physicalN3PoleAmputatedChargeHistoryRead pL pR left right polesL polesR m)
      atTop
      (𝓝 (actualElectronSign right *
          inner ℂ (physicalN3PoleState pL left polesL)
            (physicalN3PoleState pR right polesR) +
        inner ℂ (physicalN3PoleState pL left polesL)
          (physicalN3PoleCorrection pR right polesR))) :=
  ⟨fun m F => physical_n3_pole_em_action_core_return pL pR left right polesL polesR m F,
   fun m => physical_n3_pole_amputated_charge_source_return pL pR left right polesL polesR m,
   physical_n3_pole_amputated_charge_pole_return pL pR left right polesL polesR⟩

/-- The same ordered contract at zero transfer, with the literal source frame
identity `frameRead = actualElectronPhysicalChargeRead` retained as a clause.
Not a Thomson-limit identification. -/
theorem physical_n3_pole_em_action_zero_transfer_return (p : PhysicalMomentum)
    (leg : CompositeLeg) (poles : N3SourceEnergyPoleSection p leg) :
    (∀ (m : ℕ) (F : GaussUnitaryHistory.Index),
      Tendsto (fun G : GaussUnitaryHistory.Index =>
          physicalN3PoleEMActionFrameRead p p leg leg poles poles m F G)
        GaussUnitaryHistory.sourceFilter
        (𝓝 (physicalN3PoleAmputatedChargeFrameRead p p leg leg poles poles m F)))
      ∧
    (∀ (m : ℕ) (F : GaussUnitaryHistory.Index),
      physicalN3PoleAmputatedChargeFrameRead p p leg leg poles poles m F =
        actualElectronPhysicalChargeRead p F
          (physicalN3PoleApproachEnergy p F leg (poles F) m) leg)
      ∧
    (∀ m : ℕ,
      Tendsto (fun F : GaussUnitaryHistory.Index =>
          physicalN3PoleAmputatedChargeFrameRead p p leg leg poles poles m F)
        GaussUnitaryHistory.sourceFilter
        (𝓝 (physicalN3PoleAmputatedChargeHistoryRead p p leg leg poles poles m)))
      ∧
    Tendsto (fun m : ℕ =>
        physicalN3PoleAmputatedChargeHistoryRead p p leg leg poles poles m)
      atTop
      (𝓝 (actualElectronSign leg +
        inner ℂ (physicalN3PoleState p leg poles)
          (physicalN3PoleCorrection p leg poles))) :=
  ⟨fun m F => physical_n3_pole_em_action_core_return p p leg leg poles poles m F,
   fun m F => physical_n3_pole_zero_transfer_charge_value p leg poles m F,
   fun m => physical_n3_pole_amputated_charge_source_return p p leg leg poles poles m,
   physical_n3_pole_zero_transfer_charge_return p leg poles⟩

end LowEnergy.GaussComposite.PhysicalN3SourceEnergy
