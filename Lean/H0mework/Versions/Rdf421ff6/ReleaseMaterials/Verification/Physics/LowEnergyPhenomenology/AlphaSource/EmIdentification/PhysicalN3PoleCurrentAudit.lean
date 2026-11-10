import H0mework.Versions.Rdf421ff6.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.PhysicalN3PoleCoulombPacket
import Lean.Util.CollectAxioms

set_option autoImplicit false
set_option maxRecDepth 32768
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.GaussComposite.PhysicalN3PoleCurrentAudit
open SaturationMonoid.PhysicsCore SaturationMonoid.PhysicsCore.LowEnergy
open GaussCoreHilbert CanonicalGradedSpatialSource ActualCompositeFieldCurrent
open PhysicalN3SourceEnergy ActualElectronWholeChargeSoft ActualElectronWholeNoetherObserver
open ActualElectronPhysicalJointInverse CanonicalGradedCharge PreparationPhysicalPhaseGaugeRealization
open GaussComposite.SourceGraph
open PreparationVacuumSourcePreparedResponse
open PreparationVacuumNoetherChart PreparationVacuumRawJointFeedback
open PreparationVacuumActionFieldLift PreparationVacuumFullFieldRiesz
open PreparationVacuumPhysicalCharacteristic PreparationVacuumPhysicalPoleSheet
open ActualDressedFullCoulomb ActualDressedCorrectedGreen ActualDressedEMPhysicalRead
open ActualDressedNoetherCoulombUnit ActualDressedEMTensorClock ActualDressedFrequencyHalf
open ActualDressedEMNativeMomentum ActualDressedAngularSpherePrice ActualDressedAngularSectorFourier
open ActualDressedAngularWholeChart ActualDressedEMZeroClockColumns ActualEMCarrierOwn
open ActualEMCurrentSplit ActualEMResponseSplit PreparationPhysicalElectronChargeUnitReturn
open Lean Elab Command MeasureTheory Filter Set
open scoped InnerProductSpace Topology Matrix SchwartzMap
attribute [local irreducible] physicalN3PoleState actualNoetherBackground
  actualElectronPhysicalUnit chargeReader
  physicalN3PoleNoetherObserver physicalN3PoleNoetherCurrent physicalN3PoleCurrent
  physicalN3PoleCurrentContact physicalN3PoleRawEMPoleObserver physicalN3RawEMReader
  physicalN3PoleCurrentPrice correctedGreen correctedEMTensor sourceStaticNoetherTensor
  physicalN3PoleStaticEMRead physicalN3PoleOtherEMRead physicalN3PoleChargePair
  physicalN3PoleTemporalCoulombPacket physicalN3PoleNonPureRead
  noetherPairScale sourceGeneratedScalarCEM physicalN3PoleEMCouplingExpression

theorem original_action_current (event : DressedEvent) (leg : CompositeLeg)
    (poles : N3SourceEnergyPoleSection event.momentum leg) (i : Fin 289) :
    physicalN3PoleCurrent event leg poles i =
      physicalN3PoleNoetherObserver event leg poles
        (PreparationVacuumRawJointFeedback.rawReader (fieldUnit i) event.momentum event.frame 0) :=
  physical_n3_pole_current_original_action event leg poles i

theorem original_complete_contact (event : DressedEvent) (leg : CompositeLeg)
    (poles : N3SourceEnergyPoleSection event.momentum leg) (i j : Fin 289) :
    physicalN3PoleCurrentContact event leg poles i j =
      physicalN3PoleNoetherObserver event leg poles
        (finiteRiesz event.frame (fun a b => noetherContactForm (fieldUnit i) (fieldUnit j)
          event.momentum (frameTest event.frame a) (frameTest event.frame b))) :=
  physical_n3_pole_contact_source_jet event leg poles i j

theorem original_contact_derivative (event : DressedEvent) (leg : CompositeLeg)
    (poles : N3SourceEnergyPoleSection event.momentum leg) (i j : Fin 289) :
    HasDerivAt (fun r : ℝ => physicalN3PoleNoetherObserver event leg poles
        (noetherReader (fieldUnit i) event.momentum event.frame (r • fieldUnit j)))
      (physicalN3PoleCurrentContact event leg poles i j) 0 :=
  physical_n3_pole_current_contact_generated event leg poles i j

theorem original_current_price (event : DressedEvent) (leg : CompositeLeg)
    (poles : N3SourceEnergyPoleSection event.momentum leg) (i : Fin 289) :
    ‖physicalN3PoleCurrent event leg poles i‖ ≤ 2*physicalN3PoleCurrentPrice event i :=
  physical_n3_pole_current_price event leg poles i

theorem source_charge_projection (event : DressedEvent) (leg : CompositeLeg)
    (poles : N3SourceEnergyPoleSection event.momentum leg) :
    (emCurrent (physicalN3PoleCurrent event leg poles)) 0 =
      (Stage10.ActionNormalization.phaseMomentum : ℂ) * physicalN3PoleRawEMPoleObserver event leg poles :=
  physical_n3_pole_current_em_charge event leg poles

theorem original_rmix_calibration_background_charge (event : DressedEvent) (leg : CompositeLeg)
    (poles : N3SourceEnergyPoleSection event.momentum leg) :
    physicalN3PoleNoetherCurrent event leg poles 0 =
      actualElectronSign leg +
        inner ℂ (physicalN3PoleState event.momentum leg poles)
          (physicalN3PoleCorrection event.momentum leg poles +
            physicalN3PoleEMCalibrationState event event.momentum leg poles) -
        inner ℂ (actualNoetherBackground event)
          (GaussUnitaryHistory.reader (physicalN3RawEMReader event) (actualNoetherBackground event)) :=
  (physical_n3_pole_noether_current_temporal event leg poles).trans
    (physical_n3_pole_raw_em_observer_charge event leg poles)

private theorem current_raw_pair_split {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (A Q : E→L[ℂ]E) (u : E) :
    inner ℂ u (A u) = inner ℂ u (Q u) + inner ℂ u ((A-Q) u) := by
  rw [sub_apply, inner_sub_right]
  abel

theorem literal_source_rmix_frame (event : DressedEvent) (leg : CompositeLeg)
    (poles : N3SourceEnergyPoleSection event.momentum leg) (m : ℕ) (F : GaussUnitaryHistory.Index) :
    physicalN3PoleRawEMFrameObserver event leg poles m F =
      actualElectronSign leg +
        inner ℂ (actualElectronPhysicalUnit event.momentum F
          (physicalN3PoleApproachEnergy event.momentum F leg (poles F) m) leg)
          (actualElectronPhysicalChargeCorrection event.momentum F
            (physicalN3PoleApproachEnergy event.momentum F leg (poles F) m) leg) +
        inner ℂ (actualElectronPhysicalUnit event.momentum F
          (physicalN3PoleApproachEnergy event.momentum F leg (poles F) m) leg)
          (physicalN3EMCalibrationReader event (actualElectronPhysicalUnit event.momentum F
            (physicalN3PoleApproachEnergy event.momentum F leg (poles F) m) leg)) -
        inner ℂ (prepared (sourceProfile event.epsilon event.precision))
          (physicalN3RawEMReader event (prepared (sourceProfile event.epsilon event.precision))) := by
  let u := actualElectronPhysicalUnit event.momentum F
    (physicalN3PoleApproachEnergy event.momentum F leg (poles F) m) leg
  let b := prepared (sourceProfile event.epsilon event.precision)
  have split : inner ℂ u (physicalN3RawEMReader event u) =
      inner ℂ u (chargeReader sourcePhaseGaugeLie u) +
        inner ℂ u (physicalN3EMCalibrationReader event u) :=
    current_raw_pair_split (physicalN3RawEMReader event) (chargeReader sourcePhaseGaugeLie) u
  have charge : inner ℂ u (chargeReader sourcePhaseGaugeLie u) =
      actualElectronSign leg + inner ℂ u (actualElectronPhysicalChargeCorrection event.momentum F
        (physicalN3PoleApproachEnergy event.momentum F leg (poles F) m) leg) :=
    actual_electron_physical_charge_read event.momentum F
      (physicalN3PoleApproachEnergy event.momentum F leg (poles F) m)
      (physical_n3_pole_energy_nonreal event.momentum F leg (poles F) m) leg
  show inner ℂ u (physicalN3RawEMReader event u) - inner ℂ b (physicalN3RawEMReader event b) = _
  exact (congrArg (fun v : ℂ => v - inner ℂ b (physicalN3RawEMReader event b)) split).trans
    (congrArg (fun v : ℂ => v + inner ℂ u (physicalN3EMCalibrationReader event u) -
      inner ℂ b (physicalN3RawEMReader event b)) charge)

theorem source_rmix_to_current_pole_return (event : DressedEvent) (leg : CompositeLeg)
    (poles : N3SourceEnergyPoleSection event.momentum leg) :
    Tendsto (fun m => physicalN3PoleRawEMHistoryObserver event leg poles m) atTop
      (𝓝 (physicalN3PoleNoetherCurrent event leg poles 0)) := by
  rw [physical_n3_pole_noether_current_temporal]
  exact physical_n3_pole_raw_em_observer_return event leg poles

theorem whole_field_maxwell (event : DressedEvent) (leg : CompositeLeg)
    (poles : N3SourceEnergyPoleSection event.momentum leg) (eps s sigma : ℝ)
    (n : PhysicalMomentum) (positive : 0<sigma) (regular : correctedDet event eps s sigma n≠0) :
    let p := frequencyRay eps s n
    let Q := frequencyQuantumCorrection event ((eps^2:ℝ) • n) p
      (dampedFourierClock (sourceFrequency eps s) sigma)
    nativeMomentumDivergence p (sourceEMExcitation p
        (physicalN3PoleCorrectedField event leg poles eps s sigma n)) =
      sourceEMExternalCurrent p (physicalN3PoleCurrent event leg poles) +
        sourceEMInducedCurrent p Q (physicalN3PoleCorrectedField event leg poles eps s sigma n) ∧
    sourceEMContinuity p
      (sourceEMExternalCurrent p (physicalN3PoleCurrent event leg poles) +
        sourceEMInducedCurrent p Q (physicalN3PoleCorrectedField event leg poles eps s sigma n)) = 0 :=
  physical_n3_pole_maxwell_generated event leg poles eps s sigma n positive regular

theorem literal_gram_noether_scale (event : DressedEvent) (leg : CompositeLeg)
    (poles : N3SourceEnergyPoleSection event.momentum leg) :
    emCoordinateCurrent (physicalN3PoleCurrent event leg poles) =
      noetherPairScale • physicalN3PoleNoetherCurrent event leg poles :=
  physical_n3_pole_coordinate_noether_unit event leg poles

theorem complete_corrected_four_parts (fieldEvent detector source : DressedEvent)
    (dLeg sLeg : CompositeLeg)
    (dPoles : N3SourceEnergyPoleSection detector.momentum dLeg)
    (sPoles : N3SourceEnergyPoleSection source.momentum sLeg) (eps s sigma : ℝ) (n : PhysicalMomentum) :
    emCurrentObservation (correctedGreen fieldEvent eps s sigma n)
        (physicalN3PoleCurrent detector dLeg dPoles) (physicalN3PoleCurrent source sLeg sPoles) =
      dotProduct (physicalN3PoleNoetherCurrent detector dLeg dPoles)
        ((noetherPairScale^2 • correctedEMTensor fieldEvent eps s sigma n)*ᵥ
          physicalN3PoleNoetherCurrent source sLeg sPoles) +
        physicalN3PoleNonPureRead fieldEvent detector source dLeg sLeg dPoles sPoles eps s sigma n :=
  physical_n3_pole_corrected_four_parts fieldEvent detector source dLeg sLeg dPoles sPoles eps s sigma n

theorem actual_static_charge_pair (fieldEvent detector source : DressedEvent)
    (dLeg sLeg : CompositeLeg)
    (dPoles : N3SourceEnergyPoleSection detector.momentum dLeg)
    (sPoles : N3SourceEnergyPoleSection source.momentum sLeg) (n : PhysicalMomentum) :
    physicalN3PoleStaticEMRead fieldEvent detector source dLeg sLeg dPoles sPoles n =
      physicalN3PoleRawEMPoleObserver detector dLeg dPoles *
        physicalN3PoleRawEMPoleObserver source sLeg sPoles *
          (sourceStaticNoetherTensor fieldEvent n 0 0 / (4*(Real.pi : ℂ))) +
        physicalN3PoleOtherEMRead fieldEvent detector source dLeg sLeg dPoles sPoles n :=
  physical_n3_pole_static_em_charge_pair fieldEvent detector source dLeg sLeg dPoles sPoles n

theorem original_standard_cem_read (fieldEvent detector source : DressedEvent)
    (dLeg sLeg : CompositeLeg)
    (dPoles : N3SourceEnergyPoleSection detector.momentum dLeg)
    (sPoles : N3SourceEnergyPoleSection source.momentum sLeg)
    (denominator : directionLeadingDenominator fieldEvent≠0)
    (checked : sourceStandardStaticRemainder fieldEvent=0) (n : PhysicalMomentum)
    (regular : directionLeadingRead fieldEvent n≠0) (unit : spatialSquare n=1) :
    physicalN3PoleStaticEMRead fieldEvent detector source dLeg sLeg dPoles sPoles n =
      physicalN3PoleRawEMPoleObserver detector dLeg dPoles *
        physicalN3PoleRawEMPoleObserver source sLeg sPoles * sourceGeneratedScalarCEM fieldEvent +
        physicalN3PoleOtherEMRead fieldEvent detector source dLeg sLeg dPoles sPoles n :=
  physical_n3_pole_standard_cem_charge_pair fieldEvent detector source dLeg sLeg dPoles sPoles
    denominator checked n regular unit

theorem original_single_four_pi_convolution (fieldEvent detector source : DressedEvent)
    (dLeg sLeg : CompositeLeg)
    (dPoles : N3SourceEnergyPoleSection detector.momentum dLeg)
    (sPoles : N3SourceEnergyPoleSection source.momentum sLeg)
    (chart : SourceWholeDirectionChart fieldEvent) (denominator : directionLeadingDenominator fieldEvent≠0)
    (checked : sourceStandardStaticRemainder fieldEvent=0) (test : 𝓢(PhysicalMomentum,ℂ)) (x : PhysicalMomentum) :
    physicalN3PoleTemporalCoulombPacket fieldEvent detector source dLeg sLeg dPoles sPoles chart test x =
      ∫ y : PhysicalMomentum,
        (physicalN3PoleChargePair detector source dLeg sLeg dPoles sPoles *
          sourceGeneratedScalarCEM fieldEvent) / (Real.sqrt (spatialSquare y) : ℂ) * emPacket test (x-y) :=
  physical_n3_pole_actual_coulomb_convolution fieldEvent detector source dLeg sLeg dPoles sPoles
    chart denominator checked test x

theorem original_spatial_coulomb_return (fieldEvent detector source : DressedEvent)
    (dLeg sLeg : CompositeLeg)
    (dPoles : N3SourceEnergyPoleSection detector.momentum dLeg)
    (sPoles : N3SourceEnergyPoleSection source.momentum sLeg)
    (chart : SourceWholeDirectionChart fieldEvent) (denominator : directionLeadingDenominator fieldEvent≠0)
    (checked : sourceStandardStaticRemainder fieldEvent=0) (test : 𝓢(PhysicalMomentum,ℂ)) (x : PhysicalMomentum) :
    Tendsto (fun scale : ℝ =>
        physicalN3PoleChargePair detector source dLeg sLeg dPoles sPoles *
          (noetherPairScale^2 * sectorFourierPacket fieldEvent
            (directionZeroClockEM fieldEvent 0 0) chart.eta scale test x))
      (nhdsWithin 0 (Ioi 0))
      (𝓝 (physicalN3PoleTemporalCoulombPacket fieldEvent detector source dLeg sLeg dPoles sPoles chart test x)) :=
  physical_n3_pole_coulomb_spatial_return fieldEvent detector source dLeg sLeg dPoles sPoles
    chart denominator checked test x

theorem actual_source_electron_noether_unit :
    sourceElectronNoetherUnit 0 = sourceElectronChargeUnit := sourceElectronNoetherUnit_generated 0

theorem actual_electron_unit_coupling (fieldEvent : DressedEvent) :
    physicalN3PoleEMCouplingExpression fieldEvent = sourceGeneratedScalarCEM fieldEvent /
      ((Stage10.ActionNormalization.phaseMomentum * sourceGeneratedPhysicalC fieldEvent : ℝ) : ℂ) :=
  physical_n3_pole_electron_unit_coupling fieldEvent

theorem actual_corrected_normalization_nonzero (fieldEvent : DressedEvent)
    (physical : 0<sourceGeneratedPhysicalC fieldEvent) :
    ((Stage10.ActionNormalization.phaseMomentum * sourceGeneratedPhysicalC fieldEvent : ℝ) : ℂ)≠0 :=
  physical_n3_pole_em_normalization_nonzero fieldEvent physical

theorem original_normalized_coulomb_read (fieldEvent detector source : DressedEvent)
    (dLeg sLeg : CompositeLeg)
    (dPoles : N3SourceEnergyPoleSection detector.momentum dLeg)
    (sPoles : N3SourceEnergyPoleSection source.momentum sLeg)
    (chart : SourceWholeDirectionChart fieldEvent) (denominator : directionLeadingDenominator fieldEvent≠0)
    (checked : sourceStandardStaticRemainder fieldEvent=0) (physical : 0<sourceGeneratedPhysicalC fieldEvent)
    (test : 𝓢(PhysicalMomentum,ℂ)) (x : PhysicalMomentum) :
    physicalN3PoleTemporalCoulombPacket fieldEvent detector source dLeg sLeg dPoles sPoles chart test x /
        ((Stage10.ActionNormalization.phaseMomentum * sourceGeneratedPhysicalC fieldEvent : ℝ) : ℂ) =
      ∫ y : PhysicalMomentum,
        physicalN3PoleChargePair detector source dLeg sLeg dPoles sPoles *
          physicalN3PoleEMCouplingExpression fieldEvent / (Real.sqrt (spatialSquare y) : ℂ) *
          emPacket test (x-y) :=
  physical_n3_pole_coulomb_normalized_read fieldEvent detector source dLeg sLeg dPoles sPoles
    chart denominator checked physical test x

private def children (info : ConstantInfo) : Array Name := Id.run do
  let mut result := info.type.getUsedConstants
  if let some value := info.value? (allowOpaque := true) then result := result ++ value.getUsedConstants
  if let .inductInfo value := info then result := result ++ value.ctors.toArray
  if let .recInfo value := info then
    for rule in value.rules do result := result ++ rule.rhs.getUsedConstants
  return result

private def closure (env : Environment) (roots : List Name) : CommandElabM NameSet := do
  let mut pending := roots
  let mut seen : NameSet := {}
  while !pending.isEmpty do
    let name := pending.head!
    pending := pending.tail!
    unless seen.contains name do
      let some info := env.checked.get.find? name | throwError m!"UNKNOWN {name}"
      pending := (children info).toList ++ pending
      seen := seen.insert name
  return seen

private def require (env : Environment) (root : Name) (targets : Array Name) : CommandElabM Unit := do
  let mut pending := [root]
  let mut seen : NameSet := {}
  let mut found : NameSet := {}
  while !pending.isEmpty && !(targets.all found.contains) do
    let name := pending.head!
    pending := pending.tail!
    unless seen.contains name do
      let some info := env.checked.get.find? name | throwError m!"UNKNOWN {name}"
      let next := children info
      for target in targets do
        if name == target || next.contains target then found := found.insert target
      pending := next.toList ++ pending
      seen := seen.insert name
  for target in targets do
    unless found.contains target do throwError m!"UNCONSUMED_DIRECT {root} {target}"

elab "#audit_physical_n3_pole_current" : command => do
  let env ← getEnv
  let modules := env.header.moduleNames
  let owner := fun name => (env.getModuleIdxFor? name).map fun i => modules[i.toNat]!
  let candidates := #[`H0mework.Versions.Rdf421ff6.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.PhysicalN3PoleCurrentSource, `H0mework.Versions.Rdf421ff6.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.PhysicalN3PoleCoulombRead, `H0mework.Versions.Rdf421ff6.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.PhysicalN3PoleCoulombPacket]
  let owned := env.constants.toList.filterMap fun (name, _) =>
    if (owner name).any candidates.contains then some name else none
  let mouths := #[
    ``PhysicalN3SourceEnergy.physicalN3PoleNoetherObserver,
    ``PhysicalN3SourceEnergy.physical_n3_pole_noether_observer_value,
    ``PhysicalN3SourceEnergy.physicalN3PoleCurrent,
    ``PhysicalN3SourceEnergy.physicalN3PoleCurrentContact,
    ``PhysicalN3SourceEnergy.physicalN3PoleCurrentPrice,
    ``PhysicalN3SourceEnergy.physical_n3_pole_current_price,
    ``PhysicalN3SourceEnergy.physical_n3_pole_current_generated,
    ``PhysicalN3SourceEnergy.physical_n3_pole_current_original_action,
    ``PhysicalN3SourceEnergy.physical_n3_pole_contact_source_jet,
    ``PhysicalN3SourceEnergy.physical_n3_pole_current_contact_generated,
    ``PhysicalN3SourceEnergy.physical_n3_pole_current_reader,
    ``PhysicalN3SourceEnergy.physical_n3_pole_current_em_charge,
    ``PhysicalN3SourceEnergy.physicalN3PoleCorrectedField,
    ``PhysicalN3SourceEnergy.physical_n3_pole_maxwell_generated,
    ``PhysicalN3SourceEnergy.physicalN3PoleNoetherCurrent,
    ``PhysicalN3SourceEnergy.physical_n3_pole_noether_current_temporal,
    ``PhysicalN3SourceEnergy.physical_n3_pole_coordinate_noether_unit,
    ``PhysicalN3SourceEnergy.physicalN3PoleNonPureRead,
    ``PhysicalN3SourceEnergy.physical_n3_pole_corrected_four_parts,
    ``PhysicalN3SourceEnergy.physicalN3PoleStaticEMRead,
    ``PhysicalN3SourceEnergy.physicalN3PoleOtherEMRead,
    ``PhysicalN3SourceEnergy.physical_n3_pole_static_em_charge_pair,
    ``PhysicalN3SourceEnergy.physical_n3_pole_standard_cem_charge_pair,
    ``PhysicalN3SourceEnergy.physicalN3PoleChargePair,
    ``PhysicalN3SourceEnergy.physicalN3PoleTemporalCoulombPacket,
    ``PhysicalN3SourceEnergy.physical_n3_pole_actual_coulomb_convolution,
    ``PhysicalN3SourceEnergy.physical_n3_pole_coulomb_spatial_return,
    ``PhysicalN3SourceEnergy.physicalN3PoleEMCouplingExpression,
    ``PhysicalN3SourceEnergy.physical_n3_pole_electron_unit_coupling,
    ``PhysicalN3SourceEnergy.physical_n3_pole_em_normalization_nonzero,
    ``PhysicalN3SourceEnergy.physical_n3_pole_coulomb_normalized_read]
  for mouth in mouths do
    unless owned.contains mouth do throwError m!"MISSING_MOUTH {mouth}"
  let tests := #[
    ``original_action_current,
    ``original_complete_contact,
    ``original_contact_derivative,
    ``original_current_price,
    ``source_charge_projection,
    ``original_rmix_calibration_background_charge,
    ``literal_source_rmix_frame,
    ``source_rmix_to_current_pole_return,
    ``whole_field_maxwell,
    ``literal_gram_noether_scale,
    ``complete_corrected_four_parts,
    ``actual_static_charge_pair,
    ``original_standard_cem_read,
    ``original_single_four_pi_convolution,
    ``original_spatial_coulomb_return,
    ``actual_source_electron_noether_unit,
    ``actual_electron_unit_coupling,
    ``actual_corrected_normalization_nonzero,
    ``original_normalized_coulomb_read]
  let direct := #[
    (``PhysicalN3SourceEnergy.physical_n3_pole_current_original_action, #[
      ``LowEnergy.PreparationVacuumNoetherChart.noetherReader_source]),
    (``PhysicalN3SourceEnergy.physical_n3_pole_contact_source_jet, #[
      ``LowEnergy.PreparationVacuumNoetherChart.noetherReaderContact_source]),
    (``PhysicalN3SourceEnergy.physical_n3_pole_current_contact_generated, #[
      ``LowEnergy.PreparationVacuumNoetherChart.noetherReader_generated]),
    (``PhysicalN3SourceEnergy.physical_n3_pole_current_price, #[
      ``LowEnergy.PreparationVacuumFullFieldRiesz.finiteRiesz_price,
      ``LowEnergy.GaussComposite.ActualElectronWholeNoetherObserver.actual_noether_background_norm]),
    (``PhysicalN3SourceEnergy.physical_n3_pole_current_em_charge, #[
      ``LowEnergy.GaussComposite.ActualDressedConstraintRead.source_reader_initial]),
    (``PhysicalN3SourceEnergy.physical_n3_pole_maxwell_generated, #[
      ``LowEnergy.GaussComposite.ActualDressedEMPhysicalRead.actual_corrected_maxwell_generated,
      ``PhysicalN3SourceEnergy.physicalN3PoleCurrent]),
    (``PhysicalN3SourceEnergy.physical_n3_pole_noether_current_temporal, #[
      ``PhysicalN3SourceEnergy.physical_n3_pole_current_em_charge]),
    (``PhysicalN3SourceEnergy.physical_n3_pole_corrected_four_parts, #[
      ``LowEnergy.GaussComposite.ActualEMResponseSplit.em_response_four_parts,
      ``PhysicalN3SourceEnergy.physical_n3_pole_coordinate_noether_unit]),
    (``PhysicalN3SourceEnergy.physical_n3_pole_static_em_charge_pair, #[
      ``PhysicalN3SourceEnergy.physical_n3_pole_noether_current_temporal]),
    (``PhysicalN3SourceEnergy.physical_n3_pole_standard_cem_charge_pair, #[
      ``LowEnergy.GaussComposite.ActualDressedEMPhysicalRead.source_static_standard_iff,
      ``PhysicalN3SourceEnergy.physical_n3_pole_static_em_charge_pair]),
    (``PhysicalN3SourceEnergy.physical_n3_pole_actual_coulomb_convolution, #[
      ``LowEnergy.GaussComposite.ActualDressedEMPhysicalRead.source_standard_actual_coulomb_convolution]),
    (``PhysicalN3SourceEnergy.physical_n3_pole_coulomb_spatial_return, #[
      ``LowEnergy.GaussComposite.ActualDressedEMPhysicalRead.source_standard_coulomb_spatial_return]),
    (``PhysicalN3SourceEnergy.physical_n3_pole_electron_unit_coupling, #[
      ``LowEnergy.PreparationPhysicalElectronChargeUnitReturn.sourceElectronNoetherUnit_generated]),
    (``PhysicalN3SourceEnergy.physical_n3_pole_em_normalization_nonzero, #[
      ``SaturationMonoid.PhysicsCore.Stage10.ActionNormalization.phaseMomentum_positive]),
    (``PhysicalN3SourceEnergy.physical_n3_pole_coulomb_normalized_read, #[
      ``PhysicalN3SourceEnergy.physical_n3_pole_actual_coulomb_convolution,
      ``PhysicalN3SourceEnergy.physical_n3_pole_electron_unit_coupling]),
    (``original_rmix_calibration_background_charge, #[
      ``PhysicalN3SourceEnergy.physical_n3_pole_raw_em_observer_charge]),
    (``actual_source_electron_noether_unit, #[
      ``LowEnergy.PreparationPhysicalElectronChargeUnitReturn.sourceElectronIndependent_current]),
    (``literal_source_rmix_frame, #[
      ``LowEnergy.GaussComposite.ActualElectronPhysicalJointInverse.actual_electron_physical_charge_read,
      ``PhysicalN3SourceEnergy.physical_n3_pole_energy_nonreal]),
    (``source_rmix_to_current_pole_return, #[
      ``PhysicalN3SourceEnergy.physical_n3_pole_raw_em_observer_return,
      ``PhysicalN3SourceEnergy.physical_n3_pole_noether_current_temporal])]
  for (mouth, targets) in direct do require env mouth targets
  let all ← closure env (owned ++ tests.toList)
  let anchors := #[
    ``SaturationMonoid.PhysicsCore.StageNineEnrichedProofFreeSource.positiveSmoothUnifiedSource,
    ``SaturationMonoid.PhysicsCore.Stage9C.Material.SpinPair.actual,
    ``LowEnergy.PreparationVacuumNoetherChart.noetherReader_source,
    ``LowEnergy.PreparationVacuumRawJointFeedback.rawReader,
    ``LowEnergy.PreparationVacuumFullFieldRiesz.finiteRiesz,
    ``LowEnergy.PreparationVacuumFullFieldRiesz.finitePrice,
    ``LowEnergy.PreparationVacuumNoetherChart.noetherReaderContact_source,
    ``LowEnergy.GaussComposite.PhysicalN3SourceEnergy.physicalN3PoleState,
    ``LowEnergy.GaussComposite.PhysicalN3SourceEnergy.physicalN3PoleCorrection,
    ``LowEnergy.GaussComposite.PhysicalN3SourceEnergy.physicalN3PoleEMCalibrationState,
    ``LowEnergy.GaussComposite.ActualElectronPhysicalJointInverse.actualElectronPhysicalChargeCorrection,
    ``LowEnergy.GaussComposite.ActualElectronWholeNoetherObserver.actualNoetherBackground,
    ``LowEnergy.GaussComposite.SourceGraph.prepared,
    ``LowEnergy.GaussComposite.ActualEMCurrentSplit.emCurrentForce,
    ``LowEnergy.GaussComposite.ActualEMCurrentSplit.emCurrentResidual,
    ``LowEnergy.GaussComposite.ActualDressedCorrectedGreen.correctedGreen,
    ``LowEnergy.GaussComposite.ActualDressedEMPhysicalRead.actual_corrected_maxwell_generated,
    ``LowEnergy.GaussComposite.ActualDressedEMPhysicalRead.sourceEMInducedCurrent,
    ``LowEnergy.GaussComposite.ActualDressedEMPhysicalRead.sourceStaticNoetherTensor,
    ``LowEnergy.GaussComposite.ActualDressedEMPhysicalRead.sourceGeneratedScalarCEM,
    ``LowEnergy.GaussComposite.ActualDressedEMPhysicalRead.sourceGeneratedPhysicalC,
    ``LowEnergy.GaussComposite.ActualDressedNoetherCoulombUnit.noetherPairScale,
    ``LowEnergy.PreparationPhysicalElectronChargeUnitReturn.sourceElectronNoetherUnit,
    ``LowEnergy.PreparationPhysicalElectronChargeUnitReturn.sourceElectronIndependent_current,
    ``LowEnergy.GaussComposite.ActualDressedEMPhysicalRead.source_standard_actual_coulomb_convolution]
  for anchor in anchors do
    unless all.contains anchor do throwError m!"UNCONSUMED_SOURCE {anchor}"
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  let mut axiomCount : Nat := 0
  let mut opaqueCount : Nat := 0
  for name in all.toArray do
    let some info := env.checked.get.find? name | throwError m!"UNKNOWN {name}"
    if info.isUnsafe || info.isPartial then throwError m!"UNTRUSTED {name}"
    match info with
    | .defnInfo _ | .thmInfo _ | .opaqueInfo _ =>
      unless (info.value? (allowOpaque := true)).isSome do throwError m!"UNREAD {name}"
    | _ => pure ()
    if let .opaqueInfo _ := info then opaqueCount := opaqueCount + 1
    if let .axiomInfo _ := info then
      axiomCount := axiomCount + 1
      unless allowed.contains name do throwError m!"UNAUTHORIZED_AXIOM {name}"
  for name in #[`SaturationMonoid.StandardModelConstraint.alphaEMIntegerDenominator,
      `SaturationMonoid.StandardModelConstraint.alphaEMFromIntegerConstraint,
      `SaturationMonoid.StandardModelConstraint.gutWeakMixingInformationRatio,
      `SaturationMonoid.StandardModelConstraint.alphaStrongDisplayed] do
    if all.contains name then throwError m!"TARGET_CONTAMINATION {name}"
  let strings := fun xs : Array Name => xs.map (fun n => n.toString)
  let data := Json.mkObj [
    ("public", toJson (strings mouths)),
    ("owned", toJson (strings owned.toArray)),
    ("tests", toJson (strings tests)),
    ("anchors", toJson (strings anchors)),
    ("direct", toJson (direct.map (fun (n, ns) => (n.toString, strings ns)))),
    ("nodes", toJson all.toArray.size),
    ("dependency_names", toJson ((strings all.toArray).qsort (fun a b => a < b))),
    ("opaque_read", toJson opaqueCount),
    ("axioms", toJson axiomCount),
    ("unknown", toJson (0 : Nat)),
    ("unsafe", toJson (0 : Nat)),
    ("partial", toJson (0 : Nat)),
    ("target", toJson (0 : Nat))]
  if let some path ← liftIO (IO.getEnv "PHYSICAL_N3_POLE_CURRENT_AUDIT_OUTPUT") then
    liftIO <| IO.FS.writeFile path (data.pretty ++ "\n")
  logInfo m!"PHYSICAL_N3_POLE_CURRENT_PASS public={mouths.size} owned={owned.length} tests={tests.size} nodes={all.toArray.size} anchors={anchors.size} direct={direct.size} opaque_all_read={opaqueCount} axioms={axiomCount} unknown=0 unsafe=0 partial=0"

set_option maxHeartbeats 12000000 in
#audit_physical_n3_pole_current

#print axioms original_action_current
#print axioms original_complete_contact
#print axioms original_rmix_calibration_background_charge
#print axioms complete_corrected_four_parts
#print axioms original_single_four_pi_convolution
#print axioms original_normalized_coulomb_read

end LowEnergy.GaussComposite.PhysicalN3PoleCurrentAudit
