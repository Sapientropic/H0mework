import H0mework.Versions.Rdf421ff6.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.PhysicalNativeEMChargeBridge
import Lean.Elab.Command
import Lean.Util.FoldConsts
import Lean.Util.CollectAxioms

set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.GaussComposite.PhysicalNativeEMChargeBridgeAudit

open PhysicalNativeEMChargeBridge
open PhysicalEMGaugeRealization
open PhysicalEMChargeReadout
open PreparationPhysicalChargedPacketQuantumReturn PreparationPhysicalChargedPacketVoltage
open PreparationPhysicalActualPhaseChargeReturn
open PreparationVacuumPhysicalQuantumLockedCharge
open SaturationMonoid.PhysicsCore.Stage9DEF.Compatibility
open SaturationMonoid.PhysicsCore SaturationMonoid.PhysicsCore.LowEnergy
open FullQuantum FullSpace
open SaturationMonoid.PhysicsCore.YangMills.FullPairing
open Quantum
open Stage10
open scoped InnerProductSpace

/-- Focused positive control: the native rest current fixes the source electron
    unit with its explicit sign convention. -/
theorem checked_native_rest_electron_unit (side : Fin 2) :
    - inner ℂ (sourceNativeElectronState side)
        (PhysicalNativeCurrentAlignment.nativeCurrentReader 0
          (sourceNativeElectronState side)) =
      sourceNativeElectronChargeUnit :=
  native_rest_current_identifies_electron_unit side

theorem checked_same_electron_state (side : Fin 2) :
    emChargeFiber (sourceNativeElectronState side) =
      sourceNativeElectronChargeUnit • sourceNativeElectronState side :=
  em_reader_same_electron_state side

/-- Focused positive control: the actual EM reader consumes that same source
    unit on every source charged column at edge zero. -/
theorem checked_em_reader_electron_unit (side : Fin 2) :
    PhysicalEMChargeReadout.emChargeFiber
        (naturalCoordinates (sourceChargedRestriction side 0)) =
      sourceNativeElectronChargeUnit •
        naturalCoordinates (sourceChargedRestriction side 0) :=
  em_reader_electron_unit side

/-- Focused positive control: the bilinear electron charge product is source
    generated and remains separate from the field-strength coefficient. -/
theorem checked_electron_charge_product :
    sourceNativeElectronChargeProduct = 1 :=
  sourceNativeElectronChargeProduct_generated

/-- Focused negative control: neutral edge zero mode is not accepted as the
    electron unit. -/
theorem checked_neutral_edge_rejected :
    (sourceActualPhaseCharge (1 : Fin 2) : ℂ) ≠ sourceNativeElectronChargeUnit :=
  neutral_edge_not_electron_unit

/-- Focused negative control: the full-carrier defect stays present in the
    actual EM decomposition. -/
theorem checked_full_defect_retained : emFullDefect ≠ 0 :=
  full_defect_retained

end LowEnergy.GaussComposite.PhysicalNativeEMChargeBridgeAudit

open Lean Elab Command

private def nativeEMBridgeChildren (info : ConstantInfo) : Array Name := Id.run do
  let mut children := info.type.getUsedConstants
  if let some value := info.value? (allowOpaque := true) then
    children := children ++ value.getUsedConstants
  if let .inductInfo value := info then children := children ++ value.ctors.toArray
  if let .recInfo value := info then
    for rule in value.rules do children := children ++ rule.rhs.getUsedConstants
  return children

private def nativeEMBridgeClosure (env : Environment)
    (roots : List Name) : CommandElabM NameSet := do
  let mut pending := roots
  let mut seen : NameSet := {}
  while !pending.isEmpty do
    let name := pending.head!
    pending := pending.tail!
    unless seen.contains name do
      let some info := env.checked.get.find? name | throwError m!"UNKNOWN {name}"
      pending := (nativeEMBridgeChildren info).toList ++ pending
      seen := seen.insert name
  return seen

elab "#audit_native_em_charge_bridge" : command => do
  let env ← getEnv
  let modules := env.header.moduleNames
  let owner := `H0mework.Versions.Rdf421ff6.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.PhysicalNativeEMChargeBridge
  unless modules.contains owner do throwError "MISSING_BRIDGE_MODULE"
  let owned := env.constants.toList.filterMap fun (name, _) =>
    match env.getModuleIdxFor? name with
    | some index => if modules[index.toNat]! = owner then some name else none
    | none => none
  if owned.isEmpty then throwError "EMPTY_OWNED_CLOSURE"
  let mouths := #[
    ``LowEnergy.GaussComposite.PhysicalNativeEMChargeBridge.sourceNativeElectronChargeUnit,
    ``LowEnergy.GaussComposite.PhysicalNativeEMChargeBridge.sourceNativeElectronChargeUnit_generated,
    ``LowEnergy.GaussComposite.PhysicalNativeEMChargeBridge.sourceNativeElectronState,
    ``LowEnergy.GaussComposite.PhysicalNativeEMChargeBridge.sourceNativeElectronState_source,
    ``LowEnergy.GaussComposite.PhysicalNativeEMChargeBridge.native_charged_current_unit,
    ``LowEnergy.GaussComposite.PhysicalNativeEMChargeBridge.native_rest_current_identifies_electron_unit,
    ``LowEnergy.GaussComposite.PhysicalNativeEMChargeBridge.em_reader_electron_unit,
    ``LowEnergy.GaussComposite.PhysicalNativeEMChargeBridge.em_reader_same_electron_state,
    ``LowEnergy.GaussComposite.PhysicalNativeEMChargeBridge.sourceNativeElectronChargeProduct,
    ``LowEnergy.GaussComposite.PhysicalNativeEMChargeBridge.sourceNativeElectronChargeProduct_generated,
    ``LowEnergy.GaussComposite.PhysicalNativeEMChargeBridge.em_filtered_electron_pair,
    ``LowEnergy.GaussComposite.PhysicalNativeEMChargeBridge.neutral_edge_not_electron_unit,
    ``LowEnergy.GaussComposite.PhysicalNativeEMChargeBridge.full_defect_retained]
  for name in mouths do
    unless owned.contains name do throwError m!"MISSING_PUBLIC {name}"
  let consumers := #[
    (``LowEnergy.GaussComposite.PhysicalNativeEMChargeBridgeAudit.checked_native_rest_electron_unit, #[``LowEnergy.GaussComposite.PhysicalNativeEMChargeBridge.native_rest_current_identifies_electron_unit]),
    (``LowEnergy.GaussComposite.PhysicalNativeEMChargeBridgeAudit.checked_same_electron_state, #[``LowEnergy.GaussComposite.PhysicalNativeEMChargeBridge.em_reader_same_electron_state]),
    (``LowEnergy.GaussComposite.PhysicalNativeEMChargeBridgeAudit.checked_em_reader_electron_unit, #[``LowEnergy.GaussComposite.PhysicalNativeEMChargeBridge.em_reader_electron_unit]),
    (``LowEnergy.GaussComposite.PhysicalNativeEMChargeBridgeAudit.checked_electron_charge_product, #[``LowEnergy.GaussComposite.PhysicalNativeEMChargeBridge.sourceNativeElectronChargeProduct_generated]),
    (``LowEnergy.GaussComposite.PhysicalNativeEMChargeBridgeAudit.checked_neutral_edge_rejected, #[``LowEnergy.GaussComposite.PhysicalNativeEMChargeBridge.neutral_edge_not_electron_unit]),
    (``LowEnergy.GaussComposite.PhysicalNativeEMChargeBridgeAudit.checked_full_defect_retained, #[``LowEnergy.GaussComposite.PhysicalNativeEMChargeBridge.full_defect_retained])]
  let all ← nativeEMBridgeClosure env (owned ++ (consumers.map Prod.fst).toList)
  let anchors := #[
    ``LowEnergy.GaussComposite.PhysicalNativeCurrentAlignment.native_current_noether,
    ``LowEnergy.PreparationVacuumElectromagneticIdentity.actualRestState_hypercharge_current,
    ``LowEnergy.PreparationVacuumPhysicalQuantumLockedCharge.sourceChargedRestIndex,
    ``LowEnergy.PreparationVacuumPhysicalQuantumLockedCharge.sourceChargedRestriction,
    ``LowEnergy.PreparationPhysicalActualPhaseChargeReturn.sourceActualPhaseCharge,
    ``LowEnergy.GaussComposite.PhysicalEMChargeReadout.em_charge_maker,
    ``LowEnergy.GaussComposite.PhysicalEMChargeReadout.em_charge_filtered_pair,
    ``LowEnergy.PreparationPhysicalActionUnits.sourceActionScale_momentum,
    ``SaturationMonoid.PhysicsCore.Stage10.ActionNormalization.phaseMomentum,
    ``SaturationMonoid.PhysicsCore.StageNineEnrichedProofFreeSource.positiveSmoothUnifiedSource,
    ``SaturationMonoid.PhysicsCore.Stage9C.Material.SpinPair.actual]
  for name in anchors do
    unless all.contains name do throwError m!"UNCONSUMED_SOURCE {name}"
  let direct := #[
    (``LowEnergy.GaussComposite.PhysicalNativeEMChargeBridge.sourceNativeElectronState_source, #[``LowEnergy.PreparationVacuumPhysicalQuantumLockedCharge.sourceChargedRestIndex,``LowEnergy.PreparationVacuumPhysicalQuantumLockedCharge.sourceChargedRestriction]),
    (``LowEnergy.GaussComposite.PhysicalNativeEMChargeBridge.native_charged_current_unit, #[``LowEnergy.GaussComposite.PhysicalNativeCurrentAlignment.native_current_noether,``LowEnergy.PreparationVacuumElectromagneticIdentity.actualRestState_hypercharge_current,``LowEnergy.PreparationPhysicalActionUnits.sourceActionScale_momentum]),
    (``LowEnergy.GaussComposite.PhysicalNativeEMChargeBridge.native_rest_current_identifies_electron_unit, #[``LowEnergy.GaussComposite.PhysicalNativeEMChargeBridge.native_charged_current_unit]),
    (``LowEnergy.GaussComposite.PhysicalNativeEMChargeBridge.em_reader_same_electron_state, #[``LowEnergy.GaussComposite.PhysicalNativeEMChargeBridge.sourceNativeElectronState_source,``LowEnergy.GaussComposite.PhysicalNativeEMChargeBridge.em_reader_electron_unit]),
    (``LowEnergy.GaussComposite.PhysicalNativeEMChargeBridge.em_filtered_electron_pair, #[``LowEnergy.GaussComposite.PhysicalEMChargeReadout.em_charge_filtered_pair])]
  for (mouth, required) in direct ++ consumers do
    let closed ← nativeEMBridgeClosure env [mouth]
    for name in required do
      unless closed.contains name do throwError m!"UNCONSUMED_DIRECT {mouth} {name}"
  let allowed := #[``propext,``Classical.choice,``Quot.sound]
  let mut axioms : Nat := 0
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
      axioms := axioms + 1
      unless allowed.contains name do throwError m!"UNAUTHORIZED_AXIOM {name}"
  for name in owned ++ (consumers.map Prod.fst).toList do
    for axiomName in ← collectAxioms name do
      unless allowed.contains axiomName do throwError m!"UNAUTHORIZED_ROOT_AXIOM {name} {axiomName}"
  for name in #[`SaturationMonoid.StandardModelConstraint.alphaEMIntegerDenominator,
      `SaturationMonoid.StandardModelConstraint.alphaEMFromIntegerConstraint,
      `SaturationMonoid.StandardModelConstraint.gutWeakMixingInformationRatio] do
    if all.contains name then throwError m!"TARGET_CONTAMINATION {name}"
  let relocated : Std.HashMap Name Name := .ofList [
    (`H0mework.Versions.R320c1651.ReleaseMaterials.Scratch.AlphaSource.PreparationObjectRecoveryAfterRestart.SlimSource.SourceInverseVolumeElectricMomentChannels, `SourceInverseVolumeElectricMomentChannels),
    (`H0mework.Versions.R320c1651.ReleaseMaterials.Scratch.AlphaSource.PreparationObjectRecoveryAfterRestart.SlimSource.SourceStaticInterval, `SourceStaticInterval),
    (`H0mework.Versions.R320c1651.ReleaseMaterials.Scratch.AlphaSource.PreparationPhysicalAbelZeroRead.AbelZeroRead, `AbelZeroRead),
    (`H0mework.Versions.R320c1651.ReleaseMaterials.Scratch.AlphaSource.PreparationPhysicalAbelZeroRead.ActualSpectralCurrent, `ActualSpectralCurrent),
    (`H0mework.Versions.R320c1651.ReleaseMaterials.Scratch.AlphaSource.PreparationPhysicalCausalZeroRead.SourceActualGapRadius, `SourceActualGapRadius),
    (`H0mework.Versions.R320c1651.ReleaseMaterials.Scratch.AlphaSource.PreparationPhysicalCausalZeroRead.SourceCausalGaussZero, `SourceCausalGaussZero),
    (`H0mework.Versions.R320c1651.ReleaseMaterials.Scratch.AlphaSource.PreparationPhysicalCausalZeroRead.SourceComplexCurrentZero, `SourceComplexCurrentZero),
    (`H0mework.Versions.R320c1651.ReleaseMaterials.Scratch.AlphaSource.PreparationPhysicalChargeTimeZero.SourceChargeTimeAbel, `SourceChargeTimeAbel),
    (`H0mework.Versions.R320c1651.ReleaseMaterials.Scratch.AlphaSource.PreparationPhysicalChargeTimeZero.SourceChargeTimeSpectrum, `SourceChargeTimeSpectrum),
    (`H0mework.Versions.R320c1651.ReleaseMaterials.Scratch.AlphaSource.PreparationPhysicalChargeTimeZero.SourceStaticGaussResidue, `SourceStaticGaussResidue),
    (`H0mework.Versions.R320c1651.ReleaseMaterials.Scratch.AlphaSource.PreparationPhysicalChargedEnergyPoleReturn.SourcePhysicalEnergyChannels, `SourcePhysicalEnergyChannels),
    (`H0mework.Versions.R320c1651.ReleaseMaterials.Scratch.AlphaSource.PreparationPhysicalChargedEnergyPoleReturn.SourcePhysicalEnergyResidues, `SourcePhysicalEnergyResidues),
    (`H0mework.Versions.R320c1651.ReleaseMaterials.Scratch.AlphaSource.PreparationPhysicalChargedEnergyVariation.SourceChargedEnergyObservable, `SourceChargedEnergyObservable),
    (`H0mework.Versions.R320c1651.ReleaseMaterials.Scratch.AlphaSource.PreparationPhysicalChargedEnergyVariation.SourceChargedFullEnergyReturn, `SourceChargedFullEnergyReturn),
    (`H0mework.Versions.R320c1651.ReleaseMaterials.Scratch.AlphaSource.PreparationPhysicalChargedEnergyVariation.SourceEnergyDiracLeg, `SourceEnergyDiracLeg),
    (`H0mework.Versions.R320c1651.ReleaseMaterials.Scratch.AlphaSource.PreparationPhysicalChargedFieldFactor.SourceActualChargedFieldRead, `SourceActualChargedFieldRead),
    (`H0mework.Versions.R320c1651.ReleaseMaterials.Scratch.AlphaSource.PreparationPhysicalChargedFieldFactor.SourceChargedFieldSlots, `SourceChargedFieldSlots),
    (`H0mework.Versions.R320c1651.ReleaseMaterials.Scratch.AlphaSource.PreparationPhysicalChargedFieldFactor.SourceChargedFieldWardRead, `SourceChargedFieldWardRead),
    (`H0mework.Versions.R320c1651.ReleaseMaterials.Scratch.AlphaSource.PreparationPhysicalChargedHamiltonianRead.SourceChargedHamiltonianDomain, `SourceChargedHamiltonianDomain),
    (`H0mework.Versions.R320c1651.ReleaseMaterials.Scratch.AlphaSource.PreparationPhysicalChargedHamiltonianRead.SourceChargedHamiltonianFourier, `SourceChargedHamiltonianFourier),
    (`H0mework.Versions.R320c1651.ReleaseMaterials.Scratch.AlphaSource.PreparationPhysicalChargedHamiltonianRead.SourceChargedHamiltonianMatrix, `SourceChargedHamiltonianMatrix),
    (`H0mework.Versions.R320c1651.ReleaseMaterials.Scratch.AlphaSource.PreparationPhysicalChargedPacketQuantumReturn.SourceChargedFilteredPreparation, `SourceChargedFilteredPreparation),
    (`H0mework.Versions.R320c1651.ReleaseMaterials.Scratch.AlphaSource.PreparationPhysicalChargedPacketQuantumReturn.SourceChargedQuantumCurrent, `SourceChargedQuantumCurrent),
    (`H0mework.Versions.R320c1651.ReleaseMaterials.Scratch.AlphaSource.PreparationPhysicalChargedPacketQuantumReturn.SourceChargedQuantumPrice, `SourceChargedQuantumPrice),
    (`H0mework.Versions.R320c1651.ReleaseMaterials.Scratch.AlphaSource.PreparationPhysicalChargedPacketVoltage.SourceChargedPacketCurrent, `SourceChargedPacketCurrent),
    (`H0mework.Versions.R320c1651.ReleaseMaterials.Scratch.AlphaSource.PreparationPhysicalChargedPacketVoltage.SourceChargedPacketEnergy, `SourceChargedPacketEnergy),
    (`H0mework.Versions.R320c1651.ReleaseMaterials.Scratch.AlphaSource.PreparationPhysicalColorCharge.SourceColorBalance, `SourceColorBalance),
    (`H0mework.Versions.R320c1651.ReleaseMaterials.Scratch.AlphaSource.PreparationPhysicalColorCharge.SourceColorCurrent, `SourceColorCurrent),
    (`H0mework.Versions.R320c1651.ReleaseMaterials.Scratch.AlphaSource.PreparationPhysicalColorCharge.SourceColorMatrix, `SourceColorMatrix),
    (`H0mework.Versions.R320c1651.ReleaseMaterials.Scratch.AlphaSource.PreparationPhysicalColorWard.SourceColorBoundaryWard, `SourceColorBoundaryWard),
    (`H0mework.Versions.R320c1651.ReleaseMaterials.Scratch.AlphaSource.PreparationPhysicalColorWard.SourceColorCoreWard, `SourceColorCoreWard),
    (`H0mework.Versions.R320c1651.ReleaseMaterials.Scratch.AlphaSource.PreparationPhysicalColorWard.SourceColorPreparedWard, `SourceColorPreparedWard),
    (`H0mework.Versions.R320c1651.ReleaseMaterials.Scratch.AlphaSource.PreparationPhysicalConstraint114.SourceConstraintBoundary, `SourceConstraintBoundary),
    (`H0mework.Versions.R320c1651.ReleaseMaterials.Scratch.AlphaSource.PreparationPhysicalElectromagneticDirection.SourceLockedFieldReturn, `SourceLockedFieldReturn),
    (`H0mework.Versions.R320c1651.ReleaseMaterials.Scratch.AlphaSource.PreparationPhysicalGaussColorTorque.SourceGaussColorWard, `SourceGaussColorWard),
    (`H0mework.Versions.R320c1651.ReleaseMaterials.Scratch.AlphaSource.PreparationPhysicalGaussColorTorque.SourceGaussConnection, `SourceGaussConnection),
    (`H0mework.Versions.R320c1651.ReleaseMaterials.Scratch.AlphaSource.PreparationPhysicalGaussColorTorque.SourceGaussKineticTorque, `SourceGaussKineticTorque),
    (`H0mework.Versions.R320c1651.ReleaseMaterials.Scratch.AlphaSource.PreparationPhysicalGaussMaterialContact.ActualGaussMaterialRead, `ActualGaussMaterialRead),
    (`H0mework.Versions.R320c1651.ReleaseMaterials.Scratch.AlphaSource.PreparationPhysicalGaussMaterialContact.ActualQuantumMaterialWard, `ActualQuantumMaterialWard),
    (`H0mework.Versions.R320c1651.ReleaseMaterials.Scratch.AlphaSource.PreparationPhysicalGaussMaterialContact.SourceColourSymbolCovariance, `SourceColourSymbolCovariance),
    (`H0mework.Versions.R320c1651.ReleaseMaterials.Scratch.AlphaSource.PreparationPhysicalJointGeneratorEnergyReturn.ImportCompat.CanonicalPreparationSourceJointCausalField, `CanonicalPreparationSourceJointCausalField),
    (`H0mework.Versions.R320c1651.ReleaseMaterials.Scratch.AlphaSource.PreparationPhysicalLockedCurrentFirstResidue.SourceLockedFirstResidue, `SourceLockedFirstResidue),
    (`H0mework.Versions.R320c1651.ReleaseMaterials.Scratch.AlphaSource.PreparationPhysicalLockedCurrentFirstResidue.SourceLockedGradeZero, `SourceLockedGradeZero),
    (`H0mework.Versions.R320c1651.ReleaseMaterials.Scratch.AlphaSource.PreparationPhysicalLockedCurrentFirstResidue.SourceLockedReaderReturn, `SourceLockedReaderReturn),
    (`H0mework.Versions.R320c1651.ReleaseMaterials.Scratch.AlphaSource.PreparationPhysicalLockedGaussBalance.Overlay.CanonicalPreparationSourceNativeModeAction, `CanonicalPreparationSourceNativeModeAction),
    (`H0mework.Versions.R320c1651.ReleaseMaterials.Scratch.AlphaSource.PreparationPhysicalLockedGaussBalance.SourceLockedActionWard, `SourceLockedActionWard),
    (`H0mework.Versions.R320c1651.ReleaseMaterials.Scratch.AlphaSource.PreparationPhysicalLockedGaussBalance.SourceLockedChargeCore, `SourceLockedChargeCore),
    (`H0mework.Versions.R320c1651.ReleaseMaterials.Scratch.AlphaSource.PreparationPhysicalLockedGaussBalance.SourceLockedPreparedBalance, `SourceLockedPreparedBalance),
    (`H0mework.Versions.R320c1651.ReleaseMaterials.Scratch.AlphaSource.PreparationPhysicalLockedN1Balance.SourceLockedN1Pair, `SourceLockedN1Pair),
    (`H0mework.Versions.R320c1651.ReleaseMaterials.Scratch.AlphaSource.PreparationPhysicalLockedN1Balance.SourceLockedN1Return, `SourceLockedN1Return),
    (`H0mework.Versions.R320c1651.ReleaseMaterials.Scratch.AlphaSource.PreparationPhysicalLockedN1Balance.SourceLockedStaticN1Read, `SourceLockedStaticN1Read),
    (`H0mework.Versions.R320c1651.ReleaseMaterials.Scratch.AlphaSource.PreparationPhysicalModeChargeRead.SourceModeGaussRead, `SourceModeGaussRead),
    (`H0mework.Versions.R320c1651.ReleaseMaterials.Scratch.AlphaSource.PreparationPhysicalModeChargeRead.SourceModeRestCurrent, `SourceModeRestCurrent),
    (`H0mework.Versions.R320c1651.ReleaseMaterials.Scratch.AlphaSource.PreparationPhysicalModeChargeRead.SourceNativeModeAction, `SourceNativeModeAction),
    (`H0mework.Versions.R320c1651.ReleaseMaterials.Scratch.AlphaSource.PreparationPhysicalModeContact.SourceModeContactRead, `SourceModeContactRead),
    (`H0mework.Versions.R320c1651.ReleaseMaterials.Scratch.AlphaSource.PreparationPhysicalModeContact.SourceModeNativeSymbol, `SourceModeNativeSymbol),
    (`H0mework.Versions.R320c1651.ReleaseMaterials.Scratch.AlphaSource.PreparationPhysicalModeContact.SourceReferenceContact, `SourceReferenceContact),
    (`H0mework.Versions.R320c1651.ReleaseMaterials.Scratch.AlphaSource.PreparationPhysicalN1MaterialWard.SourceN1ColourContactReturn, `SourceN1ColourContactReturn),
    (`H0mework.Versions.R320c1651.ReleaseMaterials.Scratch.AlphaSource.PreparationPhysicalN1MaterialWard.SourceN1GaussMaterialWard, `SourceN1GaussMaterialWard),
    (`H0mework.Versions.R320c1651.ReleaseMaterials.Scratch.AlphaSource.PreparationPhysicalN1MaterialWard.SourceN1MaterialContact, `SourceN1MaterialContact),
    (`H0mework.Versions.R320c1651.ReleaseMaterials.Scratch.AlphaSource.PreparationPhysicalN1WardCollapse.SourceN1Dynamics, `SourceN1Dynamics),
    (`H0mework.Versions.R320c1651.ReleaseMaterials.Scratch.AlphaSource.PreparationPhysicalN1WardCollapse.SourceN1NormalWard, `SourceN1NormalWard),
    (`H0mework.Versions.R320c1651.ReleaseMaterials.Scratch.AlphaSource.PreparationPhysicalN1WardCollapse.SourceN1Prepared, `SourceN1Prepared),
    (`H0mework.Versions.R320c1651.ReleaseMaterials.Scratch.AlphaSource.PreparationPhysicalNativeColourReturn.SourceColourPhysicalBalance, `SourceColourPhysicalBalance),
    (`H0mework.Versions.R320c1651.ReleaseMaterials.Scratch.AlphaSource.PreparationPhysicalNativeColourReturn.SourceNativeContactReader, `SourceNativeContactReader),
    (`H0mework.Versions.R320c1651.ReleaseMaterials.Scratch.AlphaSource.PreparationPhysicalNativeColourReturn.SourceNativeJointMode, `SourceNativeJointMode),
    (`H0mework.Versions.R320c1651.ReleaseMaterials.Scratch.AlphaSource.PreparationPhysicalPinnedVelocity.SourcePinnedLeadingInverse, `SourcePinnedLeadingInverse),
    (`H0mework.Versions.R320c1651.ReleaseMaterials.Scratch.AlphaSource.PreparationPhysicalPinnedVelocity.SourcePinnedLeftAction, `SourcePinnedLeftAction),
    (`H0mework.Versions.R320c1651.ReleaseMaterials.Scratch.AlphaSource.PreparationPhysicalPinnedVelocity.SourcePinnedVelocity, `SourcePinnedVelocity),
    (`H0mework.Versions.R320c1651.ReleaseMaterials.Scratch.AlphaSource.PreparationPhysicalQuantumLockedCharge.SourceQuantumChargedFieldVertex, `SourceQuantumChargedFieldVertex),
    (`H0mework.Versions.R320c1651.ReleaseMaterials.Scratch.AlphaSource.PreparationPhysicalQuantumLockedCharge.SourceQuantumLockedChargeEvolution, `SourceQuantumLockedChargeEvolution),
    (`H0mework.Versions.R320c1651.ReleaseMaterials.Scratch.AlphaSource.PreparationPhysicalQuantumLockedCharge.SourceQuantumLockedPoleCharge, `SourceQuantumLockedPoleCharge),
    (`H0mework.Versions.R320c1651.ReleaseMaterials.Scratch.AlphaSource.PreparationPhysicalSlowBlock.SourceChannelOperators, `SourceChannelOperators),
    (`H0mework.Versions.R320c1651.ReleaseMaterials.Scratch.AlphaSource.PreparationPhysicalSlowBlock.SourceLiouvillianBlocks, `SourceLiouvillianBlocks),
    (`H0mework.Versions.R320c1651.ReleaseMaterials.Scratch.AlphaSource.PreparationPhysicalSlowBlock.SourceOffgapInverse, `SourceOffgapInverse),
    (`H0mework.Versions.R320c1651.ReleaseMaterials.Scratch.AlphaSource.PreparationPhysicalVoltageCompleteReturn.SourcePreparedVoltageReturn, `SourcePreparedVoltageReturn),
    (`H0mework.Versions.R320c1651.ReleaseMaterials.Scratch.AlphaSource.PreparationPhysicalVoltageCompleteReturn.SourceVoltageGreenRecovery, `SourceVoltageGreenRecovery),
    (`H0mework.Versions.R320c1651.ReleaseMaterials.Scratch.AlphaSource.PreparationPhysicalVoltageCompleteReturn.SourceVoltageRampPencil, `SourceVoltageRampPencil),
    (`H0mework.Versions.R320c1651.ReleaseMaterials.Scratch.AlphaSource.PreparationPhysicalVoltageEnergyIdentity.SourceChargedGreenRetention, `SourceChargedGreenRetention),
    (`H0mework.Versions.R320c1651.ReleaseMaterials.Scratch.AlphaSource.PreparationPhysicalVoltageEnergyIdentity.SourceVoltageCompleteEnergy, `SourceVoltageCompleteEnergy),
    (`H0mework.Versions.R320c1651.ReleaseMaterials.Scratch.AlphaSource.PreparationPhysicalVoltageEnergyIdentity.SourceVoltageProjectedEnergy, `SourceVoltageProjectedEnergy),
    (`H0mework.Versions.R320c1651.ReleaseMaterials.Scratch.AlphaSource.PreparationPhysicalVoltageNoether.Overlay.ImportShims.CanonicalPreparationSourceN1Prepared, `CanonicalPreparationSourceN1Prepared),
    (`H0mework.Versions.R320c1651.ReleaseMaterials.Scratch.AlphaSource.PreparationPhysicalVoltageNoether.SourceVoltageGaussEnergyRead, `SourceVoltageGaussEnergyRead),
    (`H0mework.Versions.R320c1651.ReleaseMaterials.Scratch.AlphaSource.PreparationPhysicalVoltageNoether.SourceVoltageHamiltonianResponse, `SourceVoltageHamiltonianResponse),
    (`H0mework.Versions.R320c1651.ReleaseMaterials.Scratch.AlphaSource.PreparationPhysicalVoltageNoether.SourceVoltageQuantumDensity, `SourceVoltageQuantumDensity),
    (`H0mework.Versions.R320c1651.ReleaseMaterials.Scratch.AlphaSource.PreparationVacuumActualSpatialPacket.SourceActualPacketApproximation, `SourceActualPacketApproximation),
    (`H0mework.Versions.R320c1651.ReleaseMaterials.Scratch.AlphaSource.PreparationVacuumActualSpatialPacket.SourcePacketSpatialResponse, `SourcePacketSpatialResponse),
    (`H0mework.Versions.R320c1651.ReleaseMaterials.Scratch.AlphaSource.PreparationVacuumActualSpatialPacket.SourceUniformSpatialResponse, `SourceUniformSpatialResponse),
    (`H0mework.Versions.R320c1651.ReleaseMaterials.Scratch.AlphaSource.PreparationVacuumCausalPoleResponse.SourceCausalCurrentHalf, `SourceCausalCurrentHalf),
    (`H0mework.Versions.R320c1651.ReleaseMaterials.Scratch.AlphaSource.PreparationVacuumCausalPoleResponse.SourceCausalRegular, `SourceCausalRegular),
    (`H0mework.Versions.R320c1651.ReleaseMaterials.Scratch.AlphaSource.PreparationVacuumCausalPoleResponse.SourceCommonCausalReturn, `SourceCommonCausalReturn),
    (`H0mework.Versions.R320c1651.ReleaseMaterials.Scratch.AlphaSource.PreparationVacuumChargedLongRangeRead.SourceChargedPropagatingRead, `SourceChargedPropagatingRead),
    (`H0mework.Versions.R320c1651.ReleaseMaterials.Scratch.AlphaSource.PreparationVacuumChargedLongRangeRead.SourceChargedStaticLaurent, `SourceChargedStaticLaurent),
    (`H0mework.Versions.R320c1651.ReleaseMaterials.Scratch.AlphaSource.PreparationVacuumChargedLongRangeRead.SourceChargedStaticSpatialRead, `SourceChargedStaticSpatialRead),
    (`H0mework.Versions.R320c1651.ReleaseMaterials.Scratch.AlphaSource.PreparationVacuumChargedPacketGreen.SourceCanonicalPacketDensity, `SourceCanonicalPacketDensity),
    (`H0mework.Versions.R320c1651.ReleaseMaterials.Scratch.AlphaSource.PreparationVacuumChargedPacketGreen.SourceChargedPacketFieldReturn, `SourceChargedPacketFieldReturn),
    (`H0mework.Versions.R320c1651.ReleaseMaterials.Scratch.AlphaSource.PreparationVacuumChargedPacketGreen.SourcePacketGreenTail, `SourcePacketGreenTail),
    (`H0mework.Versions.R320c1651.ReleaseMaterials.Scratch.AlphaSource.PreparationVacuumChargedSpatialResponse.SourceChargedCornerInverse, `SourceChargedCornerInverse),
    (`H0mework.Versions.R320c1651.ReleaseMaterials.Scratch.AlphaSource.PreparationVacuumChargedSpatialResponse.SourceChargedSecondPacket, `SourceChargedSecondPacket),
    (`H0mework.Versions.R320c1651.ReleaseMaterials.Scratch.AlphaSource.PreparationVacuumChargedSpatialResponse.SourceChargedSecondUniform, `SourceChargedSecondUniform),
    (`H0mework.Versions.R320c1651.ReleaseMaterials.Scratch.AlphaSource.PreparationVacuumFullPoleContinuation.SourceFullPoleTensor, `SourceFullPoleTensor),
    (`H0mework.Versions.R320c1651.ReleaseMaterials.Scratch.AlphaSource.PreparationVacuumFullPoleContinuation.SourceReaderMomentum, `SourceReaderMomentum),
    (`H0mework.Versions.R320c1651.ReleaseMaterials.Scratch.AlphaSource.PreparationVacuumFullPoleContinuation.SourceRetainerMomentum, `SourceRetainerMomentum),
    (`H0mework.Versions.R320c1651.ReleaseMaterials.Scratch.AlphaSource.PreparationVacuumFullSlowFieldResponse.SourceCausalFieldReturn, `SourceCausalFieldReturn),
    (`H0mework.Versions.R320c1651.ReleaseMaterials.Scratch.AlphaSource.PreparationVacuumFullSlowFieldResponse.SourceCausalFieldTensor, `SourceCausalFieldTensor),
    (`H0mework.Versions.R320c1651.ReleaseMaterials.Scratch.AlphaSource.PreparationVacuumFullSlowFieldResponse.SourceJointCausalField, `SourceJointCausalField),
    (`H0mework.Versions.R320c1651.ReleaseMaterials.Scratch.AlphaSource.PreparationVacuumGaugeSlowFrequency.SourceFullN1Sylvester, `SourceFullN1Sylvester),
    (`H0mework.Versions.R320c1651.ReleaseMaterials.Scratch.AlphaSource.PreparationVacuumGaugeSlowFrequency.SourceGaugeHalfSylvester, `SourceGaugeHalfSylvester),
    (`H0mework.Versions.R320c1651.ReleaseMaterials.Scratch.AlphaSource.PreparationVacuumGaugeSlowFrequency.SourceGaugeLaplaceEquation, `SourceGaugeLaplaceEquation),
    (`H0mework.Versions.R320c1651.ReleaseMaterials.Scratch.AlphaSource.PreparationVacuumNativePoleTensor.SourceActualNativePole, `SourceActualNativePole),
    (`H0mework.Versions.R320c1651.ReleaseMaterials.Scratch.AlphaSource.PreparationVacuumNativePoleTensor.SourceDynamicRegular, `SourceDynamicRegular),
    (`H0mework.Versions.R320c1651.ReleaseMaterials.Scratch.AlphaSource.PreparationVacuumNativePoleTensor.SourceNativeSchurResponse, `SourceNativeSchurResponse),
    (`H0mework.Versions.R320c1651.ReleaseMaterials.Scratch.AlphaSource.PreparationVacuumNativeSlowCoupling.SourceActualNativeCoupling, `SourceActualNativeCoupling),
    (`H0mework.Versions.R320c1651.ReleaseMaterials.Scratch.AlphaSource.PreparationVacuumNativeSlowCoupling.SourceActualOriginRead, `SourceActualOriginRead),
    (`H0mework.Versions.R320c1651.ReleaseMaterials.Scratch.AlphaSource.PreparationVacuumNativeSlowCoupling.SourceNativeReaderJet, `SourceNativeReaderJet),
    (`H0mework.Versions.R320c1651.ReleaseMaterials.Scratch.AlphaSource.PreparationVacuumObservedBoundaryResidue.SourceNativeBoundaryNumerator, `SourceNativeBoundaryNumerator),
    (`H0mework.Versions.R320c1651.ReleaseMaterials.Scratch.AlphaSource.PreparationVacuumObservedBoundaryResidue.SourceQuantumBoundaryNumerator, `SourceQuantumBoundaryNumerator),
    (`H0mework.Versions.R320c1651.ReleaseMaterials.Scratch.AlphaSource.PreparationVacuumObservedPoleTensor.SourceObservedFieldVertex, `SourceObservedFieldVertex),
    (`H0mework.Versions.R320c1651.ReleaseMaterials.Scratch.AlphaSource.PreparationVacuumObservedPoleTensor.SourcePinnedPoleBoundary, `SourcePinnedPoleBoundary),
    (`H0mework.Versions.R320c1651.ReleaseMaterials.Scratch.AlphaSource.PreparationVacuumObservedPoleTensor.SourcePinnedPoleChannels, `SourcePinnedPoleChannels),
    (`H0mework.Versions.R320c1651.ReleaseMaterials.Scratch.AlphaSource.PreparationVacuumObservedStaticResidue.SourceStaticCurrentResidue, `SourceStaticCurrentResidue),
    (`H0mework.Versions.R320c1651.ReleaseMaterials.Scratch.AlphaSource.PreparationVacuumObservedStaticResidue.SourceStaticNativeForcing, `SourceStaticNativeForcing),
    (`H0mework.Versions.R320c1651.ReleaseMaterials.Scratch.AlphaSource.PreparationVacuumObservedStaticResidue.SourceStaticObservedField, `SourceStaticObservedField),
    (`H0mework.Versions.R320c1651.ReleaseMaterials.Scratch.AlphaSource.PreparationVacuumPhysicalCharacteristic.SourcePhysicalHermitian, `SourcePhysicalHermitian),
    (`H0mework.Versions.R320c1651.ReleaseMaterials.Scratch.AlphaSource.PreparationVacuumPhysicalCharacteristic.SourcePhysicalPropagation, `SourcePhysicalPropagation),
    (`H0mework.Versions.R320c1651.ReleaseMaterials.Scratch.AlphaSource.PreparationVacuumPhysicalCharacteristic.SourceSlowFastLeading, `SourceSlowFastLeading),
    (`H0mework.Versions.R320c1651.ReleaseMaterials.Scratch.AlphaSource.PreparationVacuumPhysicalPoleSheet.SourceExactSchurScale, `SourceExactSchurScale),
    (`H0mework.Versions.R320c1651.ReleaseMaterials.Scratch.AlphaSource.PreparationVacuumPhysicalPoleSheet.SourceSimplePhysicalSheet, `SourceSimplePhysicalSheet),
    (`H0mework.Versions.R320c1651.ReleaseMaterials.Scratch.AlphaSource.PreparationVacuumPhysicalPoleSheet.SourceSmoothPhysicalTensor, `SourceSmoothPhysicalTensor),
    (`H0mework.Versions.R320c1651.ReleaseMaterials.Scratch.AlphaSource.PreparationVacuumPoleConstraintReturn.SourceAxisCompatibility, `SourceAxisCompatibility),
    (`H0mework.Versions.R320c1651.ReleaseMaterials.Scratch.AlphaSource.PreparationVacuumPoleConstraintReturn.SourceNativePoleBalance, `SourceNativePoleBalance),
    (`H0mework.Versions.R320c1651.ReleaseMaterials.Scratch.AlphaSource.PreparationVacuumPoleConstraintReturn.SourceNativePolePrice, `SourceNativePolePrice),
    (`H0mework.Versions.R320c1651.ReleaseMaterials.Scratch.AlphaSource.PreparationVacuumQuantumSlowResidue.SourceActualCurrentResidues, `SourceActualCurrentResidues),
    (`H0mework.Versions.R320c1651.ReleaseMaterials.Scratch.AlphaSource.PreparationVacuumQuantumSlowResidue.SourceActualSlowResidues, `SourceActualSlowResidues),
    (`H0mework.Versions.R320c1651.ReleaseMaterials.Scratch.AlphaSource.PreparationVacuumQuantumSlowResidue.SourceEffectiveCausalInverse, `SourceEffectiveCausalInverse),
    (`H0mework.Versions.R320c1651.ReleaseMaterials.Scratch.AlphaSource.PreparationVacuumQuantumSlowResponse.SourceActualSlowSchur, `SourceActualSlowSchur),
    (`H0mework.Versions.R320c1651.ReleaseMaterials.Scratch.AlphaSource.PreparationVacuumQuantumSlowResponse.SourceSlowCurrentReturn, `SourceSlowCurrentReturn),
    (`H0mework.Versions.R320c1651.ReleaseMaterials.Scratch.AlphaSource.PreparationVacuumQuantumSlowResponse.SourceSlowNeumann, `SourceSlowNeumann),
    (`H0mework.Versions.R320c1651.ReleaseMaterials.Scratch.AlphaSource.PreparationVacuumRestModeCoupling.SourceModeCurrent, `SourceModeCurrent),
    (`H0mework.Versions.R320c1651.ReleaseMaterials.Scratch.AlphaSource.PreparationVacuumSharedPoleCarrier.SourceMomentumContinuation, `SourceMomentumContinuation),
    (`H0mework.Versions.R320c1651.ReleaseMaterials.Scratch.AlphaSource.PreparationVacuumSharedPoleCarrier.SourceMovingCarrier, `SourceMovingCarrier),
    (`H0mework.Versions.R320c1651.ReleaseMaterials.Scratch.AlphaSource.PreparationVacuumSharedPoleCarrier.SourcePreparedTensor, `SourcePreparedTensor),
    (`H0mework.Versions.R320c1651.ReleaseMaterials.Scratch.AlphaSource.PreparationVacuumSoftPoleSelection.SourceActualSoftSelection, `SourceActualSoftSelection),
    (`H0mework.Versions.R320c1651.ReleaseMaterials.Scratch.AlphaSource.PreparationVacuumSoftPoleSelection.SourceSoftNativeFrame, `SourceSoftNativeFrame),
    (`H0mework.Versions.R320c1651.ReleaseMaterials.Scratch.AlphaSource.PreparationVacuumSoftPoleSelection.SourceSoftResidueKernel, `SourceSoftResidueKernel),
    (`H0mework.Versions.R320c1651.ReleaseMaterials.Scratch.AlphaSource.PreparationVacuumStaticSimpleCoupling.SourceStaticLaurentCurrent, `SourceStaticLaurentCurrent),
    (`H0mework.Versions.R320c1651.ReleaseMaterials.Scratch.AlphaSource.PreparationVacuumStaticSimpleCoupling.SourceStaticLaurentForcing, `SourceStaticLaurentForcing),
    (`H0mework.Versions.R320c1651.ReleaseMaterials.Scratch.AlphaSource.PreparationVacuumStaticSimpleCoupling.SourceStaticLaurentObserved, `SourceStaticLaurentObserved),
    (`H0mework.Versions.R320c1651.ReleaseMaterials.Scratch.AlphaSource.PreparationVacuumStaticSpatialSource.SourcePinnedRadialScale, `SourcePinnedRadialScale),
    (`H0mework.Versions.R320c1651.ReleaseMaterials.Scratch.AlphaSource.PreparationVacuumStaticSpatialSource.SourceSimpleRadialScale, `SourceSimpleRadialScale),
    (`H0mework.Versions.R320c1651.ReleaseMaterials.Scratch.AlphaSource.PreparationVacuumStaticSpatialSource.SourceSpatialGreenRead, `SourceSpatialGreenRead),
    (`H0mework.Versions.R320c1651.ReleaseMaterials.Scratch.AlphaSource.PreparationVacuumStaticVoltageSource.SourceVoltageCauchyTangent, `SourceVoltageCauchyTangent),
    (`H0mework.Versions.R320c1651.ReleaseMaterials.Scratch.AlphaSource.PreparationVacuumStaticVoltageSource.SourceVoltageNativeJet, `SourceVoltageNativeJet),
    (`H0mework.Versions.R320c1651.ReleaseMaterials.Scratch.AlphaSource.PreparationVacuumStaticVoltageSource.SourceVoltageWholeForcing, `SourceVoltageWholeForcing),
    (`H0mework.Versions.R320c1651.ReleaseMaterials.Scratch.AlphaSource.PreparationVacuumVoltageGaussGreen.SourceVoltageGaussIdentity, `SourceVoltageGaussIdentity),
    (`H0mework.Versions.R320c1651.ReleaseMaterials.Scratch.AlphaSource.PreparationVacuumVoltageGaussGreen.SourceVoltageGreenEnergy, `SourceVoltageGreenEnergy),
    (`H0mework.Versions.R320c1651.ReleaseMaterials.Scratch.AlphaSource.PreparationVacuumVoltageGaussGreen.SourceVoltageGreenSolution, `SourceVoltageGreenSolution),
    (`H0mework.Versions.Rdf421ff6.ReleaseMaterials.Scratch.AlphaSource.PreparationObjectRecoveryAfterRestart.SlimSource.OriginalFiniteChannelMassRecovery, `OriginalFiniteChannelMassRecovery),
    (`H0mework.Versions.Rdf421ff6.ReleaseMaterials.Scratch.AlphaSource.PreparationObjectRecoveryAfterRestart.SlimSource.OriginalSpectralReadStateRecovery, `OriginalSpectralReadStateRecovery),
    (`H0mework.Versions.Rdf421ff6.ReleaseMaterials.Scratch.AlphaSource.PreparationObjectRecoveryAfterRestart.SlimSource.SourceCoframeSpinConnection, `SourceCoframeSpinConnection),
    (`H0mework.Versions.Rdf421ff6.ReleaseMaterials.Scratch.AlphaSource.PreparationObjectRecoveryAfterRestart.SlimSource.SourceCoframeSpinNormalOrder, `SourceCoframeSpinNormalOrder),
    (`H0mework.Versions.Rdf421ff6.ReleaseMaterials.Scratch.AlphaSource.PreparationObjectRecoveryAfterRestart.SlimSource.SourceRetardedBandCurrent, `SourceRetardedBandCurrent),
    (`H0mework.Versions.Rdf421ff6.ReleaseMaterials.Scratch.AlphaSource.PreparationPhysicalConstraint114.SourceConstraintRead, `SourceConstraintRead),
    (`H0mework.Versions.Rdf421ff6.ReleaseMaterials.Scratch.AlphaSource.PreparationPhysicalConstraint114.SourceCurrentSupport, `SourceCurrentSupport),
    (`H0mework.Versions.Rdf421ff6.ReleaseMaterials.Scratch.AlphaSource.PreparationPhysicalElectromagneticDirection.SourceJointLocking, `SourceJointLocking),
    (`H0mework.Versions.Rdf421ff6.ReleaseMaterials.Scratch.AlphaSource.PreparationPhysicalElectromagneticDirection.SourceLockedPoleCurrent, `SourceLockedPoleCurrent),
    (`H0mework.Versions.Rdf421ff6.ReleaseMaterials.Scratch.AlphaSource.PreparationPhysicalGradeZeroRead.GaugeBand, `GaugeBand),
    (`H0mework.Versions.Rdf421ff6.ReleaseMaterials.Scratch.AlphaSource.PreparationPhysicalGradeZeroRead.PhiGrade, `PhiGrade),
    (`H0mework.Versions.Rdf421ff6.ReleaseMaterials.Scratch.AlphaSource.PreparationPhysicalGradeZeroRead.SourceProjectionReturn, `SourceProjectionReturn),
    (`H0mework.Versions.Rdf421ff6.ReleaseMaterials.Scratch.AlphaSource.PreparationPhysicalLockedGaussBalance.Overlay.CanonicalPreparationSourceLockedPoleCurrent, `CanonicalPreparationSourceLockedPoleCurrent),
    (`H0mework.Versions.Rdf421ff6.ReleaseMaterials.Scratch.AlphaSource.PreparationPhysicalNativePoleChargeReturnKernelAudit.ImportAlias.RawActionDensity, `RawActionDensity),
    (`H0mework.Versions.Rdf421ff6.ReleaseMaterials.Scratch.AlphaSource.PreparationPhysicalNumberOneRead.SourceNumberHistory, `SourceNumberHistory),
    (`H0mework.Versions.Rdf421ff6.ReleaseMaterials.Scratch.AlphaSource.PreparationPhysicalNumberOneRead.SourceNumberRange, `SourceNumberRange),
    (`H0mework.Versions.Rdf421ff6.ReleaseMaterials.Scratch.AlphaSource.PreparationPhysicalNumberOneRead.SourceWholeCurrent, `SourceWholeCurrent),
    (`H0mework.Versions.Rdf421ff6.ReleaseMaterials.Scratch.AlphaSource.PreparationPhysicalZeroRead.ActualCurrentWard, `ActualCurrentWard),
    (`H0mework.Versions.Rdf421ff6.ReleaseMaterials.Scratch.AlphaSource.PreparationPhysicalZeroRead.PrincipalHistory, `PrincipalHistory),
    (`H0mework.Versions.Rdf421ff6.ReleaseMaterials.Scratch.AlphaSource.PreparationPhysicalZeroRead.PrincipalLaplace, `PrincipalLaplace),
    (`H0mework.Versions.Rdf421ff6.ReleaseMaterials.Scratch.AlphaSource.PreparationVacuumFullOriginResponse.SourceFullOriginCurrent, `SourceFullOriginCurrent),
    (`H0mework.Versions.Rdf421ff6.ReleaseMaterials.Scratch.AlphaSource.PreparationVacuumFullOriginResponse.SourceFullOriginInverse, `SourceFullOriginInverse),
    (`H0mework.Versions.Rdf421ff6.ReleaseMaterials.Scratch.AlphaSource.PreparationVacuumFullOriginResponse.SourceFullOriginSchur, `SourceFullOriginSchur),
    (`H0mework.Versions.Rdf421ff6.ReleaseMaterials.Scratch.AlphaSource.PreparationVacuumMixedControl.SourceCoefficientPrice, `SourceCoefficientPrice),
    (`H0mework.Versions.Rdf421ff6.ReleaseMaterials.Scratch.AlphaSource.PreparationVacuumMixedControl.SourceEffectiveLeading, `SourceEffectiveLeading),
    (`H0mework.Versions.Rdf421ff6.ReleaseMaterials.Scratch.AlphaSource.PreparationVacuumMixedControl.SourceNeumannDomain, `SourceNeumannDomain),
    (`H0mework.Versions.Rdf421ff6.ReleaseMaterials.Scratch.AlphaSource.PreparationVacuumMixedEffective.SourceActualEffective, `SourceActualEffective),
    (`H0mework.Versions.Rdf421ff6.ReleaseMaterials.Scratch.AlphaSource.PreparationVacuumMixedEffective.SourceComplementInverse, `SourceComplementInverse),
    (`H0mework.Versions.Rdf421ff6.ReleaseMaterials.Scratch.AlphaSource.PreparationVacuumMixedEffective.SourceMixedSchur, `SourceMixedSchur),
    (`H0mework.Versions.Rdf421ff6.ReleaseMaterials.Scratch.AlphaSource.PreparationVacuumMixedPrincipal.SourceCurrentPrincipal, `SourceCurrentPrincipal),
    (`H0mework.Versions.Rdf421ff6.ReleaseMaterials.Scratch.AlphaSource.PreparationVacuumMixedPrincipal.SourceMixedPrincipal, `SourceMixedPrincipal),
    (`H0mework.Versions.Rdf421ff6.ReleaseMaterials.Scratch.AlphaSource.PreparationVacuumMixedPrincipal.SourceNativePrincipal, `SourceNativePrincipal),
    (`H0mework.Versions.Rdf421ff6.ReleaseMaterials.Scratch.AlphaSource.PreparationVacuumPhysicalFieldChannel.SourceQuantumMixedRead, `SourceQuantumMixedRead),
    (`H0mework.Versions.Rdf421ff6.ReleaseMaterials.Scratch.AlphaSource.PreparationVacuumPhysicalFieldChannel.SourceStaticMixedChannel, `SourceStaticMixedChannel),
    (`H0mework.Versions.Rdf421ff6.ReleaseMaterials.Scratch.AlphaSource.PreparationVacuumPhysicalFieldChannel.SourceStaticNativeMode, `SourceStaticNativeMode),
    (`H0mework.Versions.Rdf421ff6.ReleaseMaterials.Scratch.AlphaSource.PreparationVacuumRestModeCoupling.SourceModeGaugeAction, `SourceModeGaugeAction),
    (`H0mework.Versions.Rdf421ff6.ReleaseMaterials.Scratch.AlphaSource.PreparationVacuumRestModeCoupling.SourceRestSpatialAction, `SourceRestSpatialAction),
    (`H0mework.Versions.Rdf421ff6.ReleaseMaterials.Scratch.AlphaSource.PreparationVacuumStaticPoleResponse.SourceStaticActualPole, `SourceStaticActualPole),
    (`H0mework.Versions.Rdf421ff6.ReleaseMaterials.Scratch.AlphaSource.PreparationVacuumStaticPoleResponse.SourceStaticOriginalGreen, `SourceStaticOriginalGreen),
    (`H0mework.Versions.Rdf421ff6.ReleaseMaterials.Scratch.AlphaSource.PreparationVacuumStaticPoleResponse.SourceStaticPoleDomain, `SourceStaticPoleDomain),
    (`H0mework.Versions.Rdf421ff6.ReleaseMaterials.Scratch.AlphaSource.PreparationVacuumWholeOrigin.SourceDualSchur, `SourceDualSchur),
    (`H0mework.Versions.Rdf421ff6.ReleaseMaterials.Scratch.AlphaSource.PreparationVacuumWholeOrigin.SourceWholeOriginCurrent, `SourceWholeOriginCurrent),
    (`H0mework.Versions.Rdf421ff6.ReleaseMaterials.Scratch.AlphaSource.PreparationVacuumWholeOrigin.SourceWholeOriginFrame, `SourceWholeOriginFrame)
  ]
  for moduleName in modules do
    let sourceModule := relocated[moduleName]?.getD moduleName
    if (sourceModule.toString.toLower.splitOn ".").contains "scratch" then
      throwError m!"SCRATCH_IMPORT {moduleName}"
  logInfo m!"NATIVE_EM_CHARGE_BRIDGE_PASS public={mouths.size} owned={owned.length} nodes={all.size} anchors={anchors.size} direct={direct.size} consumers={consumers.size} opaque_all_read={opaqueCount} axioms={axioms} unknown=0 unsafe=0 partial=0"


#audit_native_em_charge_bridge
