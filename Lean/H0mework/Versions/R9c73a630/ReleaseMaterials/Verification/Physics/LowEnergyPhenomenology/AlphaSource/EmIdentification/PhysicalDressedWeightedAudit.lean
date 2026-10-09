import H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.PhysicalDressedWeightedCreation
import Lean

set_option autoImplicit false
noncomputable section

namespace LowEnergy.DressedWeightedAudit

open SaturationMonoid.PhysicsCore SaturationMonoid.PhysicsCore.LowEnergy
open StageNineDynamicBreakingVacuum
open SourceQuantumScalarChart SourceQuantumConfigurationHilbert SourceQuantumFockGauge
open SourceQuantumGaugeSliceCoordinates GaussCoreHilbert GaussHistoryHilbert GaussQuantumMultiplier
open GaussCoreDifferential GaussDensityCore
open PreparationVacuumActualFieldQuantization PreparationVacuumLowerClassical
open FullQuantum.StateGreen CanonicalGradedCharge NamedColorQtNext
open GaussComposite GaussComposite.SourceGraph WeightedActualSeed
open PreparationVacuumWeightedChargeActionWard PreparationPhysicalPhaseGaugeRealization

theorem checked_arbitrary_weight (W : FullMatrix) (a : NativeLie)
    (channel s : Fin 2) (phi : ScalarCoordinateCarrier) :
    (quantizer (W * chargeMatrix a) * fiberCreation channel s phi -
        fiberCreation channel s phi * quantizer (W * chargeMatrix a)) -
      Complex.I • scalarWeightedCreation a W channel s phi =
        (Complex.I • (nativeData a).2.2.1) • weightedCreation W channel s phi :=
  weighted_creation_coupling W a channel s phi

theorem checked_original_normal_pair (a : Fin 12) (z : physicalChart)
    (channel s : Fin 2) :
    (weightFiber z.val * quantizer (chargeMatrix (originalUnit a)) -
        normalChargeFiber a z.val) *
      fiberCreation channel s (GaussNativePotential.scalarField z.val) -
      fiberCreation channel s (GaussNativePotential.scalarField z.val) *
        (weightFiber z.val * quantizer (chargeMatrix (originalUnit a)) -
          normalChargeFiber a z.val) -
      Complex.I • scalarWeightedCreation (originalUnit a)
        (sourceWeightSymbol z.val) channel s (GaussNativePotential.scalarField z.val) =
      (Complex.I • (nativeData (originalUnit a)).2.2.1) •
        weightedCreation (sourceWeightSymbol z.val) channel s
          (GaussNativePotential.scalarField z.val) :=
  raw_charge_weighted_creation_explicit a z channel s

theorem checked_original_core (a : Fin 12) (channel s : Fin 2) (f : QuantumTest) :
    rawChargeCore a (creationTest channel s f) -
      creationTest channel s (rawChargeCore a f) =
        Complex.I • scalarWeightedCore (originalUnit a) channel s f +
          (Complex.I • (nativeData (originalUnit a)).2.2.1) •
            weightedCreationCore channel s f :=
  raw_charge_core_ward a channel s f

theorem checked_original_seed (a : Fin 12) (channel s : Fin 2) (g : ScalarTest) :
    rawChargeCore a (creationTest channel s (seedSection g)) =
      creationTest channel s (rawChargeCore a (seedSection g)) +
        Complex.I • scalarWeightedCore (originalUnit a) channel s (seedSection g) +
          (Complex.I • (nativeData (originalUnit a)).2.2.1) •
            weightedCreationCore channel s (seedSection g) :=
  raw_charge_seed_current a channel s g

theorem checked_seed_field (channel s : Fin 2) (g : ScalarTest) (z : physicalChart) :
    (weightedCreationCore channel s (seedSection g)) z.val =
      (rootVolume z.val : ℂ)⁻¹ •
        (weightedCreation (sourceWeightSymbol z.val) channel s
          (GaussNativePotential.scalarField z.val))
          (g z.val • CanonicalCompletedSector.seed) :=
  weighted_creation_seed_eval channel s g z

theorem checked_source_em (channel s : Fin 2) (phi : ScalarCoordinateCarrier)
    (z : physicalChart) :
    (quantizer (sourceWeightSymbol z.val * chargeMatrix sourcePhaseGaugeLie) *
        fiberCreation channel s phi -
      fiberCreation channel s phi *
        quantizer (sourceWeightSymbol z.val * chargeMatrix sourcePhaseGaugeLie)) -
      Complex.I • scalarWeightedCreation sourcePhaseGaugeLie
        (sourceWeightSymbol z.val) channel s phi =
      (1 / 2 : ℂ) • weightedCreation (sourceWeightSymbol z.val) channel s phi :=
  weighted_creation_phase_vertex channel s phi z

theorem checked_source_y (channel s : Fin 2) (phi : ScalarCoordinateCarrier)
    (z : physicalChart) :
    (quantizer (sourceWeightSymbol z.val * chargeMatrix nativeY) *
        fiberCreation channel s phi -
      fiberCreation channel s phi *
        quantizer (sourceWeightSymbol z.val * chargeMatrix nativeY)) -
      Complex.I • scalarWeightedCreation nativeY
        (sourceWeightSymbol z.val) channel s phi =
      (-1 : ℂ) • weightedCreation (sourceWeightSymbol z.val) channel s phi :=
  weighted_creation_nativeY_vertex channel s phi z

theorem checked_scalar_compensation (W : FullMatrix) (a : NativeLie)
    (hhyper : (nativeData a).2.2.1 = 0) (channel s : Fin 2)
    (phi : ScalarCoordinateCarrier) :
    quantizer (W * chargeMatrix a) * fiberCreation channel s phi -
      fiberCreation channel s phi * quantizer (W * chargeMatrix a) =
        Complex.I • scalarWeightedCreation a W channel s phi :=
  weighted_creation_colour_compensator W a hhyper channel s phi

end LowEnergy.DressedWeightedAudit
end

open Lean Elab Command

private def dressedWeightedChildren (info : ConstantInfo) : Array Name := Id.run do
  let mut children := info.type.getUsedConstants
  if let some value := info.value? (allowOpaque := true) then
    children := children ++ value.getUsedConstants
  if let .inductInfo value := info then children := children ++ value.ctors.toArray
  if let .recInfo value := info then
    for rule in value.rules do children := children ++ rule.rhs.getUsedConstants
  return children

private def dressedWeightedClosure (env : Environment) (roots : List Name) :
    CommandElabM NameSet := do
  let mut pending := roots
  let mut seen : NameSet := {}
  while !pending.isEmpty do
    let name := pending.head!
    pending := pending.tail!
    unless seen.contains name do
      let some info := env.checked.get.find? name | throwError m!"UNKNOWN {name}"
      pending := (dressedWeightedChildren info).toList ++ pending
      seen := seen.insert name
  return seen

elab "#audit_dressed_weighted" : command => do
  let env ← getEnv
  let modules := env.header.moduleNames
  let moduleName := `H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.PhysicalDressedWeightedCreation
  unless modules.contains moduleName do throwError m!"MISSING_MODULE {moduleName}"
  let owned := env.constants.toList.filterMap fun (name, _) =>
    match env.getModuleIdxFor? name with
    | some index => if modules[index.toNat]! == moduleName then some name else none
    | none => none
  if owned.isEmpty then throwError "EMPTY_OWNED_CLOSURE"
  let mouths := #[
    ``LowEnergy.WeightedActualSeed.weightedCreation,
    ``LowEnergy.WeightedActualSeed.scalarWeightedCreation,
    ``LowEnergy.WeightedActualSeed.weighted_creation_coupling,
    ``LowEnergy.WeightedActualSeed.raw_charge_weighted_creation,
    ``LowEnergy.WeightedActualSeed.raw_charge_weighted_creation_explicit,
    ``LowEnergy.WeightedActualSeed.weightedCreationCore,
    ``LowEnergy.WeightedActualSeed.scalarWeightedCore,
    ``LowEnergy.WeightedActualSeed.raw_charge_core_ward,
    ``LowEnergy.WeightedActualSeed.raw_charge_seed_ward,
    ``LowEnergy.WeightedActualSeed.raw_charge_seed_current,
    ``LowEnergy.WeightedActualSeed.weighted_creation_seed_eval,
    ``LowEnergy.WeightedActualSeed.weighted_creation_phase_vertex,
    ``LowEnergy.WeightedActualSeed.weighted_creation_nativeY_vertex,
    ``LowEnergy.WeightedActualSeed.weighted_creation_colour_compensator]
  for name in mouths do
    unless owned.contains name do throwError m!"MISSING_PUBLIC {name}"
  let consumers := #[
    (``LowEnergy.DressedWeightedAudit.checked_arbitrary_weight,
      #[``LowEnergy.WeightedActualSeed.weighted_creation_coupling]),
    (``LowEnergy.DressedWeightedAudit.checked_original_normal_pair,
      #[``LowEnergy.WeightedActualSeed.raw_charge_weighted_creation_explicit]),
    (``LowEnergy.DressedWeightedAudit.checked_original_core,
      #[``LowEnergy.WeightedActualSeed.raw_charge_core_ward]),
    (``LowEnergy.DressedWeightedAudit.checked_original_seed,
      #[``LowEnergy.WeightedActualSeed.raw_charge_seed_current]),
    (``LowEnergy.DressedWeightedAudit.checked_seed_field,
      #[``LowEnergy.WeightedActualSeed.weighted_creation_seed_eval]),
    (``LowEnergy.DressedWeightedAudit.checked_source_em,
      #[``LowEnergy.WeightedActualSeed.weighted_creation_phase_vertex]),
    (``LowEnergy.DressedWeightedAudit.checked_source_y,
      #[``LowEnergy.WeightedActualSeed.weighted_creation_nativeY_vertex]),
    (``LowEnergy.DressedWeightedAudit.checked_scalar_compensation,
      #[``LowEnergy.WeightedActualSeed.weighted_creation_colour_compensator])]
  let all ← dressedWeightedClosure env (owned ++ (consumers.map Prod.fst).toList)
  let anchors := #[
    ``SaturationMonoid.PhysicsCore.StageNineEnrichedProofFreeSource.positiveSmoothUnifiedSource,
    ``SaturationMonoid.PhysicsCore.Stage9C.Material.SpinPair.actual,
    ``LowEnergy.DressedColourY.scalar_action_row,
    ``LowEnergy.NamedColorQtNext.actual_full_native_column,
    ``LowEnergy.GaussNativeMatter.nativeFull,
    ``LowEnergy.PreparationVacuumWeightedChargeActionWard.sourceWeightSymbol,
    ``LowEnergy.PreparationVacuumWeightedChargeActionWard.rawChargeFiber_source,
    ``LowEnergy.PreparationVacuumWeightedChargeActionWard.normalChargeFiber,
    ``LowEnergy.PreparationVacuumWeightedChargeActionWard.rawChargeCore,
    ``LowEnergy.GaussComposite.fiberCreation,
    ``LowEnergy.GaussComposite.creationTest,
    ``LowEnergy.GaussNativePotential.scalarField,
    ``LowEnergy.GaussComposite.SourceGraph.seedSection,
    ``LowEnergy.CanonicalCompletedSector.seed,
    ``LowEnergy.PreparationPhysicalPhaseGaugeRealization.sourcePhaseGaugeLie]
  for name in anchors do
    unless all.contains name do throwError m!"UNCONSUMED_SOURCE {name}"
  let direct := #[
    (``LowEnergy.WeightedActualSeed.weighted_creation_coupling,
      #[``LowEnergy.DressedColourY.scalar_action_row,
        ``LowEnergy.NamedColorQtNext.actual_full_native_column]),
    (``LowEnergy.WeightedActualSeed.raw_charge_weighted_creation,
      #[``LowEnergy.WeightedActualSeed.weighted_creation_coupling,
        ``LowEnergy.PreparationVacuumWeightedChargeActionWard.rawChargeFiber_source]),
    (``LowEnergy.WeightedActualSeed.raw_charge_weighted_creation_explicit,
      #[``LowEnergy.WeightedActualSeed.raw_charge_weighted_creation,
        ``LowEnergy.PreparationVacuumWeightedChargeActionWard.rawChargeFiber_source]),
    (``LowEnergy.WeightedActualSeed.raw_charge_core_ward,
      #[``LowEnergy.WeightedActualSeed.raw_charge_weighted_creation]),
    (``LowEnergy.WeightedActualSeed.raw_charge_seed_current,
      #[``LowEnergy.WeightedActualSeed.raw_charge_core_ward]),
    (``LowEnergy.WeightedActualSeed.weighted_creation_phase_vertex,
      #[``LowEnergy.WeightedActualSeed.weighted_creation_coupling,
        ``LowEnergy.DressedColourY.joint_phase_character])]
  for (mouth, required) in direct ++ consumers do
    let closed ← dressedWeightedClosure env [mouth]
    for name in required do
      unless closed.contains name do throwError m!"UNCONSUMED_DIRECT {mouth} {name}"
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
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
      unless allowed.contains axiomName do
        throwError m!"UNAUTHORIZED_ROOT_AXIOM {name} {axiomName}"
  for name in #[`SaturationMonoid.StandardModelConstraint.alphaEMIntegerDenominator,
      `SaturationMonoid.StandardModelConstraint.alphaEMFromIntegerConstraint,
      `SaturationMonoid.StandardModelConstraint.gutWeakMixingInformationRatio] do
    if all.contains name then throwError m!"TARGET_CONTAMINATION {name}"
  for name in modules do
    if (name.toString.toLower.splitOn ".").contains "scratch" then
      throwError m!"SCRATCH_IMPORT {name}"
  logInfo m!"DRESSED_WEIGHTED_PASS public={mouths.size} owned={owned.length} nodes={all.size} anchors={anchors.size} direct={direct.size} consumers={consumers.size} opaque_all_read={opaqueCount} axioms={axioms} unknown=0 unsafe=0 partial=0"

#audit_dressed_weighted
