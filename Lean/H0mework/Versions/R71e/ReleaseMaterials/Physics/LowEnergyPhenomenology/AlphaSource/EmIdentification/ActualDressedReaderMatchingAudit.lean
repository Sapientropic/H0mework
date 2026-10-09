import H0mework.Versions.R71e.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualDressedReaderComponents
import H0mework.Versions.R71e.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualDressedCutReturn
import H0mework.Versions.R71e.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualDressedReaderMatching

import Lean.Elab.Command
import Lean.Util.FoldConsts
import Lean.Util.CollectAxioms
set_option autoImplicit false
set_option maxHeartbeats 12000000
set_option maxRecDepth 32768
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.GaussComposite.ActualDressedReaderMatchingAudit
elab "checked_temporal_fiber_residual_sourceContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualDressedReaderComponents.temporal_fiber_residual_source).type
theorem checked_temporal_fiber_residual_source : checked_temporal_fiber_residual_sourceContract := @LowEnergy.GaussComposite.ActualDressedReaderComponents.temporal_fiber_residual_source

elab "checked_temporal_fiber_residual_integrableContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualDressedReaderComponents.temporal_fiber_residual_integrable).type
theorem checked_temporal_fiber_residual_integrable : checked_temporal_fiber_residual_integrableContract := @LowEnergy.GaussComposite.ActualDressedReaderComponents.temporal_fiber_residual_integrable

elab "checked_temporal_fiber_firstContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualDressedReaderComponents.temporal_fiber_first).type
theorem checked_temporal_fiber_first : checked_temporal_fiber_firstContract := @LowEnergy.GaussComposite.ActualDressedReaderComponents.temporal_fiber_first

elab "checked_temporal_reader_form_generatedContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualDressedReaderComponents.temporal_reader_form_generated).type
theorem checked_temporal_reader_form_generated : checked_temporal_reader_form_generatedContract := @LowEnergy.GaussComposite.ActualDressedReaderComponents.temporal_reader_form_generated

elab "checked_temporal_reader_generatedContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualDressedReaderComponents.temporal_reader_generated).type
theorem checked_temporal_reader_generated : checked_temporal_reader_generatedContract := @LowEnergy.GaussComposite.ActualDressedReaderComponents.temporal_reader_generated

elab "checked_temporal_reader_compensation_priceContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualDressedReaderComponents.temporal_reader_compensation_price).type
theorem checked_temporal_reader_compensation_price : checked_temporal_reader_compensation_priceContract := @LowEnergy.GaussComposite.ActualDressedReaderComponents.temporal_reader_compensation_price

elab "checked_cut_tail_generatedContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualDressedCutReturn.cut_tail_generated).type
theorem checked_cut_tail_generated : checked_cut_tail_generatedContract := @LowEnergy.GaussComposite.ActualDressedCutReturn.cut_tail_generated

elab "checked_cut_jet_error_priceContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualDressedCutReturn.cut_jet_error_price).type
theorem checked_cut_jet_error_price : checked_cut_jet_error_priceContract := @LowEnergy.GaussComposite.ActualDressedCutReturn.cut_jet_error_price

elab "checked_cut_retainer_leak_retainedContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualDressedCutReturn.cut_retainer_leak_retained).type
theorem checked_cut_retainer_leak_retained : checked_cut_retainer_leak_retainedContract := @LowEnergy.GaussComposite.ActualDressedCutReturn.cut_retainer_leak_retained

elab "checked_joint_generator_originalContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualDressedCutReturn.joint_generator_original).type
theorem checked_joint_generator_original : checked_joint_generator_originalContract := @LowEnergy.GaussComposite.ActualDressedCutReturn.joint_generator_original

elab "checked_cut_resolvent_returnContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualDressedCutReturn.cut_resolvent_return).type
theorem checked_cut_resolvent_return : checked_cut_resolvent_returnContract := @LowEnergy.GaussComposite.ActualDressedCutReturn.cut_resolvent_return

elab "checked_cut_resolvent_error_priceContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualDressedCutReturn.cut_resolvent_error_price).type
theorem checked_cut_resolvent_error_price : checked_cut_resolvent_error_priceContract := @LowEnergy.GaussComposite.ActualDressedCutReturn.cut_resolvent_error_price

elab "checked_temporal_cut_noether_matchContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualDressedReaderMatching.temporal_cut_noether_match).type
theorem checked_temporal_cut_noether_match : checked_temporal_cut_noether_matchContract := @LowEnergy.GaussComposite.ActualDressedReaderMatching.temporal_cut_noether_match

elab "checked_dressed_temporal_cut_noetherContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualDressedReaderMatching.dressed_temporal_cut_noether).type
theorem checked_dressed_temporal_cut_noether : checked_dressed_temporal_cut_noetherContract := @LowEnergy.GaussComposite.ActualDressedReaderMatching.dressed_temporal_cut_noether

elab "checked_dressed_temporal_coulomb_matchContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualDressedReaderMatching.dressed_temporal_coulomb_match).type
theorem checked_dressed_temporal_coulomb_match : checked_dressed_temporal_coulomb_matchContract := @LowEnergy.GaussComposite.ActualDressedReaderMatching.dressed_temporal_coulomb_match

elab "checked_dressed_original_retainedContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualDressedReaderMatching.dressed_original_retained).type
theorem checked_dressed_original_retained : checked_dressed_original_retainedContract := @LowEnergy.GaussComposite.ActualDressedReaderMatching.dressed_original_retained

elab "checked_dressed_original_right_leakContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualDressedReaderMatching.dressed_original_right_leak).type
theorem checked_dressed_original_right_leak : checked_dressed_original_right_leakContract := @LowEnergy.GaussComposite.ActualDressedReaderMatching.dressed_original_right_leak

open SaturationMonoid.PhysicsCore SaturationMonoid.PhysicsCore.LowEnergy
open StageNineHolonomicField StageNineCurrentCoframeMatterTemporalPrincipal
open FullQuantum FullQuantum.CoframeResponse FullQuantum.StateGreen
open PreparationVacuumSourceFieldFamily PreparationVacuumMixedFieldReturn
open PreparationVacuumGaugeSourceInjection PreparationVacuumOriginalDensity
open PreparationVacuumActualFieldQuantization PreparationVacuumNonlinearFieldCurve
open SourceQuantumFockGauge SourceQuantumGaugeSliceCoordinates SourceQuantumConfigurationHilbert
open GaussHistoryHilbert GaussQuantumMultiplier GaussCoreDifferential CanonicalGradedSpatialSource
open scoped Matrix BigOperators
local instance : DecidableEq Quantum.Index:=Classical.decEq _
local instance : DecidableEq Mode:=Classical.decEq _
attribute [local instance] SourceRealScalarFock.branchOrder

open GaussCoreHilbert PreparationVacuumPhysicalFeedback PreparationVacuumJointFieldResponse
open GaussNativeMatter CanonicalGradedCharge PreparationPhysicalPhaseGaugeRealization GaussComposite.PhysicalEMPoleWard
open PreparationVacuumActionFieldLift GaussComposite.PhysicalEMGaugeRealization
open PreparationPhysicalActionUnits GaussComposite.PhysicalEMVoltage PreparationPhysicalNormalizedFullField GaussComposite.ActualDressedSourcePreparation GaussComposite.ActualDressedSourceResponse PreparationVacuumFullElectricWard


open ActualDressedActionPhase PreparationVacuumTemporalCharge PreparationVacuumLowerClassical


open ActualDressedTemporalNormalization GaussFockPair PreparationVacuumSourceActionJets
open MeasureTheory Filter Set


open ActualDressedTemporalForm ActualDressedJointTemporal ActualDressedJointOrbitCurrent
open ActualDressedFullCoulomb PreparationVacuumWeightedChargeActionWard
open PreparationVacuumSourceChargeWard PreparationVacuumNoetherOrdinaryWard
open PreparationVacuumFullFieldRiesz PreparationVacuumNoetherChart
open scoped Topology InnerProductSpace
open PreparationVacuumFieldConstraintResponse CanonicalPhysicalYResolvent PreparationVacuumSourcePreparedResponse
open CanonicalPreparationCore.Completed CanonicalScalarPreparation GaussComposite.SourceGraph
attribute [local irreducible] sourceDressedUnit sourceDressedExcitation sourceProfile finiteFull sourceDressedResponse chargeReader


open PreparationVacuumFieldCovector PreparationVacuumRawJointFeedback PreparationVacuumCausalFieldResponse
open PreparationVacuumActionDecomposition PreparationVacuumGradedTransport
open ActualDressedTemporalCurrent


open ActualDressedReaderComponents ActualDressedCutReturn ActualDressedNoether
open CanonicalPhysicalYResolvent
attribute [local irreducible] currentVertex currentRestriction temporalReaderCompensation noetherReader
  jointResolvent dressedEulerObserver


open ActualDressedReaderMatching
open PreparationVacuumYukawaTransport PreparationVacuumUncutYukawa
open CanonicalPhysicalSpatial FullYSourceCutoffVolterra
theorem checked_actual_event_nonempty : Nonempty DressedEvent := by
  exact ⟨{
    epsilon := 1
    precision := by norm_num
    momentum := 0
    frame := Classical.choice inferInstance
    cut := 0
    energy := Complex.I
    nonreal := by simp }⟩

theorem checked_actual_unit_nonzero (event : DressedEvent) : sourceDressedUnit event.epsilon event.precision≠0 := by
  intro h
  have paid:=source_dressed_unit_norm event.epsilon event.precision
  rw [h,norm_zero] at paid
  exact zero_ne_one paid

theorem checked_generic_leak_cannot_drop : (0:ℂ)-1≠0-0*1 := by norm_num

end LowEnergy.GaussComposite.ActualDressedReaderMatchingAudit

open Lean Elab Command
private def packageCertChildren (info : ConstantInfo) : Array Name := Id.run do
  let mut children := info.type.getUsedConstants
  if let some value := info.value? (allowOpaque := true) then
    children := children ++ value.getUsedConstants
  if let .inductInfo value := info then children := children ++ value.ctors.toArray
  if let .recInfo value := info then
    for rule in value.rules do children := children ++ rule.rhs.getUsedConstants
  return children

private def packageCertClosure (env : Environment)
    (roots : List Name) : CommandElabM NameSet := do
  let mut pending := roots
  let mut seen : NameSet := {}
  while !pending.isEmpty do
    let name := pending.head!
    pending := pending.tail!
    unless seen.contains name do
      let some info := env.checked.get.find? name | throwError m!"UNKNOWN {name}"
      pending := (packageCertChildren info).toList ++ pending
      seen := seen.insert name
  return seen


private def packageCertRequire (env : Environment) (root : Name) (required : Array Name) : CommandElabM Unit := do
  let mut pending := [root]
  let mut seen : NameSet := {}
  let mut found : NameSet := {}
  while !pending.isEmpty && !(required.all found.contains) do
    let name := pending.head!
    pending := pending.tail!
    unless seen.contains name do
      let some info := env.checked.get.find? name | throwError m!"UNKNOWN {name}"
      let children := packageCertChildren info
      for target in required do
        if name == target || children.contains target then found := found.insert target
      pending := children.toList ++ pending
      seen := seen.insert name
  for name in required do
    unless found.contains name do throwError m!"UNCONSUMED_DIRECT {root} {name}"

elab "#audit_dressed_reader_matching" : command => do
  let env ← getEnv
  let modules := env.header.moduleNames
  let owner := fun name => (env.getModuleIdxFor? name).map fun i => modules[i.toNat]!
  let candidates := #[`H0mework.Versions.R71e.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualDressedReaderComponents,`H0mework.Versions.R71e.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualDressedCutReturn,`H0mework.Versions.R71e.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualDressedReaderMatching]
  let owned := env.constants.toList.filterMap fun (name, _) =>
    if (owner name).any candidates.contains then some name else none
  let mouths := #[
    ``LowEnergy.GaussComposite.ActualDressedReaderComponents.temporalFiberResidualSample,
    ``LowEnergy.GaussComposite.ActualDressedReaderComponents.temporal_fiber_residual_source,
    ``LowEnergy.GaussComposite.ActualDressedReaderComponents.temporal_fiber_residual_integrable,
    ``LowEnergy.GaussComposite.ActualDressedReaderComponents.temporal_fiber_first,
    ``LowEnergy.GaussComposite.ActualDressedReaderComponents.temporalReaderCompensationForm,
    ``LowEnergy.GaussComposite.ActualDressedReaderComponents.temporal_reader_form_generated,
    ``LowEnergy.GaussComposite.ActualDressedReaderComponents.temporalReaderCompensation,
    ``LowEnergy.GaussComposite.ActualDressedReaderComponents.temporal_reader_generated,
    ``LowEnergy.GaussComposite.ActualDressedReaderComponents.temporal_reader_compensation_price,
    ``LowEnergy.GaussComposite.ActualDressedCutReturn.cutJetError,
    ``LowEnergy.GaussComposite.ActualDressedCutReturn.cutRetainerLeak,
    ``LowEnergy.GaussComposite.ActualDressedCutReturn.cut_tail_generated,
    ``LowEnergy.GaussComposite.ActualDressedCutReturn.cut_jet_error_price,
    ``LowEnergy.GaussComposite.ActualDressedCutReturn.cut_retainer_leak_retained,
    ``LowEnergy.GaussComposite.ActualDressedCutReturn.joint_generator_original,
    ``LowEnergy.GaussComposite.ActualDressedCutReturn.cut_resolvent_return,
    ``LowEnergy.GaussComposite.ActualDressedCutReturn.cut_resolvent_error_price,
    ``LowEnergy.GaussComposite.ActualDressedReaderMatching.temporalCutCompensation,
    ``LowEnergy.GaussComposite.ActualDressedReaderMatching.temporal_cut_noether_match,
    ``LowEnergy.GaussComposite.ActualDressedReaderMatching.dressed_temporal_cut_noether,
    ``LowEnergy.GaussComposite.ActualDressedReaderMatching.dressed_temporal_coulomb_match,
    ``LowEnergy.GaussComposite.ActualDressedReaderMatching.dressed_original_retained,
    ``LowEnergy.GaussComposite.ActualDressedReaderMatching.dressed_original_right_leak]
  for name in mouths do
    unless owned.contains name do throwError m!"MISSING_MOUTH {name}"
  let tests := #[
    ``LowEnergy.GaussComposite.ActualDressedReaderMatchingAudit.checked_temporal_fiber_residual_source,
    ``LowEnergy.GaussComposite.ActualDressedReaderMatchingAudit.checked_temporal_fiber_residual_integrable,
    ``LowEnergy.GaussComposite.ActualDressedReaderMatchingAudit.checked_temporal_fiber_first,
    ``LowEnergy.GaussComposite.ActualDressedReaderMatchingAudit.checked_temporal_reader_form_generated,
    ``LowEnergy.GaussComposite.ActualDressedReaderMatchingAudit.checked_temporal_reader_generated,
    ``LowEnergy.GaussComposite.ActualDressedReaderMatchingAudit.checked_temporal_reader_compensation_price,
    ``LowEnergy.GaussComposite.ActualDressedReaderMatchingAudit.checked_cut_tail_generated,
    ``LowEnergy.GaussComposite.ActualDressedReaderMatchingAudit.checked_cut_jet_error_price,
    ``LowEnergy.GaussComposite.ActualDressedReaderMatchingAudit.checked_cut_retainer_leak_retained,
    ``LowEnergy.GaussComposite.ActualDressedReaderMatchingAudit.checked_joint_generator_original,
    ``LowEnergy.GaussComposite.ActualDressedReaderMatchingAudit.checked_cut_resolvent_return,
    ``LowEnergy.GaussComposite.ActualDressedReaderMatchingAudit.checked_cut_resolvent_error_price,
    ``LowEnergy.GaussComposite.ActualDressedReaderMatchingAudit.checked_temporal_cut_noether_match,
    ``LowEnergy.GaussComposite.ActualDressedReaderMatchingAudit.checked_dressed_temporal_cut_noether,
    ``LowEnergy.GaussComposite.ActualDressedReaderMatchingAudit.checked_dressed_temporal_coulomb_match,
    ``LowEnergy.GaussComposite.ActualDressedReaderMatchingAudit.checked_dressed_original_retained,
    ``LowEnergy.GaussComposite.ActualDressedReaderMatchingAudit.checked_dressed_original_right_leak,
    ``LowEnergy.GaussComposite.ActualDressedReaderMatchingAudit.checked_actual_event_nonempty,
    ``LowEnergy.GaussComposite.ActualDressedReaderMatchingAudit.checked_actual_unit_nonzero,
    ``LowEnergy.GaussComposite.ActualDressedReaderMatchingAudit.checked_generic_leak_cannot_drop]
  let direct := #[
    (``LowEnergy.GaussComposite.ActualDressedReaderComponents.temporal_fiber_residual_source,#[
    ``LowEnergy.PreparationVacuumFieldCovector.fiber_sample_mother_balance]),
    (``LowEnergy.GaussComposite.ActualDressedReaderComponents.temporal_fiber_first,#[
    ``LowEnergy.GaussComposite.ActualDressedReaderComponents.temporal_fiber_residual_source,
    ``LowEnergy.GaussComposite.ActualDressedReaderComponents.temporal_fiber_residual_integrable]),
    (``LowEnergy.GaussComposite.ActualDressedReaderComponents.temporal_reader_form_generated,#[
    ``LowEnergy.GaussComposite.ActualDressedReaderComponents.temporal_fiber_first,
    ``LowEnergy.GaussComposite.ActualDressedTemporalCurrent.temporal_raw_noether_return]),
    (``LowEnergy.GaussComposite.ActualDressedReaderComponents.temporal_reader_generated,#[
    ``LowEnergy.GaussComposite.ActualDressedReaderComponents.temporal_reader_form_generated]),
    (``LowEnergy.GaussComposite.ActualDressedCutReturn.cut_tail_generated,#[
    ``LowEnergy.PreparationVacuumYukawaTransport.jetOperator_cutoff]),
    (``LowEnergy.GaussComposite.ActualDressedCutReturn.cut_jet_error_price,#[
    ``LowEnergy.PreparationVacuumUncutYukawa.operator_error_bound]),
    (``LowEnergy.GaussComposite.ActualDressedCutReturn.cut_resolvent_return,#[
    ``LowEnergy.GaussComposite.ActualDressedCutReturn.joint_generator_original,
    ``LowEnergy.GaussComposite.ActualDressedCutReturn.cut_tail_generated,
    ``LowEnergy.CanonicalPhysicalYResolvent.finiteFull_left,
    ``LowEnergy.PreparationVacuumJointFieldResponse.jointGenerator_unit]),
    (``LowEnergy.GaussComposite.ActualDressedCutReturn.cut_resolvent_error_price,#[
    ``LowEnergy.GaussComposite.ActualDressedCutReturn.cut_resolvent_return,
    ``LowEnergy.GaussComposite.ActualDressedCutReturn.cut_jet_error_price,
    ``LowEnergy.CanonicalPhysicalYResolvent.finiteFull_bound]),
    (``LowEnergy.GaussComposite.ActualDressedReaderMatching.temporal_cut_noether_match,#[
    ``LowEnergy.GaussComposite.ActualDressedReaderComponents.temporal_reader_generated,
    ``LowEnergy.GaussComposite.ActualDressedCutReturn.cut_resolvent_return]),
    (``LowEnergy.GaussComposite.ActualDressedReaderMatching.dressed_temporal_cut_noether,#[
    ``LowEnergy.GaussComposite.ActualDressedReaderMatching.temporal_cut_noether_match,
    ``LowEnergy.GaussComposite.ActualDressedNoether.dressedNoetherKernel]),
    (``LowEnergy.GaussComposite.ActualDressedReaderMatching.dressed_temporal_coulomb_match,#[
    ``LowEnergy.GaussComposite.ActualDressedReaderMatching.dressed_temporal_cut_noether,
    ``LowEnergy.PreparationVacuumFieldCovector.field_first_coordinates,
    ``LowEnergy.GaussComposite.ActualDressedFullCoulomb.dressedCurrent,
    ``LowEnergy.GaussComposite.ActualDressedNoether.dressed_euler_observer_original]),
    (``LowEnergy.GaussComposite.ActualDressedReaderMatching.dressed_original_retained,#[
    ``LowEnergy.PreparationVacuumYukawaTransport.profileLeg_retained,
    ``LowEnergy.PreparationVacuumYukawaTransport.sourceCarrier_retained,
    ``LowEnergy.GaussComposite.ActualDressedSourcePreparation.source_dressed_unit_original]),
    (``LowEnergy.GaussComposite.ActualDressedReaderMatching.dressed_original_right_leak,#[
    ``LowEnergy.GaussComposite.ActualDressedReaderMatching.dressed_original_retained,
    ``LowEnergy.GaussComposite.ActualDressedCutReturn.cut_retainer_leak_retained,
    ``LowEnergy.PreparationVacuumUncutYukawa.sourceResolvent_retained])]
  for (mouth,required) in direct do packageCertRequire env mouth required
  let testProducers := #[
    ``LowEnergy.GaussComposite.ActualDressedReaderComponents.temporal_fiber_residual_source,
    ``LowEnergy.GaussComposite.ActualDressedReaderComponents.temporal_fiber_residual_integrable,
    ``LowEnergy.GaussComposite.ActualDressedReaderComponents.temporal_fiber_first,
    ``LowEnergy.GaussComposite.ActualDressedReaderComponents.temporal_reader_form_generated,
    ``LowEnergy.GaussComposite.ActualDressedReaderComponents.temporal_reader_generated,
    ``LowEnergy.GaussComposite.ActualDressedReaderComponents.temporal_reader_compensation_price,
    ``LowEnergy.GaussComposite.ActualDressedCutReturn.cut_tail_generated,
    ``LowEnergy.GaussComposite.ActualDressedCutReturn.cut_jet_error_price,
    ``LowEnergy.GaussComposite.ActualDressedCutReturn.cut_retainer_leak_retained,
    ``LowEnergy.GaussComposite.ActualDressedCutReturn.joint_generator_original,
    ``LowEnergy.GaussComposite.ActualDressedCutReturn.cut_resolvent_return,
    ``LowEnergy.GaussComposite.ActualDressedCutReturn.cut_resolvent_error_price,
    ``LowEnergy.GaussComposite.ActualDressedReaderMatching.temporal_cut_noether_match,
    ``LowEnergy.GaussComposite.ActualDressedReaderMatching.dressed_temporal_cut_noether,
    ``LowEnergy.GaussComposite.ActualDressedReaderMatching.dressed_temporal_coulomb_match,
    ``LowEnergy.GaussComposite.ActualDressedReaderMatching.dressed_original_retained,
    ``LowEnergy.GaussComposite.ActualDressedReaderMatching.dressed_original_right_leak]
  for i in [:testProducers.size] do packageCertRequire env tests[i]! #[testProducers[i]!]
  let all ← packageCertClosure env (owned ++ tests.toList)
  let anchors := #[
    ``SaturationMonoid.PhysicsCore.StageNineEnrichedProofFreeSource.positiveSmoothUnifiedSource,
    ``SaturationMonoid.PhysicsCore.Stage9C.Material.SpinPair.actual,
    ``LowEnergy.GaussComposite.ActualDressedSourcePreparation.sourceDressedUnit,
    ``LowEnergy.PreparationVacuumSourcePreparedResponse.sourceProfile,
    ``LowEnergy.GaussComposite.ActualDressedNoether.dressedEulerObserver,
    ``LowEnergy.GaussComposite.ActualDressedNoether.dressedNoetherKernel,
    ``LowEnergy.GaussComposite.ActualDressedFullCoulomb.dressedCurrent,
    ``LowEnergy.PreparationVacuumNoetherChart.noetherReader,
    ``LowEnergy.PreparationVacuumJointFieldResponse.jointResolvent,
    ``LowEnergy.CanonicalPhysicalYResolvent.finiteFull,
    ``LowEnergy.PreparationPhysicalActionUnits.sourceTimeWeightCore,
    ``LowEnergy.PreparationVacuumFieldConstraintResponse.fieldJets]
  for name in anchors do
    unless all.contains name do throwError m!"UNCONSUMED_SOURCE {name}"
  let allowed := #[``propext,``Classical.choice,``Quot.sound]
  let mut axioms : Nat := 0
  let mut opaques : Nat := 0
  for name in all.toArray do
    let some info := env.checked.get.find? name | throwError m!"UNKNOWN {name}"
    if info.isUnsafe || info.isPartial then throwError m!"UNTRUSTED {name}"
    match info with
    | .defnInfo _ | .thmInfo _ | .opaqueInfo _ =>
      unless (info.value? (allowOpaque := true)).isSome do throwError m!"UNREAD {name}"
    | _ => pure ()
    if let .opaqueInfo _ := info then opaques := opaques + 1
    if let .axiomInfo _ := info then
      axioms := axioms + 1
      unless allowed.contains name do throwError m!"UNAUTHORIZED_AXIOM {name}"
  for name in #[`SaturationMonoid.StandardModelConstraint.alphaEMIntegerDenominator,
      `SaturationMonoid.StandardModelConstraint.alphaEMFromIntegerConstraint,
      `SaturationMonoid.StandardModelConstraint.gutWeakMixingInformationRatio,
      `SaturationMonoid.StandardModelConstraint.alphaStrongDisplayed] do
    if all.contains name then throwError m!"TARGET_CONTAMINATION {name}"
  if let some path ← liftIO (IO.getEnv "ALPHA_DRESSED_READER_MATCHING_AUDIT_OUTPUT") then
    let project := all.toArray.filter fun name =>
      match owner name with
      | none => false
      | some m => !(#["Mathlib","Init","Lean","Std","Batteries","Aesop","Qq","Plausible","ImportGraph","ProofWidgets"].any (fun h => h.isPrefixOf m.toString))
    liftIO <| IO.FS.writeFile path <| (Json.mkObj [
      ("owned",toJson (owned.map Name.toString)),("public",toJson (mouths.map Name.toString)),
      ("tests",toJson (tests.map Name.toString)),("nodes",toJson all.size),("opaque_read",toJson opaques),
      ("axioms",toJson axioms),("anchors",toJson (anchors.map Name.toString)),
      ("direct",toJson (direct.map fun p => (p.1.toString,p.2.map Name.toString))),
      ("project",toJson (project.map fun n => (n.toString,(owner n).map Name.toString)))]).compress
  logInfo m!"DRESSED_READER_MATCHING_PASS public={mouths.size} owned={owned.length} tests={tests.size} nodes={all.size} anchors={anchors.size} direct={direct.size} opaque_all_read={opaques} axioms={axioms} unknown=0 unsafe=0 partial=0"
#audit_dressed_reader_matching
#print axioms LowEnergy.GaussComposite.ActualDressedReaderComponents.temporal_fiber_residual_source
#print axioms LowEnergy.GaussComposite.ActualDressedReaderComponents.temporal_fiber_residual_integrable
#print axioms LowEnergy.GaussComposite.ActualDressedReaderComponents.temporal_fiber_first
#print axioms LowEnergy.GaussComposite.ActualDressedReaderComponents.temporal_reader_form_generated
#print axioms LowEnergy.GaussComposite.ActualDressedReaderComponents.temporal_reader_generated
#print axioms LowEnergy.GaussComposite.ActualDressedReaderComponents.temporal_reader_compensation_price
#print axioms LowEnergy.GaussComposite.ActualDressedCutReturn.cut_tail_generated
#print axioms LowEnergy.GaussComposite.ActualDressedCutReturn.cut_jet_error_price
#print axioms LowEnergy.GaussComposite.ActualDressedCutReturn.cut_retainer_leak_retained
#print axioms LowEnergy.GaussComposite.ActualDressedCutReturn.joint_generator_original
#print axioms LowEnergy.GaussComposite.ActualDressedCutReturn.cut_resolvent_return
#print axioms LowEnergy.GaussComposite.ActualDressedCutReturn.cut_resolvent_error_price
#print axioms LowEnergy.GaussComposite.ActualDressedReaderMatching.temporal_cut_noether_match
#print axioms LowEnergy.GaussComposite.ActualDressedReaderMatching.dressed_temporal_cut_noether
#print axioms LowEnergy.GaussComposite.ActualDressedReaderMatching.dressed_temporal_coulomb_match
#print axioms LowEnergy.GaussComposite.ActualDressedReaderMatching.dressed_original_retained
#print axioms LowEnergy.GaussComposite.ActualDressedReaderMatching.dressed_original_right_leak
