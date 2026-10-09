import H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualDressedPreparationWardResidual
import H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualDressedTemporalHalfResidual
import H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualDressedTemporalQuantumResidual
import H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualDressedStaticPoleWard

import Lean.Elab.Command
import Lean.Util.FoldConsts
import Lean.Util.CollectAxioms
set_option autoImplicit false
set_option maxHeartbeats 12000000
set_option maxRecDepth 32768
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.GaussComposite.ActualDressedTemporalResidualAudit
elab "checked_preparation_ward_residual_returnContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualDressedTemporalResidual.preparation_ward_residual_return).type
theorem checked_preparation_ward_residual_return : checked_preparation_ward_residual_returnContract := @LowEnergy.GaussComposite.ActualDressedTemporalResidual.preparation_ward_residual_return

elab "checked_preparation_ward_observer_priceContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualDressedTemporalResidual.preparation_ward_observer_price).type
theorem checked_preparation_ward_observer_price : checked_preparation_ward_observer_priceContract := @LowEnergy.GaussComposite.ActualDressedTemporalResidual.preparation_ward_observer_price

elab "checked_preparation_ward_observer_limitContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualDressedTemporalResidual.preparation_ward_observer_limit).type
theorem checked_preparation_ward_observer_limit : checked_preparation_ward_observer_limitContract := @LowEnergy.GaussComposite.ActualDressedTemporalResidual.preparation_ward_observer_limit

elab "checked_physical_preparation_returnContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualDressedTemporalResidual.physical_preparation_return).type
theorem checked_physical_preparation_return : checked_physical_preparation_returnContract := @LowEnergy.GaussComposite.ActualDressedTemporalResidual.physical_preparation_return

elab "checked_temporal_half_physical_actionContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualDressedTemporalResidual.temporal_half_physical_action).type
theorem checked_temporal_half_physical_action : checked_temporal_half_physical_actionContract := @LowEnergy.GaussComposite.ActualDressedTemporalResidual.temporal_half_physical_action

elab "checked_temporal_half_preparation_returnContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualDressedTemporalResidual.temporal_half_preparation_return).type
theorem checked_temporal_half_preparation_return : checked_temporal_half_preparation_returnContract := @LowEnergy.GaussComposite.ActualDressedTemporalResidual.temporal_half_preparation_return

elab "checked_temporal_half_preparation_priceContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualDressedTemporalResidual.temporal_half_preparation_price).type
theorem checked_temporal_half_preparation_price : checked_temporal_half_preparation_priceContract := @LowEnergy.GaussComposite.ActualDressedTemporalResidual.temporal_half_preparation_price

elab "checked_temporal_half_preparation_limitContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualDressedTemporalResidual.temporal_half_preparation_limit).type
theorem checked_temporal_half_preparation_limit : checked_temporal_half_preparation_limitContract := @LowEnergy.GaussComposite.ActualDressedTemporalResidual.temporal_half_preparation_limit

elab "checked_temporal_quantum_physical_actionContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualDressedTemporalResidual.temporal_quantum_physical_action).type
theorem checked_temporal_quantum_physical_action : checked_temporal_quantum_physical_actionContract := @LowEnergy.GaussComposite.ActualDressedTemporalResidual.temporal_quantum_physical_action

elab "checked_temporal_quantum_preparation_returnContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualDressedTemporalResidual.temporal_quantum_preparation_return).type
theorem checked_temporal_quantum_preparation_return : checked_temporal_quantum_preparation_returnContract := @LowEnergy.GaussComposite.ActualDressedTemporalResidual.temporal_quantum_preparation_return

elab "checked_temporal_quantum_preparation_priceContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualDressedTemporalResidual.temporal_quantum_preparation_price).type
theorem checked_temporal_quantum_preparation_price : checked_temporal_quantum_preparation_priceContract := @LowEnergy.GaussComposite.ActualDressedTemporalResidual.temporal_quantum_preparation_price

elab "checked_temporal_quantum_preparation_limitContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualDressedTemporalResidual.temporal_quantum_preparation_limit).type
theorem checked_temporal_quantum_preparation_limit : checked_temporal_quantum_preparation_limitContract := @LowEnergy.GaussComposite.ActualDressedTemporalResidual.temporal_quantum_preparation_limit

elab "checked_source_leading_pencil_zeroContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualDressedTemporalResidual.source_leading_pencil_zero).type
theorem checked_source_leading_pencil_zero : checked_source_leading_pencil_zeroContract := @LowEnergy.GaussComposite.ActualDressedTemporalResidual.source_leading_pencil_zero

elab "checked_source_leading_physical_actionContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualDressedTemporalResidual.source_leading_physical_action).type
theorem checked_source_leading_physical_action : checked_source_leading_physical_actionContract := @LowEnergy.GaussComposite.ActualDressedTemporalResidual.source_leading_physical_action

elab "checked_static_pole_physical_actionContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualDressedTemporalResidual.static_pole_physical_action).type
theorem checked_static_pole_physical_action : checked_static_pole_physical_actionContract := @LowEnergy.GaussComposite.ActualDressedTemporalResidual.static_pole_physical_action

elab "checked_static_pole_preparation_returnContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualDressedTemporalResidual.static_pole_preparation_return).type
theorem checked_static_pole_preparation_return : checked_static_pole_preparation_returnContract := @LowEnergy.GaussComposite.ActualDressedTemporalResidual.static_pole_preparation_return

elab "checked_static_pole_preparation_priceContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualDressedTemporalResidual.static_pole_preparation_price).type
theorem checked_static_pole_preparation_price : checked_static_pole_preparation_priceContract := @LowEnergy.GaussComposite.ActualDressedTemporalResidual.static_pole_preparation_price

elab "checked_static_pole_preparation_limitContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualDressedTemporalResidual.static_pole_preparation_limit).type
theorem checked_static_pole_preparation_limit : checked_static_pole_preparation_limitContract := @LowEnergy.GaussComposite.ActualDressedTemporalResidual.static_pole_preparation_limit

open CanonicalGradedSpatialSource GaussCoreHilbert
open PreparationVacuumMixedFieldReturn PreparationVacuumActionFieldLift
open PreparationVacuumPhysicalFeedback PreparationVacuumGaugeSourceInjection PreparationVacuumNoetherOrdinaryWard
open PreparationVacuumSourcePreparedState PreparationVacuumPreparedCurrent
open ActualDressedFullCoulomb ActualDressedNoether ActualDressedSylvester ActualDressedStaticResponse
open ActualDressedTemporalHalf ActualDressedTemporalResidual ActualDressedStaticPole ActualDressedPreparationEnergy
open Filter
open scoped Topology Matrix

theorem actual_event_nonempty : Nonempty DressedEvent := by
  exact ⟨{
    epsilon := 1
    precision := by norm_num
    momentum := 0
    frame := Classical.choice inferInstance
    cut := 0
    energy := Complex.I
    nonreal := by simp
  }⟩

theorem actual_nonreal_not_variational_energy (event : DressedEvent) : event.energy≠(sourceEnergy:ℂ) := by
  intro same
  apply event.nonreal
  rw [same]
  exact Complex.ofReal_im _

theorem actual_all289_temporal_quantum (event : DressedEvent) (a : Fin 12) (j : Fin 289) :
    (staticQuantumCorrection event 0 1*ᵥ(fun k=>(fieldUnit j k:ℂ))) (gaugeSlot 0 a)-
      dressedEulerObserver event (temporalGaussInitialJet (dressedKinematicPoint event 0) a (fieldUnit j))-
      Complex.I*dressedEulerObserver event (temporalPhysicalDrive (dressedKinematicPoint event 0) a (fieldUnit j) 1)-
      Complex.I*physicalPreparationMismatch event 0
        (temporalGaussHalfJet (dressedKinematicPoint event 0) a (fieldUnit j) 1)=
      Complex.I*preparationWardObserver event
        (temporalGaussHalfJet (dressedKinematicPoint event 0) a (fieldUnit j) 1) :=
  temporal_quantum_preparation_return event 0 a (fieldUnit j) 1 (by norm_num)

theorem actual_all289_pole_preparation (event : DressedEvent) (i j : Fin 289) :
    physicalPreparationMismatch event 0
      (staticPoleLeadingOperator (dressedKinematicPoint event 0) (fieldUnit i) (fieldUnit j))=
      -preparationWardObserver event
        (staticPoleLeadingOperator (dressedKinematicPoint event 0) (fieldUnit i) (fieldUnit j)) :=
  static_pole_preparation_return event (fieldUnit i) (fieldUnit j)

theorem actual_all289_pole_preparation_limit (event : DressedEvent) (i j : Fin 289) :
    Tendsto (fun n : ℕ=>physicalPreparationMismatch (preparationEventSequence event n) 0
      (staticPoleLeadingOperator (dressedKinematicPoint (preparationEventSequence event n) 0) (fieldUnit i) (fieldUnit j)))
      atTop (𝓝 0) :=
  static_pole_preparation_limit event (fieldUnit i) (fieldUnit j)
end LowEnergy.GaussComposite.ActualDressedTemporalResidualAudit

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

elab "#audit_dressed_temporal_residual" : command => do
  let env ← getEnv
  let modules := env.header.moduleNames
  let owner := fun name => (env.getModuleIdxFor? name).map fun i => modules[i.toNat]!
  let candidates := #[`H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualDressedPreparationWardResidual,`H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualDressedTemporalHalfResidual,`H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualDressedTemporalQuantumResidual,`H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualDressedStaticPoleWard]
  let owned := env.constants.toList.filterMap fun (name, _) =>
    if (owner name).any candidates.contains then some name else none
  let mouths := #[
    ``LowEnergy.GaussComposite.ActualDressedTemporalResidual.preparationLeftObserver,
    ``LowEnergy.GaussComposite.ActualDressedTemporalResidual.preparationRightObserver,
    ``LowEnergy.GaussComposite.ActualDressedTemporalResidual.preparationWardObserver,
    ``LowEnergy.GaussComposite.ActualDressedTemporalResidual.preparation_ward_residual_return,
    ``LowEnergy.GaussComposite.ActualDressedTemporalResidual.preparation_ward_observer_price,
    ``LowEnergy.GaussComposite.ActualDressedTemporalResidual.preparation_ward_observer_limit,
    ``LowEnergy.GaussComposite.ActualDressedTemporalResidual.physicalPreparationMismatch,
    ``LowEnergy.GaussComposite.ActualDressedTemporalResidual.physical_preparation_return,
    ``LowEnergy.GaussComposite.ActualDressedTemporalResidual.temporal_half_physical_action,
    ``LowEnergy.GaussComposite.ActualDressedTemporalResidual.temporal_half_preparation_return,
    ``LowEnergy.GaussComposite.ActualDressedTemporalResidual.temporal_half_preparation_price,
    ``LowEnergy.GaussComposite.ActualDressedTemporalResidual.temporal_half_preparation_limit,
    ``LowEnergy.GaussComposite.ActualDressedTemporalResidual.temporalPhysicalDrive,
    ``LowEnergy.GaussComposite.ActualDressedTemporalResidual.temporal_quantum_physical_action,
    ``LowEnergy.GaussComposite.ActualDressedTemporalResidual.temporal_quantum_preparation_return,
    ``LowEnergy.GaussComposite.ActualDressedTemporalResidual.temporal_quantum_preparation_price,
    ``LowEnergy.GaussComposite.ActualDressedTemporalResidual.temporal_quantum_preparation_limit,
    ``LowEnergy.GaussComposite.ActualDressedTemporalResidual.source_leading_pencil_zero,
    ``LowEnergy.GaussComposite.ActualDressedTemporalResidual.source_leading_physical_action,
    ``LowEnergy.GaussComposite.ActualDressedTemporalResidual.static_pole_physical_action,
    ``LowEnergy.GaussComposite.ActualDressedTemporalResidual.static_pole_preparation_return,
    ``LowEnergy.GaussComposite.ActualDressedTemporalResidual.static_pole_preparation_price,
    ``LowEnergy.GaussComposite.ActualDressedTemporalResidual.static_pole_preparation_limit]
  for name in mouths do
    unless owned.contains name do throwError m!"MISSING_MOUTH {name}"
  let tests := #[
    ``LowEnergy.GaussComposite.ActualDressedTemporalResidualAudit.checked_preparation_ward_residual_return,
    ``LowEnergy.GaussComposite.ActualDressedTemporalResidualAudit.checked_preparation_ward_observer_price,
    ``LowEnergy.GaussComposite.ActualDressedTemporalResidualAudit.checked_preparation_ward_observer_limit,
    ``LowEnergy.GaussComposite.ActualDressedTemporalResidualAudit.checked_physical_preparation_return,
    ``LowEnergy.GaussComposite.ActualDressedTemporalResidualAudit.checked_temporal_half_physical_action,
    ``LowEnergy.GaussComposite.ActualDressedTemporalResidualAudit.checked_temporal_half_preparation_return,
    ``LowEnergy.GaussComposite.ActualDressedTemporalResidualAudit.checked_temporal_half_preparation_price,
    ``LowEnergy.GaussComposite.ActualDressedTemporalResidualAudit.checked_temporal_half_preparation_limit,
    ``LowEnergy.GaussComposite.ActualDressedTemporalResidualAudit.checked_temporal_quantum_physical_action,
    ``LowEnergy.GaussComposite.ActualDressedTemporalResidualAudit.checked_temporal_quantum_preparation_return,
    ``LowEnergy.GaussComposite.ActualDressedTemporalResidualAudit.checked_temporal_quantum_preparation_price,
    ``LowEnergy.GaussComposite.ActualDressedTemporalResidualAudit.checked_temporal_quantum_preparation_limit,
    ``LowEnergy.GaussComposite.ActualDressedTemporalResidualAudit.checked_source_leading_pencil_zero,
    ``LowEnergy.GaussComposite.ActualDressedTemporalResidualAudit.checked_source_leading_physical_action,
    ``LowEnergy.GaussComposite.ActualDressedTemporalResidualAudit.checked_static_pole_physical_action,
    ``LowEnergy.GaussComposite.ActualDressedTemporalResidualAudit.checked_static_pole_preparation_return,
    ``LowEnergy.GaussComposite.ActualDressedTemporalResidualAudit.checked_static_pole_preparation_price,
    ``LowEnergy.GaussComposite.ActualDressedTemporalResidualAudit.checked_static_pole_preparation_limit,
    ``LowEnergy.GaussComposite.ActualDressedTemporalResidualAudit.actual_event_nonempty,
    ``LowEnergy.GaussComposite.ActualDressedTemporalResidualAudit.actual_nonreal_not_variational_energy,
    ``LowEnergy.GaussComposite.ActualDressedTemporalResidualAudit.actual_all289_temporal_quantum,
    ``LowEnergy.GaussComposite.ActualDressedTemporalResidualAudit.actual_all289_pole_preparation,
    ``LowEnergy.GaussComposite.ActualDressedTemporalResidualAudit.actual_all289_pole_preparation_limit]
  let direct := #[
    (``LowEnergy.GaussComposite.ActualDressedTemporalResidual.preparation_ward_residual_return,#[
    ``LowEnergy.GaussComposite.ActualDressedPreparationEnergy.preparation_creation_actual,
    ``LowEnergy.GaussComposite.ActualDressedPreparationEnergy.preparation_background,
    ``LowEnergy.GaussComposite.ActualDressedTemporalResidual.preparationWardObserver]),
    (``LowEnergy.GaussComposite.ActualDressedTemporalResidual.preparation_ward_observer_price,#[
    ``LowEnergy.GaussComposite.ActualDressedPreparationEnergy.preparation_residual_price,
    ``LowEnergy.GaussComposite.ActualDressedPreparationEnergy.preparation_creation_map_price,
    ``LowEnergy.GaussComposite.ActualDressedTemporalResidual.preparation_ward_residual_return]),
    (``LowEnergy.GaussComposite.ActualDressedTemporalResidual.preparation_ward_observer_limit,#[
    ``LowEnergy.GaussComposite.ActualDressedTemporalResidual.preparation_ward_observer_price,
    ``LowEnergy.GaussComposite.ActualDressedPreparationEnergy.preparationEventSequence]),
    (``LowEnergy.GaussComposite.ActualDressedTemporalResidual.temporal_half_physical_action,#[
    ``LowEnergy.SourcePropagationResolvent.sourceInverse_left,
    ``LowEnergy.GaussComposite.ActualDressedTemporalHalf.temporal_gauss_half_inverse]),
    (``LowEnergy.GaussComposite.ActualDressedTemporalResidual.temporal_half_preparation_return,#[
    ``LowEnergy.GaussComposite.ActualDressedTemporalResidual.temporal_half_physical_action,
    ``LowEnergy.GaussComposite.ActualDressedTemporalResidual.physical_preparation_return,
    ``LowEnergy.GaussComposite.ActualDressedTemporalHalf.temporal_actual_half_source]),
    (``LowEnergy.GaussComposite.ActualDressedTemporalResidual.temporal_half_preparation_limit,#[
    ``LowEnergy.GaussComposite.ActualDressedTemporalResidual.preparation_ward_observer_limit,
    ``LowEnergy.GaussComposite.ActualDressedTemporalResidual.temporal_half_preparation_return]),
    (``LowEnergy.GaussComposite.ActualDressedTemporalResidual.temporal_quantum_physical_action,#[
    ``LowEnergy.GaussComposite.ActualDressedSylvester.noether_static_half_pencil,
    ``LowEnergy.GaussComposite.ActualDressedTemporalHalf.temporal_gauss_half_jet,
    ``LowEnergy.GaussComposite.ActualDressedTemporalHalf.temporal_gauss_initial_jet]),
    (``LowEnergy.GaussComposite.ActualDressedTemporalResidual.temporal_quantum_preparation_return,#[
    ``LowEnergy.GaussComposite.ActualDressedTemporalResidual.temporal_quantum_physical_action,
    ``LowEnergy.GaussComposite.ActualDressedTemporalResidual.physical_preparation_return,
    ``LowEnergy.GaussComposite.ActualDressedTemporalHalf.temporal_actual_normalized_polarization,
    ``LowEnergy.GaussComposite.ActualDressedStaticResponse.static_input_normalizer_generated]),
    (``LowEnergy.GaussComposite.ActualDressedTemporalResidual.temporal_quantum_preparation_limit,#[
    ``LowEnergy.GaussComposite.ActualDressedTemporalResidual.preparation_ward_observer_limit,
    ``LowEnergy.GaussComposite.ActualDressedTemporalResidual.temporal_quantum_preparation_return]),
    (``LowEnergy.GaussComposite.ActualDressedTemporalResidual.source_leading_pencil_zero,#[
    ``LowEnergy.SourcePropagationAlgebraicResponse.sourceNumerator_pencil,
    ``LowEnergy.SourcePropagationConstrainedPoleReturn.zero_transfer_sourcePole]),
    (``LowEnergy.GaussComposite.ActualDressedTemporalResidual.source_leading_physical_action,#[
    ``LowEnergy.GaussComposite.ActualDressedTemporalResidual.source_leading_pencil_zero,
    ``LowEnergy.PreparationVacuumPropagationPencil.propagationPencil_actual]),
    (``LowEnergy.GaussComposite.ActualDressedTemporalResidual.static_pole_physical_action,#[
    ``LowEnergy.GaussComposite.ActualDressedTemporalResidual.source_leading_physical_action,
    ``LowEnergy.GaussComposite.ActualDressedStaticPole.staticPoleLeadingOperator]),
    (``LowEnergy.GaussComposite.ActualDressedTemporalResidual.static_pole_preparation_return,#[
    ``LowEnergy.GaussComposite.ActualDressedTemporalResidual.static_pole_physical_action,
    ``LowEnergy.GaussComposite.ActualDressedTemporalResidual.physical_preparation_return]),
    (``LowEnergy.GaussComposite.ActualDressedTemporalResidual.static_pole_preparation_limit,#[
    ``LowEnergy.GaussComposite.ActualDressedTemporalResidual.preparation_ward_observer_limit,
    ``LowEnergy.GaussComposite.ActualDressedTemporalResidual.static_pole_preparation_return])]
  for (mouth,required) in direct do packageCertRequire env mouth required
  let testProducers := #[
    ``LowEnergy.GaussComposite.ActualDressedTemporalResidual.preparation_ward_residual_return,
    ``LowEnergy.GaussComposite.ActualDressedTemporalResidual.preparation_ward_observer_price,
    ``LowEnergy.GaussComposite.ActualDressedTemporalResidual.preparation_ward_observer_limit,
    ``LowEnergy.GaussComposite.ActualDressedTemporalResidual.physical_preparation_return,
    ``LowEnergy.GaussComposite.ActualDressedTemporalResidual.temporal_half_physical_action,
    ``LowEnergy.GaussComposite.ActualDressedTemporalResidual.temporal_half_preparation_return,
    ``LowEnergy.GaussComposite.ActualDressedTemporalResidual.temporal_half_preparation_price,
    ``LowEnergy.GaussComposite.ActualDressedTemporalResidual.temporal_half_preparation_limit,
    ``LowEnergy.GaussComposite.ActualDressedTemporalResidual.temporal_quantum_physical_action,
    ``LowEnergy.GaussComposite.ActualDressedTemporalResidual.temporal_quantum_preparation_return,
    ``LowEnergy.GaussComposite.ActualDressedTemporalResidual.temporal_quantum_preparation_price,
    ``LowEnergy.GaussComposite.ActualDressedTemporalResidual.temporal_quantum_preparation_limit,
    ``LowEnergy.GaussComposite.ActualDressedTemporalResidual.source_leading_pencil_zero,
    ``LowEnergy.GaussComposite.ActualDressedTemporalResidual.source_leading_physical_action,
    ``LowEnergy.GaussComposite.ActualDressedTemporalResidual.static_pole_physical_action,
    ``LowEnergy.GaussComposite.ActualDressedTemporalResidual.static_pole_preparation_return,
    ``LowEnergy.GaussComposite.ActualDressedTemporalResidual.static_pole_preparation_price,
    ``LowEnergy.GaussComposite.ActualDressedTemporalResidual.static_pole_preparation_limit]
  for i in [:testProducers.size] do packageCertRequire env tests[i]! #[testProducers[i]!]
  let all ← packageCertClosure env (owned ++ tests.toList)
  let anchors := #[
    ``SaturationMonoid.PhysicsCore.StageNineEnrichedProofFreeSource.positiveSmoothUnifiedSource,
    ``SaturationMonoid.PhysicsCore.Stage9C.Material.SpinPair.actual,
    ``LowEnergy.GaussComposite.ActualDressedSourcePreparation.sourceDressedUnit,
    ``LowEnergy.PreparationVacuumSourcePreparedResponse.sourceProfile,
    ``LowEnergy.PreparationVacuumSourcePreparedState.sourceOperator,
    ``LowEnergy.PreparationVacuumSourcePreparedState.sourceEnergy,
    ``LowEnergy.PreparationVacuumPreparedCurrent.sourceLeg,
    ``LowEnergy.GaussComposite.ActualDressedNoether.dressedEulerObserver,
    ``LowEnergy.PreparationVacuumNoetherOrdinaryWard.sourceHamiltonian,
    ``LowEnergy.SourcePropagationResolvent.sourceInverse,
    ``LowEnergy.SourcePropagationAlgebraicResponse.sourceLeadingPole,
    ``LowEnergy.GaussComposite.ActualDressedStaticPole.staticPoleLeadingOperator,
    ``LowEnergy.GaussComposite.ActualDressedTemporalHalf.temporalGaussHalfJet,
    ``LowEnergy.GaussComposite.ActualDressedStaticResponse.staticQuantumCorrection]
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
  if let some path ← liftIO (IO.getEnv "ALPHA_DRESSED_TEMPORAL_RESIDUAL_AUDIT_OUTPUT") then
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
  logInfo m!"DRESSED_TEMPORAL_RESIDUAL_PASS public={mouths.size} owned={owned.length} tests={tests.size} nodes={all.size} anchors={anchors.size} direct={direct.size} opaque_all_read={opaques} axioms={axioms} unknown=0 unsafe=0 partial=0"
#audit_dressed_temporal_residual
#print axioms LowEnergy.GaussComposite.ActualDressedTemporalResidual.preparation_ward_residual_return
#print axioms LowEnergy.GaussComposite.ActualDressedTemporalResidual.preparation_ward_observer_price
#print axioms LowEnergy.GaussComposite.ActualDressedTemporalResidual.preparation_ward_observer_limit
#print axioms LowEnergy.GaussComposite.ActualDressedTemporalResidual.physical_preparation_return
#print axioms LowEnergy.GaussComposite.ActualDressedTemporalResidual.temporal_half_physical_action
#print axioms LowEnergy.GaussComposite.ActualDressedTemporalResidual.temporal_half_preparation_return
#print axioms LowEnergy.GaussComposite.ActualDressedTemporalResidual.temporal_half_preparation_price
#print axioms LowEnergy.GaussComposite.ActualDressedTemporalResidual.temporal_half_preparation_limit
#print axioms LowEnergy.GaussComposite.ActualDressedTemporalResidual.temporal_quantum_physical_action
#print axioms LowEnergy.GaussComposite.ActualDressedTemporalResidual.temporal_quantum_preparation_return
#print axioms LowEnergy.GaussComposite.ActualDressedTemporalResidual.temporal_quantum_preparation_price
#print axioms LowEnergy.GaussComposite.ActualDressedTemporalResidual.temporal_quantum_preparation_limit
#print axioms LowEnergy.GaussComposite.ActualDressedTemporalResidual.source_leading_pencil_zero
#print axioms LowEnergy.GaussComposite.ActualDressedTemporalResidual.source_leading_physical_action
#print axioms LowEnergy.GaussComposite.ActualDressedTemporalResidual.static_pole_physical_action
#print axioms LowEnergy.GaussComposite.ActualDressedTemporalResidual.static_pole_preparation_return
#print axioms LowEnergy.GaussComposite.ActualDressedTemporalResidual.static_pole_preparation_price
#print axioms LowEnergy.GaussComposite.ActualDressedTemporalResidual.static_pole_preparation_limit
