import H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualDressedPhysicalClockJet
import H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualDressedNativeClockFlux
import H0mework.Versions.R9c73a630.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualEMDressedGaugePole
import Lean.Elab.Command
import Lean.Util.FoldConsts
import Lean.Util.CollectAxioms
set_option autoImplicit false
set_option maxHeartbeats 12000000
set_option maxRecDepth 32768
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.GaussComposite.ActualDressedPhysicalClockAudit
elab "checked_dressed_coincident_polarization_kernelContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualDressedPhysicalClock.dressed_coincident_polarization_kernel).type
theorem checked_dressed_coincident_polarization_kernel : checked_dressed_coincident_polarization_kernelContract := @LowEnergy.GaussComposite.ActualDressedPhysicalClock.dressed_coincident_polarization_kernel

elab "checked_dressed_coincident_clock_jet_generatedContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualDressedPhysicalClock.dressed_coincident_clock_jet_generated).type
theorem checked_dressed_coincident_clock_jet_generated : checked_dressed_coincident_clock_jet_generatedContract := @LowEnergy.GaussComposite.ActualDressedPhysicalClock.dressed_coincident_clock_jet_generated

elab "checked_dressed_synchronized_pencil_original_actionContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualDressedPhysicalClock.dressed_synchronized_pencil_original_action).type
theorem checked_dressed_synchronized_pencil_original_action : checked_dressed_synchronized_pencil_original_actionContract := @LowEnergy.GaussComposite.ActualDressedPhysicalClock.dressed_synchronized_pencil_original_action

elab "checked_dressed_native_clock_flux_generatedContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualDressedPhysicalClock.dressed_native_clock_flux_generated).type
theorem checked_dressed_native_clock_flux_generated : checked_dressed_native_clock_flux_generatedContract := @LowEnergy.GaussComposite.ActualDressedPhysicalClock.dressed_native_clock_flux_generated

elab "checked_dressed_native_physical_frequency_fluxContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualDressedPhysicalClock.dressed_native_physical_frequency_flux).type
theorem checked_dressed_native_physical_frequency_flux : checked_dressed_native_physical_frequency_fluxContract := @LowEnergy.GaussComposite.ActualDressedPhysicalClock.dressed_native_physical_frequency_flux

open SaturationMonoid.PhysicsCore SaturationMonoid.PhysicsCore.LowEnergy
open CanonicalGradedSpatialSource PreparationVacuumMixedFieldReturn PreparationVacuumPhysicalFeedback
open PreparationVacuumPhysicalCharacteristic PreparationVacuumPhysicalPoleSheet PreparationVacuumOriginalGreenFeedback
open ActualDressedFullCoulomb ActualDressedNoether ActualDressedSignal ActualDressedPencil ActualDressedHistoryKernel
open ActualDressedClockMoment ActualDressedPhysicalClock ActualEMDressedGaugePole
open MeasureTheory
open scoped Matrix BigOperators Topology Interval

theorem actual_synchronized_window_zero (event : DressedEvent) (transfer : PhysicalMomentum) (z : ℂ) :
    dressedSynchronizedPencil event transfer z 0=0 := by
  rw [dressed_synchronized_pencil_original_action]
  ext i j
  simp [dressedWindowPolarization]

theorem actual_source_sheet_clock (event : DressedEvent) (e s : ℝ) (n : PhysicalMomentum) (T : ℝ) :
    dressedSynchronizedPencil event ((e^2:ℝ) • n) (-Complex.I*(sourceFrequency e s:ℂ)) T=
      dressedNativeWindowPencil event ((e^2:ℝ) • n) (frequencyRay e s n)
        (-Complex.I*(sourceFrequency e s:ℂ)) T := by
  have original:=congrArg
    (fun p=>dressedNativeWindowPencil event ((e^2:ℝ) • n) p (-Complex.I*(sourceFrequency e s:ℂ)) T)
    (dressed_gauge_clock e s n)
  simpa only [dressedSynchronizedPencil,dressedGaugeMomentum] using original

theorem actual_physical_memory_lag_unit (omega t s : ℝ) :
    ‖Complex.exp (((s-t:ℝ):ℂ)*(-Complex.I*(omega:ℂ)))‖=1 := by
  simp [Complex.norm_exp,Complex.mul_re]

end LowEnergy.GaussComposite.ActualDressedPhysicalClockAudit

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

elab "#audit_dressed_physical_clock" : command => do
  let env ← getEnv
  let modules := env.header.moduleNames
  let owner := fun name => (env.getModuleIdxFor? name).map fun i => modules[i.toNat]!
  let candidates := #[`H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualDressedPhysicalClockJet,`H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualDressedNativeClockFlux]
  let owned := env.constants.toList.filterMap fun (name, _) =>
    if (owner name).any candidates.contains then some name else none
  let mouths := #[
    ``LowEnergy.GaussComposite.ActualDressedPhysicalClock.dressed_coincident_polarization_kernel,
    ``LowEnergy.GaussComposite.ActualDressedPhysicalClock.dressedCoincidentClockJet,
    ``LowEnergy.GaussComposite.ActualDressedPhysicalClock.dressed_coincident_clock_jet_generated,
    ``LowEnergy.GaussComposite.ActualDressedPhysicalClock.dressedSynchronizedPencil,
    ``LowEnergy.GaussComposite.ActualDressedPhysicalClock.dressed_synchronized_pencil_original_action,
    ``LowEnergy.GaussComposite.ActualDressedPhysicalClock.dressedNativeClockFlux,
    ``LowEnergy.GaussComposite.ActualDressedPhysicalClock.dressed_native_clock_flux_generated,
    ``LowEnergy.GaussComposite.ActualDressedPhysicalClock.dressed_native_physical_frequency_flux]
  for name in mouths do
    unless owned.contains name do throwError m!"MISSING_MOUTH {name}"
  let tests := #[
    ``LowEnergy.GaussComposite.ActualDressedPhysicalClockAudit.checked_dressed_coincident_polarization_kernel,
    ``LowEnergy.GaussComposite.ActualDressedPhysicalClockAudit.checked_dressed_coincident_clock_jet_generated,
    ``LowEnergy.GaussComposite.ActualDressedPhysicalClockAudit.checked_dressed_synchronized_pencil_original_action,
    ``LowEnergy.GaussComposite.ActualDressedPhysicalClockAudit.checked_dressed_native_clock_flux_generated,
    ``LowEnergy.GaussComposite.ActualDressedPhysicalClockAudit.checked_dressed_native_physical_frequency_flux,
    ``LowEnergy.GaussComposite.ActualDressedPhysicalClockAudit.actual_synchronized_window_zero,
    ``LowEnergy.GaussComposite.ActualDressedPhysicalClockAudit.actual_source_sheet_clock,
    ``LowEnergy.GaussComposite.ActualDressedPhysicalClockAudit.actual_physical_memory_lag_unit]
  let direct := #[
    (``LowEnergy.GaussComposite.ActualDressedPhysicalClock.dressed_coincident_polarization_kernel,#[
    ``LowEnergy.GaussComposite.ActualDressedClockMoment.dressed_signal_history_matrix]),
    (``LowEnergy.GaussComposite.ActualDressedPhysicalClock.dressed_coincident_clock_jet_generated,#[
    ``LowEnergy.GaussComposite.ActualDressedPhysicalClock.dressed_coincident_polarization_kernel]),
    (``LowEnergy.GaussComposite.ActualDressedPhysicalClock.dressed_synchronized_pencil_original_action,#[
    ``LowEnergy.GaussComposite.ActualEMAction.em_jacobi_source,
    ``LowEnergy.GaussComposite.ActualDressedPencil.dressed_coincident_clock_factor]),
    (``LowEnergy.GaussComposite.ActualDressedPhysicalClock.dressed_native_clock_flux_generated,#[
    ``LowEnergy.GaussComposite.ActualDressedPhysicalClock.dressed_coincident_clock_jet_generated,
    ``LowEnergy.GaussComposite.ActualDressedPhysicalClock.dressed_synchronized_pencil_original_action]),
    (``LowEnergy.GaussComposite.ActualDressedPhysicalClock.dressed_native_physical_frequency_flux,#[
    ``LowEnergy.GaussComposite.ActualDressedPhysicalClock.dressed_coincident_clock_jet_generated]),
    (``LowEnergy.GaussComposite.ActualDressedPhysicalClockAudit.actual_source_sheet_clock,#[
    ``LowEnergy.GaussComposite.ActualEMDressedGaugePole.dressed_gauge_clock])]
  for (mouth,required) in direct do packageCertRequire env mouth required
  let testProducers := #[
    ``LowEnergy.GaussComposite.ActualDressedPhysicalClock.dressed_coincident_polarization_kernel,
    ``LowEnergy.GaussComposite.ActualDressedPhysicalClock.dressed_coincident_clock_jet_generated,
    ``LowEnergy.GaussComposite.ActualDressedPhysicalClock.dressed_synchronized_pencil_original_action,
    ``LowEnergy.GaussComposite.ActualDressedPhysicalClock.dressed_native_clock_flux_generated,
    ``LowEnergy.GaussComposite.ActualDressedPhysicalClock.dressed_native_physical_frequency_flux]
  for i in [:testProducers.size] do packageCertRequire env tests[i]! #[testProducers[i]!]
  let all ← packageCertClosure env (owned ++ tests.toList)
  let anchors := #[
    ``SaturationMonoid.PhysicsCore.StageNineEnrichedProofFreeSource.positiveSmoothUnifiedSource,
    ``SaturationMonoid.PhysicsCore.Stage9C.Material.SpinPair.actual,
    ``LowEnergy.GaussComposite.ActualDressedSourcePreparation.sourceDressedUnit,
    ``LowEnergy.PreparationVacuumSourcePreparedResponse.sourceProfile,
    ``LowEnergy.GaussComposite.ActualDressedNoether.dressedEulerObserver,
    ``LowEnergy.GaussComposite.ActualDressedHistoryKernel.dressedHistoryInitial,
    ``LowEnergy.GaussComposite.ActualDressedHistoryKernel.dressedHistoryContact,
    ``LowEnergy.GaussComposite.ActualDressedHistoryKernel.dressedHistoryMemory,
    ``LowEnergy.GaussComposite.ActualDressedPencil.dressedNativeWindowPencil,
    ``LowEnergy.GaussComposite.ActualEMAction.emOriginalJacobi,
    ``LowEnergy.GaussComposite.ActualDressedPhysicalClock.dressedCoincidentClockJet]
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
  if let some path ← liftIO (IO.getEnv "ALPHA_DRESSED_PHYSICAL_CLOCK_AUDIT_OUTPUT") then
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
  logInfo m!"DRESSED_PHYSICAL_CLOCK_PASS public={mouths.size} owned={owned.length} tests={tests.size} nodes={all.size} anchors={anchors.size} direct={direct.size} opaque_all_read={opaques} axioms={axioms} unknown=0 unsafe=0 partial=0"
#audit_dressed_physical_clock
#print axioms LowEnergy.GaussComposite.ActualDressedPhysicalClock.dressed_coincident_polarization_kernel
#print axioms LowEnergy.GaussComposite.ActualDressedPhysicalClock.dressed_coincident_clock_jet_generated
#print axioms LowEnergy.GaussComposite.ActualDressedPhysicalClock.dressed_synchronized_pencil_original_action
#print axioms LowEnergy.GaussComposite.ActualDressedPhysicalClock.dressed_native_clock_flux_generated
#print axioms LowEnergy.GaussComposite.ActualDressedPhysicalClock.dressed_native_physical_frequency_flux
