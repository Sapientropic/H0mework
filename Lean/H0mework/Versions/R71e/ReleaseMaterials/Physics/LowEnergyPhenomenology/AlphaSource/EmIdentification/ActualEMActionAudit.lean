import H0mework.Versions.R71e.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualEMClock
import Lean.Elab.Command
import Lean.Util.FoldConsts
import Lean.Util.CollectAxioms

set_option autoImplicit false
set_option maxHeartbeats 12000000
set_option maxRecDepth 32768
noncomputable section
namespace LowEnergy.GaussComposite.ActualEMActionAudit
open SaturationMonoid.PhysicsCore SaturationMonoid.PhysicsCore.LowEnergy
open ProofFreeRicherAnholonomicSource StageNineEnrichedProofFreeSource
open StageNineHolonomicField StageNineGlobalIntegratedAction
open StageNineDiracDualFormNativeMotherAction StageNineDiracDualFormNativePointwiseActionJetCarrier
open SourcePropagationNativeActionHessian SourcePropagationMotherEulerKernel
open PreparationVacuumOriginalGreenFeedback PreparationVacuumMixedFieldReturn
open PreparationVacuumPhysicalCharacteristic PreparationVacuumPhysicalPoleSheet
open PreparationPhysicalNativePhotonFluxReturn PreparationVacuumPhysicalChargedFieldFactor
open CanonicalGradedSpatialSource
open ActualEMCarrierOwn Filter Set
open scoped Matrix BigOperators Topology

open SaturationMonoid.PhysicsCore SaturationMonoid.PhysicsCore.LowEnergy
open PreparationVacuumOriginalGreenFeedback PreparationVacuumPhysicalCharacteristic
open PreparationVacuumPhysicalPoleSheet PreparationPhysicalNativePhotonFluxReturn
open PreparationVacuumPhysicalChargedFieldFactor CanonicalGradedSpatialSource
open ActualEMCarrierOwn ActualEMAction Filter Set
open scoped Matrix BigOperators Topology Matrix.Norms.Operator

open ActualEMAction ActualEMClock
theorem checked_em_action_source (jet : NativeFirstJet) : emOriginalAction jet = nativeJetDensity jet  := LowEnergy.GaussComposite.ActualEMAction.em_action_source jet

theorem checked_em_hessian_source : emOriginalHessian = nativeHessian  := LowEnergy.GaussComposite.ActualEMAction.em_hessian_source

theorem checked_em_jacobi_source (p : Fin 4 → ℂ) : emOriginalJacobi p = originalJacobi p  := LowEnergy.GaussComposite.ActualEMAction.em_jacobi_source p

theorem checked_em_action_sheet_jet (epsilon s : ℝ) (n : PhysicalMomentum) :
    emActionSheetJet epsilon s n = sourcePhotonSheetJacobiJet epsilon s n  := LowEnergy.GaussComposite.ActualEMAction.em_action_sheet_jet epsilon s n

theorem checked_em_action_frequency_jet (epsilon omega : ℝ) (n : PhysicalMomentum) :
    emActionFrequencyJet epsilon omega n = sourcePhotonFrequencyJacobiJet epsilon omega n  := LowEnergy.GaussComposite.ActualEMAction.em_action_frequency_jet epsilon omega n

theorem checked_em_action_carrier_homogeneous (branch : Fin 2) (n : PhysicalMomentum)
    (unit : spatialSquare n = 1) :
    ∀ᶠ e in scaleApproach,
      emOriginalJacobi (frequencyRay e.val (sourceSheet branch n unit e.val) n) *
        emPropagatingCarrier e.val (sourceSheet branch n unit e.val) n = 0  := LowEnergy.GaussComposite.ActualEMAction.em_action_carrier_homogeneous branch n unit

theorem checked_em_action_sheet_flux (branch : Fin 2) (n : PhysicalMomentum)
    (unit : spatialSquare n = 1) :
    ∀ᶠ e in scaleApproach,
      emInsertion.transpose * sourceWholePhotonResidue e.val (sourceSheet branch n unit e.val) n *
        emActionSheetJet e.val (sourceSheet branch n unit e.val) n *
        emPropagatingCarrier e.val (sourceSheet branch n unit e.val) n =
      emPoleTensor e.val (sourceSheet branch n unit e.val) n  := LowEnergy.GaussComposite.ActualEMAction.em_action_sheet_flux branch n unit

theorem checked_em_action_frequency_flux (branch : Fin 2) (n : PhysicalMomentum)
    (unit : spatialSquare n = 1) :
    ∀ᶠ e in scaleApproach,
      emInsertion.transpose * sourceWholePhotonFrequencyResidue e.val (sourceSheet branch n unit e.val) n *
        emActionFrequencyJet e.val (sourceFrequency e.val (sourceSheet branch n unit e.val)) n *
        (sourceWholePhotonFrequencyResidue e.val (sourceSheet branch n unit e.val) n * emInsertion) =
      emInsertion.transpose * sourceWholePhotonFrequencyResidue e.val (sourceSheet branch n unit e.val) n *
        emInsertion  := LowEnergy.GaussComposite.ActualEMAction.em_action_frequency_flux branch n unit

theorem checked_em_clock_pole_generated (scale : ℝ) (positive : 0 < scale)
    (branch : Fin 2) (n : PhysicalMomentum) (unit : spatialSquare n = 1) :
    ∀ᶠ e in scaleApproach, Tendsto
      (fun w : ℝ => ((w - sourceFrequency e.val (sourceSheet branch n unit e.val) / scale : ℝ) : ℂ) •
        emClockGreen scale e.val w n)
      (𝓝[≠] (sourceFrequency e.val (sourceSheet branch n unit e.val) / scale))
      (𝓝 (emClockResidue scale e.val (sourceSheet branch n unit e.val) n))  := LowEnergy.GaussComposite.ActualEMClock.em_clock_pole_generated scale positive branch n unit

theorem checked_em_clock_jet_generated (scale : ℝ) (positive : 0 < scale) (e : scaleDomain)
    (s : ℝ) (n : PhysicalMomentum) :
    emClockJet scale e.val (sourceFrequency e.val s / scale) n =
      scale • emActionFrequencyJet e.val (sourceFrequency e.val s) n  := LowEnergy.GaussComposite.ActualEMClock.em_clock_jet_generated scale positive e s n

theorem checked_em_clock_frequency_flux (scale : ℝ) (positive : 0 < scale)
    (branch : Fin 2) (n : PhysicalMomentum) (unit : spatialSquare n = 1) :
    ∀ᶠ e in scaleApproach,
      emInsertion.transpose * emClockResidue scale e.val (sourceSheet branch n unit e.val) n *
        emClockJet scale e.val (sourceFrequency e.val (sourceSheet branch n unit e.val) / scale) n *
        (emClockResidue scale e.val (sourceSheet branch n unit e.val) n * emInsertion) =
      emInsertion.transpose * emClockResidue scale e.val (sourceSheet branch n unit e.val) n * emInsertion  := LowEnergy.GaussComposite.ActualEMClock.em_clock_frequency_flux scale positive branch n unit

theorem checked_nonempty_scale : scaleApproach.NeBot := scaleApproach_nonempty

theorem checked_nonempty_clock_puncture (w : ℝ) : (𝓝[≠] w).NeBot := inferInstance

theorem checked_positive_unit_clock : (0:ℝ)<1 := by norm_num

theorem checked_clock_unit (epsilon s : ℝ) (n : PhysicalMomentum) :
    emClockResidue 1 epsilon s n = sourceWholePhotonFrequencyResidue epsilon s n := by
  simp [emClockResidue]

theorem checked_clock_two (epsilon s : ℝ) (n : PhysicalMomentum) :
    emClockResidue 2 epsilon s n = (1/2:ℝ) • sourceWholePhotonFrequencyResidue epsilon s n := by
  norm_num [emClockResidue]

end LowEnergy.GaussComposite.ActualEMActionAudit

open Lean Elab Command
private def actionCertChildren (info : ConstantInfo) : Array Name := Id.run do
  let mut children := info.type.getUsedConstants
  if let some value := info.value? (allowOpaque := true) then
    children := children ++ value.getUsedConstants
  if let .inductInfo value := info then children := children ++ value.ctors.toArray
  if let .recInfo value := info then
    for rule in value.rules do children := children ++ rule.rhs.getUsedConstants
  return children

private def actionCertClosure (env : Environment)
    (roots : List Name) : CommandElabM NameSet := do
  let mut pending := roots
  let mut seen : NameSet := {}
  while !pending.isEmpty do
    let name := pending.head!
    pending := pending.tail!
    unless seen.contains name do
      let some info := env.checked.get.find? name | throwError m!"UNKNOWN {name}"
      pending := (actionCertChildren info).toList ++ pending
      seen := seen.insert name
  return seen


private def actionCertRequire (env : Environment) (root : Name) (required : Array Name) : CommandElabM Unit := do
  let mut pending := [root]
  let mut seen : NameSet := {}
  let mut found : NameSet := {}
  while !pending.isEmpty && !(required.all found.contains) do
    let name := pending.head!
    pending := pending.tail!
    unless seen.contains name do
      let some info := env.checked.get.find? name | throwError m!"UNKNOWN {name}"
      let children := actionCertChildren info
      for target in required do
        if name == target || children.contains target then found := found.insert target
      pending := children.toList ++ pending
      seen := seen.insert name
  for name in required do
    unless found.contains name do throwError m!"UNCONSUMED_DIRECT {root} {name}"

elab "#audit_actual_em_action" : command => do
  let env ← getEnv
  let modules := env.header.moduleNames
  let owner := fun name => (env.getModuleIdxFor? name).map fun i => modules[i.toNat]!
  let candidates := #[`ActualEMAction,`H0mework.Versions.R71e.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualEMClock]
  let owned := env.constants.toList.filterMap fun (name, _) =>
    if (owner name).any candidates.contains then some name else none
  let mouths := #[
    ``LowEnergy.GaussComposite.ActualEMAction.emOriginalAction,
    ``LowEnergy.GaussComposite.ActualEMAction.em_action_source,
    ``LowEnergy.GaussComposite.ActualEMAction.emOriginalHessian,
    ``LowEnergy.GaussComposite.ActualEMAction.em_hessian_source,
    ``LowEnergy.GaussComposite.ActualEMAction.emOriginalJacobi,
    ``LowEnergy.GaussComposite.ActualEMAction.em_jacobi_source,
    ``LowEnergy.GaussComposite.ActualEMAction.emActionSheetJet,
    ``LowEnergy.GaussComposite.ActualEMAction.em_action_sheet_jet,
    ``LowEnergy.GaussComposite.ActualEMAction.emActionFrequencyJacobi,
    ``LowEnergy.GaussComposite.ActualEMAction.emActionFrequencyJet,
    ``LowEnergy.GaussComposite.ActualEMAction.em_action_frequency_jet,
    ``LowEnergy.GaussComposite.ActualEMAction.em_action_carrier_homogeneous,
    ``LowEnergy.GaussComposite.ActualEMAction.em_action_sheet_flux,
    ``LowEnergy.GaussComposite.ActualEMAction.em_action_frequency_flux,
    ``LowEnergy.GaussComposite.ActualEMClock.emClockGreen,
    ``LowEnergy.GaussComposite.ActualEMClock.emClockResidue,
    ``LowEnergy.GaussComposite.ActualEMClock.emClockJacobi,
    ``LowEnergy.GaussComposite.ActualEMClock.emClockJet,
    ``LowEnergy.GaussComposite.ActualEMClock.em_clock_pole_generated,
    ``LowEnergy.GaussComposite.ActualEMClock.em_clock_jet_generated,
    ``LowEnergy.GaussComposite.ActualEMClock.em_clock_frequency_flux]
  for name in mouths do
    unless owned.contains name do throwError m!"MISSING_MOUTH {name}"
  let tests := #[
    ``LowEnergy.GaussComposite.ActualEMActionAudit.checked_em_action_source,
    ``LowEnergy.GaussComposite.ActualEMActionAudit.checked_em_hessian_source,
    ``LowEnergy.GaussComposite.ActualEMActionAudit.checked_em_jacobi_source,
    ``LowEnergy.GaussComposite.ActualEMActionAudit.checked_em_action_sheet_jet,
    ``LowEnergy.GaussComposite.ActualEMActionAudit.checked_em_action_frequency_jet,
    ``LowEnergy.GaussComposite.ActualEMActionAudit.checked_em_action_carrier_homogeneous,
    ``LowEnergy.GaussComposite.ActualEMActionAudit.checked_em_action_sheet_flux,
    ``LowEnergy.GaussComposite.ActualEMActionAudit.checked_em_action_frequency_flux,
    ``LowEnergy.GaussComposite.ActualEMActionAudit.checked_em_clock_pole_generated,
    ``LowEnergy.GaussComposite.ActualEMActionAudit.checked_em_clock_jet_generated,
    ``LowEnergy.GaussComposite.ActualEMActionAudit.checked_em_clock_frequency_flux,
    ``LowEnergy.GaussComposite.ActualEMActionAudit.checked_nonempty_scale,
    ``LowEnergy.GaussComposite.ActualEMActionAudit.checked_nonempty_clock_puncture,
    ``LowEnergy.GaussComposite.ActualEMActionAudit.checked_positive_unit_clock,
    ``LowEnergy.GaussComposite.ActualEMActionAudit.checked_clock_unit,
    ``LowEnergy.GaussComposite.ActualEMActionAudit.checked_clock_two]
  let all ← actionCertClosure env (owned ++ tests.toList)
  let anchors := #[
    ``LowEnergy.GaussComposite.ActualEMAction.emOriginalAction,
    ``LowEnergy.GaussComposite.ActualEMAction.emOriginalHessian,
    ``LowEnergy.GaussComposite.ActualEMAction.emOriginalJacobi,
    ``LowEnergy.SourcePropagationMotherEulerKernel.nativeLocalAction_original,
    ``LowEnergy.SourcePropagationMotherEulerKernel.nativeLocalAction_zero,
    ``LowEnergy.SourcePropagationNativeActionHessian.nativeActionFourierHessian_original,
    ``LowEnergy.SourcePropagationNativeActionHessian.nativeHessian_complete_source,
    ``LowEnergy.SourcePropagationNativeActionHessian.nativeHessian,
    ``SaturationMonoid.PhysicsCore.StageNineEnrichedProofFreeSource.positiveSmoothUnifiedSource,
    ``SaturationMonoid.PhysicsCore.Stage9C.Material.SpinPair.actual,
    ``LowEnergy.GaussComposite.ActualEMCarrierOwn.emInsertion,
    ``LowEnergy.GaussComposite.ActualEMCarrierOwn.emPropagatingCarrier,
    ``LowEnergy.PreparationPhysicalNativePhotonFluxReturn.sourceWholePhotonFrequencyResidue,
    ``LowEnergy.PreparationPhysicalNativePhotonFluxReturn.sourceWholePhotonGreen_residue,
    ``LowEnergy.PreparationPhysicalNativePhotonFluxReturn.sourcePhotonFrequencyJacobi_hasDerivAt]
  for name in anchors do
    unless all.contains name do throwError m!"UNCONSUMED_SOURCE {name}"
  let direct := #[
    (``LowEnergy.GaussComposite.ActualEMAction.em_action_source,#[
    ``LowEnergy.SourcePropagationMotherEulerKernel.nativeLocalAction_original,
    ``LowEnergy.SourcePropagationMotherEulerKernel.nativeLocalAction_zero]),
    (``LowEnergy.GaussComposite.ActualEMAction.em_hessian_source,#[
    ``LowEnergy.GaussComposite.ActualEMAction.em_action_source,
    ``LowEnergy.SourcePropagationNativeActionHessian.nativeHessian]),
    (``LowEnergy.GaussComposite.ActualEMAction.em_jacobi_source,#[
    ``LowEnergy.GaussComposite.ActualEMAction.em_hessian_source,
    ``LowEnergy.SourcePropagationNativeActionHessian.nativeActionFourierHessian_original]),
    (``LowEnergy.GaussComposite.ActualEMAction.em_action_sheet_jet,#[
    ``LowEnergy.GaussComposite.ActualEMAction.em_jacobi_source]),
    (``LowEnergy.GaussComposite.ActualEMAction.em_action_frequency_jet,#[
    ``LowEnergy.GaussComposite.ActualEMAction.em_jacobi_source]),
    (``LowEnergy.GaussComposite.ActualEMAction.em_action_carrier_homogeneous,#[
    ``LowEnergy.GaussComposite.ActualEMAction.em_jacobi_source,
    ``LowEnergy.GaussComposite.ActualEMCarrierOwn.em_carrier_homogeneous]),
    (``LowEnergy.GaussComposite.ActualEMAction.em_action_sheet_flux,#[
    ``LowEnergy.GaussComposite.ActualEMAction.em_action_sheet_jet,
    ``LowEnergy.GaussComposite.ActualEMCarrierOwn.em_flux_generated]),
    (``LowEnergy.GaussComposite.ActualEMAction.em_action_frequency_flux,#[
    ``LowEnergy.GaussComposite.ActualEMAction.em_action_frequency_jet,
    ``LowEnergy.PreparationPhysicalNativePhotonFluxReturn.sourceWholePhotonResidue_frequencyFlux]),
    (``LowEnergy.GaussComposite.ActualEMClock.em_clock_pole_generated,#[
    ``LowEnergy.PreparationPhysicalNativePhotonFluxReturn.sourceWholePhotonGreen_residue]),
    (``LowEnergy.GaussComposite.ActualEMClock.em_clock_jet_generated,#[
    ``LowEnergy.GaussComposite.ActualEMAction.em_jacobi_source,
    ``LowEnergy.GaussComposite.ActualEMAction.em_action_frequency_jet,
    ``LowEnergy.PreparationPhysicalNativePhotonFluxReturn.sourcePhotonFrequencyJacobi_hasDerivAt]),
    (``LowEnergy.GaussComposite.ActualEMClock.em_clock_frequency_flux,#[
    ``LowEnergy.GaussComposite.ActualEMClock.em_clock_jet_generated,
    ``LowEnergy.GaussComposite.ActualEMAction.em_action_frequency_flux]),
    (``LowEnergy.GaussComposite.ActualEMAction.em_action_carrier_homogeneous,#[
    ``LowEnergy.GaussComposite.ActualEMAction.emOriginalAction,
    ``LowEnergy.SourcePropagationNativeActionHessian.nativeActionFourierHessian_original,
    ``SaturationMonoid.PhysicsCore.StageNineEnrichedProofFreeSource.positiveSmoothUnifiedSource,
    ``SaturationMonoid.PhysicsCore.Stage9C.Material.SpinPair.actual]),
    (``LowEnergy.GaussComposite.ActualEMAction.em_action_sheet_flux,#[
    ``LowEnergy.GaussComposite.ActualEMAction.emOriginalAction,
    ``LowEnergy.SourcePropagationNativeActionHessian.nativeActionFourierHessian_original,
    ``SaturationMonoid.PhysicsCore.StageNineEnrichedProofFreeSource.positiveSmoothUnifiedSource,
    ``SaturationMonoid.PhysicsCore.Stage9C.Material.SpinPair.actual]),
    (``LowEnergy.GaussComposite.ActualEMAction.em_action_frequency_flux,#[
    ``LowEnergy.GaussComposite.ActualEMAction.emOriginalAction,
    ``LowEnergy.SourcePropagationNativeActionHessian.nativeActionFourierHessian_original,
    ``SaturationMonoid.PhysicsCore.StageNineEnrichedProofFreeSource.positiveSmoothUnifiedSource,
    ``SaturationMonoid.PhysicsCore.Stage9C.Material.SpinPair.actual]),
    (``LowEnergy.GaussComposite.ActualEMClock.em_clock_frequency_flux,#[
    ``LowEnergy.GaussComposite.ActualEMAction.emOriginalAction,
    ``LowEnergy.SourcePropagationNativeActionHessian.nativeActionFourierHessian_original,
    ``SaturationMonoid.PhysicsCore.StageNineEnrichedProofFreeSource.positiveSmoothUnifiedSource,
    ``SaturationMonoid.PhysicsCore.Stage9C.Material.SpinPair.actual])]
  for (mouth,required) in direct do actionCertRequire env mouth required
  let testProducers := #[
    ``LowEnergy.GaussComposite.ActualEMAction.em_action_source,
    ``LowEnergy.GaussComposite.ActualEMAction.em_hessian_source,
    ``LowEnergy.GaussComposite.ActualEMAction.em_jacobi_source,
    ``LowEnergy.GaussComposite.ActualEMAction.em_action_sheet_jet,
    ``LowEnergy.GaussComposite.ActualEMAction.em_action_frequency_jet,
    ``LowEnergy.GaussComposite.ActualEMAction.em_action_carrier_homogeneous,
    ``LowEnergy.GaussComposite.ActualEMAction.em_action_sheet_flux,
    ``LowEnergy.GaussComposite.ActualEMAction.em_action_frequency_flux,
    ``LowEnergy.GaussComposite.ActualEMClock.em_clock_pole_generated,
    ``LowEnergy.GaussComposite.ActualEMClock.em_clock_jet_generated,
    ``LowEnergy.GaussComposite.ActualEMClock.em_clock_frequency_flux]
  for i in [:testProducers.size] do actionCertRequire env tests[i]! #[testProducers[i]!]
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
  if let some path ← liftIO (IO.getEnv "ALPHA_ACTUAL_EM_ACTION_AUDIT_OUTPUT") then
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
  logInfo m!"ACTUAL_EM_ACTION_PASS public={mouths.size} owned={owned.length} tests={tests.size} nodes={all.size} anchors={anchors.size} direct={direct.size} opaque_all_read={opaques} axioms={axioms} unknown=0 unsafe=0 partial=0"
#audit_actual_em_action
#print axioms LowEnergy.GaussComposite.ActualEMAction.em_jacobi_source
#print axioms LowEnergy.GaussComposite.ActualEMAction.em_action_frequency_flux
#print axioms LowEnergy.GaussComposite.ActualEMClock.em_clock_pole_generated
#print axioms LowEnergy.GaussComposite.ActualEMClock.em_clock_frequency_flux
