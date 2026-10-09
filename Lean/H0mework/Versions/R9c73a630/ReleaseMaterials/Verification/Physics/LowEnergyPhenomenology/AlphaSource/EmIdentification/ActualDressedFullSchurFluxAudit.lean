import H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualDressedConstraintClockColumns
import H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualDressedFullSchurFlux

import Lean.Elab.Command
import Lean.Util.FoldConsts
import Lean.Util.CollectAxioms
set_option autoImplicit false
set_option maxHeartbeats 12000000
set_option maxRecDepth 32768
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.GaussComposite.ActualDressedFullSchurFluxAudit
elab "checked_clock_native_columns_actualContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualDressedSchurClock.clock_native_columns_actual).type
theorem checked_clock_native_columns_actual : checked_clock_native_columns_actualContract := @LowEnergy.GaussComposite.ActualDressedSchurClock.clock_native_columns_actual

elab "checked_clock_native_columns_derivativeContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualDressedSchurClock.clock_native_columns_derivative).type
theorem checked_clock_native_columns_derivative : checked_clock_native_columns_derivativeContract := @LowEnergy.GaussComposite.ActualDressedSchurClock.clock_native_columns_derivative

elab "checked_clock_schur_original_productContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualDressedSchurClock.clock_schur_original_product).type
theorem checked_clock_schur_original_product : checked_clock_schur_original_productContract := @LowEnergy.GaussComposite.ActualDressedSchurClock.clock_schur_original_product

elab "checked_clock_source_schur_flux_generatedContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualDressedSchurClock.clock_source_schur_flux_generated).type
theorem checked_clock_source_schur_flux_generated : checked_clock_source_schur_flux_generatedContract := @LowEnergy.GaussComposite.ActualDressedSchurClock.clock_source_schur_flux_generated

open CanonicalGradedSpatialSource PreparationVacuumMixedFieldReturn PreparationVacuumPhysicalFeedback
open PreparationVacuumOriginalGreenFeedback PreparationPhysicalVoltageCompleteReturn
open PreparationVacuumCurrentSignalOperator
open ActualDressedFullCoulomb ActualDressedNoether ActualDressedSignal ActualDressedPencil
open ActualDressedClockMoment ActualDressedPhysicalClock
open ActualEMDressedSourceAnchor ActualEMDressedAnchorInverse ActualEMDressedConstraint ActualEMDressedSchur
open ActualDressedNullNative ActualEMDressedClockGerm ActualEMDressedClockSchur ActualDressedSchurClock
open Filter
open scoped Matrix BigOperators Topology
attribute [local irreducible] originalChange clockSchur clockSourceSchurFlux dressedWindowPolarization

/-- Both genuine constraint maps have nonzero original clock derivatives. -/
theorem actual_source_column_jets :
    clockNativeNullJet 10 0=-(1/2:ℂ) ∧ (-clockNativeNullJet.transpose) 0 10=(1/2:ℂ) := by
  have right : clockNativeNullJet 10 0=-(1/2:ℂ) := by
    change originalNullColumn (sourceInputClock 1) 0 10-originalNullColumn (sourceInputClock 0) 0 10=-(1/2:ℂ)
    rw [original_null_column_literal,original_null_column_literal]
    norm_num [nullColumnTerms,sourceMatrix,SourceTerm.matrix,Matrix.single_apply,
      nullColumnIndex,Fin.ext_iff,Powers.value,coefficientValue,sourceInputClock,Pi.single_apply]
  refine ⟨right,?_⟩
  rw [Matrix.neg_apply,Matrix.transpose_apply,right]
  norm_num

/-- The germ is consumed at a source-generated nonlinear window for an actual nonzero field amplitude. -/
theorem actual_anchor_schur_flux (event : DressedEvent) :
    HasDerivAt (clockSchur event (anchorWindow event (Pi.single 20 1)))
      (clockSourceSchurFlux event (anchorWindow event (Pi.single 20 1)) 3) 3 := by
  have window:=anchor_window_source event (Pi.single 20 1)
  exact (clock_source_schur_flux_generated event _ window.1 window.2.1).self_of_nhds

/-- Real frequency on the nonempty original damped germ carries exactly one minus-I. -/
theorem actual_damped_frequency_factor (event : DressedEvent) :
    HasDerivAt (fun w : ℝ=>clockSchur event (anchorWindow event (Pi.single 20 1)) (3-Complex.I*(w:ℂ)))
      ((-Complex.I) • clockSourceSchurFlux event (anchorWindow event (Pi.single 20 1)) 3) 0 := by
  apply hasDerivAt_pi.mpr
  intro i
  apply hasDerivAt_pi.mpr
  intro j
  have entry : HasDerivAt (fun z=>clockSchur event (anchorWindow event (Pi.single 20 1)) z i j)
      (clockSourceSchurFlux event (anchorWindow event (Pi.single 20 1)) 3 i j) ((3:ℂ)-Complex.I*0) := by
    simpa using! hasDerivAt_pi.mp (hasDerivAt_pi.mp (actual_anchor_schur_flux event) i) j
  have path : HasDerivAt (fun w : ℂ=>3-Complex.I*w) (-Complex.I) 0 := by
    simpa only [zero_sub,mul_one] using! (hasDerivAt_const (0:ℂ) (3:ℂ)).sub
      ((hasDerivAt_id (0:ℂ)).const_mul Complex.I)
  have mapped:=entry.comp (0:ℂ) path
  simpa only [Function.comp_def,Matrix.smul_apply,smul_eq_mul,mul_comm (-Complex.I)] using! mapped.comp_ofReal

end LowEnergy.GaussComposite.ActualDressedFullSchurFluxAudit

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

elab "#audit_dressed_full_schur_flux" : command => do
  let env ← getEnv
  let modules := env.header.moduleNames
  let owner := fun name => (env.getModuleIdxFor? name).map fun i => modules[i.toNat]!
  let candidates := #[`H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualDressedConstraintClockColumns,`H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualDressedFullSchurFlux]
  let owned := env.constants.toList.filterMap fun (name, _) =>
    if (owner name).any candidates.contains then some name else none
  let mouths := #[
    ``LowEnergy.GaussComposite.ActualDressedSchurClock.clockNativeNull,
    ``LowEnergy.GaussComposite.ActualDressedSchurClock.clockNativeNullJet,
    ``LowEnergy.GaussComposite.ActualDressedSchurClock.clockNativeCokernel,
    ``LowEnergy.GaussComposite.ActualDressedSchurClock.clock_native_columns_actual,
    ``LowEnergy.GaussComposite.ActualDressedSchurClock.clock_native_columns_derivative,
    ``LowEnergy.GaussComposite.ActualDressedSchurClock.clock_schur_original_product,
    ``LowEnergy.GaussComposite.ActualDressedSchurClock.clockSourceSchurFlux,
    ``LowEnergy.GaussComposite.ActualDressedSchurClock.clock_source_schur_flux_generated]
  for name in mouths do
    unless owned.contains name do throwError m!"MISSING_MOUTH {name}"
  let tests := #[
    ``LowEnergy.GaussComposite.ActualDressedFullSchurFluxAudit.checked_clock_native_columns_actual,
    ``LowEnergy.GaussComposite.ActualDressedFullSchurFluxAudit.checked_clock_native_columns_derivative,
    ``LowEnergy.GaussComposite.ActualDressedFullSchurFluxAudit.checked_clock_schur_original_product,
    ``LowEnergy.GaussComposite.ActualDressedFullSchurFluxAudit.checked_clock_source_schur_flux_generated,
    ``LowEnergy.GaussComposite.ActualDressedFullSchurFluxAudit.actual_source_column_jets,
    ``LowEnergy.GaussComposite.ActualDressedFullSchurFluxAudit.actual_anchor_schur_flux,
    ``LowEnergy.GaussComposite.ActualDressedFullSchurFluxAudit.actual_damped_frequency_factor]
  let direct := #[
    (``LowEnergy.GaussComposite.ActualDressedSchurClock.clock_native_columns_actual,#[
    ``LowEnergy.GaussComposite.ActualDressedNullNative.original_null_lift_single,
    ``LowEnergy.GaussComposite.ActualEMDressedSchur.sourceCokernel]),
    (``LowEnergy.GaussComposite.ActualDressedSchurClock.clock_native_columns_derivative,#[
    ``LowEnergy.GaussComposite.ActualDressedNullNative.original_null_column_literal,
    ``LowEnergy.GaussComposite.ActualDressedSchurClock.clockNativeNullJet]),
    (``LowEnergy.GaussComposite.ActualDressedSchurClock.clock_schur_original_product,#[
    ``LowEnergy.GaussComposite.ActualDressedSchurClock.clock_native_columns_actual,
    ``LowEnergy.GaussComposite.ActualEMDressedClockSchur.clockSchur]),
    (``LowEnergy.GaussComposite.ActualDressedSchurClock.clock_source_schur_flux_generated,#[
    ``LowEnergy.GaussComposite.ActualEMDressedClockGerm.clock_resolvent_derivative,
    ``LowEnergy.GaussComposite.ActualEMDressedClockGerm.clock_feedback_full_flux,
    ``LowEnergy.GaussComposite.ActualDressedPhysicalClock.dressed_coincident_clock_jet_generated,
    ``LowEnergy.GaussComposite.ActualDressedSchurClock.clock_native_columns_derivative,
    ``LowEnergy.GaussComposite.ActualDressedSchurClock.clock_schur_original_product]),
    (``LowEnergy.GaussComposite.ActualDressedFullSchurFluxAudit.actual_anchor_schur_flux,#[
    ``LowEnergy.GaussComposite.ActualEMDressedSourceAnchor.anchor_window_source,
    ``LowEnergy.GaussComposite.ActualDressedSchurClock.clock_source_schur_flux_generated]),
    (``LowEnergy.GaussComposite.ActualDressedFullSchurFluxAudit.actual_damped_frequency_factor,#[
    ``LowEnergy.GaussComposite.ActualDressedFullSchurFluxAudit.actual_anchor_schur_flux])]
  for (mouth,required) in direct do packageCertRequire env mouth required
  let testProducers := #[
    ``LowEnergy.GaussComposite.ActualDressedSchurClock.clock_native_columns_actual,
    ``LowEnergy.GaussComposite.ActualDressedSchurClock.clock_native_columns_derivative,
    ``LowEnergy.GaussComposite.ActualDressedSchurClock.clock_schur_original_product,
    ``LowEnergy.GaussComposite.ActualDressedSchurClock.clock_source_schur_flux_generated]
  for i in [:testProducers.size] do packageCertRequire env tests[i]! #[testProducers[i]!]
  let all ← packageCertClosure env (owned ++ tests.toList)
  let anchors := #[
    ``SaturationMonoid.PhysicsCore.StageNineEnrichedProofFreeSource.positiveSmoothUnifiedSource,
    ``SaturationMonoid.PhysicsCore.Stage9C.Material.SpinPair.actual,
    ``LowEnergy.GaussComposite.ActualDressedSourcePreparation.sourceDressedUnit,
    ``LowEnergy.PreparationVacuumSourcePreparedResponse.sourceProfile,
    ``LowEnergy.GaussComposite.ActualDressedNoether.dressedEulerObserver,
    ``LowEnergy.GaussComposite.ActualDressedNullNative.originalNullColumn,
    ``LowEnergy.GaussComposite.ActualEMDressedSchur.sourceNullLift,
    ``LowEnergy.GaussComposite.ActualEMDressedSchur.sourceCokernel,
    ``LowEnergy.GaussComposite.ActualDressedPhysicalClock.dressedNativeClockFlux,
    ``LowEnergy.GaussComposite.ActualDressedPhysicalClock.dressedCoincidentClockJet,
    ``LowEnergy.GaussComposite.ActualEMDressedClockGerm.clockNullJet]
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
  if let some path ← liftIO (IO.getEnv "ALPHA_DRESSED_FULL_SCHUR_FLUX_AUDIT_OUTPUT") then
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
  logInfo m!"DRESSED_FULL_SCHUR_FLUX_PASS public={mouths.size} owned={owned.length} tests={tests.size} nodes={all.size} anchors={anchors.size} direct={direct.size} opaque_all_read={opaques} axioms={axioms} unknown=0 unsafe=0 partial=0"
#audit_dressed_full_schur_flux
#print axioms LowEnergy.GaussComposite.ActualDressedSchurClock.clock_native_columns_actual
#print axioms LowEnergy.GaussComposite.ActualDressedSchurClock.clock_native_columns_derivative
#print axioms LowEnergy.GaussComposite.ActualDressedSchurClock.clock_schur_original_product
#print axioms LowEnergy.GaussComposite.ActualDressedSchurClock.clock_source_schur_flux_generated
