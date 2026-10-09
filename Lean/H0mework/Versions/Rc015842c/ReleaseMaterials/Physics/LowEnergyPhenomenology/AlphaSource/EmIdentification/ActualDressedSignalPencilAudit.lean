import H0mework.Versions.Rc015842c.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualDressedSignalPencil

import Lean.Elab.Command
import Lean.Util.FoldConsts
import Lean.Util.CollectAxioms
set_option autoImplicit false
set_option maxHeartbeats 12000000
set_option maxRecDepth 32768
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.GaussComposite.ActualDressedSignalPencilAudit
elab "checked_dressed_window_polarization_actualContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualDressedPencil.dressed_window_polarization_actual).type
theorem checked_dressed_window_polarization_actual : checked_dressed_window_polarization_actualContract := @LowEnergy.GaussComposite.ActualDressedPencil.dressed_window_polarization_actual

elab "checked_dressed_native_window_pencil_generatedContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualDressedPencil.dressed_native_window_pencil_generated).type
theorem checked_dressed_native_window_pencil_generated : checked_dressed_native_window_pencil_generatedContract := @LowEnergy.GaussComposite.ActualDressedPencil.dressed_native_window_pencil_generated

elab "checked_dressed_coincident_clock_factorContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualDressedPencil.dressed_coincident_clock_factor).type
theorem checked_dressed_coincident_clock_factor : checked_dressed_coincident_clock_factorContract := @LowEnergy.GaussComposite.ActualDressedPencil.dressed_coincident_clock_factor

open SaturationMonoid.PhysicsCore StageNineHolonomicField ProofFreeRicherAnholonomicSource
open CanonicalGradedSpatialSource PreparationVacuumMixedFieldReturn PreparationVacuumPhysicalFeedback
open PreparationVacuumGaugeSourceInjection PreparationVacuumActionFieldLift
open PreparationVacuumCurrentSignalOperator PreparationVacuumCurrentSignalRealization
open SourcePropagationMotherEulerKernel SourcePropagationNativeActionHessian
open ActualDressedFullCoulomb ActualDressedNoether ActualDressedSignal
open MeasureTheory Filter Set
open ActualDressedPencil
open scoped Matrix BigOperators Topology Interval
attribute [local irreducible] nativeHessian dressedSignalRawEuler dressedNativeWindowPencil

theorem zero_actual_input_window (p : Fin 4→ℂ) (lambda : ℂ) : dressedClassicalTimeFactor p lambda 0=0 := by
  simp only [dressedClassicalTimeFactor,intervalIntegral.integral_same]

theorem actual_coincident_clock_nonzero (p : Fin 4→ℂ) (T : ℝ) (future : 0<T) :
    dressedClassicalTimeFactor p (p 0) T≠0 := by
  rw [dressed_coincident_clock_factor]
  exact_mod_cast future.ne'

theorem shifted_clock_does_not_drop_weight : dressedClassicalTimeFactor 0 1 1≠1 := by
  have paid (t : ℝ) : HasDerivAt (fun s : ℝ=> -Complex.exp (-(s:ℂ))) (Complex.exp (-(t:ℂ))) t := by
    have base:=Complex.ofRealCLM.hasFDerivAt.comp_hasDerivAt t (hasDerivAt_id t)
    simpa using! base.neg.cexp.neg
  have continuousIntegrand : Continuous (fun t : ℝ=>Complex.exp (-(t:ℂ))) := by fun_prop
  have original:=intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _=>paid t)
    (continuousIntegrand.intervalIntegrable (0:ℝ) 1)
  have equation : dressedClassicalTimeFactor 0 1 1=1-Complex.exp (-1) := by
    simpa [dressedClassicalTimeFactor,laplaceWeight,sub_eq_add_neg,add_comm] using original
  rw [equation]
  intro same
  have contradiction : Complex.exp (-1)=0 := by linear_combination -same
  exact Complex.exp_ne_zero _ contradiction

end LowEnergy.GaussComposite.ActualDressedSignalPencilAudit

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

elab "#audit_dressed_signal_pencil" : command => do
  let env ← getEnv
  let modules := env.header.moduleNames
  let owner := fun name => (env.getModuleIdxFor? name).map fun i => modules[i.toNat]!
  let candidates := #[`H0mework.Versions.Rc015842c.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualDressedSignalPencil]
  let owned := env.constants.toList.filterMap fun (name, _) =>
    if (owner name).any candidates.contains then some name else none
  let mouths := #[
    ``LowEnergy.GaussComposite.ActualDressedPencil.dressedWindowPolarization,
    ``LowEnergy.GaussComposite.ActualDressedPencil.dressed_window_polarization_actual,
    ``LowEnergy.GaussComposite.ActualDressedPencil.dressedClassicalTimeFactor,
    ``LowEnergy.GaussComposite.ActualDressedPencil.dressedNativeWindowPencil,
    ``LowEnergy.GaussComposite.ActualDressedPencil.dressed_native_window_pencil_generated,
    ``LowEnergy.GaussComposite.ActualDressedPencil.dressed_coincident_clock_factor]
  for name in mouths do
    unless owned.contains name do throwError m!"MISSING_MOUTH {name}"
  let tests := #[
    ``LowEnergy.GaussComposite.ActualDressedSignalPencilAudit.checked_dressed_window_polarization_actual,
    ``LowEnergy.GaussComposite.ActualDressedSignalPencilAudit.checked_dressed_native_window_pencil_generated,
    ``LowEnergy.GaussComposite.ActualDressedSignalPencilAudit.checked_dressed_coincident_clock_factor,
    ``LowEnergy.GaussComposite.ActualDressedSignalPencilAudit.zero_actual_input_window,
    ``LowEnergy.GaussComposite.ActualDressedSignalPencilAudit.actual_coincident_clock_nonzero,
    ``LowEnergy.GaussComposite.ActualDressedSignalPencilAudit.shifted_clock_does_not_drop_weight]
  let direct := #[
    (``LowEnergy.GaussComposite.ActualDressedPencil.dressed_window_polarization_actual,#[
    ``LowEnergy.GaussComposite.ActualDressedSignal.dressed_signal_window_actual,
    ``LowEnergy.GaussComposite.ActualDressedSignal.dressed_signal_matrix_actual]),
    (``LowEnergy.GaussComposite.ActualDressedPencil.dressed_native_window_pencil_generated,#[
    ``LowEnergy.GaussComposite.ActualDressedSignal.dressed_signal_raw_euler_generated,
    ``LowEnergy.GaussComposite.ActualDressedSignal.dressed_signal_quadrature_continuous,
    ``LowEnergy.GaussComposite.ActualDressedPencil.dressedClassicalTimeFactor,
    ``LowEnergy.GaussComposite.ActualDressedPencil.dressedWindowPolarization]),
    (``LowEnergy.GaussComposite.ActualDressedPencil.dressed_coincident_clock_factor,#[
    ``LowEnergy.GaussComposite.ActualDressedPencil.dressedClassicalTimeFactor])]
  for (mouth,required) in direct do packageCertRequire env mouth required
  let testProducers := #[
    ``LowEnergy.GaussComposite.ActualDressedPencil.dressed_window_polarization_actual,
    ``LowEnergy.GaussComposite.ActualDressedPencil.dressed_native_window_pencil_generated,
    ``LowEnergy.GaussComposite.ActualDressedPencil.dressed_coincident_clock_factor]
  for i in [:testProducers.size] do packageCertRequire env tests[i]! #[testProducers[i]!]
  let all ← packageCertClosure env (owned ++ tests.toList)
  let anchors := #[
    ``SaturationMonoid.PhysicsCore.StageNineEnrichedProofFreeSource.positiveSmoothUnifiedSource,
    ``SaturationMonoid.PhysicsCore.Stage9C.Material.SpinPair.actual,
    ``LowEnergy.GaussComposite.ActualDressedSourcePreparation.sourceDressedUnit,
    ``LowEnergy.PreparationVacuumSourcePreparedResponse.sourceProfile,
    ``LowEnergy.GaussComposite.ActualDressedSignal.dressedSignalMatrix,
    ``LowEnergy.GaussComposite.ActualDressedSignal.dressedSignalRawEuler,
    ``LowEnergy.GaussComposite.ActualDressedSignal.dressedSignalWindow,
    ``LowEnergy.GaussComposite.ActualDressedSignal.dressedSignalDuration,
    ``LowEnergy.SourcePropagationMotherResidualDirections.actualMotherEulerRead,
    ``LowEnergy.SourcePropagationNativeActionHessian.nativeHessian,
    ``LowEnergy.PreparationVacuumCurrentSignalRealization.sourceSignalAmplitude]
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
  if let some path ← liftIO (IO.getEnv "ALPHA_DRESSED_SIGNAL_PENCIL_AUDIT_OUTPUT") then
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
  logInfo m!"DRESSED_SIGNAL_PENCIL_PASS public={mouths.size} owned={owned.length} tests={tests.size} nodes={all.size} anchors={anchors.size} direct={direct.size} opaque_all_read={opaques} axioms={axioms} unknown=0 unsafe=0 partial=0"
#audit_dressed_signal_pencil
#print axioms LowEnergy.GaussComposite.ActualDressedPencil.dressed_window_polarization_actual
#print axioms LowEnergy.GaussComposite.ActualDressedPencil.dressed_native_window_pencil_generated
#print axioms LowEnergy.GaussComposite.ActualDressedPencil.dressed_coincident_clock_factor
