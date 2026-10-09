import H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualDressedCubicIRFactor
import H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualDressedCubicIRReturn

import Lean.Elab.Command
import Lean.Util.FoldConsts
import Lean.Util.CollectAxioms
set_option autoImplicit false
set_option maxHeartbeats 12000000
set_option maxRecDepth 32768
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.GaussComposite.ActualDressedCubicIRAudit
elab "checked_actual_ir_source_price_nonnegContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualDressedCubicIRReturn.actual_ir_source_price_nonneg).type
theorem checked_actual_ir_source_price_nonneg : checked_actual_ir_source_price_nonnegContract := @LowEnergy.GaussComposite.ActualDressedCubicIRReturn.actual_ir_source_price_nonneg

elab "checked_actual_regular_matrix_real_priceContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualDressedCubicIRReturn.actual_regular_matrix_real_price).type
theorem checked_actual_regular_matrix_real_price : checked_actual_regular_matrix_real_priceContract := @LowEnergy.GaussComposite.ActualDressedCubicIRReturn.actual_regular_matrix_real_price

elab "checked_actual_regular_matrix_order_lowerContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualDressedCubicIRReturn.actual_regular_matrix_order_lower).type
theorem checked_actual_regular_matrix_order_lower : checked_actual_regular_matrix_order_lowerContract := @LowEnergy.GaussComposite.ActualDressedCubicIRReturn.actual_regular_matrix_order_lower

elab "checked_actual_regular_matrix_factorContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualDressedCubicIRReturn.actual_regular_matrix_factor).type
theorem checked_actual_regular_matrix_factor : checked_actual_regular_matrix_factorContract := @LowEnergy.GaussComposite.ActualDressedCubicIRReturn.actual_regular_matrix_factor

elab "checked_actual_fourth_ir_regularizationContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualDressedCubicIRReturn.actual_fourth_ir_regularization).type
theorem checked_actual_fourth_ir_regularization : checked_actual_fourth_ir_regularizationContract := @LowEnergy.GaussComposite.ActualDressedCubicIRReturn.actual_fourth_ir_regularization

elab "checked_actual_fourth_ir_returnContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualDressedCubicIRReturn.actual_fourth_ir_return).type
theorem checked_actual_fourth_ir_return : checked_actual_fourth_ir_returnContract := @LowEnergy.GaussComposite.ActualDressedCubicIRReturn.actual_fourth_ir_return

elab "checked_actual_fourth_ir_real_returnContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualDressedCubicIRReturn.actual_fourth_ir_real_return).type
theorem checked_actual_fourth_ir_real_return : checked_actual_fourth_ir_real_returnContract := @LowEnergy.GaussComposite.ActualDressedCubicIRReturn.actual_fourth_ir_real_return

elab "checked_actual_sixth_ir_zero_returnContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualDressedCubicIRReturn.actual_sixth_ir_zero_return).type
theorem checked_actual_sixth_ir_zero_return : checked_actual_sixth_ir_zero_returnContract := @LowEnergy.GaussComposite.ActualDressedCubicIRReturn.actual_sixth_ir_zero_return

open CanonicalGradedSpatialSource
open ActualDressedFullCoulomb ActualDressedSourcePreparation ActualDressedSylvester ActualDressedStaticPole
open Set Filter
open scoped Topology Matrix.Norms.Elementwise

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

theorem actual_unit_nonzero (event : DressedEvent) : sourceDressedUnit event.epsilon event.precision≠0 := by
  intro zero
  have source:=source_dressed_unit_norm event.epsilon event.precision
  rw [zero,norm_zero] at source
  exact zero_ne_one source

theorem same_original_fourth_factor (event : DressedEvent) :
    ∃G : ℂ→Matrix (Fin 289) (Fin 289) ℂ,AnalyticAt ℂ G 0 ∧
      ∀ᶠz : ℂ in 𝓝 0,dressedStaticPoleRegular event z=z^(2*dressedStaticPoleOrder event-4) • G z :=
  ActualDressedCubicIRReturn.actual_regular_matrix_factor event

theorem same_full_actual_fourth_return (event : DressedEvent) :
    ∃L : Matrix (Fin 289) (Fin 289) ℂ,
      Tendsto (fun s : ℝ=>(s:ℂ)^4 • dressedStaticPolarization event 0 (s:ℂ))
        (nhdsWithin 0 (Ioi (0:ℝ))) (𝓝 L) :=
  ActualDressedCubicIRReturn.actual_fourth_ir_real_return event

theorem same_original_sixth_zero_return (event : DressedEvent) :
    Tendsto (fun z : ℂ=>z^6 • dressedStaticPolarization event 0 z)
      (nhdsWithin 0 {z : ℂ|0<z.re}) (𝓝 0) :=
  ActualDressedCubicIRReturn.actual_sixth_ir_zero_return event
end LowEnergy.GaussComposite.ActualDressedCubicIRAudit

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

elab "#audit_dressed_cubic_ir" : command => do
  let env ← getEnv
  let modules := env.header.moduleNames
  let owner := fun name => (env.getModuleIdxFor? name).map fun i => modules[i.toNat]!
  let candidates := #[`H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualDressedCubicIRFactor,`H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualDressedCubicIRReturn]
  let owned := env.constants.toList.filterMap fun (name, _) =>
    if (owner name).any candidates.contains then some name else none
  let mouths := #[
    ``LowEnergy.GaussComposite.ActualDressedCubicIRReturn.actualIRSourcePrice,
    ``LowEnergy.GaussComposite.ActualDressedCubicIRReturn.actual_ir_source_price_nonneg,
    ``LowEnergy.GaussComposite.ActualDressedCubicIRReturn.actual_regular_matrix_real_price,
    ``LowEnergy.GaussComposite.ActualDressedCubicIRReturn.actual_regular_matrix_order_lower,
    ``LowEnergy.GaussComposite.ActualDressedCubicIRReturn.actual_regular_matrix_factor,
    ``LowEnergy.GaussComposite.ActualDressedCubicIRReturn.actual_fourth_ir_regularization,
    ``LowEnergy.GaussComposite.ActualDressedCubicIRReturn.actual_fourth_ir_return,
    ``LowEnergy.GaussComposite.ActualDressedCubicIRReturn.actual_fourth_ir_real_return,
    ``LowEnergy.GaussComposite.ActualDressedCubicIRReturn.actual_sixth_ir_zero_return]
  for name in mouths do
    unless owned.contains name do throwError m!"MISSING_MOUTH {name}"
  let tests := #[
    ``LowEnergy.GaussComposite.ActualDressedCubicIRAudit.checked_actual_ir_source_price_nonneg,
    ``LowEnergy.GaussComposite.ActualDressedCubicIRAudit.checked_actual_regular_matrix_real_price,
    ``LowEnergy.GaussComposite.ActualDressedCubicIRAudit.checked_actual_regular_matrix_order_lower,
    ``LowEnergy.GaussComposite.ActualDressedCubicIRAudit.checked_actual_regular_matrix_factor,
    ``LowEnergy.GaussComposite.ActualDressedCubicIRAudit.checked_actual_fourth_ir_regularization,
    ``LowEnergy.GaussComposite.ActualDressedCubicIRAudit.checked_actual_fourth_ir_return,
    ``LowEnergy.GaussComposite.ActualDressedCubicIRAudit.checked_actual_fourth_ir_real_return,
    ``LowEnergy.GaussComposite.ActualDressedCubicIRAudit.checked_actual_sixth_ir_zero_return,
    ``LowEnergy.GaussComposite.ActualDressedCubicIRAudit.actual_event_nonempty,
    ``LowEnergy.GaussComposite.ActualDressedCubicIRAudit.actual_unit_nonzero,
    ``LowEnergy.GaussComposite.ActualDressedCubicIRAudit.same_original_fourth_factor,
    ``LowEnergy.GaussComposite.ActualDressedCubicIRAudit.same_full_actual_fourth_return,
    ``LowEnergy.GaussComposite.ActualDressedCubicIRAudit.same_original_sixth_zero_return]
  let direct := #[
    (``LowEnergy.GaussComposite.ActualDressedCubicIRReturn.actual_regular_matrix_real_price,#[
    ``LowEnergy.GaussComposite.ActualDressedCubicPrice.actual_static_polarization_sigma_four_price,
    ``LowEnergy.GaussComposite.ActualDressedStaticPole.dressed_static_polarization_regularized]),
    (``LowEnergy.GaussComposite.ActualDressedCubicIRReturn.actual_regular_matrix_order_lower,#[
    ``LowEnergy.GaussComposite.ActualDressedIRReturn.actual_regular_matrix_analytic,
    ``LowEnergy.GaussComposite.ActualDressedCubicIRReturn.actual_regular_matrix_real_price]),
    (``LowEnergy.GaussComposite.ActualDressedCubicIRReturn.actual_regular_matrix_factor,#[
    ``LowEnergy.GaussComposite.ActualDressedCubicIRReturn.actual_regular_matrix_order_lower]),
    (``LowEnergy.GaussComposite.ActualDressedCubicIRReturn.actual_fourth_ir_regularization,#[
    ``LowEnergy.GaussComposite.ActualDressedCubicIRReturn.actual_regular_matrix_factor,
    ``LowEnergy.GaussComposite.ActualDressedIRReturn.actual_regular_matrix_analytic,
    ``LowEnergy.GaussComposite.ActualDressedStaticPole.dressed_static_polarization_regularized]),
    (``LowEnergy.GaussComposite.ActualDressedCubicIRReturn.actual_fourth_ir_return,#[
    ``LowEnergy.GaussComposite.ActualDressedCubicIRReturn.actual_fourth_ir_regularization]),
    (``LowEnergy.GaussComposite.ActualDressedCubicIRReturn.actual_fourth_ir_real_return,#[
    ``LowEnergy.GaussComposite.ActualDressedCubicIRReturn.actual_fourth_ir_regularization]),
    (``LowEnergy.GaussComposite.ActualDressedCubicIRReturn.actual_sixth_ir_zero_return,#[
    ``LowEnergy.GaussComposite.ActualDressedCubicIRReturn.actual_fourth_ir_regularization])]
  for (mouth,required) in direct do packageCertRequire env mouth required
  let testProducers := #[
    ``LowEnergy.GaussComposite.ActualDressedCubicIRReturn.actual_ir_source_price_nonneg,
    ``LowEnergy.GaussComposite.ActualDressedCubicIRReturn.actual_regular_matrix_real_price,
    ``LowEnergy.GaussComposite.ActualDressedCubicIRReturn.actual_regular_matrix_order_lower,
    ``LowEnergy.GaussComposite.ActualDressedCubicIRReturn.actual_regular_matrix_factor,
    ``LowEnergy.GaussComposite.ActualDressedCubicIRReturn.actual_fourth_ir_regularization,
    ``LowEnergy.GaussComposite.ActualDressedCubicIRReturn.actual_fourth_ir_return,
    ``LowEnergy.GaussComposite.ActualDressedCubicIRReturn.actual_fourth_ir_real_return,
    ``LowEnergy.GaussComposite.ActualDressedCubicIRReturn.actual_sixth_ir_zero_return]
  for i in [:testProducers.size] do packageCertRequire env tests[i]! #[testProducers[i]!]
  let all ← packageCertClosure env (owned ++ tests.toList)
  let anchors := #[
    ``SaturationMonoid.PhysicsCore.StageNineEnrichedProofFreeSource.positiveSmoothUnifiedSource,
    ``SaturationMonoid.PhysicsCore.Stage9C.Material.SpinPair.actual,
    ``LowEnergy.CanonicalCompletedSector.seed,
    ``LowEnergy.NativeHistoryGrade.projection,
    ``LowEnergy.GaussComposite.SourceGraph.prepared,
    ``LowEnergy.PreparationVacuumUncutYukawa.uncutOperator,
    ``LowEnergy.PreparationVacuumRawJointFeedback.physicalTime,
    ``LowEnergy.PreparationVacuumJointFieldResponse.jointResolvent,
    ``LowEnergy.GaussComposite.ActualDressedSourcePreparation.sourceDressedUnit,
    ``LowEnergy.PreparationVacuumSourcePreparedResponse.sourceProfile,
    ``LowEnergy.GaussComposite.ActualDressedNoether.dressedNoetherKernel,
    ``LowEnergy.GaussComposite.ActualDressedNoether.dressedEulerObserver,
    ``LowEnergy.PreparationVacuumJointFieldResponse.jointCompression,
    ``LowEnergy.PreparationVacuumJointFieldResponse.jointCurrent,
    ``LowEnergy.PreparationVacuumJointFieldResponse.jointGenerator,
    ``LowEnergy.GaussComposite.ActualDressedNoether.dressedNoetherJet,
    ``LowEnergy.CanonicalPhysicalSpatial.compression,
    ``LowEnergy.PreparationVacuumJointFieldResponse.jointY_source,
    ``LowEnergy.GaussComposite.ActualDressedSylvester.dressedStaticPolarization,
    ``LowEnergy.PreparationVacuumNoetherChart.noetherReader,
    ``LowEnergy.PreparationVacuumNoetherChart.noetherReaderContact,
    ``LowEnergy.GaussComposite.ActualDressedStaticPole.dressedStaticPoleOrder,
    ``LowEnergy.GaussComposite.ActualDressedStaticPole.dressedStaticPoleRegular,
    ``LowEnergy.GaussComposite.ActualDressedCubicPrice.observedCubicStaticSourcePrice]
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
  if let some path ← liftIO (IO.getEnv "ALPHA_DRESSED_CUBIC_IR_AUDIT_OUTPUT") then
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
  logInfo m!"DRESSED_CUBIC_IR_PASS public={mouths.size} owned={owned.length} tests={tests.size} nodes={all.size} anchors={anchors.size} direct={direct.size} opaque_all_read={opaques} axioms={axioms} unknown=0 unsafe=0 partial=0"
#audit_dressed_cubic_ir
#print axioms LowEnergy.GaussComposite.ActualDressedCubicIRReturn.actual_ir_source_price_nonneg
#print axioms LowEnergy.GaussComposite.ActualDressedCubicIRReturn.actual_regular_matrix_real_price
#print axioms LowEnergy.GaussComposite.ActualDressedCubicIRReturn.actual_regular_matrix_order_lower
#print axioms LowEnergy.GaussComposite.ActualDressedCubicIRReturn.actual_regular_matrix_factor
#print axioms LowEnergy.GaussComposite.ActualDressedCubicIRReturn.actual_fourth_ir_regularization
#print axioms LowEnergy.GaussComposite.ActualDressedCubicIRReturn.actual_fourth_ir_return
#print axioms LowEnergy.GaussComposite.ActualDressedCubicIRReturn.actual_fourth_ir_real_return
#print axioms LowEnergy.GaussComposite.ActualDressedCubicIRReturn.actual_sixth_ir_zero_return
