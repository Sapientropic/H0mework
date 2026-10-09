import H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualNullNativeTable
import H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualNullNativeColumn
import H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualDressedConstraintTranspose
import H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualDressedConstraintHistory

import Lean.Elab.Command
import Lean.Util.FoldConsts
import Lean.Util.CollectAxioms
set_option autoImplicit false
set_option maxHeartbeats 12000000
set_option maxRecDepth 32768
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.GaussComposite.ActualDressedConstraintWardAudit
elab "checked_original_null_column_literalContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualDressedNullNative.original_null_column_literal).type
theorem checked_original_null_column_literal : checked_original_null_column_literalContract := @LowEnergy.GaussComposite.ActualDressedNullNative.original_null_column_literal

elab "checked_original_null_cokernelContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualDressedNullNative.original_null_cokernel).type
theorem checked_original_null_cokernel : checked_original_null_cokernelContract := @LowEnergy.GaussComposite.ActualDressedNullNative.original_null_cokernel

elab "checked_original_null_lift_singleContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualDressedNullNative.original_null_lift_single).type
theorem checked_original_null_lift_single : checked_original_null_lift_singleContract := @LowEnergy.GaussComposite.ActualDressedNullNative.original_null_lift_single

elab "checked_source_cokernel_actual_pencilContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualDressedConstraintWard.source_cokernel_actual_pencil).type
theorem checked_source_cokernel_actual_pencil : checked_source_cokernel_actual_pencilContract := @LowEnergy.GaussComposite.ActualDressedConstraintWard.source_cokernel_actual_pencil

elab "checked_dressed_complex_reader_actualContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualDressedConstraintWard.dressed_complex_reader_actual).type
theorem checked_dressed_complex_reader_actual : checked_dressed_complex_reader_actualContract := @LowEnergy.GaussComposite.ActualDressedConstraintWard.dressed_complex_reader_actual

elab "checked_dressed_quantum_reader_actualContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualDressedConstraintWard.dressed_quantum_reader_actual).type
theorem checked_dressed_quantum_reader_actual : checked_dressed_quantum_reader_actualContract := @LowEnergy.GaussComposite.ActualDressedConstraintWard.dressed_quantum_reader_actual

elab "checked_source_constraint_quantum_historyContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualDressedConstraintWard.source_constraint_quantum_history).type
theorem checked_source_constraint_quantum_history : checked_source_constraint_quantum_historyContract := @LowEnergy.GaussComposite.ActualDressedConstraintWard.source_constraint_quantum_history

elab "checked_source_constraint_nonlinear_historyContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualDressedConstraintWard.source_constraint_nonlinear_history).type
theorem checked_source_constraint_nonlinear_history : checked_source_constraint_nonlinear_historyContract := @LowEnergy.GaussComposite.ActualDressedConstraintWard.source_constraint_nonlinear_history

elab "checked_source_constraint_schur_historyContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualDressedConstraintWard.source_constraint_schur_history).type
theorem checked_source_constraint_schur_history : checked_source_constraint_schur_historyContract := @LowEnergy.GaussComposite.ActualDressedConstraintWard.source_constraint_schur_history

open CanonicalGradedSpatialSource PreparationVacuumMixedFieldReturn PreparationVacuumOriginalGreenFeedback
open ActualEMDressedSchur ActualDressedNullNative
open scoped Matrix BigOperators

theorem checked_parent_original_lift (p : Fin 4→ℂ) (n : Fin 9) :
    sourceNullLift p (Pi.single n 1)=originalNullColumn p n := original_null_lift_single p n

theorem checked_parent_column_temporal_sign (p : Fin 4→ℂ) : originalNullColumn p 0 10= -(p 0)/2 := by
  rw [original_null_column_literal]
  norm_num [nullColumnTerms,sourceMatrix,SourceTerm.matrix,Matrix.single_apply,
    nullColumnIndex,Fin.ext_iff,Powers.value,coefficientValue]
  ring

theorem checked_parent_opposite_cokernel_sign (p : Fin 4→ℂ) : sourceCokernel p (Pi.single 10 1) 0=p 0/2 := by
  rw [original_null_cokernel]
  simp only [Pi.single_apply,mul_ite,mul_one,mul_zero,Finset.sum_ite_eq',Finset.mem_univ,if_true]
  rw [original_null_column_literal]
  norm_num [nullColumnTerms,sourceMatrix,SourceTerm.matrix,Matrix.single_apply,
    nullColumnIndex,Fin.ext_iff,Powers.value,coefficientValue]
  ring

theorem checked_parent_other_column_zero (p : Fin 4→ℂ) : sourceCokernel p (Pi.single 10 1) 1=0 := by
  rw [original_null_cokernel]
  simp only [Pi.single_apply,mul_ite,mul_one,mul_zero,Finset.sum_ite_eq',Finset.mem_univ,if_true]
  rw [original_null_column_literal]
  norm_num [nullColumnTerms,sourceMatrix,SourceTerm.matrix,Matrix.single_apply,
    nullColumnIndex,Fin.ext_iff]


open SaturationMonoid.PhysicsCore SaturationMonoid.PhysicsCore.LowEnergy
open CanonicalGradedSpatialSource PreparationVacuumMixedFieldReturn PreparationVacuumPhysicalFeedback
open PreparationVacuumOriginalGreenFeedback PreparationPhysicalVoltageCompleteReturn
open PreparationVacuumCurrentSignalOperator PreparationVacuumCurrentSignalRealization
open PreparationVacuumGaugeSourceInjection PreparationVacuumActionFieldLift
open SourcePropagationNativeActionHessian SourcePropagationNoetherTime SourcePropagationMotherEulerKernel
open ActualDressedFullCoulomb ActualDressedNoether ActualDressedSignal ActualDressedPencil
open ActualEMDressedSourceAnchor ActualEMDressedAnchorInverse ActualEMDressedConstraint ActualEMDressedSchur
open ActualDressedConstraintRead ActualDressedNullNative ActualDressedConstraintWard
open MeasureTheory
open scoped Matrix BigOperators Topology Interval
attribute [local irreducible] originalChange dressedEulerObserver noetherHistoryOperatorJet dressedNoetherJet

/-- The original derivative column detects the opposite Fourier momentum. -/
theorem original_opposite_momentum_detected :
    originalNullColumn (-(Pi.single 0 1 : Fin 4→ℂ)) 0 10≠
      originalNullColumn (Pi.single 0 1) 0 10 := by
  rw [original_null_column_literal,original_null_column_literal]
  norm_num [nullColumnTerms,sourceMatrix,SourceTerm.matrix,Matrix.single_apply,
    nullColumnIndex,Fin.ext_iff,Powers.value,coefficientValue,Pi.single_apply]

/-- A pure imaginary reader remains an actual real source field multiplied once by I. -/
theorem actual_imaginary_reader (event : DressedEvent) (transfer : PhysicalMomentum)
    (f : Field289) (signal : ℝ→SourceJet Field289) (t : ℝ) :
    dressedComplexReader event transfer (fun j=>Complex.I*(f j:ℂ)) signal t=
      Complex.I*dressedEulerObserver event
        (noetherHistoryOperatorJet (dressedKinematicPoint event transfer) f signal t).value := by
  rw [dressed_complex_reader_actual,actual_noether_reader_contraction,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- Even at zero quantum age, the full Schur forcing has its original nine-row responsibility. -/
theorem actual_zero_age_forcing (event : DressedEvent) (forcing : SignalAmplitude)
    (initial : Fin 9→ℂ) (n : Fin 9) :
    (anchorSchur event 0*ᵥinitial-anchorSchurSource event 0 forcing) n=sourceCokernel anchorInput forcing n := by
  rw [source_constraint_schur_history]
  simp

end LowEnergy.GaussComposite.ActualDressedConstraintWardAudit

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

elab "#audit_dressed_constraint_ward_union" : command => do
  let env ← getEnv
  let modules := env.header.moduleNames
  let owner := fun name => (env.getModuleIdxFor? name).map fun i => modules[i.toNat]!
  let candidates := #[`H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualNullNativeTable,`H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualNullNativeColumn,`H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualDressedConstraintTranspose,`H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualDressedConstraintHistory]
  let owned := env.constants.toList.filterMap fun (name, _) =>
    if (owner name).any candidates.contains then some name else none
  let mouths := #[
    ``LowEnergy.GaussComposite.ActualDressedNullNative.nullColumnIndex,
    ``LowEnergy.GaussComposite.ActualDressedNullNative.originalNullColumn,
    ``LowEnergy.GaussComposite.ActualDressedNullNative.originalNullReal,
    ``LowEnergy.GaussComposite.ActualDressedNullNative.nullColumnTerms,
    ``LowEnergy.GaussComposite.ActualDressedNullNative.original_null_column_literal,
    ``LowEnergy.GaussComposite.ActualDressedNullNative.original_null_cokernel,
    ``LowEnergy.GaussComposite.ActualDressedNullNative.original_null_lift_single,
    ``LowEnergy.GaussComposite.ActualDressedConstraintWard.source_cokernel_actual_pencil,
    ``LowEnergy.GaussComposite.ActualDressedConstraintWard.dressedComplexReader,
    ``LowEnergy.GaussComposite.ActualDressedConstraintWard.dressed_complex_reader_actual,
    ``LowEnergy.GaussComposite.ActualDressedConstraintWard.dressedQuantumReader,
    ``LowEnergy.GaussComposite.ActualDressedConstraintWard.dressed_quantum_reader_actual,
    ``LowEnergy.GaussComposite.ActualDressedConstraintWard.source_constraint_quantum_history,
    ``LowEnergy.GaussComposite.ActualDressedConstraintWard.source_constraint_nonlinear_history,
    ``LowEnergy.GaussComposite.ActualDressedConstraintWard.source_constraint_schur_history]
  for name in mouths do
    unless owned.contains name do throwError m!"MISSING_MOUTH {name}"
  let tests := #[
    ``LowEnergy.GaussComposite.ActualDressedConstraintWardAudit.checked_original_null_column_literal,
    ``LowEnergy.GaussComposite.ActualDressedConstraintWardAudit.checked_original_null_cokernel,
    ``LowEnergy.GaussComposite.ActualDressedConstraintWardAudit.checked_original_null_lift_single,
    ``LowEnergy.GaussComposite.ActualDressedConstraintWardAudit.checked_source_cokernel_actual_pencil,
    ``LowEnergy.GaussComposite.ActualDressedConstraintWardAudit.checked_dressed_complex_reader_actual,
    ``LowEnergy.GaussComposite.ActualDressedConstraintWardAudit.checked_dressed_quantum_reader_actual,
    ``LowEnergy.GaussComposite.ActualDressedConstraintWardAudit.checked_source_constraint_quantum_history,
    ``LowEnergy.GaussComposite.ActualDressedConstraintWardAudit.checked_source_constraint_nonlinear_history,
    ``LowEnergy.GaussComposite.ActualDressedConstraintWardAudit.checked_source_constraint_schur_history,
    ``LowEnergy.GaussComposite.ActualDressedConstraintWardAudit.checked_parent_original_lift,
    ``LowEnergy.GaussComposite.ActualDressedConstraintWardAudit.checked_parent_column_temporal_sign,
    ``LowEnergy.GaussComposite.ActualDressedConstraintWardAudit.checked_parent_opposite_cokernel_sign,
    ``LowEnergy.GaussComposite.ActualDressedConstraintWardAudit.checked_parent_other_column_zero,
    ``LowEnergy.GaussComposite.ActualDressedConstraintWardAudit.original_opposite_momentum_detected,
    ``LowEnergy.GaussComposite.ActualDressedConstraintWardAudit.actual_imaginary_reader,
    ``LowEnergy.GaussComposite.ActualDressedConstraintWardAudit.actual_zero_age_forcing]
  let direct := #[
    (``LowEnergy.GaussComposite.ActualDressedNullNative.original_null_column_literal,#[
    ``LowEnergy.PreparationVacuumOriginalGreenFeedback.originalChangeTerms]),
    (``LowEnergy.GaussComposite.ActualDressedNullNative.original_null_lift_single,#[
    ``LowEnergy.GaussComposite.ActualEMDressedSchur.sourceNullLift,
    ``LowEnergy.GaussComposite.ActualDressedNullNative.originalNullColumn]),
    (``LowEnergy.GaussComposite.ActualDressedConstraintWard.source_cokernel_actual_pencil,#[
    ``LowEnergy.GaussComposite.ActualEMDressedConstraint.source_compatibility_euler,
    ``LowEnergy.GaussComposite.ActualEMDressedSchur.source_compatibility_nine]),
    (``LowEnergy.GaussComposite.ActualDressedConstraintWard.dressed_complex_reader_actual,#[
    ``LowEnergy.GaussComposite.ActualDressedConstraintRead.actual_complex_noether_contraction]),
    (``LowEnergy.GaussComposite.ActualDressedConstraintWard.dressed_quantum_reader_actual,#[
    ``LowEnergy.GaussComposite.ActualDressedConstraintWard.dressed_complex_reader_actual,
    ``LowEnergy.GaussComposite.ActualDressedSignal.dressedSignalQuadrature]),
    (``LowEnergy.GaussComposite.ActualDressedConstraintWard.source_constraint_quantum_history,#[
    ``LowEnergy.GaussComposite.ActualDressedNullNative.originalNullColumn,
    ``LowEnergy.GaussComposite.ActualDressedConstraintWard.dressed_quantum_reader_actual]),
    (``LowEnergy.GaussComposite.ActualDressedConstraintWard.source_constraint_nonlinear_history,#[
    ``LowEnergy.GaussComposite.ActualDressedPencil.dressed_native_window_pencil_generated,
    ``LowEnergy.GaussComposite.ActualDressedConstraintWard.source_cokernel_actual_pencil,
    ``LowEnergy.GaussComposite.ActualDressedConstraintWard.source_constraint_quantum_history]),
    (``LowEnergy.GaussComposite.ActualDressedConstraintWard.source_constraint_schur_history,#[
    ``LowEnergy.GaussComposite.ActualEMDressedSchur.anchor_schur_generated,
    ``LowEnergy.GaussComposite.ActualDressedConstraintWard.source_constraint_quantum_history])]
  for (mouth,required) in direct do packageCertRequire env mouth required
  let testProducers := #[
    ``LowEnergy.GaussComposite.ActualDressedNullNative.original_null_column_literal,
    ``LowEnergy.GaussComposite.ActualDressedNullNative.original_null_cokernel,
    ``LowEnergy.GaussComposite.ActualDressedNullNative.original_null_lift_single,
    ``LowEnergy.GaussComposite.ActualDressedConstraintWard.source_cokernel_actual_pencil,
    ``LowEnergy.GaussComposite.ActualDressedConstraintWard.dressed_complex_reader_actual,
    ``LowEnergy.GaussComposite.ActualDressedConstraintWard.dressed_quantum_reader_actual,
    ``LowEnergy.GaussComposite.ActualDressedConstraintWard.source_constraint_quantum_history,
    ``LowEnergy.GaussComposite.ActualDressedConstraintWard.source_constraint_nonlinear_history,
    ``LowEnergy.GaussComposite.ActualDressedConstraintWard.source_constraint_schur_history]
  for i in [:testProducers.size] do packageCertRequire env tests[i]! #[testProducers[i]!]
  let all ← packageCertClosure env (owned ++ tests.toList)
  let anchors := #[
    ``SaturationMonoid.PhysicsCore.StageNineEnrichedProofFreeSource.positiveSmoothUnifiedSource,
    ``SaturationMonoid.PhysicsCore.Stage9C.Material.SpinPair.actual,
    ``LowEnergy.GaussComposite.ActualDressedSourcePreparation.sourceDressedUnit,
    ``LowEnergy.PreparationVacuumSourcePreparedResponse.sourceProfile,
    ``LowEnergy.GaussComposite.ActualDressedNoether.dressedEulerObserver,
    ``LowEnergy.GaussComposite.ActualEMDressedSchur.sourceNullLift,
    ``LowEnergy.GaussComposite.ActualEMDressedSchur.sourceCokernel,
    ``LowEnergy.GaussComposite.ActualDressedNullNative.originalNullColumn,
    ``LowEnergy.GaussComposite.ActualDressedPencil.dressedWindowPolarization,
    ``LowEnergy.GaussComposite.ActualEMDressedSchur.anchorSchur,
    ``LowEnergy.SourcePropagationNoetherTime.noetherHistoryOperatorJet]
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
  if let some path ← liftIO (IO.getEnv "ALPHA_DRESSED_CONSTRAINT_WARD_UNION_AUDIT_OUTPUT") then
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
  logInfo m!"DRESSED_CONSTRAINT_WARD_UNION_PASS public={mouths.size} owned={owned.length} tests={tests.size} nodes={all.size} anchors={anchors.size} direct={direct.size} opaque_all_read={opaques} axioms={axioms} unknown=0 unsafe=0 partial=0"
#audit_dressed_constraint_ward_union
#print axioms LowEnergy.GaussComposite.ActualDressedNullNative.original_null_column_literal
#print axioms LowEnergy.GaussComposite.ActualDressedNullNative.original_null_cokernel
#print axioms LowEnergy.GaussComposite.ActualDressedNullNative.original_null_lift_single
#print axioms LowEnergy.GaussComposite.ActualDressedConstraintWard.source_cokernel_actual_pencil
#print axioms LowEnergy.GaussComposite.ActualDressedConstraintWard.dressed_complex_reader_actual
#print axioms LowEnergy.GaussComposite.ActualDressedConstraintWard.dressed_quantum_reader_actual
#print axioms LowEnergy.GaussComposite.ActualDressedConstraintWard.source_constraint_quantum_history
#print axioms LowEnergy.GaussComposite.ActualDressedConstraintWard.source_constraint_nonlinear_history
#print axioms LowEnergy.GaussComposite.ActualDressedConstraintWard.source_constraint_schur_history
