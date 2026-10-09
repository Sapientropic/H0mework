import H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualDressedNoetherBackground
import H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualDressedNoetherHalfIntegral
import H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualDressedNonlinearHalfResponse
import H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualDressedNonlinearPolarization

import Lean.Elab.Command
import Lean.Util.FoldConsts
import Lean.Util.CollectAxioms
set_option autoImplicit false
set_option maxHeartbeats 12000000
set_option maxRecDepth 32768
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.GaussComposite.ActualDressedNonlinearHalfAudit
elab "checked_noether_background_initial_sourceContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualDressedNonlinearHalf.noether_background_initial_source).type
theorem checked_noether_background_initial_source : checked_noether_background_initial_sourceContract := @LowEnergy.GaussComposite.ActualDressedNonlinearHalf.noether_background_initial_source

elab "checked_noether_background_initial_C2Contract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualDressedNonlinearHalf.noether_background_initial_C2).type
theorem checked_noether_background_initial_C2 : checked_noether_background_initial_C2Contract := @LowEnergy.GaussComposite.ActualDressedNonlinearHalf.noether_background_initial_C2

elab "checked_noether_background_initial_derivativeContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualDressedNonlinearHalf.noether_background_initial_derivative).type
theorem checked_noether_background_initial_derivative : checked_noether_background_initial_derivativeContract := @LowEnergy.GaussComposite.ActualDressedNonlinearHalf.noether_background_initial_derivative

elab "checked_noether_background_operator_C2Contract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualDressedNonlinearHalf.noether_background_operator_C2).type
theorem checked_noether_background_operator_C2 : checked_noether_background_operator_C2Contract := @LowEnergy.GaussComposite.ActualDressedNonlinearHalf.noether_background_operator_C2

elab "checked_noether_background_operator_sourceContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualDressedNonlinearHalf.noether_background_operator_source).type
theorem checked_noether_background_operator_source : checked_noether_background_operator_sourceContract := @LowEnergy.GaussComposite.ActualDressedNonlinearHalf.noether_background_operator_source

elab "checked_noether_background_operator_pencilContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualDressedNonlinearHalf.noether_background_operator_pencil).type
theorem checked_noether_background_operator_pencil : checked_noether_background_operator_pencilContract := @LowEnergy.GaussComposite.ActualDressedNonlinearHalf.noether_background_operator_pencil

elab "checked_noether_background_operator_derivativeContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualDressedNonlinearHalf.noether_background_operator_derivative).type
theorem checked_noether_background_operator_derivative : checked_noether_background_operator_derivativeContract := @LowEnergy.GaussComposite.ActualDressedNonlinearHalf.noether_background_operator_derivative

elab "checked_noether_nonlinear_kernel_actualContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualDressedNonlinearHalf.noether_nonlinear_kernel_actual).type
theorem checked_noether_nonlinear_kernel_actual : checked_noether_nonlinear_kernel_actualContract := @LowEnergy.GaussComposite.ActualDressedNonlinearHalf.noether_nonlinear_kernel_actual

elab "checked_noether_nonlinear_half_integrableContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualDressedNonlinearHalf.noether_nonlinear_half_integrable).type
theorem checked_noether_nonlinear_half_integrable : checked_noether_nonlinear_half_integrableContract := @LowEnergy.GaussComposite.ActualDressedNonlinearHalf.noether_nonlinear_half_integrable

elab "checked_noether_nonlinear_half_backgroundContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualDressedNonlinearHalf.noether_nonlinear_half_background).type
theorem checked_noether_nonlinear_half_background : checked_noether_nonlinear_half_backgroundContract := @LowEnergy.GaussComposite.ActualDressedNonlinearHalf.noether_nonlinear_half_background

elab "checked_noether_nonlinear_half_C2Contract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualDressedNonlinearHalf.noether_nonlinear_half_C2).type
theorem checked_noether_nonlinear_half_C2 : checked_noether_nonlinear_half_C2Contract := @LowEnergy.GaussComposite.ActualDressedNonlinearHalf.noether_nonlinear_half_C2

elab "checked_noether_nonlinear_half_derivativeContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualDressedNonlinearHalf.noether_nonlinear_half_derivative).type
theorem checked_noether_nonlinear_half_derivative : checked_noether_nonlinear_half_derivativeContract := @LowEnergy.GaussComposite.ActualDressedNonlinearHalf.noether_nonlinear_half_derivative

elab "checked_noether_nonlinear_weighted_priceContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualDressedNonlinearHalf.noether_nonlinear_weighted_price).type
theorem checked_noether_nonlinear_weighted_price : checked_noether_nonlinear_weighted_priceContract := @LowEnergy.GaussComposite.ActualDressedNonlinearHalf.noether_nonlinear_weighted_price

elab "checked_noether_nonlinear_half_tailContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualDressedNonlinearHalf.noether_nonlinear_half_tail).type
theorem checked_noether_nonlinear_half_tail : checked_noether_nonlinear_half_tailContract := @LowEnergy.GaussComposite.ActualDressedNonlinearHalf.noether_nonlinear_half_tail

elab "checked_dressed_noether_half_integrableContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualDressedNonlinearHalf.dressed_noether_half_integrable).type
theorem checked_dressed_noether_half_integrable : checked_dressed_noether_half_integrableContract := @LowEnergy.GaussComposite.ActualDressedNonlinearHalf.dressed_noether_half_integrable

elab "checked_dressed_noether_half_readContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualDressedNonlinearHalf.dressed_noether_half_read).type
theorem checked_dressed_noether_half_read : checked_dressed_noether_half_readContract := @LowEnergy.GaussComposite.ActualDressedNonlinearHalf.dressed_noether_half_read

elab "checked_dressed_noether_window_readContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualDressedNonlinearHalf.dressed_noether_window_read).type
theorem checked_dressed_noether_window_read : checked_dressed_noether_window_readContract := @LowEnergy.GaussComposite.ActualDressedNonlinearHalf.dressed_noether_window_read

elab "checked_dressed_noether_half_backgroundContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualDressedNonlinearHalf.dressed_noether_half_background).type
theorem checked_dressed_noether_half_background : checked_dressed_noether_half_backgroundContract := @LowEnergy.GaussComposite.ActualDressedNonlinearHalf.dressed_noether_half_background

elab "checked_dressed_noether_half_C2Contract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualDressedNonlinearHalf.dressed_noether_half_C2).type
theorem checked_dressed_noether_half_C2 : checked_dressed_noether_half_C2Contract := @LowEnergy.GaussComposite.ActualDressedNonlinearHalf.dressed_noether_half_C2

elab "checked_dressed_noether_half_derivativeContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualDressedNonlinearHalf.dressed_noether_half_derivative).type
theorem checked_dressed_noether_half_derivative : checked_dressed_noether_half_derivativeContract := @LowEnergy.GaussComposite.ActualDressedNonlinearHalf.dressed_noether_half_derivative

elab "checked_dressed_noether_half_column_derivativeContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualDressedNonlinearHalf.dressed_noether_half_column_derivative).type
theorem checked_dressed_noether_half_column_derivative : checked_dressed_noether_half_column_derivativeContract := @LowEnergy.GaussComposite.ActualDressedNonlinearHalf.dressed_noether_half_column_derivative

elab "checked_dressed_noether_half_tailContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualDressedNonlinearHalf.dressed_noether_half_tail).type
theorem checked_dressed_noether_half_tail : checked_dressed_noether_half_tailContract := @LowEnergy.GaussComposite.ActualDressedNonlinearHalf.dressed_noether_half_tail

elab "checked_dressed_noether_half_fderivContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualDressedNonlinearHalf.dressed_noether_half_fderiv).type
theorem checked_dressed_noether_half_fderiv : checked_dressed_noether_half_fderivContract := @LowEnergy.GaussComposite.ActualDressedNonlinearHalf.dressed_noether_half_fderiv

elab "checked_dressed_noether_half_full_derivativeContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualDressedNonlinearHalf.dressed_noether_half_full_derivative).type
theorem checked_dressed_noether_half_full_derivative : checked_dressed_noether_half_full_derivativeContract := @LowEnergy.GaussComposite.ActualDressedNonlinearHalf.dressed_noether_half_full_derivative

elab "checked_dressed_normalized_noether_derivativeContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualDressedNonlinearHalf.dressed_normalized_noether_derivative).type
theorem checked_dressed_normalized_noether_derivative : checked_dressed_normalized_noether_derivativeContract := @LowEnergy.GaussComposite.ActualDressedNonlinearHalf.dressed_normalized_noether_derivative

open CanonicalGradedSpatialSource PreparationVacuumMixedFieldReturn PreparationVacuumPhysicalFeedback
open PreparationVacuumGaugeSourceInjection PreparationVacuumActionFieldLift
open ActualDressedFullCoulomb ActualDressedNoether ActualDressedSylvester ActualDressedStaticResponse ActualDressedNonlinearHalf
open Filter
open scoped Topology Matrix

theorem checked_actual_event_nonempty : Nonempty DressedEvent := by
  exact ⟨{
    epsilon:=1
    precision:=by norm_num
    momentum:=0
    frame:=Classical.choice inferInstance
    cut:=0
    energy:=Complex.I
    nonreal:=by simp}⟩

/-- The actual nonlinear halfline has a source-generated common field neighborhood. -/
theorem checked_actual_half_common_neighborhood (event : DressedEvent) :
    ∃radius : ℝ,0<radius ∧ ∀h : Field289,‖h‖<radius→
      dressedNoetherHalfSource event 0 1 h=dressedNoetherBackgroundSource event 0 1 h := by
  have source:=dressed_noether_half_background event 0 1 (by norm_num)
  obtain ⟨radius,positive,inside⟩:=Metric.mem_nhds_iff.mp source
  refine ⟨radius,positive,fun h bound=>inside ?_⟩
  simpa only [Metric.mem_ball,dist_zero_right] using bound

/-- A nonzero original field slot is consumed at an independent positive observation clock. -/
theorem checked_actual_normalized_field_direction (event : DressedEvent) :
    HasDerivAt (fun r : ℝ=>dressedNormalizedNoetherSource event 0 2 (r • fieldUnit 20))
      (staticQuantumCorrection event 0 2*ᵥ(fun j=>(fieldUnit 20 j:ℂ))) 0 :=
  dressed_normalized_noether_derivative event 0 2 (by norm_num) (fieldUnit 20)

end LowEnergy.GaussComposite.ActualDressedNonlinearHalfAudit

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

elab "#audit_dressed_nonlinear_half" : command => do
  let env ← getEnv
  let modules := env.header.moduleNames
  let owner := fun name => (env.getModuleIdxFor? name).map fun i => modules[i.toNat]!
  let candidates := #[`H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualDressedNoetherBackground,`H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualDressedNoetherHalfIntegral,`H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualDressedNonlinearHalfResponse,`H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualDressedNonlinearPolarization]
  let owned := env.constants.toList.filterMap fun (name, _) =>
    if (owner name).any candidates.contains then some name else none
  let mouths := #[
    ``LowEnergy.GaussComposite.ActualDressedNonlinearHalf.noetherBackgroundInitial,
    ``LowEnergy.GaussComposite.ActualDressedNonlinearHalf.noether_background_initial_source,
    ``LowEnergy.GaussComposite.ActualDressedNonlinearHalf.noether_background_initial_C2,
    ``LowEnergy.GaussComposite.ActualDressedNonlinearHalf.noether_background_initial_derivative,
    ``LowEnergy.GaussComposite.ActualDressedNonlinearHalf.noetherBackgroundOperator,
    ``LowEnergy.GaussComposite.ActualDressedNonlinearHalf.noether_background_operator_C2,
    ``LowEnergy.GaussComposite.ActualDressedNonlinearHalf.noether_background_operator_source,
    ``LowEnergy.GaussComposite.ActualDressedNonlinearHalf.noether_background_operator_pencil,
    ``LowEnergy.GaussComposite.ActualDressedNonlinearHalf.noether_background_operator_derivative,
    ``LowEnergy.GaussComposite.ActualDressedNonlinearHalf.noetherNonlinearHalf,
    ``LowEnergy.GaussComposite.ActualDressedNonlinearHalf.noetherNonlinearWindow,
    ``LowEnergy.GaussComposite.ActualDressedNonlinearHalf.noether_nonlinear_kernel_actual,
    ``LowEnergy.GaussComposite.ActualDressedNonlinearHalf.noether_nonlinear_half_integrable,
    ``LowEnergy.GaussComposite.ActualDressedNonlinearHalf.noether_nonlinear_half_background,
    ``LowEnergy.GaussComposite.ActualDressedNonlinearHalf.noether_nonlinear_half_C2,
    ``LowEnergy.GaussComposite.ActualDressedNonlinearHalf.noether_nonlinear_half_derivative,
    ``LowEnergy.GaussComposite.ActualDressedNonlinearHalf.noetherNonlinearCoefficient,
    ``LowEnergy.GaussComposite.ActualDressedNonlinearHalf.noetherNonlinearTailPrice,
    ``LowEnergy.GaussComposite.ActualDressedNonlinearHalf.noether_nonlinear_weighted_price,
    ``LowEnergy.GaussComposite.ActualDressedNonlinearHalf.noether_nonlinear_half_tail,
    ``LowEnergy.GaussComposite.ActualDressedNonlinearHalf.dressedNoetherHalfSource,
    ``LowEnergy.GaussComposite.ActualDressedNonlinearHalf.dressedNoetherWindowSource,
    ``LowEnergy.GaussComposite.ActualDressedNonlinearHalf.dressedNoetherBackgroundSource,
    ``LowEnergy.GaussComposite.ActualDressedNonlinearHalf.dressed_noether_half_integrable,
    ``LowEnergy.GaussComposite.ActualDressedNonlinearHalf.dressed_noether_half_read,
    ``LowEnergy.GaussComposite.ActualDressedNonlinearHalf.dressed_noether_window_read,
    ``LowEnergy.GaussComposite.ActualDressedNonlinearHalf.dressed_noether_half_background,
    ``LowEnergy.GaussComposite.ActualDressedNonlinearHalf.dressed_noether_half_C2,
    ``LowEnergy.GaussComposite.ActualDressedNonlinearHalf.dressed_noether_half_derivative,
    ``LowEnergy.GaussComposite.ActualDressedNonlinearHalf.dressed_noether_half_column_derivative,
    ``LowEnergy.GaussComposite.ActualDressedNonlinearHalf.dressed_noether_half_tail,
    ``LowEnergy.GaussComposite.ActualDressedNonlinearHalf.dressed_noether_half_fderiv,
    ``LowEnergy.GaussComposite.ActualDressedNonlinearHalf.dressed_noether_half_full_derivative,
    ``LowEnergy.GaussComposite.ActualDressedNonlinearHalf.dressedNormalizedNoetherSource,
    ``LowEnergy.GaussComposite.ActualDressedNonlinearHalf.dressed_normalized_noether_derivative]
  for name in mouths do
    unless owned.contains name do throwError m!"MISSING_MOUTH {name}"
  let tests := #[
    ``LowEnergy.GaussComposite.ActualDressedNonlinearHalfAudit.checked_noether_background_initial_source,
    ``LowEnergy.GaussComposite.ActualDressedNonlinearHalfAudit.checked_noether_background_initial_C2,
    ``LowEnergy.GaussComposite.ActualDressedNonlinearHalfAudit.checked_noether_background_initial_derivative,
    ``LowEnergy.GaussComposite.ActualDressedNonlinearHalfAudit.checked_noether_background_operator_C2,
    ``LowEnergy.GaussComposite.ActualDressedNonlinearHalfAudit.checked_noether_background_operator_source,
    ``LowEnergy.GaussComposite.ActualDressedNonlinearHalfAudit.checked_noether_background_operator_pencil,
    ``LowEnergy.GaussComposite.ActualDressedNonlinearHalfAudit.checked_noether_background_operator_derivative,
    ``LowEnergy.GaussComposite.ActualDressedNonlinearHalfAudit.checked_noether_nonlinear_kernel_actual,
    ``LowEnergy.GaussComposite.ActualDressedNonlinearHalfAudit.checked_noether_nonlinear_half_integrable,
    ``LowEnergy.GaussComposite.ActualDressedNonlinearHalfAudit.checked_noether_nonlinear_half_background,
    ``LowEnergy.GaussComposite.ActualDressedNonlinearHalfAudit.checked_noether_nonlinear_half_C2,
    ``LowEnergy.GaussComposite.ActualDressedNonlinearHalfAudit.checked_noether_nonlinear_half_derivative,
    ``LowEnergy.GaussComposite.ActualDressedNonlinearHalfAudit.checked_noether_nonlinear_weighted_price,
    ``LowEnergy.GaussComposite.ActualDressedNonlinearHalfAudit.checked_noether_nonlinear_half_tail,
    ``LowEnergy.GaussComposite.ActualDressedNonlinearHalfAudit.checked_dressed_noether_half_integrable,
    ``LowEnergy.GaussComposite.ActualDressedNonlinearHalfAudit.checked_dressed_noether_half_read,
    ``LowEnergy.GaussComposite.ActualDressedNonlinearHalfAudit.checked_dressed_noether_window_read,
    ``LowEnergy.GaussComposite.ActualDressedNonlinearHalfAudit.checked_dressed_noether_half_background,
    ``LowEnergy.GaussComposite.ActualDressedNonlinearHalfAudit.checked_dressed_noether_half_C2,
    ``LowEnergy.GaussComposite.ActualDressedNonlinearHalfAudit.checked_dressed_noether_half_derivative,
    ``LowEnergy.GaussComposite.ActualDressedNonlinearHalfAudit.checked_dressed_noether_half_column_derivative,
    ``LowEnergy.GaussComposite.ActualDressedNonlinearHalfAudit.checked_dressed_noether_half_tail,
    ``LowEnergy.GaussComposite.ActualDressedNonlinearHalfAudit.checked_dressed_noether_half_fderiv,
    ``LowEnergy.GaussComposite.ActualDressedNonlinearHalfAudit.checked_dressed_noether_half_full_derivative,
    ``LowEnergy.GaussComposite.ActualDressedNonlinearHalfAudit.checked_dressed_normalized_noether_derivative,
    ``LowEnergy.GaussComposite.ActualDressedNonlinearHalfAudit.checked_actual_event_nonempty,
    ``LowEnergy.GaussComposite.ActualDressedNonlinearHalfAudit.checked_actual_half_common_neighborhood,
    ``LowEnergy.GaussComposite.ActualDressedNonlinearHalfAudit.checked_actual_normalized_field_direction]
  let direct := #[
    (``LowEnergy.GaussComposite.ActualDressedNonlinearHalf.noether_background_initial_derivative,#[
    ``LowEnergy.GaussComposite.ActualDressedSylvester.noetherStaticContact,
    ``LowEnergy.PreparationVacuumNoetherChart.noetherReader_generated]),
    (``LowEnergy.GaussComposite.ActualDressedNonlinearHalf.noether_background_operator_C2,#[
    ``LowEnergy.SourcePropagationFieldFeedback.fieldInverse_C2,
    ``LowEnergy.GaussComposite.ActualDressedNonlinearHalf.noether_background_initial_C2]),
    (``LowEnergy.GaussComposite.ActualDressedNonlinearHalf.noether_background_operator_source,#[
    ``LowEnergy.SourcePropagationFieldFeedback.fieldInverse_initial,
    ``LowEnergy.SourcePropagationResolvent.rawHalf_true_inverse]),
    (``LowEnergy.GaussComposite.ActualDressedNonlinearHalf.noether_background_operator_pencil,#[
    ``LowEnergy.SourcePropagationFieldFeedback.fieldInverse_left_generated]),
    (``LowEnergy.GaussComposite.ActualDressedNonlinearHalf.noether_background_operator_derivative,#[
    ``LowEnergy.SourcePropagationFieldFeedback.fieldInverse_ray_derivative,
    ``LowEnergy.GaussComposite.ActualDressedNonlinearHalf.noether_background_initial_derivative,
    ``LowEnergy.GaussComposite.ActualDressedSylvester.noether_static_half_inverse]),
    (``LowEnergy.GaussComposite.ActualDressedNonlinearHalf.noether_nonlinear_kernel_actual,#[
    ``LowEnergy.GaussComposite.ActualDressedNonlinearHalf.noetherBackgroundInitial,
    ``LowEnergy.GaussComposite.ActualDressedNoether.dressedNoetherKernel,
    ``LowEnergy.SourcePropagationNearFieldTime.physicalBackgroundMap]),
    (``LowEnergy.GaussComposite.ActualDressedNonlinearHalf.noether_nonlinear_half_integrable,#[
    ``LowEnergy.SourcePropagationNearFieldTime.physicalBackgroundMap_integrable]),
    (``LowEnergy.GaussComposite.ActualDressedNonlinearHalf.noether_nonlinear_half_background,#[
    ``LowEnergy.SourcePropagationNearFieldTime.timeDomain_source_near,
    ``LowEnergy.SourcePropagationNearFieldTime.nearTimeHalf_inverse_generated,
    ``LowEnergy.SourcePropagationNearFieldTime.physicalBackgroundMap_integrable]),
    (``LowEnergy.GaussComposite.ActualDressedNonlinearHalf.noether_nonlinear_half_C2,#[
    ``LowEnergy.GaussComposite.ActualDressedNonlinearHalf.noether_background_operator_C2,
    ``LowEnergy.GaussComposite.ActualDressedNonlinearHalf.noether_nonlinear_half_background]),
    (``LowEnergy.GaussComposite.ActualDressedNonlinearHalf.noether_nonlinear_half_derivative,#[
    ``LowEnergy.GaussComposite.ActualDressedNonlinearHalf.noether_background_operator_derivative,
    ``LowEnergy.GaussComposite.ActualDressedNonlinearHalf.noether_nonlinear_half_background]),
    (``LowEnergy.GaussComposite.ActualDressedNonlinearHalf.noether_nonlinear_weighted_price,#[
    ``LowEnergy.SourcePropagationNearFieldTime.physicalBackgroundMap_damped_bound]),
    (``LowEnergy.GaussComposite.ActualDressedNonlinearHalf.noether_nonlinear_half_tail,#[
    ``LowEnergy.GaussComposite.ActualDressedNonlinearHalf.noether_nonlinear_half_integrable,
    ``LowEnergy.GaussComposite.ActualDressedNonlinearHalf.noether_nonlinear_weighted_price]),
    (``LowEnergy.GaussComposite.ActualDressedNonlinearHalf.dressed_noether_half_read,#[
    ``LowEnergy.GaussComposite.ActualDressedNonlinearHalf.noether_nonlinear_half_integrable,
    ``LowEnergy.GaussComposite.ActualDressedNonlinearHalf.noether_nonlinear_kernel_actual]),
    (``LowEnergy.GaussComposite.ActualDressedNonlinearHalf.dressed_noether_half_background,#[
    ``LowEnergy.GaussComposite.ActualDressedNonlinearHalf.dressed_noether_half_read,
    ``LowEnergy.GaussComposite.ActualDressedNonlinearHalf.noether_nonlinear_half_background,
    ``LowEnergy.SourcePropagationNearFieldTime.timeDomain_source_near]),
    (``LowEnergy.GaussComposite.ActualDressedNonlinearHalf.dressed_noether_half_C2,#[
    ``LowEnergy.GaussComposite.ActualDressedNonlinearHalf.noether_background_operator_C2,
    ``LowEnergy.GaussComposite.ActualDressedNonlinearHalf.dressed_noether_half_background]),
    (``LowEnergy.GaussComposite.ActualDressedNonlinearHalf.dressed_noether_half_derivative,#[
    ``LowEnergy.GaussComposite.ActualDressedNonlinearHalf.noether_background_operator_derivative,
    ``LowEnergy.GaussComposite.ActualDressedNonlinearHalf.dressed_noether_half_background]),
    (``LowEnergy.GaussComposite.ActualDressedNonlinearHalf.dressed_noether_half_column_derivative,#[
    ``LowEnergy.GaussComposite.ActualDressedNonlinearHalf.dressed_noether_half_derivative,
    ``LowEnergy.GaussComposite.ActualDressedSylvester.dressedStaticPolarization]),
    (``LowEnergy.GaussComposite.ActualDressedNonlinearHalf.dressed_noether_half_tail,#[
    ``LowEnergy.GaussComposite.ActualDressedNonlinearHalf.dressed_noether_half_read,
    ``LowEnergy.GaussComposite.ActualDressedNonlinearHalf.dressed_noether_window_read,
    ``LowEnergy.GaussComposite.ActualDressedNonlinearHalf.noether_nonlinear_half_tail,
    ``LowEnergy.GaussComposite.ActualDressedSignal.dressed_euler_observer_price]),
    (``LowEnergy.GaussComposite.ActualDressedNonlinearHalf.dressed_noether_half_fderiv,#[
    ``LowEnergy.GaussComposite.ActualDressedNonlinearHalf.dressed_noether_half_C2,
    ``LowEnergy.GaussComposite.ActualDressedNonlinearHalf.dressed_noether_half_column_derivative]),
    (``LowEnergy.GaussComposite.ActualDressedNonlinearHalf.dressed_noether_half_full_derivative,#[
    ``LowEnergy.GaussComposite.ActualDressedNonlinearHalf.dressed_noether_half_fderiv,
    ``LowEnergy.GaussComposite.ActualDressedNonlinearHalf.dressed_noether_half_C2]),
    (``LowEnergy.GaussComposite.ActualDressedNonlinearHalf.dressed_normalized_noether_derivative,#[
    ``LowEnergy.GaussComposite.ActualDressedNonlinearHalf.dressed_noether_half_full_derivative,
    ``LowEnergy.GaussComposite.ActualDressedNonlinearHalf.dressedNormalizedNoetherSource,
    ``LowEnergy.GaussComposite.ActualDressedStaticResponse.staticQuantumCorrection])]
  for (mouth,required) in direct do packageCertRequire env mouth required
  let testProducers := #[
    ``LowEnergy.GaussComposite.ActualDressedNonlinearHalf.noether_background_initial_source,
    ``LowEnergy.GaussComposite.ActualDressedNonlinearHalf.noether_background_initial_C2,
    ``LowEnergy.GaussComposite.ActualDressedNonlinearHalf.noether_background_initial_derivative,
    ``LowEnergy.GaussComposite.ActualDressedNonlinearHalf.noether_background_operator_C2,
    ``LowEnergy.GaussComposite.ActualDressedNonlinearHalf.noether_background_operator_source,
    ``LowEnergy.GaussComposite.ActualDressedNonlinearHalf.noether_background_operator_pencil,
    ``LowEnergy.GaussComposite.ActualDressedNonlinearHalf.noether_background_operator_derivative,
    ``LowEnergy.GaussComposite.ActualDressedNonlinearHalf.noether_nonlinear_kernel_actual,
    ``LowEnergy.GaussComposite.ActualDressedNonlinearHalf.noether_nonlinear_half_integrable,
    ``LowEnergy.GaussComposite.ActualDressedNonlinearHalf.noether_nonlinear_half_background,
    ``LowEnergy.GaussComposite.ActualDressedNonlinearHalf.noether_nonlinear_half_C2,
    ``LowEnergy.GaussComposite.ActualDressedNonlinearHalf.noether_nonlinear_half_derivative,
    ``LowEnergy.GaussComposite.ActualDressedNonlinearHalf.noether_nonlinear_weighted_price,
    ``LowEnergy.GaussComposite.ActualDressedNonlinearHalf.noether_nonlinear_half_tail,
    ``LowEnergy.GaussComposite.ActualDressedNonlinearHalf.dressed_noether_half_integrable,
    ``LowEnergy.GaussComposite.ActualDressedNonlinearHalf.dressed_noether_half_read,
    ``LowEnergy.GaussComposite.ActualDressedNonlinearHalf.dressed_noether_window_read,
    ``LowEnergy.GaussComposite.ActualDressedNonlinearHalf.dressed_noether_half_background,
    ``LowEnergy.GaussComposite.ActualDressedNonlinearHalf.dressed_noether_half_C2,
    ``LowEnergy.GaussComposite.ActualDressedNonlinearHalf.dressed_noether_half_derivative,
    ``LowEnergy.GaussComposite.ActualDressedNonlinearHalf.dressed_noether_half_column_derivative,
    ``LowEnergy.GaussComposite.ActualDressedNonlinearHalf.dressed_noether_half_tail,
    ``LowEnergy.GaussComposite.ActualDressedNonlinearHalf.dressed_noether_half_fderiv,
    ``LowEnergy.GaussComposite.ActualDressedNonlinearHalf.dressed_noether_half_full_derivative,
    ``LowEnergy.GaussComposite.ActualDressedNonlinearHalf.dressed_normalized_noether_derivative]
  for i in [:testProducers.size] do packageCertRequire env tests[i]! #[testProducers[i]!]
  let all ← packageCertClosure env (owned ++ tests.toList)
  let anchors := #[
    ``SaturationMonoid.PhysicsCore.StageNineEnrichedProofFreeSource.positiveSmoothUnifiedSource,
    ``SaturationMonoid.PhysicsCore.Stage9C.Material.SpinPair.actual,
    ``LowEnergy.GaussComposite.ActualDressedSourcePreparation.sourceDressedUnit,
    ``LowEnergy.PreparationVacuumSourcePreparedResponse.sourceProfile,
    ``LowEnergy.GaussComposite.ActualDressedNoether.dressedEulerObserver,
    ``LowEnergy.GaussComposite.ActualDressedNoether.dressedNoetherKernel,
    ``LowEnergy.SourcePropagationFieldFeedback.fieldInverse,
    ``LowEnergy.SourcePropagationNearFieldTime.physicalBackgroundMap,
    ``LowEnergy.SourcePropagationNearFieldTime.timeDomain,
    ``LowEnergy.GaussComposite.ActualDressedSylvester.noetherStaticContact,
    ``LowEnergy.PreparationVacuumNoetherChart.noetherReader,
    ``LowEnergy.PreparationVacuumJointFieldResponse.jointResolvent,
    ``LowEnergy.GaussComposite.ActualDressedSylvester.dressedStaticPolarization,
    ``LowEnergy.GaussComposite.ActualDressedStaticResponse.staticInputNormalizer]
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
  if let some path ← liftIO (IO.getEnv "ALPHA_DRESSED_NONLINEAR_HALF_AUDIT_OUTPUT") then
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
  logInfo m!"DRESSED_NONLINEAR_HALF_PASS public={mouths.size} owned={owned.length} tests={tests.size} nodes={all.size} anchors={anchors.size} direct={direct.size} opaque_all_read={opaques} axioms={axioms} unknown=0 unsafe=0 partial=0"
#audit_dressed_nonlinear_half
#print axioms LowEnergy.GaussComposite.ActualDressedNonlinearHalf.noether_background_initial_source
#print axioms LowEnergy.GaussComposite.ActualDressedNonlinearHalf.noether_background_initial_C2
#print axioms LowEnergy.GaussComposite.ActualDressedNonlinearHalf.noether_background_initial_derivative
#print axioms LowEnergy.GaussComposite.ActualDressedNonlinearHalf.noether_background_operator_C2
#print axioms LowEnergy.GaussComposite.ActualDressedNonlinearHalf.noether_background_operator_source
#print axioms LowEnergy.GaussComposite.ActualDressedNonlinearHalf.noether_background_operator_pencil
#print axioms LowEnergy.GaussComposite.ActualDressedNonlinearHalf.noether_background_operator_derivative
#print axioms LowEnergy.GaussComposite.ActualDressedNonlinearHalf.noether_nonlinear_kernel_actual
#print axioms LowEnergy.GaussComposite.ActualDressedNonlinearHalf.noether_nonlinear_half_integrable
#print axioms LowEnergy.GaussComposite.ActualDressedNonlinearHalf.noether_nonlinear_half_background
#print axioms LowEnergy.GaussComposite.ActualDressedNonlinearHalf.noether_nonlinear_half_C2
#print axioms LowEnergy.GaussComposite.ActualDressedNonlinearHalf.noether_nonlinear_half_derivative
#print axioms LowEnergy.GaussComposite.ActualDressedNonlinearHalf.noether_nonlinear_weighted_price
#print axioms LowEnergy.GaussComposite.ActualDressedNonlinearHalf.noether_nonlinear_half_tail
#print axioms LowEnergy.GaussComposite.ActualDressedNonlinearHalf.dressed_noether_half_integrable
#print axioms LowEnergy.GaussComposite.ActualDressedNonlinearHalf.dressed_noether_half_read
#print axioms LowEnergy.GaussComposite.ActualDressedNonlinearHalf.dressed_noether_window_read
#print axioms LowEnergy.GaussComposite.ActualDressedNonlinearHalf.dressed_noether_half_background
#print axioms LowEnergy.GaussComposite.ActualDressedNonlinearHalf.dressed_noether_half_C2
#print axioms LowEnergy.GaussComposite.ActualDressedNonlinearHalf.dressed_noether_half_derivative
#print axioms LowEnergy.GaussComposite.ActualDressedNonlinearHalf.dressed_noether_half_column_derivative
#print axioms LowEnergy.GaussComposite.ActualDressedNonlinearHalf.dressed_noether_half_tail
#print axioms LowEnergy.GaussComposite.ActualDressedNonlinearHalf.dressed_noether_half_fderiv
#print axioms LowEnergy.GaussComposite.ActualDressedNonlinearHalf.dressed_noether_half_full_derivative
#print axioms LowEnergy.GaussComposite.ActualDressedNonlinearHalf.dressed_normalized_noether_derivative
