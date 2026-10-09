import H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualDressedFieldTimeFull
import H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualDressedFieldTimeSector
import H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualDressedFieldTimeConsumer

import Lean.Elab.Command
import Lean.Util.FoldConsts
import Lean.Util.CollectAxioms
set_option autoImplicit false
set_option maxHeartbeats 12000000
set_option maxRecDepth 32768
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.GaussComposite.ActualDressedFieldTimeAudit
elab "checked_actual_field_C_gradeContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualDressedFieldTime.actual_field_C_grade).type
theorem checked_actual_field_C_grade : checked_actual_field_C_gradeContract := @LowEnergy.GaussComposite.ActualDressedFieldTime.actual_field_C_grade

elab "checked_actual_field_generator_sourceContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualDressedFieldTime.actual_field_generator_source).type
theorem checked_actual_field_generator_source : checked_actual_field_generator_sourceContract := @LowEnergy.GaussComposite.ActualDressedFieldTime.actual_field_generator_source

elab "checked_actual_field_prefix_terminalContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualDressedFieldTime.actual_field_prefix_terminal).type
theorem checked_actual_field_prefix_terminal : checked_actual_field_prefix_terminalContract := @LowEnergy.GaussComposite.ActualDressedFieldTime.actual_field_prefix_terminal

elab "checked_actual_field_prefix_derivativeContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualDressedFieldTime.actual_field_prefix_derivative).type
theorem checked_actual_field_prefix_derivative : checked_actual_field_prefix_derivativeContract := @LowEnergy.GaussComposite.ActualDressedFieldTime.actual_field_prefix_derivative

elab "checked_actual_field_time_finitePrefixContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualDressedFieldTime.actual_field_time_finitePrefix).type
theorem checked_actual_field_time_finitePrefix : checked_actual_field_time_finitePrefixContract := @LowEnergy.GaussComposite.ActualDressedFieldTime.actual_field_time_finitePrefix

elab "checked_actual_field_interaction_N2G0_rangeContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualDressedFieldTime.actual_field_interaction_N2G0_range).type
theorem checked_actual_field_interaction_N2G0_range : checked_actual_field_interaction_N2G0_rangeContract := @LowEnergy.GaussComposite.ActualDressedFieldTime.actual_field_interaction_N2G0_range

elab "checked_actual_field_interaction_N2G1_rangeContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualDressedFieldTime.actual_field_interaction_N2G1_range).type
theorem checked_actual_field_interaction_N2G1_range : checked_actual_field_interaction_N2G1_rangeContract := @LowEnergy.GaussComposite.ActualDressedFieldTime.actual_field_interaction_N2G1_range

elab "checked_actual_field_interaction_N2G2_zeroContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualDressedFieldTime.actual_field_interaction_N2G2_zero).type
theorem checked_actual_field_interaction_N2G2_zero : checked_actual_field_interaction_N2G2_zeroContract := @LowEnergy.GaussComposite.ActualDressedFieldTime.actual_field_interaction_N2G2_zero

elab "checked_actual_field_ordered_N2G2_zeroContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualDressedFieldTime.actual_field_ordered_N2G2_zero).type
theorem checked_actual_field_ordered_N2G2_zero : checked_actual_field_ordered_N2G2_zeroContract := @LowEnergy.GaussComposite.ActualDressedFieldTime.actual_field_ordered_N2G2_zero

elab "checked_actual_field_ordered_N2G1_high_zeroContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualDressedFieldTime.actual_field_ordered_N2G1_high_zero).type
theorem checked_actual_field_ordered_N2G1_high_zero : checked_actual_field_ordered_N2G1_high_zeroContract := @LowEnergy.GaussComposite.ActualDressedFieldTime.actual_field_ordered_N2G1_high_zero

elab "checked_actual_field_ordered_N2G0_high_zeroContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualDressedFieldTime.actual_field_ordered_N2G0_high_zero).type
theorem checked_actual_field_ordered_N2G0_high_zero : checked_actual_field_ordered_N2G0_high_zeroContract := @LowEnergy.GaussComposite.ActualDressedFieldTime.actual_field_ordered_N2G0_high_zero

elab "checked_actual_field_prefix_N2_high_zeroContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualDressedFieldTime.actual_field_prefix_N2_high_zero).type
theorem checked_actual_field_prefix_N2_high_zero : checked_actual_field_prefix_N2_high_zeroContract := @LowEnergy.GaussComposite.ActualDressedFieldTime.actual_field_prefix_N2_high_zero

elab "checked_actual_field_time_N2_grade_returnContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualDressedFieldTime.actual_field_time_N2_grade_return).type
theorem checked_actual_field_time_N2_grade_return : checked_actual_field_time_N2_grade_returnContract := @LowEnergy.GaussComposite.ActualDressedFieldTime.actual_field_time_N2_grade_return

elab "checked_actual_field_time_N2_projection_returnContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualDressedFieldTime.actual_field_time_N2_projection_return).type
theorem checked_actual_field_time_N2_projection_return : checked_actual_field_time_N2_projection_returnContract := @LowEnergy.GaussComposite.ActualDressedFieldTime.actual_field_time_N2_projection_return

elab "checked_actual_field_time_created_unitContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualDressedFieldTime.actual_field_time_created_unit).type
theorem checked_actual_field_time_created_unit : checked_actual_field_time_created_unitContract := @LowEnergy.GaussComposite.ActualDressedFieldTime.actual_field_time_created_unit

elab "checked_actual_field_interaction_N1G0_rangeContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualDressedFieldTime.actual_field_interaction_N1G0_range).type
theorem checked_actual_field_interaction_N1G0_range : checked_actual_field_interaction_N1G0_rangeContract := @LowEnergy.GaussComposite.ActualDressedFieldTime.actual_field_interaction_N1G0_range

elab "checked_actual_field_interaction_N1G1_zeroContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualDressedFieldTime.actual_field_interaction_N1G1_zero).type
theorem checked_actual_field_interaction_N1G1_zero : checked_actual_field_interaction_N1G1_zeroContract := @LowEnergy.GaussComposite.ActualDressedFieldTime.actual_field_interaction_N1G1_zero

elab "checked_actual_field_ordered_N1G1_zeroContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualDressedFieldTime.actual_field_ordered_N1G1_zero).type
theorem checked_actual_field_ordered_N1G1_zero : checked_actual_field_ordered_N1G1_zeroContract := @LowEnergy.GaussComposite.ActualDressedFieldTime.actual_field_ordered_N1G1_zero

elab "checked_actual_field_ordered_N1G0_high_zeroContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualDressedFieldTime.actual_field_ordered_N1G0_high_zero).type
theorem checked_actual_field_ordered_N1G0_high_zero : checked_actual_field_ordered_N1G0_high_zeroContract := @LowEnergy.GaussComposite.ActualDressedFieldTime.actual_field_ordered_N1G0_high_zero

elab "checked_actual_field_prefix_N1G0_high_zeroContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualDressedFieldTime.actual_field_prefix_N1G0_high_zero).type
theorem checked_actual_field_prefix_N1G0_high_zero : checked_actual_field_prefix_N1G0_high_zeroContract := @LowEnergy.GaussComposite.ActualDressedFieldTime.actual_field_prefix_N1G0_high_zero

elab "checked_actual_field_prefix_N1G1_high_zeroContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualDressedFieldTime.actual_field_prefix_N1G1_high_zero).type
theorem checked_actual_field_prefix_N1G1_high_zero : checked_actual_field_prefix_N1G1_high_zeroContract := @LowEnergy.GaussComposite.ActualDressedFieldTime.actual_field_prefix_N1G1_high_zero

elab "checked_actual_field_prefix_N1_high_zeroContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualDressedFieldTime.actual_field_prefix_N1_high_zero).type
theorem checked_actual_field_prefix_N1_high_zero : checked_actual_field_prefix_N1_high_zeroContract := @LowEnergy.GaussComposite.ActualDressedFieldTime.actual_field_prefix_N1_high_zero

elab "checked_actual_field_time_N1_projection_returnContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualDressedFieldTime.actual_field_time_N1_projection_return).type
theorem checked_actual_field_time_N1_projection_return : checked_actual_field_time_N1_projection_returnContract := @LowEnergy.GaussComposite.ActualDressedFieldTime.actual_field_time_N1_projection_return

elab "checked_actual_field_time_backgroundContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualDressedFieldTime.actual_field_time_background).type
theorem checked_actual_field_time_background : checked_actual_field_time_backgroundContract := @LowEnergy.GaussComposite.ActualDressedFieldTime.actual_field_time_background

elab "checked_actual_finite_number_field_readContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualDressedFieldTime.actual_finite_number_field_read).type
theorem checked_actual_finite_number_field_read : checked_actual_finite_number_field_readContract := @LowEnergy.GaussComposite.ActualDressedFieldTime.actual_finite_number_field_read

elab "checked_actual_finite_noether_field_germContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualDressedFieldTime.actual_finite_noether_field_germ).type
theorem checked_actual_finite_noether_field_germ : checked_actual_finite_noether_field_germContract := @LowEnergy.GaussComposite.ActualDressedFieldTime.actual_finite_noether_field_germ

elab "checked_actual_finite_number_field_quantum_derivativeContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualDressedFieldTime.actual_finite_number_field_quantum_derivative).type
theorem checked_actual_finite_number_field_quantum_derivative : checked_actual_finite_number_field_quantum_derivativeContract := @LowEnergy.GaussComposite.ActualDressedFieldTime.actual_finite_number_field_quantum_derivative

elab "checked_actual_finite_created_time_directionContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualDressedFieldTime.actual_finite_created_time_direction).type
theorem checked_actual_finite_created_time_direction : checked_actual_finite_created_time_directionContract := @LowEnergy.GaussComposite.ActualDressedFieldTime.actual_finite_created_time_direction

elab "checked_actual_finite_background_time_directionContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualDressedFieldTime.actual_finite_background_time_direction).type
theorem checked_actual_finite_background_time_direction : checked_actual_finite_background_time_directionContract := @LowEnergy.GaussComposite.ActualDressedFieldTime.actual_finite_background_time_direction

open GaussCoreHilbert CanonicalGradedSpatialSource
open PreparationVacuumMixedFieldReturn PreparationVacuumPhysicalHalfAxis PreparationVacuumRawJointFeedback
open PreparationVacuumNoetherChart PreparationVacuumJointFieldResponse
open ActualDressedFullCoulomb ActualDressedSourcePreparation ActualDressedNoether ActualDressedNumberSector
open ActualDressedNumberZero GaussComposite.SourceGraph PreparationVacuumSourcePreparedResponse
open PreparationVacuumPhysicalN1WardCollapse FullYSourceCutoffVolterra
open scoped InnerProductSpace

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
  have norm:=source_dressed_unit_norm event.epsilon event.precision
  rw [zero,norm_zero] at norm
  exact zero_ne_one norm


open ActualDressedFieldTime Filter
open scoped Topology


theorem same_actual_field_time_carriers (p : PhysicalMomentum) (F : GaussUnitaryHistory.Index) (h : Field289) (t : ℝ) :
    physicalTime p F t h*numberTwoProjection=
      FullYSourceCutoffVolterra.partialEvolution (jointCompression p F h)
        (jointY (PreparationVacuumYukawaTransport.finiteRetainer p F) h) 2 t*numberTwoProjection ∧
    physicalTime p F t h*sourceN1Projection=
      FullYSourceCutoffVolterra.partialEvolution (jointCompression p F h)
        (jointY (PreparationVacuumYukawaTransport.finiteRetainer p F) h) 1 t*sourceN1Projection :=
  ⟨actual_field_time_N2_projection_return p F h t,actual_field_time_N1_projection_return p F h t⟩

theorem same_actual_finite_noether_zero (event : DressedEvent) (transfer : PhysicalMomentum)
    (age : ℝ) (reader : Field289) :
    dressedEulerObserver event (dressedNoetherKernel event transfer reader age 0)=
      finiteNumberFieldRead event transfer reader age 0 :=
  (actual_finite_noether_field_germ event transfer).self_of_nhds age reader

theorem same_actual_finite_quantum_response (event : DressedEvent) (transfer : PhysicalMomentum)
    (force : Field289) (age : ℝ) (i : Fin 289) :
    deriv (fun r : ℝ=>finiteNumberFieldRead event transfer
      (PreparationVacuumActionFieldLift.fieldUnit i) age (r • force)) 0=
      (dressedNoetherJet event transfer (fun _=>⟨force,0,0⟩) age i).value :=
  (actual_finite_number_field_quantum_derivative event transfer force age i).deriv
end LowEnergy.GaussComposite.ActualDressedFieldTimeAudit

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

elab "#audit_dressed_field_time" : command => do
  let env ← getEnv
  let modules := env.header.moduleNames
  let owner := fun name => (env.getModuleIdxFor? name).map fun i => modules[i.toNat]!
  let candidates := #[`H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualDressedFieldTimeFull,`H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualDressedFieldTimeSector,`H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualDressedFieldTimeConsumer]
  let owned := env.constants.toList.filterMap fun (name, _) =>
    if (owner name).any candidates.contains then some name else none
  let mouths := #[
    ``LowEnergy.GaussComposite.ActualDressedFieldTime.actual_field_C_grade,
    ``LowEnergy.GaussComposite.ActualDressedFieldTime.actual_field_generator_source,
    ``LowEnergy.GaussComposite.ActualDressedFieldTime.actual_field_prefix_terminal,
    ``LowEnergy.GaussComposite.ActualDressedFieldTime.actual_field_prefix_derivative,
    ``LowEnergy.GaussComposite.ActualDressedFieldTime.actual_field_time_finitePrefix,
    ``LowEnergy.GaussComposite.ActualDressedFieldTime.actual_field_interaction_N2G0_range,
    ``LowEnergy.GaussComposite.ActualDressedFieldTime.actual_field_interaction_N2G1_range,
    ``LowEnergy.GaussComposite.ActualDressedFieldTime.actual_field_interaction_N2G2_zero,
    ``LowEnergy.GaussComposite.ActualDressedFieldTime.actual_field_ordered_N2G2_zero,
    ``LowEnergy.GaussComposite.ActualDressedFieldTime.actual_field_ordered_N2G1_high_zero,
    ``LowEnergy.GaussComposite.ActualDressedFieldTime.actual_field_ordered_N2G0_high_zero,
    ``LowEnergy.GaussComposite.ActualDressedFieldTime.actual_field_prefix_N2_high_zero,
    ``LowEnergy.GaussComposite.ActualDressedFieldTime.actual_field_time_N2_grade_return,
    ``LowEnergy.GaussComposite.ActualDressedFieldTime.actual_field_time_N2_projection_return,
    ``LowEnergy.GaussComposite.ActualDressedFieldTime.actual_field_time_created_unit,
    ``LowEnergy.GaussComposite.ActualDressedFieldTime.actual_field_interaction_N1G0_range,
    ``LowEnergy.GaussComposite.ActualDressedFieldTime.actual_field_interaction_N1G1_zero,
    ``LowEnergy.GaussComposite.ActualDressedFieldTime.actual_field_ordered_N1G1_zero,
    ``LowEnergy.GaussComposite.ActualDressedFieldTime.actual_field_ordered_N1G0_high_zero,
    ``LowEnergy.GaussComposite.ActualDressedFieldTime.actual_field_prefix_N1G0_high_zero,
    ``LowEnergy.GaussComposite.ActualDressedFieldTime.actual_field_prefix_N1G1_high_zero,
    ``LowEnergy.GaussComposite.ActualDressedFieldTime.actual_field_prefix_N1_high_zero,
    ``LowEnergy.GaussComposite.ActualDressedFieldTime.actual_field_time_N1_projection_return,
    ``LowEnergy.GaussComposite.ActualDressedFieldTime.actual_field_time_background,
    ``LowEnergy.GaussComposite.ActualDressedFieldTime.finiteNumberFieldRead,
    ``LowEnergy.GaussComposite.ActualDressedFieldTime.actual_finite_number_field_read,
    ``LowEnergy.GaussComposite.ActualDressedFieldTime.actual_finite_noether_field_germ,
    ``LowEnergy.GaussComposite.ActualDressedFieldTime.actual_finite_number_field_quantum_derivative,
    ``LowEnergy.GaussComposite.ActualDressedFieldTime.actual_finite_created_time_direction,
    ``LowEnergy.GaussComposite.ActualDressedFieldTime.actual_finite_background_time_direction]
  for name in mouths do
    unless owned.contains name do throwError m!"MISSING_MOUTH {name}"
  let tests := #[
    ``LowEnergy.GaussComposite.ActualDressedFieldTimeAudit.checked_actual_field_C_grade,
    ``LowEnergy.GaussComposite.ActualDressedFieldTimeAudit.checked_actual_field_generator_source,
    ``LowEnergy.GaussComposite.ActualDressedFieldTimeAudit.checked_actual_field_prefix_terminal,
    ``LowEnergy.GaussComposite.ActualDressedFieldTimeAudit.checked_actual_field_prefix_derivative,
    ``LowEnergy.GaussComposite.ActualDressedFieldTimeAudit.checked_actual_field_time_finitePrefix,
    ``LowEnergy.GaussComposite.ActualDressedFieldTimeAudit.checked_actual_field_interaction_N2G0_range,
    ``LowEnergy.GaussComposite.ActualDressedFieldTimeAudit.checked_actual_field_interaction_N2G1_range,
    ``LowEnergy.GaussComposite.ActualDressedFieldTimeAudit.checked_actual_field_interaction_N2G2_zero,
    ``LowEnergy.GaussComposite.ActualDressedFieldTimeAudit.checked_actual_field_ordered_N2G2_zero,
    ``LowEnergy.GaussComposite.ActualDressedFieldTimeAudit.checked_actual_field_ordered_N2G1_high_zero,
    ``LowEnergy.GaussComposite.ActualDressedFieldTimeAudit.checked_actual_field_ordered_N2G0_high_zero,
    ``LowEnergy.GaussComposite.ActualDressedFieldTimeAudit.checked_actual_field_prefix_N2_high_zero,
    ``LowEnergy.GaussComposite.ActualDressedFieldTimeAudit.checked_actual_field_time_N2_grade_return,
    ``LowEnergy.GaussComposite.ActualDressedFieldTimeAudit.checked_actual_field_time_N2_projection_return,
    ``LowEnergy.GaussComposite.ActualDressedFieldTimeAudit.checked_actual_field_time_created_unit,
    ``LowEnergy.GaussComposite.ActualDressedFieldTimeAudit.checked_actual_field_interaction_N1G0_range,
    ``LowEnergy.GaussComposite.ActualDressedFieldTimeAudit.checked_actual_field_interaction_N1G1_zero,
    ``LowEnergy.GaussComposite.ActualDressedFieldTimeAudit.checked_actual_field_ordered_N1G1_zero,
    ``LowEnergy.GaussComposite.ActualDressedFieldTimeAudit.checked_actual_field_ordered_N1G0_high_zero,
    ``LowEnergy.GaussComposite.ActualDressedFieldTimeAudit.checked_actual_field_prefix_N1G0_high_zero,
    ``LowEnergy.GaussComposite.ActualDressedFieldTimeAudit.checked_actual_field_prefix_N1G1_high_zero,
    ``LowEnergy.GaussComposite.ActualDressedFieldTimeAudit.checked_actual_field_prefix_N1_high_zero,
    ``LowEnergy.GaussComposite.ActualDressedFieldTimeAudit.checked_actual_field_time_N1_projection_return,
    ``LowEnergy.GaussComposite.ActualDressedFieldTimeAudit.checked_actual_field_time_background,
    ``LowEnergy.GaussComposite.ActualDressedFieldTimeAudit.checked_actual_finite_number_field_read,
    ``LowEnergy.GaussComposite.ActualDressedFieldTimeAudit.checked_actual_finite_noether_field_germ,
    ``LowEnergy.GaussComposite.ActualDressedFieldTimeAudit.checked_actual_finite_number_field_quantum_derivative,
    ``LowEnergy.GaussComposite.ActualDressedFieldTimeAudit.checked_actual_finite_created_time_direction,
    ``LowEnergy.GaussComposite.ActualDressedFieldTimeAudit.checked_actual_finite_background_time_direction,
    ``LowEnergy.GaussComposite.ActualDressedFieldTimeAudit.actual_event_nonempty,
    ``LowEnergy.GaussComposite.ActualDressedFieldTimeAudit.actual_unit_nonzero,
    ``LowEnergy.GaussComposite.ActualDressedFieldTimeAudit.same_actual_field_time_carriers,
    ``LowEnergy.GaussComposite.ActualDressedFieldTimeAudit.same_actual_finite_noether_zero,
    ``LowEnergy.GaussComposite.ActualDressedFieldTimeAudit.same_actual_finite_quantum_response]
  let direct := #[
    (``LowEnergy.GaussComposite.ActualDressedFieldTime.actual_field_C_grade,#[
    ``LowEnergy.GaussComposite.ActualDressedNumberField.actual_joint_compression_blocks]),
    (``LowEnergy.GaussComposite.ActualDressedFieldTime.actual_field_prefix_terminal,#[
    ``LowEnergy.GaussComposite.ActualDressedFieldTime.actual_field_C_grade,
    ``LowEnergy.GaussComposite.ActualDressedNumberField.actual_joint_Y_raises,
    ``LowEnergy.FullYSourceCutoffVolterra.finitePrefix_homogeneous]),
    (``LowEnergy.GaussComposite.ActualDressedFieldTime.actual_field_prefix_derivative,#[
    ``LowEnergy.GaussComposite.ActualDressedFieldTime.actual_field_prefix_terminal,
    ``LowEnergy.GaussComposite.ActualDressedFieldTime.actual_field_generator_source,
    ``LowEnergy.FullYSourceCutoffVolterra.partialEvolution_derivative]),
    (``LowEnergy.GaussComposite.ActualDressedFieldTime.actual_field_time_finitePrefix,#[
    ``LowEnergy.GaussComposite.ActualDressedFieldTime.actual_field_prefix_derivative,
    ``LowEnergy.FullYSourceCutoffVolterra.autonomous_evolution_unique]),
    (``LowEnergy.GaussComposite.ActualDressedFieldTime.actual_field_interaction_N2G0_range,#[
    ``LowEnergy.GaussComposite.ActualDressedNumberField.actual_joint_Y_N2G0_range]),
    (``LowEnergy.GaussComposite.ActualDressedFieldTime.actual_field_interaction_N2G1_range,#[
    ``LowEnergy.GaussComposite.ActualDressedNumberField.actual_joint_Y_N2G1_range]),
    (``LowEnergy.GaussComposite.ActualDressedFieldTime.actual_field_interaction_N2G2_zero,#[
    ``LowEnergy.GaussComposite.ActualDressedNumberField.actual_joint_Y_N2G2_zero]),
    (``LowEnergy.GaussComposite.ActualDressedFieldTime.actual_field_time_N2_grade_return,#[
    ``LowEnergy.GaussComposite.ActualDressedFieldTime.actual_field_time_finitePrefix,
    ``LowEnergy.GaussComposite.ActualDressedFieldTime.actual_field_prefix_N2_high_zero]),
    (``LowEnergy.GaussComposite.ActualDressedFieldTime.actual_field_time_N2_projection_return,#[
    ``LowEnergy.GaussComposite.ActualDressedFieldTime.actual_field_time_N2_grade_return]),
    (``LowEnergy.GaussComposite.ActualDressedFieldTime.actual_field_time_created_unit,#[
    ``LowEnergy.GaussComposite.ActualDressedFieldTime.actual_field_time_N2_projection_return,
    ``LowEnergy.GaussComposite.ActualDressedNumberSector.actual_created_unit_N2]),
    (``LowEnergy.GaussComposite.ActualDressedFieldTime.actual_field_interaction_N1G0_range,#[
    ``LowEnergy.GaussComposite.ActualDressedNumberField.actual_joint_Y_N1G0_range]),
    (``LowEnergy.GaussComposite.ActualDressedFieldTime.actual_field_interaction_N1G1_zero,#[
    ``LowEnergy.GaussComposite.ActualDressedNumberField.actual_joint_Y_N1G1_zero]),
    (``LowEnergy.GaussComposite.ActualDressedFieldTime.actual_field_time_N1_projection_return,#[
    ``LowEnergy.GaussComposite.ActualDressedFieldTime.actual_field_time_finitePrefix,
    ``LowEnergy.GaussComposite.ActualDressedFieldTime.actual_field_prefix_N1_high_zero]),
    (``LowEnergy.GaussComposite.ActualDressedFieldTime.actual_field_time_background,#[
    ``LowEnergy.GaussComposite.ActualDressedFieldTime.actual_field_time_N1_projection_return,
    ``LowEnergy.GaussComposite.ActualDressedNumberZero.actual_background_number_one]),
    (``LowEnergy.GaussComposite.ActualDressedFieldTime.actual_finite_number_field_read,#[
    ``LowEnergy.GaussComposite.ActualDressedFieldTime.actual_field_time_created_unit,
    ``LowEnergy.GaussComposite.ActualDressedFieldTime.actual_field_time_background]),
    (``LowEnergy.GaussComposite.ActualDressedFieldTime.actual_finite_noether_field_germ,#[
    ``LowEnergy.GaussComposite.ActualDressedNumberField.actual_noether_number_field_germ,
    ``LowEnergy.GaussComposite.ActualDressedFieldTime.actual_finite_number_field_read]),
    (``LowEnergy.GaussComposite.ActualDressedFieldTime.actual_finite_number_field_quantum_derivative,#[
    ``LowEnergy.GaussComposite.ActualDressedNumberField.actual_number_field_quantum_derivative,
    ``LowEnergy.GaussComposite.ActualDressedFieldTime.actual_finite_number_field_read]),
    (``LowEnergy.GaussComposite.ActualDressedFieldTime.actual_finite_created_time_direction,#[
    ``LowEnergy.GaussComposite.ActualDressedFieldTime.actual_field_time_created_unit,
    ``LowEnergy.PreparationVacuumRawJointFeedback.physicalTime_direction]),
    (``LowEnergy.GaussComposite.ActualDressedFieldTime.actual_finite_background_time_direction,#[
    ``LowEnergy.GaussComposite.ActualDressedFieldTime.actual_field_time_background,
    ``LowEnergy.PreparationVacuumRawJointFeedback.physicalTime_direction])]
  for (mouth,required) in direct do packageCertRequire env mouth required
  let testProducers := #[
    ``LowEnergy.GaussComposite.ActualDressedFieldTime.actual_field_C_grade,
    ``LowEnergy.GaussComposite.ActualDressedFieldTime.actual_field_generator_source,
    ``LowEnergy.GaussComposite.ActualDressedFieldTime.actual_field_prefix_terminal,
    ``LowEnergy.GaussComposite.ActualDressedFieldTime.actual_field_prefix_derivative,
    ``LowEnergy.GaussComposite.ActualDressedFieldTime.actual_field_time_finitePrefix,
    ``LowEnergy.GaussComposite.ActualDressedFieldTime.actual_field_interaction_N2G0_range,
    ``LowEnergy.GaussComposite.ActualDressedFieldTime.actual_field_interaction_N2G1_range,
    ``LowEnergy.GaussComposite.ActualDressedFieldTime.actual_field_interaction_N2G2_zero,
    ``LowEnergy.GaussComposite.ActualDressedFieldTime.actual_field_ordered_N2G2_zero,
    ``LowEnergy.GaussComposite.ActualDressedFieldTime.actual_field_ordered_N2G1_high_zero,
    ``LowEnergy.GaussComposite.ActualDressedFieldTime.actual_field_ordered_N2G0_high_zero,
    ``LowEnergy.GaussComposite.ActualDressedFieldTime.actual_field_prefix_N2_high_zero,
    ``LowEnergy.GaussComposite.ActualDressedFieldTime.actual_field_time_N2_grade_return,
    ``LowEnergy.GaussComposite.ActualDressedFieldTime.actual_field_time_N2_projection_return,
    ``LowEnergy.GaussComposite.ActualDressedFieldTime.actual_field_time_created_unit,
    ``LowEnergy.GaussComposite.ActualDressedFieldTime.actual_field_interaction_N1G0_range,
    ``LowEnergy.GaussComposite.ActualDressedFieldTime.actual_field_interaction_N1G1_zero,
    ``LowEnergy.GaussComposite.ActualDressedFieldTime.actual_field_ordered_N1G1_zero,
    ``LowEnergy.GaussComposite.ActualDressedFieldTime.actual_field_ordered_N1G0_high_zero,
    ``LowEnergy.GaussComposite.ActualDressedFieldTime.actual_field_prefix_N1G0_high_zero,
    ``LowEnergy.GaussComposite.ActualDressedFieldTime.actual_field_prefix_N1G1_high_zero,
    ``LowEnergy.GaussComposite.ActualDressedFieldTime.actual_field_prefix_N1_high_zero,
    ``LowEnergy.GaussComposite.ActualDressedFieldTime.actual_field_time_N1_projection_return,
    ``LowEnergy.GaussComposite.ActualDressedFieldTime.actual_field_time_background,
    ``LowEnergy.GaussComposite.ActualDressedFieldTime.actual_finite_number_field_read,
    ``LowEnergy.GaussComposite.ActualDressedFieldTime.actual_finite_noether_field_germ,
    ``LowEnergy.GaussComposite.ActualDressedFieldTime.actual_finite_number_field_quantum_derivative,
    ``LowEnergy.GaussComposite.ActualDressedFieldTime.actual_finite_created_time_direction,
    ``LowEnergy.GaussComposite.ActualDressedFieldTime.actual_finite_background_time_direction]
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
    ``LowEnergy.PreparationVacuumJointFieldResponse.jointY_source]
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
  if let some path ← liftIO (IO.getEnv "ALPHA_DRESSED_FIELD_TIME_AUDIT_OUTPUT") then
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
  logInfo m!"DRESSED_FIELD_TIME_PASS public={mouths.size} owned={owned.length} tests={tests.size} nodes={all.size} anchors={anchors.size} direct={direct.size} opaque_all_read={opaques} axioms={axioms} unknown=0 unsafe=0 partial=0"
#audit_dressed_field_time
#print axioms LowEnergy.GaussComposite.ActualDressedFieldTime.actual_field_C_grade
#print axioms LowEnergy.GaussComposite.ActualDressedFieldTime.actual_field_generator_source
#print axioms LowEnergy.GaussComposite.ActualDressedFieldTime.actual_field_prefix_terminal
#print axioms LowEnergy.GaussComposite.ActualDressedFieldTime.actual_field_prefix_derivative
#print axioms LowEnergy.GaussComposite.ActualDressedFieldTime.actual_field_time_finitePrefix
#print axioms LowEnergy.GaussComposite.ActualDressedFieldTime.actual_field_interaction_N2G0_range
#print axioms LowEnergy.GaussComposite.ActualDressedFieldTime.actual_field_interaction_N2G1_range
#print axioms LowEnergy.GaussComposite.ActualDressedFieldTime.actual_field_interaction_N2G2_zero
#print axioms LowEnergy.GaussComposite.ActualDressedFieldTime.actual_field_ordered_N2G2_zero
#print axioms LowEnergy.GaussComposite.ActualDressedFieldTime.actual_field_ordered_N2G1_high_zero
#print axioms LowEnergy.GaussComposite.ActualDressedFieldTime.actual_field_ordered_N2G0_high_zero
#print axioms LowEnergy.GaussComposite.ActualDressedFieldTime.actual_field_prefix_N2_high_zero
#print axioms LowEnergy.GaussComposite.ActualDressedFieldTime.actual_field_time_N2_grade_return
#print axioms LowEnergy.GaussComposite.ActualDressedFieldTime.actual_field_time_N2_projection_return
#print axioms LowEnergy.GaussComposite.ActualDressedFieldTime.actual_field_time_created_unit
#print axioms LowEnergy.GaussComposite.ActualDressedFieldTime.actual_field_interaction_N1G0_range
#print axioms LowEnergy.GaussComposite.ActualDressedFieldTime.actual_field_interaction_N1G1_zero
#print axioms LowEnergy.GaussComposite.ActualDressedFieldTime.actual_field_ordered_N1G1_zero
#print axioms LowEnergy.GaussComposite.ActualDressedFieldTime.actual_field_ordered_N1G0_high_zero
#print axioms LowEnergy.GaussComposite.ActualDressedFieldTime.actual_field_prefix_N1G0_high_zero
#print axioms LowEnergy.GaussComposite.ActualDressedFieldTime.actual_field_prefix_N1G1_high_zero
#print axioms LowEnergy.GaussComposite.ActualDressedFieldTime.actual_field_prefix_N1_high_zero
#print axioms LowEnergy.GaussComposite.ActualDressedFieldTime.actual_field_time_N1_projection_return
#print axioms LowEnergy.GaussComposite.ActualDressedFieldTime.actual_field_time_background
#print axioms LowEnergy.GaussComposite.ActualDressedFieldTime.actual_finite_number_field_read
#print axioms LowEnergy.GaussComposite.ActualDressedFieldTime.actual_finite_noether_field_germ
#print axioms LowEnergy.GaussComposite.ActualDressedFieldTime.actual_finite_number_field_quantum_derivative
#print axioms LowEnergy.GaussComposite.ActualDressedFieldTime.actual_finite_created_time_direction
#print axioms LowEnergy.GaussComposite.ActualDressedFieldTime.actual_finite_background_time_direction
