import H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualDressedLeftFreeJet
import H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualDressedN1TimePrice
import H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualDressedN1SlopePrice
import H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualDressedCompleteNoetherPrice
import H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualDressedFifthLaplacePrice
import H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualDressedObservedPolePrice

import Lean.Elab.Command
import Lean.Util.FoldConsts
import Lean.Util.CollectAxioms
set_option autoImplicit false
set_option maxHeartbeats 12000000
set_option maxRecDepth 32768
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.GaussComposite.ActualDressedObservedPoleAudit
elab "checked_free_compression_baseContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualDressedLeftFreeJet.free_compression_base).type
theorem checked_free_compression_base : checked_free_compression_baseContract := @LowEnergy.GaussComposite.ActualDressedLeftFreeJet.free_compression_base

elab "checked_free_compression_directionContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualDressedLeftFreeJet.free_compression_direction).type
theorem checked_free_compression_direction : checked_free_compression_directionContract := @LowEnergy.GaussComposite.ActualDressedLeftFreeJet.free_compression_direction

elab "checked_free_time_directionContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualDressedLeftFreeJet.free_time_direction).type
theorem checked_free_time_direction : checked_free_time_directionContract := @LowEnergy.GaussComposite.ActualDressedLeftFreeJet.free_time_direction

elab "checked_free_time_slope_priceContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualDressedLeftFreeJet.free_time_slope_price).type
theorem checked_free_time_slope_price : checked_free_time_slope_priceContract := @LowEnergy.GaussComposite.ActualDressedLeftFreeJet.free_time_slope_price

elab "checked_free_green_baseContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualDressedLeftFreeJet.free_green_base).type
theorem checked_free_green_base : checked_free_green_baseContract := @LowEnergy.GaussComposite.ActualDressedLeftFreeJet.free_green_base

elab "checked_free_green_directionContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualDressedLeftFreeJet.free_green_direction).type
theorem checked_free_green_direction : checked_free_green_directionContract := @LowEnergy.GaussComposite.ActualDressedLeftFreeJet.free_green_direction

elab "checked_free_green_slope_priceContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualDressedLeftFreeJet.free_green_slope_price).type
theorem checked_free_green_slope_price : checked_free_green_slope_priceContract := @LowEnergy.GaussComposite.ActualDressedLeftFreeJet.free_green_slope_price

elab "checked_free_green_source_priceContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualDressedLeftFreeJet.free_green_source_price).type
theorem checked_free_green_source_price : checked_free_green_source_priceContract := @LowEnergy.GaussComposite.ActualDressedLeftFreeJet.free_green_source_price

elab "checked_actual_left_time_directionContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualDressedLeftFreeJet.actual_left_time_direction).type
theorem checked_actual_left_time_direction : checked_actual_left_time_directionContract := @LowEnergy.GaussComposite.ActualDressedLeftFreeJet.actual_left_time_direction

elab "checked_actual_left_green_directionContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualDressedLeftFreeJet.actual_left_green_direction).type
theorem checked_actual_left_green_direction : checked_actual_left_green_directionContract := @LowEnergy.GaussComposite.ActualDressedLeftFreeJet.actual_left_green_direction

elab "checked_actual_joint_current_number_oneContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualDressedN1Price.actual_joint_current_number_one).type
theorem checked_actual_joint_current_number_one : checked_actual_joint_current_number_oneContract := @LowEnergy.GaussComposite.ActualDressedN1Price.actual_joint_current_number_one

elab "checked_actual_time_N1_projection_returnContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualDressedN1Price.actual_time_N1_projection_return).type
theorem checked_actual_time_N1_projection_return : checked_actual_time_N1_projection_returnContract := @LowEnergy.GaussComposite.ActualDressedN1Price.actual_time_N1_projection_return

elab "checked_actual_time_N1_returnContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualDressedN1Price.actual_time_N1_return).type
theorem checked_actual_time_N1_return : checked_actual_time_N1_returnContract := @LowEnergy.GaussComposite.ActualDressedN1Price.actual_time_N1_return

elab "checked_actual_time_N1_priceContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualDressedN1Price.actual_time_N1_price).type
theorem checked_actual_time_N1_price : checked_actual_time_N1_priceContract := @LowEnergy.GaussComposite.ActualDressedN1Price.actual_time_N1_price

elab "checked_actual_timeSlope_N1_rangeContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualDressedN1Price.actual_timeSlope_N1_range).type
theorem checked_actual_timeSlope_N1_range : checked_actual_timeSlope_N1_rangeContract := @LowEnergy.GaussComposite.ActualDressedN1Price.actual_timeSlope_N1_range

elab "checked_actual_timeSlope_N1_priceContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualDressedN1Price.actual_timeSlope_N1_price).type
theorem checked_actual_timeSlope_N1_price : checked_actual_timeSlope_N1_priceContract := @LowEnergy.GaussComposite.ActualDressedN1Price.actual_timeSlope_N1_price

elab "checked_actual_background_timeSlope_priceContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualDressedN1Price.actual_background_timeSlope_price).type
theorem checked_actual_background_timeSlope_price : checked_actual_background_timeSlope_priceContract := @LowEnergy.GaussComposite.ActualDressedN1Price.actual_background_timeSlope_price

elab "checked_actual_left_free_read_germContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualDressedCompletePrice.actual_left_free_read_germ).type
theorem checked_actual_left_free_read_germ : checked_actual_left_free_read_germContract := @LowEnergy.GaussComposite.ActualDressedCompletePrice.actual_left_free_read_germ

elab "checked_actual_complete_noether_jet_priceContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualDressedCompletePrice.actual_complete_noether_jet_price).type
theorem checked_actual_complete_noether_jet_price : checked_actual_complete_noether_jet_priceContract := @LowEnergy.GaussComposite.ActualDressedCompletePrice.actual_complete_noether_jet_price

elab "checked_complete_noether_price_nonnegContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualDressedCompletePrice.complete_noether_price_nonneg).type
theorem checked_complete_noether_price_nonneg : checked_complete_noether_price_nonnegContract := @LowEnergy.GaussComposite.ActualDressedCompletePrice.complete_noether_price_nonneg

elab "checked_actual_complete_noether_polynomial_priceContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualDressedCompletePrice.actual_complete_noether_polynomial_price).type
theorem checked_actual_complete_noether_polynomial_price : checked_actual_complete_noether_polynomial_priceContract := @LowEnergy.GaussComposite.ActualDressedCompletePrice.actual_complete_noether_polynomial_price

elab "checked_fifth_laplace_integrableContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualDressedObservedPolePrice.fifth_laplace_integrable).type
theorem checked_fifth_laplace_integrable : checked_fifth_laplace_integrableContract := @LowEnergy.GaussComposite.ActualDressedObservedPolePrice.fifth_laplace_integrable

elab "checked_fifth_laplace_sigma_six_priceContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualDressedObservedPolePrice.fifth_laplace_sigma_six_price).type
theorem checked_fifth_laplace_sigma_six_price : checked_fifth_laplace_sigma_six_priceContract := @LowEnergy.GaussComposite.ActualDressedObservedPolePrice.fifth_laplace_sigma_six_price

elab "checked_actual_static_polarization_laplace_priceContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualDressedObservedPolePrice.actual_static_polarization_laplace_price).type
theorem checked_actual_static_polarization_laplace_price : checked_actual_static_polarization_laplace_priceContract := @LowEnergy.GaussComposite.ActualDressedObservedPolePrice.actual_static_polarization_laplace_price

elab "checked_observed_static_source_price_nonnegContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualDressedObservedPolePrice.observed_static_source_price_nonneg).type
theorem checked_observed_static_source_price_nonneg : checked_observed_static_source_price_nonnegContract := @LowEnergy.GaussComposite.ActualDressedObservedPolePrice.observed_static_source_price_nonneg

elab "checked_actual_static_polarization_sigma_six_priceContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualDressedObservedPolePrice.actual_static_polarization_sigma_six_price).type
theorem checked_actual_static_polarization_sigma_six_price : checked_actual_static_polarization_sigma_six_priceContract := @LowEnergy.GaussComposite.ActualDressedObservedPolePrice.actual_static_polarization_sigma_six_price

elab "checked_actual_static_pole_leading_zero_of_order_gt_threeContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualDressedObservedPolePrice.actual_static_pole_leading_zero_of_order_gt_three).type
theorem checked_actual_static_pole_leading_zero_of_order_gt_three : checked_actual_static_pole_leading_zero_of_order_gt_threeContract := @LowEnergy.GaussComposite.ActualDressedObservedPolePrice.actual_static_pole_leading_zero_of_order_gt_three

open GaussCoreHilbert CanonicalGradedSpatialSource
open PreparationVacuumMixedFieldReturn PreparationVacuumPhysicalHalfAxis PreparationVacuumRawJointFeedback
open PreparationVacuumJointFieldResponse PreparationVacuumActionFieldLift
open ActualDressedFullCoulomb ActualDressedSourcePreparation ActualDressedNoether ActualDressedNumberZero
open GaussComposite.SourceGraph PreparationVacuumSourcePreparedResponse
open ActualDressedPreparedPrice ActualDressedN1Price ActualDressedCompletePrice
open ActualDressedSylvester ActualDressedStaticPole ActualDressedObservedPolePrice
open scoped Topology

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

theorem same_real_background_variation_price (event : DressedEvent) (force : Field289) (t : ℝ) :
    ‖timeSlope force event.momentum event.frame t (prepared (sourceProfile event.epsilon event.precision))‖≤
      |t| *‖jointCurrent event.momentum event.frame 0 0 force‖*
        (occupationPrice 1 ‖actualA event.momentum event.frame‖ |t|)^2*
          ‖prepared (sourceProfile event.epsilon event.precision)‖ :=
  actual_background_timeSlope_price event.momentum event.frame force t _

theorem same_actual_static_entry_unit_damping (event : DressedEvent) (transfer : PhysicalMomentum)
    (i j : Fin 289) :
    ‖dressedStaticPolarization event transfer (1:ℂ) i j‖≤observedStaticSourcePrice event transfer i j := by
  simpa only [one_pow,one_mul,Complex.ofReal_one] using
    actual_static_polarization_sigma_six_price event transfer 1 (by norm_num) le_rfl i j

theorem same_original_source_leading_cancellation (event : DressedEvent)
    (high : 3<dressedStaticPoleOrder event) : dressedStaticPoleLeading event 20 20=0 :=
  actual_static_pole_leading_zero_of_order_gt_three event high 20 20
end LowEnergy.GaussComposite.ActualDressedObservedPoleAudit

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

elab "#audit_dressed_observed_pole" : command => do
  let env ← getEnv
  let modules := env.header.moduleNames
  let owner := fun name => (env.getModuleIdxFor? name).map fun i => modules[i.toNat]!
  let candidates := #[`H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualDressedLeftFreeJet,`H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualDressedN1TimePrice,`H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualDressedN1SlopePrice,`H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualDressedCompleteNoetherPrice,`H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualDressedFifthLaplacePrice,`H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualDressedObservedPolePrice]
  let owned := env.constants.toList.filterMap fun (name, _) =>
    if (owner name).any candidates.contains then some name else none
  let mouths := #[
    ``LowEnergy.GaussComposite.ActualDressedLeftFreeJet.FreeOp,
    ``LowEnergy.GaussComposite.ActualDressedLeftFreeJet.freeCompressionCurrent,
    ``LowEnergy.GaussComposite.ActualDressedLeftFreeJet.free_compression_base,
    ``LowEnergy.GaussComposite.ActualDressedLeftFreeJet.free_compression_direction,
    ``LowEnergy.GaussComposite.ActualDressedLeftFreeJet.freeTimeSlope,
    ``LowEnergy.GaussComposite.ActualDressedLeftFreeJet.free_time_direction,
    ``LowEnergy.GaussComposite.ActualDressedLeftFreeJet.free_time_slope_price,
    ``LowEnergy.GaussComposite.ActualDressedLeftFreeJet.free_green_base,
    ``LowEnergy.GaussComposite.ActualDressedLeftFreeJet.free_green_direction,
    ``LowEnergy.GaussComposite.ActualDressedLeftFreeJet.free_green_slope_price,
    ``LowEnergy.GaussComposite.ActualDressedLeftFreeJet.free_green_source_price,
    ``LowEnergy.GaussComposite.ActualDressedLeftFreeJet.actual_left_time_direction,
    ``LowEnergy.GaussComposite.ActualDressedLeftFreeJet.actual_left_green_direction,
    ``LowEnergy.GaussComposite.ActualDressedN1Price.actual_joint_current_number_one,
    ``LowEnergy.GaussComposite.ActualDressedN1Price.actual_time_N1_projection_return,
    ``LowEnergy.GaussComposite.ActualDressedN1Price.actual_time_N1_return,
    ``LowEnergy.GaussComposite.ActualDressedN1Price.actual_time_N1_price,
    ``LowEnergy.GaussComposite.ActualDressedN1Price.actual_timeSlope_N1_range,
    ``LowEnergy.GaussComposite.ActualDressedN1Price.actual_timeSlope_N1_price,
    ``LowEnergy.GaussComposite.ActualDressedN1Price.actual_background_timeSlope_price,
    ``LowEnergy.GaussComposite.ActualDressedCompletePrice.leftFreeKernel,
    ``LowEnergy.GaussComposite.ActualDressedCompletePrice.leftFreeRead,
    ``LowEnergy.GaussComposite.ActualDressedCompletePrice.actual_left_free_read_germ,
    ``LowEnergy.GaussComposite.ActualDressedCompletePrice.completeNoetherPrice,
    ``LowEnergy.GaussComposite.ActualDressedCompletePrice.actual_complete_noether_jet_price,
    ``LowEnergy.GaussComposite.ActualDressedCompletePrice.complete_noether_price_nonneg,
    ``LowEnergy.GaussComposite.ActualDressedCompletePrice.actual_complete_noether_polynomial_price,
    ``LowEnergy.GaussComposite.ActualDressedObservedPolePrice.fifth_laplace_integrable,
    ``LowEnergy.GaussComposite.ActualDressedObservedPolePrice.fifth_laplace_sigma_six_price,
    ``LowEnergy.GaussComposite.ActualDressedObservedPolePrice.actual_static_polarization_laplace_price,
    ``LowEnergy.GaussComposite.ActualDressedObservedPolePrice.observedStaticSourcePrice,
    ``LowEnergy.GaussComposite.ActualDressedObservedPolePrice.observed_static_source_price_nonneg,
    ``LowEnergy.GaussComposite.ActualDressedObservedPolePrice.actual_static_polarization_sigma_six_price,
    ``LowEnergy.GaussComposite.ActualDressedObservedPolePrice.actual_static_pole_leading_zero_of_order_gt_three]
  for name in mouths do
    unless owned.contains name do throwError m!"MISSING_MOUTH {name}"
  let tests := #[
    ``LowEnergy.GaussComposite.ActualDressedObservedPoleAudit.checked_free_compression_base,
    ``LowEnergy.GaussComposite.ActualDressedObservedPoleAudit.checked_free_compression_direction,
    ``LowEnergy.GaussComposite.ActualDressedObservedPoleAudit.checked_free_time_direction,
    ``LowEnergy.GaussComposite.ActualDressedObservedPoleAudit.checked_free_time_slope_price,
    ``LowEnergy.GaussComposite.ActualDressedObservedPoleAudit.checked_free_green_base,
    ``LowEnergy.GaussComposite.ActualDressedObservedPoleAudit.checked_free_green_direction,
    ``LowEnergy.GaussComposite.ActualDressedObservedPoleAudit.checked_free_green_slope_price,
    ``LowEnergy.GaussComposite.ActualDressedObservedPoleAudit.checked_free_green_source_price,
    ``LowEnergy.GaussComposite.ActualDressedObservedPoleAudit.checked_actual_left_time_direction,
    ``LowEnergy.GaussComposite.ActualDressedObservedPoleAudit.checked_actual_left_green_direction,
    ``LowEnergy.GaussComposite.ActualDressedObservedPoleAudit.checked_actual_joint_current_number_one,
    ``LowEnergy.GaussComposite.ActualDressedObservedPoleAudit.checked_actual_time_N1_projection_return,
    ``LowEnergy.GaussComposite.ActualDressedObservedPoleAudit.checked_actual_time_N1_return,
    ``LowEnergy.GaussComposite.ActualDressedObservedPoleAudit.checked_actual_time_N1_price,
    ``LowEnergy.GaussComposite.ActualDressedObservedPoleAudit.checked_actual_timeSlope_N1_range,
    ``LowEnergy.GaussComposite.ActualDressedObservedPoleAudit.checked_actual_timeSlope_N1_price,
    ``LowEnergy.GaussComposite.ActualDressedObservedPoleAudit.checked_actual_background_timeSlope_price,
    ``LowEnergy.GaussComposite.ActualDressedObservedPoleAudit.checked_actual_left_free_read_germ,
    ``LowEnergy.GaussComposite.ActualDressedObservedPoleAudit.checked_actual_complete_noether_jet_price,
    ``LowEnergy.GaussComposite.ActualDressedObservedPoleAudit.checked_complete_noether_price_nonneg,
    ``LowEnergy.GaussComposite.ActualDressedObservedPoleAudit.checked_actual_complete_noether_polynomial_price,
    ``LowEnergy.GaussComposite.ActualDressedObservedPoleAudit.checked_fifth_laplace_integrable,
    ``LowEnergy.GaussComposite.ActualDressedObservedPoleAudit.checked_fifth_laplace_sigma_six_price,
    ``LowEnergy.GaussComposite.ActualDressedObservedPoleAudit.checked_actual_static_polarization_laplace_price,
    ``LowEnergy.GaussComposite.ActualDressedObservedPoleAudit.checked_observed_static_source_price_nonneg,
    ``LowEnergy.GaussComposite.ActualDressedObservedPoleAudit.checked_actual_static_polarization_sigma_six_price,
    ``LowEnergy.GaussComposite.ActualDressedObservedPoleAudit.checked_actual_static_pole_leading_zero_of_order_gt_three,
    ``LowEnergy.GaussComposite.ActualDressedObservedPoleAudit.actual_event_nonempty,
    ``LowEnergy.GaussComposite.ActualDressedObservedPoleAudit.actual_unit_nonzero,
    ``LowEnergy.GaussComposite.ActualDressedObservedPoleAudit.same_real_background_variation_price,
    ``LowEnergy.GaussComposite.ActualDressedObservedPoleAudit.same_actual_static_entry_unit_damping,
    ``LowEnergy.GaussComposite.ActualDressedObservedPoleAudit.same_original_source_leading_cancellation]
  let direct := #[
    (``LowEnergy.GaussComposite.ActualDressedLeftFreeJet.free_time_direction,#[
    ``LowEnergy.GaussComposite.ActualDressedLeftFreeJet.free_compression_direction,
    ``LowEnergy.PreparationVacuumActionDecomposition.nonlinear_time_derivative]),
    (``LowEnergy.GaussComposite.ActualDressedLeftFreeJet.free_green_direction,#[
    ``LowEnergy.GaussComposite.ActualDressedLeftFreeJet.free_compression_direction,
    ``LowEnergy.GaussComposite.ActualDressedNumberField.actual_joint_free_units_near_zero]),
    (``LowEnergy.GaussComposite.ActualDressedLeftFreeJet.free_green_source_price,#[
    ``LowEnergy.GaussComposite.ActualDressedLeftFreeJet.free_green_slope_price,
    ``LowEnergy.CanonicalPhysicalResolvent.finite_bound]),
    (``LowEnergy.GaussComposite.ActualDressedLeftFreeJet.actual_left_time_direction,#[
    ``LowEnergy.GaussComposite.ActualDressedLeftFreeJet.free_time_direction,
    ``LowEnergy.GaussComposite.ActualDressedNumberField.actual_joint_time_grade_zero_left]),
    (``LowEnergy.GaussComposite.ActualDressedLeftFreeJet.actual_left_green_direction,#[
    ``LowEnergy.GaussComposite.ActualDressedLeftFreeJet.free_green_direction,
    ``LowEnergy.GaussComposite.ActualDressedNumberField.actual_joint_resolvent_grade_zero_left]),
    (``LowEnergy.GaussComposite.ActualDressedN1Price.actual_joint_current_number_one,#[
    ``LowEnergy.PreparationVacuumJointFieldResponse.jointGenerator_C2,
    ``LowEnergy.GaussComposite.ActualDressedNumberField.actual_joint_generator_number_one]),
    (``LowEnergy.GaussComposite.ActualDressedN1Price.actual_time_N1_projection_return,#[
    ``LowEnergy.GaussComposite.ActualDressedFieldTime.actual_field_time_N1_projection_return]),
    (``LowEnergy.GaussComposite.ActualDressedN1Price.actual_time_N1_price,#[
    ``LowEnergy.GaussComposite.ActualDressedN1Price.actual_time_N1_return,
    ``LowEnergy.FullYSourceCutoffVolterra.partialEvolution_bound]),
    (``LowEnergy.GaussComposite.ActualDressedN1Price.actual_timeSlope_N1_range,#[
    ``LowEnergy.GaussComposite.ActualDressedN1Price.actual_joint_current_number_one,
    ``LowEnergy.GaussComposite.ActualDressedNumberField.actual_joint_time_number_one_range]),
    (``LowEnergy.GaussComposite.ActualDressedN1Price.actual_timeSlope_N1_price,#[
    ``LowEnergy.GaussComposite.ActualDressedN1Price.actual_time_N1_price,
    ``LowEnergy.GaussComposite.ActualDressedN1Price.actual_joint_current_number_one]),
    (``LowEnergy.GaussComposite.ActualDressedN1Price.actual_background_timeSlope_price,#[
    ``LowEnergy.GaussComposite.ActualDressedN1Price.actual_timeSlope_N1_price,
    ``LowEnergy.GaussComposite.ActualDressedNumberZero.actual_background_number_one]),
    (``LowEnergy.GaussComposite.ActualDressedCompletePrice.actual_left_free_read_germ,#[
    ``LowEnergy.GaussComposite.ActualDressedNumberField.actual_noether_number_field_germ]),
    (``LowEnergy.GaussComposite.ActualDressedCompletePrice.actual_complete_noether_jet_price,#[
    ``LowEnergy.GaussComposite.ActualDressedCompletePrice.actual_left_free_read_germ,
    ``LowEnergy.GaussComposite.ActualDressedLeftFreeJet.free_time_direction,
    ``LowEnergy.GaussComposite.ActualDressedLeftFreeJet.free_green_direction,
    ``LowEnergy.GaussComposite.ActualDressedN1Price.actual_timeSlope_N1_price,
    ``LowEnergy.GaussComposite.ActualDressedPreparedPrice.actual_timeSlope_N2_polynomial_price,
    ``LowEnergy.GaussComposite.ActualDressedNoether.dressed_noether_action_derivative]),
    (``LowEnergy.GaussComposite.ActualDressedCompletePrice.actual_complete_noether_polynomial_price,#[
    ``LowEnergy.GaussComposite.ActualDressedCompletePrice.actual_complete_noether_jet_price,
    ``LowEnergy.GaussComposite.ActualDressedCompletePrice.complete_noether_price_nonneg]),
    (``LowEnergy.GaussComposite.ActualDressedObservedPolePrice.actual_static_polarization_laplace_price,#[
    ``LowEnergy.GaussComposite.ActualDressedCompletePrice.actual_complete_noether_jet_price,
    ``LowEnergy.GaussComposite.ActualDressedFiniteStaticRead.dressed_static_polarization_finite,
    ``LowEnergy.GaussComposite.ActualDressedFiniteStaticRead.finite_static_integrand_integrable]),
    (``LowEnergy.GaussComposite.ActualDressedObservedPolePrice.actual_static_polarization_sigma_six_price,#[
    ``LowEnergy.GaussComposite.ActualDressedObservedPolePrice.actual_static_polarization_laplace_price,
    ``LowEnergy.GaussComposite.ActualDressedObservedPolePrice.fifth_laplace_sigma_six_price,
    ``LowEnergy.GaussComposite.ActualDressedCompletePrice.complete_noether_price_nonneg]),
    (``LowEnergy.GaussComposite.ActualDressedObservedPolePrice.actual_static_pole_leading_zero_of_order_gt_three,#[
    ``LowEnergy.GaussComposite.ActualDressedObservedPolePrice.actual_static_polarization_sigma_six_price,
    ``LowEnergy.GaussComposite.ActualDressedStaticPole.dressed_static_pole_leading_limit])]
  for (mouth,required) in direct do packageCertRequire env mouth required
  let testProducers := #[
    ``LowEnergy.GaussComposite.ActualDressedLeftFreeJet.free_compression_base,
    ``LowEnergy.GaussComposite.ActualDressedLeftFreeJet.free_compression_direction,
    ``LowEnergy.GaussComposite.ActualDressedLeftFreeJet.free_time_direction,
    ``LowEnergy.GaussComposite.ActualDressedLeftFreeJet.free_time_slope_price,
    ``LowEnergy.GaussComposite.ActualDressedLeftFreeJet.free_green_base,
    ``LowEnergy.GaussComposite.ActualDressedLeftFreeJet.free_green_direction,
    ``LowEnergy.GaussComposite.ActualDressedLeftFreeJet.free_green_slope_price,
    ``LowEnergy.GaussComposite.ActualDressedLeftFreeJet.free_green_source_price,
    ``LowEnergy.GaussComposite.ActualDressedLeftFreeJet.actual_left_time_direction,
    ``LowEnergy.GaussComposite.ActualDressedLeftFreeJet.actual_left_green_direction,
    ``LowEnergy.GaussComposite.ActualDressedN1Price.actual_joint_current_number_one,
    ``LowEnergy.GaussComposite.ActualDressedN1Price.actual_time_N1_projection_return,
    ``LowEnergy.GaussComposite.ActualDressedN1Price.actual_time_N1_return,
    ``LowEnergy.GaussComposite.ActualDressedN1Price.actual_time_N1_price,
    ``LowEnergy.GaussComposite.ActualDressedN1Price.actual_timeSlope_N1_range,
    ``LowEnergy.GaussComposite.ActualDressedN1Price.actual_timeSlope_N1_price,
    ``LowEnergy.GaussComposite.ActualDressedN1Price.actual_background_timeSlope_price,
    ``LowEnergy.GaussComposite.ActualDressedCompletePrice.actual_left_free_read_germ,
    ``LowEnergy.GaussComposite.ActualDressedCompletePrice.actual_complete_noether_jet_price,
    ``LowEnergy.GaussComposite.ActualDressedCompletePrice.complete_noether_price_nonneg,
    ``LowEnergy.GaussComposite.ActualDressedCompletePrice.actual_complete_noether_polynomial_price,
    ``LowEnergy.GaussComposite.ActualDressedObservedPolePrice.fifth_laplace_integrable,
    ``LowEnergy.GaussComposite.ActualDressedObservedPolePrice.fifth_laplace_sigma_six_price,
    ``LowEnergy.GaussComposite.ActualDressedObservedPolePrice.actual_static_polarization_laplace_price,
    ``LowEnergy.GaussComposite.ActualDressedObservedPolePrice.observed_static_source_price_nonneg,
    ``LowEnergy.GaussComposite.ActualDressedObservedPolePrice.actual_static_polarization_sigma_six_price,
    ``LowEnergy.GaussComposite.ActualDressedObservedPolePrice.actual_static_pole_leading_zero_of_order_gt_three]
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
    ``LowEnergy.GaussComposite.ActualDressedStaticPole.dressedStaticPoleOrder,
    ``LowEnergy.GaussComposite.ActualDressedStaticPole.dressedStaticPoleRegular,
    ``LowEnergy.GaussComposite.ActualDressedStaticPole.dressedStaticPoleLeading,
    ``LowEnergy.PreparationVacuumNoetherChart.noetherReader,
    ``LowEnergy.PreparationVacuumNoetherChart.noetherReaderContact]
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
  if let some path ← liftIO (IO.getEnv "ALPHA_DRESSED_OBSERVED_POLE_AUDIT_OUTPUT") then
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
  logInfo m!"DRESSED_OBSERVED_POLE_PASS public={mouths.size} owned={owned.length} tests={tests.size} nodes={all.size} anchors={anchors.size} direct={direct.size} opaque_all_read={opaques} axioms={axioms} unknown=0 unsafe=0 partial=0"
#audit_dressed_observed_pole
#print axioms LowEnergy.GaussComposite.ActualDressedLeftFreeJet.free_compression_base
#print axioms LowEnergy.GaussComposite.ActualDressedLeftFreeJet.free_compression_direction
#print axioms LowEnergy.GaussComposite.ActualDressedLeftFreeJet.free_time_direction
#print axioms LowEnergy.GaussComposite.ActualDressedLeftFreeJet.free_time_slope_price
#print axioms LowEnergy.GaussComposite.ActualDressedLeftFreeJet.free_green_base
#print axioms LowEnergy.GaussComposite.ActualDressedLeftFreeJet.free_green_direction
#print axioms LowEnergy.GaussComposite.ActualDressedLeftFreeJet.free_green_slope_price
#print axioms LowEnergy.GaussComposite.ActualDressedLeftFreeJet.free_green_source_price
#print axioms LowEnergy.GaussComposite.ActualDressedLeftFreeJet.actual_left_time_direction
#print axioms LowEnergy.GaussComposite.ActualDressedLeftFreeJet.actual_left_green_direction
#print axioms LowEnergy.GaussComposite.ActualDressedN1Price.actual_joint_current_number_one
#print axioms LowEnergy.GaussComposite.ActualDressedN1Price.actual_time_N1_projection_return
#print axioms LowEnergy.GaussComposite.ActualDressedN1Price.actual_time_N1_return
#print axioms LowEnergy.GaussComposite.ActualDressedN1Price.actual_time_N1_price
#print axioms LowEnergy.GaussComposite.ActualDressedN1Price.actual_timeSlope_N1_range
#print axioms LowEnergy.GaussComposite.ActualDressedN1Price.actual_timeSlope_N1_price
#print axioms LowEnergy.GaussComposite.ActualDressedN1Price.actual_background_timeSlope_price
#print axioms LowEnergy.GaussComposite.ActualDressedCompletePrice.actual_left_free_read_germ
#print axioms LowEnergy.GaussComposite.ActualDressedCompletePrice.actual_complete_noether_jet_price
#print axioms LowEnergy.GaussComposite.ActualDressedCompletePrice.complete_noether_price_nonneg
#print axioms LowEnergy.GaussComposite.ActualDressedCompletePrice.actual_complete_noether_polynomial_price
#print axioms LowEnergy.GaussComposite.ActualDressedObservedPolePrice.fifth_laplace_integrable
#print axioms LowEnergy.GaussComposite.ActualDressedObservedPolePrice.fifth_laplace_sigma_six_price
#print axioms LowEnergy.GaussComposite.ActualDressedObservedPolePrice.actual_static_polarization_laplace_price
#print axioms LowEnergy.GaussComposite.ActualDressedObservedPolePrice.observed_static_source_price_nonneg
#print axioms LowEnergy.GaussComposite.ActualDressedObservedPolePrice.actual_static_polarization_sigma_six_price
#print axioms LowEnergy.GaussComposite.ActualDressedObservedPolePrice.actual_static_pole_leading_zero_of_order_gt_three
