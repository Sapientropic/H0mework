import H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualDressedUpperCurrent
import H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.FiniteFlagVariationPrice
import H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualDressedGradedSlopePrice
import H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualDressedCubicNoetherPrice
import H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualDressedCubicLaplacePrice
import H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualDressedCubicStaticPrice

import Lean.Elab.Command
import Lean.Util.FoldConsts
import Lean.Util.CollectAxioms
set_option autoImplicit false
set_option maxHeartbeats 12000000
set_option maxRecDepth 32768
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.GaussComposite.ActualDressedCubicPriceAudit
elab "checked_actual_joint_Y_upperContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualDressedGradedPrice.actual_joint_Y_upper).type
theorem checked_actual_joint_Y_upper : checked_actual_joint_Y_upperContract := @LowEnergy.GaussComposite.ActualDressedGradedPrice.actual_joint_Y_upper

elab "checked_actual_interaction_upperContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualDressedGradedPrice.actual_interaction_upper).type
theorem checked_actual_interaction_upper : checked_actual_interaction_upperContract := @LowEnergy.GaussComposite.ActualDressedGradedPrice.actual_interaction_upper

elab "checked_actual_joint_C_upperContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualDressedGradedPrice.actual_joint_C_upper).type
theorem checked_actual_joint_C_upper : checked_actual_joint_C_upperContract := @LowEnergy.GaussComposite.ActualDressedGradedPrice.actual_joint_C_upper

elab "checked_actual_joint_generator_upperContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualDressedGradedPrice.actual_joint_generator_upper).type
theorem checked_actual_joint_generator_upper : checked_actual_joint_generator_upperContract := @LowEnergy.GaussComposite.ActualDressedGradedPrice.actual_joint_generator_upper

elab "checked_actual_joint_current_upperContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualDressedGradedPrice.actual_joint_current_upper).type
theorem checked_actual_joint_current_upper : checked_actual_joint_current_upperContract := @LowEnergy.GaussComposite.ActualDressedGradedPrice.actual_joint_current_upper

elab "checked_ordered_one_rangeContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualDressedGradedPrice.ordered_one_range).type
theorem checked_ordered_one_range : checked_ordered_one_rangeContract := @LowEnergy.GaussComposite.ActualDressedGradedPrice.ordered_one_range

elab "checked_prefix_one_rangeContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualDressedGradedPrice.prefix_one_range).type
theorem checked_prefix_one_range : checked_prefix_one_rangeContract := @LowEnergy.GaussComposite.ActualDressedGradedPrice.prefix_one_range

elab "checked_prefix_two_rangeContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualDressedGradedPrice.prefix_two_range).type
theorem checked_prefix_two_range : checked_prefix_two_rangeContract := @LowEnergy.GaussComposite.ActualDressedGradedPrice.prefix_two_range

elab "checked_finite_flag_variation_priceContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualDressedGradedPrice.finite_flag_variation_price).type
theorem checked_finite_flag_variation_price : checked_finite_flag_variation_priceContract := @LowEnergy.GaussComposite.ActualDressedGradedPrice.finite_flag_variation_price

elab "checked_actual_time_upper_returnContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualDressedGradedPrice.actual_time_upper_return).type
theorem checked_actual_time_upper_return : checked_actual_time_upper_returnContract := @LowEnergy.GaussComposite.ActualDressedGradedPrice.actual_time_upper_return

elab "checked_actual_timeSlope_N2_cubic_priceContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualDressedGradedPrice.actual_timeSlope_N2_cubic_price).type
theorem checked_actual_timeSlope_N2_cubic_price : checked_actual_timeSlope_N2_cubic_priceContract := @LowEnergy.GaussComposite.ActualDressedGradedPrice.actual_timeSlope_N2_cubic_price

elab "checked_actual_created_timeSlope_cubic_priceContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualDressedGradedPrice.actual_created_timeSlope_cubic_price).type
theorem checked_actual_created_timeSlope_cubic_price : checked_actual_created_timeSlope_cubic_priceContract := @LowEnergy.GaussComposite.ActualDressedGradedPrice.actual_created_timeSlope_cubic_price

elab "checked_actual_timeSlope_N2_cubic_growthContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualDressedGradedPrice.actual_timeSlope_N2_cubic_growth).type
theorem checked_actual_timeSlope_N2_cubic_growth : checked_actual_timeSlope_N2_cubic_growthContract := @LowEnergy.GaussComposite.ActualDressedGradedPrice.actual_timeSlope_N2_cubic_growth

elab "checked_actual_timeSlope_N1_cubic_growthContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualDressedGradedPrice.actual_timeSlope_N1_cubic_growth).type
theorem checked_actual_timeSlope_N1_cubic_growth : checked_actual_timeSlope_N1_cubic_growthContract := @LowEnergy.GaussComposite.ActualDressedGradedPrice.actual_timeSlope_N1_cubic_growth

elab "checked_actual_complete_noether_cubic_jet_priceContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualDressedCubicPrice.actual_complete_noether_cubic_jet_price).type
theorem checked_actual_complete_noether_cubic_jet_price : checked_actual_complete_noether_cubic_jet_priceContract := @LowEnergy.GaussComposite.ActualDressedCubicPrice.actual_complete_noether_cubic_jet_price

elab "checked_complete_cubic_noether_price_nonnegContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualDressedCubicPrice.complete_cubic_noether_price_nonneg).type
theorem checked_complete_cubic_noether_price_nonneg : checked_complete_cubic_noether_price_nonnegContract := @LowEnergy.GaussComposite.ActualDressedCubicPrice.complete_cubic_noether_price_nonneg

elab "checked_cubic_laplace_integrableContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualDressedCubicPrice.cubic_laplace_integrable).type
theorem checked_cubic_laplace_integrable : checked_cubic_laplace_integrableContract := @LowEnergy.GaussComposite.ActualDressedCubicPrice.cubic_laplace_integrable

elab "checked_cubic_laplace_sigma_four_priceContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualDressedCubicPrice.cubic_laplace_sigma_four_price).type
theorem checked_cubic_laplace_sigma_four_price : checked_cubic_laplace_sigma_four_priceContract := @LowEnergy.GaussComposite.ActualDressedCubicPrice.cubic_laplace_sigma_four_price

elab "checked_actual_static_polarization_cubic_laplace_priceContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualDressedCubicPrice.actual_static_polarization_cubic_laplace_price).type
theorem checked_actual_static_polarization_cubic_laplace_price : checked_actual_static_polarization_cubic_laplace_priceContract := @LowEnergy.GaussComposite.ActualDressedCubicPrice.actual_static_polarization_cubic_laplace_price

elab "checked_observed_cubic_static_source_price_nonnegContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualDressedCubicPrice.observed_cubic_static_source_price_nonneg).type
theorem checked_observed_cubic_static_source_price_nonneg : checked_observed_cubic_static_source_price_nonnegContract := @LowEnergy.GaussComposite.ActualDressedCubicPrice.observed_cubic_static_source_price_nonneg

elab "checked_actual_static_polarization_sigma_four_priceContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualDressedCubicPrice.actual_static_polarization_sigma_four_price).type
theorem checked_actual_static_polarization_sigma_four_price : checked_actual_static_polarization_sigma_four_priceContract := @LowEnergy.GaussComposite.ActualDressedCubicPrice.actual_static_polarization_sigma_four_price

open GaussCoreHilbert CanonicalGradedSpatialSource
open PreparationVacuumMixedFieldReturn PreparationVacuumPhysicalHalfAxis PreparationVacuumRawJointFeedback
open PreparationVacuumJointFieldResponse PreparationVacuumActionFieldLift
open ActualDressedFullCoulomb ActualDressedSourcePreparation ActualDressedNoether ActualDressedNumberZero
open ActualDressedGradedPrice ActualDressedCubicPrice ActualDressedSylvester
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

theorem same_actual_created_cubic_slope (event : DressedEvent) (force : Field289) (t : ℝ) :
    ‖timeSlope force event.momentum event.frame t (sourceDressedUnit event.epsilon event.precision)‖≤
      |t| * ‖jointCurrent event.momentum event.frame 0 0 force‖*
        (1+2*(|t| * ‖actualA event.momentum event.frame‖)+3*(|t| * ‖actualA event.momentum event.frame‖)^2) :=
  actual_created_timeSlope_cubic_price event.momentum event.frame force t event.epsilon event.precision

theorem same_complete_original_cubic_jet (event : DressedEvent) (transfer : PhysicalMomentum)
    (force : Field289) (t : ℝ) (i : Fin 289) :
    ‖(dressedNoetherJet event transfer (fun _=>⟨force,0,0⟩) t i).value‖≤
      completeCubicNoetherPrice event transfer (fieldUnit i) force*(1+|t|)^3 :=
  actual_complete_noether_cubic_jet_price event transfer force t i

theorem same_original_static_entry_unit_damping (event : DressedEvent) (transfer : PhysicalMomentum)
    (i j : Fin 289) :
    ‖dressedStaticPolarization event transfer (1:ℂ) i j‖≤observedCubicStaticSourcePrice event transfer i j := by
  simpa only [one_pow,one_mul,Complex.ofReal_one] using
    actual_static_polarization_sigma_four_price event transfer 1 (by norm_num) le_rfl i j
end LowEnergy.GaussComposite.ActualDressedCubicPriceAudit

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

elab "#audit_dressed_cubic_price" : command => do
  let env ← getEnv
  let modules := env.header.moduleNames
  let owner := fun name => (env.getModuleIdxFor? name).map fun i => modules[i.toNat]!
  let candidates := #[`H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualDressedUpperCurrent,`H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.FiniteFlagVariationPrice,`H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualDressedGradedSlopePrice,`H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualDressedCubicNoetherPrice,`H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualDressedCubicLaplacePrice,`H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualDressedCubicStaticPrice]
  let owned := env.constants.toList.filterMap fun (name, _) =>
    if (owner name).any candidates.contains then some name else none
  let mouths := #[
    ``LowEnergy.GaussComposite.ActualDressedGradedPrice.upperOne,
    ``LowEnergy.GaussComposite.ActualDressedGradedPrice.upperTwo,
    ``LowEnergy.GaussComposite.ActualDressedGradedPrice.actual_joint_Y_upper,
    ``LowEnergy.GaussComposite.ActualDressedGradedPrice.actual_interaction_upper,
    ``LowEnergy.GaussComposite.ActualDressedGradedPrice.actual_joint_C_upper,
    ``LowEnergy.GaussComposite.ActualDressedGradedPrice.actual_joint_generator_upper,
    ``LowEnergy.GaussComposite.ActualDressedGradedPrice.actual_joint_current_upper,
    ``LowEnergy.GaussComposite.ActualDressedGradedPrice.ordered_one_range,
    ``LowEnergy.GaussComposite.ActualDressedGradedPrice.prefix_one_range,
    ``LowEnergy.GaussComposite.ActualDressedGradedPrice.prefix_two_range,
    ``LowEnergy.GaussComposite.ActualDressedGradedPrice.finite_flag_variation_price,
    ``LowEnergy.GaussComposite.ActualDressedGradedPrice.actual_time_upper_return,
    ``LowEnergy.GaussComposite.ActualDressedGradedPrice.actual_timeSlope_N2_cubic_price,
    ``LowEnergy.GaussComposite.ActualDressedGradedPrice.actual_created_timeSlope_cubic_price,
    ``LowEnergy.GaussComposite.ActualDressedGradedPrice.actual_timeSlope_N2_cubic_growth,
    ``LowEnergy.GaussComposite.ActualDressedGradedPrice.actual_timeSlope_N1_cubic_growth,
    ``LowEnergy.GaussComposite.ActualDressedCubicPrice.completeCubicNoetherPrice,
    ``LowEnergy.GaussComposite.ActualDressedCubicPrice.actual_complete_noether_cubic_jet_price,
    ``LowEnergy.GaussComposite.ActualDressedCubicPrice.complete_cubic_noether_price_nonneg,
    ``LowEnergy.GaussComposite.ActualDressedCubicPrice.cubic_laplace_integrable,
    ``LowEnergy.GaussComposite.ActualDressedCubicPrice.cubic_laplace_sigma_four_price,
    ``LowEnergy.GaussComposite.ActualDressedCubicPrice.actual_static_polarization_cubic_laplace_price,
    ``LowEnergy.GaussComposite.ActualDressedCubicPrice.observedCubicStaticSourcePrice,
    ``LowEnergy.GaussComposite.ActualDressedCubicPrice.observed_cubic_static_source_price_nonneg,
    ``LowEnergy.GaussComposite.ActualDressedCubicPrice.actual_static_polarization_sigma_four_price]
  for name in mouths do
    unless owned.contains name do throwError m!"MISSING_MOUTH {name}"
  let tests := #[
    ``LowEnergy.GaussComposite.ActualDressedCubicPriceAudit.checked_actual_joint_Y_upper,
    ``LowEnergy.GaussComposite.ActualDressedCubicPriceAudit.checked_actual_interaction_upper,
    ``LowEnergy.GaussComposite.ActualDressedCubicPriceAudit.checked_actual_joint_C_upper,
    ``LowEnergy.GaussComposite.ActualDressedCubicPriceAudit.checked_actual_joint_generator_upper,
    ``LowEnergy.GaussComposite.ActualDressedCubicPriceAudit.checked_actual_joint_current_upper,
    ``LowEnergy.GaussComposite.ActualDressedCubicPriceAudit.checked_ordered_one_range,
    ``LowEnergy.GaussComposite.ActualDressedCubicPriceAudit.checked_prefix_one_range,
    ``LowEnergy.GaussComposite.ActualDressedCubicPriceAudit.checked_prefix_two_range,
    ``LowEnergy.GaussComposite.ActualDressedCubicPriceAudit.checked_finite_flag_variation_price,
    ``LowEnergy.GaussComposite.ActualDressedCubicPriceAudit.checked_actual_time_upper_return,
    ``LowEnergy.GaussComposite.ActualDressedCubicPriceAudit.checked_actual_timeSlope_N2_cubic_price,
    ``LowEnergy.GaussComposite.ActualDressedCubicPriceAudit.checked_actual_created_timeSlope_cubic_price,
    ``LowEnergy.GaussComposite.ActualDressedCubicPriceAudit.checked_actual_timeSlope_N2_cubic_growth,
    ``LowEnergy.GaussComposite.ActualDressedCubicPriceAudit.checked_actual_timeSlope_N1_cubic_growth,
    ``LowEnergy.GaussComposite.ActualDressedCubicPriceAudit.checked_actual_complete_noether_cubic_jet_price,
    ``LowEnergy.GaussComposite.ActualDressedCubicPriceAudit.checked_complete_cubic_noether_price_nonneg,
    ``LowEnergy.GaussComposite.ActualDressedCubicPriceAudit.checked_cubic_laplace_integrable,
    ``LowEnergy.GaussComposite.ActualDressedCubicPriceAudit.checked_cubic_laplace_sigma_four_price,
    ``LowEnergy.GaussComposite.ActualDressedCubicPriceAudit.checked_actual_static_polarization_cubic_laplace_price,
    ``LowEnergy.GaussComposite.ActualDressedCubicPriceAudit.checked_observed_cubic_static_source_price_nonneg,
    ``LowEnergy.GaussComposite.ActualDressedCubicPriceAudit.checked_actual_static_polarization_sigma_four_price,
    ``LowEnergy.GaussComposite.ActualDressedCubicPriceAudit.actual_event_nonempty,
    ``LowEnergy.GaussComposite.ActualDressedCubicPriceAudit.actual_unit_nonzero,
    ``LowEnergy.GaussComposite.ActualDressedCubicPriceAudit.same_actual_created_cubic_slope,
    ``LowEnergy.GaussComposite.ActualDressedCubicPriceAudit.same_complete_original_cubic_jet,
    ``LowEnergy.GaussComposite.ActualDressedCubicPriceAudit.same_original_static_entry_unit_damping]
  let direct := #[
    (``LowEnergy.GaussComposite.ActualDressedGradedPrice.actual_joint_current_upper,#[
    ``LowEnergy.GaussComposite.ActualDressedGradedPrice.actual_joint_generator_upper,
    ``LowEnergy.PreparationVacuumJointFieldResponse.jointGenerator_C2]),
    (``LowEnergy.GaussComposite.ActualDressedGradedPrice.actual_interaction_upper,#[
    ``LowEnergy.GaussComposite.ActualDressedNumberSector.actual_interaction_N2G0_range,
    ``LowEnergy.GaussComposite.ActualDressedNumberSector.actual_interaction_N2G1_range,
    ``LowEnergy.GaussComposite.ActualDressedNumberSector.actual_interaction_N2G2_zero]),
    (``LowEnergy.GaussComposite.ActualDressedGradedPrice.prefix_one_range,#[
    ``LowEnergy.GaussComposite.ActualDressedGradedPrice.ordered_one_range]),
    (``LowEnergy.GaussComposite.ActualDressedGradedPrice.actual_time_upper_return,#[
    ``LowEnergy.GaussComposite.ActualDressedNumberSector.actual_time_N2_grade_return]),
    (``LowEnergy.GaussComposite.ActualDressedGradedPrice.actual_timeSlope_N2_cubic_price,#[
    ``LowEnergy.GaussComposite.ActualDressedGradedPrice.actual_joint_current_upper,
    ``LowEnergy.GaussComposite.ActualDressedGradedPrice.finite_flag_variation_price,
    ``LowEnergy.GaussComposite.ActualDressedGradedPrice.prefix_one_range,
    ``LowEnergy.GaussComposite.ActualDressedGradedPrice.prefix_two_range,
    ``LowEnergy.GaussComposite.ActualDressedGradedPrice.actual_time_upper_return,
    ``LowEnergy.GaussComposite.ActualDressedPreparedPrice.actual_time_N2_price]),
    (``LowEnergy.GaussComposite.ActualDressedGradedPrice.actual_created_timeSlope_cubic_price,#[
    ``LowEnergy.GaussComposite.ActualDressedGradedPrice.actual_timeSlope_N2_cubic_price,
    ``LowEnergy.GaussComposite.ActualDressedSourcePreparation.source_dressed_unit_norm,
    ``LowEnergy.GaussComposite.ActualDressedNumberSector.actual_created_unit_N2]),
    (``LowEnergy.GaussComposite.ActualDressedGradedPrice.actual_timeSlope_N2_cubic_growth,#[
    ``LowEnergy.GaussComposite.ActualDressedGradedPrice.actual_timeSlope_N2_cubic_price]),
    (``LowEnergy.GaussComposite.ActualDressedGradedPrice.actual_timeSlope_N1_cubic_growth,#[
    ``LowEnergy.GaussComposite.ActualDressedN1Price.actual_timeSlope_N1_price]),
    (``LowEnergy.GaussComposite.ActualDressedCubicPrice.actual_complete_noether_cubic_jet_price,#[
    ``LowEnergy.GaussComposite.ActualDressedCompletePrice.actual_left_free_read_germ,
    ``LowEnergy.GaussComposite.ActualDressedGradedPrice.actual_timeSlope_N2_cubic_growth,
    ``LowEnergy.GaussComposite.ActualDressedGradedPrice.actual_timeSlope_N1_cubic_growth,
    ``LowEnergy.GaussComposite.ActualDressedLeftFreeJet.free_time_direction,
    ``LowEnergy.GaussComposite.ActualDressedLeftFreeJet.free_green_direction,
    ``LowEnergy.GaussComposite.ActualDressedNoether.dressed_noether_action_derivative]),
    (``LowEnergy.GaussComposite.ActualDressedCubicPrice.actual_static_polarization_cubic_laplace_price,#[
    ``LowEnergy.GaussComposite.ActualDressedCubicPrice.actual_complete_noether_cubic_jet_price,
    ``LowEnergy.GaussComposite.ActualDressedFiniteStaticRead.dressed_static_polarization_finite,
    ``LowEnergy.GaussComposite.ActualDressedFiniteStaticRead.finite_static_integrand_integrable]),
    (``LowEnergy.GaussComposite.ActualDressedCubicPrice.actual_static_polarization_sigma_four_price,#[
    ``LowEnergy.GaussComposite.ActualDressedCubicPrice.actual_static_polarization_cubic_laplace_price,
    ``LowEnergy.GaussComposite.ActualDressedCubicPrice.cubic_laplace_sigma_four_price,
    ``LowEnergy.GaussComposite.ActualDressedCubicPrice.complete_cubic_noether_price_nonneg]),
    (``LowEnergy.GaussComposite.ActualDressedGradedPrice.actual_joint_generator_upper,#[
    ``LowEnergy.GaussComposite.ActualDressedGradedPrice.actual_joint_Y_upper,
    ``LowEnergy.GaussComposite.ActualDressedGradedPrice.actual_joint_C_upper])]
  for (mouth,required) in direct do packageCertRequire env mouth required
  let testProducers := #[
    ``LowEnergy.GaussComposite.ActualDressedGradedPrice.actual_joint_Y_upper,
    ``LowEnergy.GaussComposite.ActualDressedGradedPrice.actual_interaction_upper,
    ``LowEnergy.GaussComposite.ActualDressedGradedPrice.actual_joint_C_upper,
    ``LowEnergy.GaussComposite.ActualDressedGradedPrice.actual_joint_generator_upper,
    ``LowEnergy.GaussComposite.ActualDressedGradedPrice.actual_joint_current_upper,
    ``LowEnergy.GaussComposite.ActualDressedGradedPrice.ordered_one_range,
    ``LowEnergy.GaussComposite.ActualDressedGradedPrice.prefix_one_range,
    ``LowEnergy.GaussComposite.ActualDressedGradedPrice.prefix_two_range,
    ``LowEnergy.GaussComposite.ActualDressedGradedPrice.finite_flag_variation_price,
    ``LowEnergy.GaussComposite.ActualDressedGradedPrice.actual_time_upper_return,
    ``LowEnergy.GaussComposite.ActualDressedGradedPrice.actual_timeSlope_N2_cubic_price,
    ``LowEnergy.GaussComposite.ActualDressedGradedPrice.actual_created_timeSlope_cubic_price,
    ``LowEnergy.GaussComposite.ActualDressedGradedPrice.actual_timeSlope_N2_cubic_growth,
    ``LowEnergy.GaussComposite.ActualDressedGradedPrice.actual_timeSlope_N1_cubic_growth,
    ``LowEnergy.GaussComposite.ActualDressedCubicPrice.actual_complete_noether_cubic_jet_price,
    ``LowEnergy.GaussComposite.ActualDressedCubicPrice.complete_cubic_noether_price_nonneg,
    ``LowEnergy.GaussComposite.ActualDressedCubicPrice.cubic_laplace_integrable,
    ``LowEnergy.GaussComposite.ActualDressedCubicPrice.cubic_laplace_sigma_four_price,
    ``LowEnergy.GaussComposite.ActualDressedCubicPrice.actual_static_polarization_cubic_laplace_price,
    ``LowEnergy.GaussComposite.ActualDressedCubicPrice.observed_cubic_static_source_price_nonneg,
    ``LowEnergy.GaussComposite.ActualDressedCubicPrice.actual_static_polarization_sigma_four_price]
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
  if let some path ← liftIO (IO.getEnv "ALPHA_DRESSED_CUBIC_PRICE_AUDIT_OUTPUT") then
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
  logInfo m!"DRESSED_CUBIC_PRICE_PASS public={mouths.size} owned={owned.length} tests={tests.size} nodes={all.size} anchors={anchors.size} direct={direct.size} opaque_all_read={opaques} axioms={axioms} unknown=0 unsafe=0 partial=0"
#audit_dressed_cubic_price
#print axioms LowEnergy.GaussComposite.ActualDressedGradedPrice.actual_joint_Y_upper
#print axioms LowEnergy.GaussComposite.ActualDressedGradedPrice.actual_interaction_upper
#print axioms LowEnergy.GaussComposite.ActualDressedGradedPrice.actual_joint_C_upper
#print axioms LowEnergy.GaussComposite.ActualDressedGradedPrice.actual_joint_generator_upper
#print axioms LowEnergy.GaussComposite.ActualDressedGradedPrice.actual_joint_current_upper
#print axioms LowEnergy.GaussComposite.ActualDressedGradedPrice.ordered_one_range
#print axioms LowEnergy.GaussComposite.ActualDressedGradedPrice.prefix_one_range
#print axioms LowEnergy.GaussComposite.ActualDressedGradedPrice.prefix_two_range
#print axioms LowEnergy.GaussComposite.ActualDressedGradedPrice.finite_flag_variation_price
#print axioms LowEnergy.GaussComposite.ActualDressedGradedPrice.actual_time_upper_return
#print axioms LowEnergy.GaussComposite.ActualDressedGradedPrice.actual_timeSlope_N2_cubic_price
#print axioms LowEnergy.GaussComposite.ActualDressedGradedPrice.actual_created_timeSlope_cubic_price
#print axioms LowEnergy.GaussComposite.ActualDressedGradedPrice.actual_timeSlope_N2_cubic_growth
#print axioms LowEnergy.GaussComposite.ActualDressedGradedPrice.actual_timeSlope_N1_cubic_growth
#print axioms LowEnergy.GaussComposite.ActualDressedCubicPrice.actual_complete_noether_cubic_jet_price
#print axioms LowEnergy.GaussComposite.ActualDressedCubicPrice.complete_cubic_noether_price_nonneg
#print axioms LowEnergy.GaussComposite.ActualDressedCubicPrice.cubic_laplace_integrable
#print axioms LowEnergy.GaussComposite.ActualDressedCubicPrice.cubic_laplace_sigma_four_price
#print axioms LowEnergy.GaussComposite.ActualDressedCubicPrice.actual_static_polarization_cubic_laplace_price
#print axioms LowEnergy.GaussComposite.ActualDressedCubicPrice.observed_cubic_static_source_price_nonneg
#print axioms LowEnergy.GaussComposite.ActualDressedCubicPrice.actual_static_polarization_sigma_four_price
