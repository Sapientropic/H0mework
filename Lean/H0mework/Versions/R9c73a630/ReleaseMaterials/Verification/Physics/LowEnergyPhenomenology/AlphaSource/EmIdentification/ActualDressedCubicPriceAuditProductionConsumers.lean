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

