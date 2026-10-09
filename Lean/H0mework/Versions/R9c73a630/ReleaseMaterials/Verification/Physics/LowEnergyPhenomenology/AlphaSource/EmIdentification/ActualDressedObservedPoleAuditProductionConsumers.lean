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

