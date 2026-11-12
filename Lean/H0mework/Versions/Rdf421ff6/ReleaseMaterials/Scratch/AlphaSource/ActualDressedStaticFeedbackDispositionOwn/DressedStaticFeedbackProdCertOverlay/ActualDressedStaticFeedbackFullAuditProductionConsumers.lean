import H0mework.Versions.Rdf421ff6.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualDressedStaticFeedback
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualDressedStaticCurrentCircuit
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualDressedStaticLongrangeReturn

import Lean.Elab.Command
import Lean.Util.FoldConsts
import Lean.Util.CollectAxioms
set_option autoImplicit false
set_option maxHeartbeats 12000000
set_option maxRecDepth 32768
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.GaussComposite.ActualDressedStaticFeedbackFullAudit
elab "checked_actual_static_rayContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualDressedStaticFeedback.actual_static_ray).type
theorem checked_actual_static_ray : checked_actual_static_rayContract := @LowEnergy.GaussComposite.ActualDressedStaticFeedback.actual_static_ray

elab "checked_actual_corrected_static_feedbackContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualDressedStaticFeedback.actual_corrected_static_feedback).type
theorem checked_actual_corrected_static_feedback : checked_actual_corrected_static_feedbackContract := @LowEnergy.GaussComposite.ActualDressedStaticFeedback.actual_corrected_static_feedback

elab "checked_actual_corrected_static_nineContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualDressedStaticFeedback.actual_corrected_static_nine).type
theorem checked_actual_corrected_static_nine : checked_actual_corrected_static_nineContract := @LowEnergy.GaussComposite.ActualDressedStaticFeedback.actual_corrected_static_nine

elab "checked_actual_static_current_circuitContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualDressedStaticFeedback.actual_static_current_circuit).type
theorem checked_actual_static_current_circuit : checked_actual_static_current_circuitContract := @LowEnergy.GaussComposite.ActualDressedStaticFeedback.actual_static_current_circuit

elab "checked_actual_native_current_spatial_returnContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualDressedStaticFeedback.actual_native_current_spatial_return).type
theorem checked_actual_native_current_spatial_return : checked_actual_native_current_spatial_returnContract := @LowEnergy.GaussComposite.ActualDressedStaticFeedback.actual_native_current_spatial_return

elab "checked_actual_native_current_uniform_priceContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualDressedStaticFeedback.actual_native_current_uniform_price).type
theorem checked_actual_native_current_uniform_price : checked_actual_native_current_uniform_priceContract := @LowEnergy.GaussComposite.ActualDressedStaticFeedback.actual_native_current_uniform_price

elab "checked_actual_feedback_null_damping_returnContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualDressedStaticFeedback.actual_feedback_null_damping_return).type
theorem checked_actual_feedback_null_damping_return : checked_actual_feedback_null_damping_returnContract := @LowEnergy.GaussComposite.ActualDressedStaticFeedback.actual_feedback_null_damping_return

elab "checked_actual_feedback_null_spatial_returnContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualDressedStaticFeedback.actual_feedback_null_spatial_return).type
theorem checked_actual_feedback_null_spatial_return : checked_actual_feedback_null_spatial_returnContract := @LowEnergy.GaussComposite.ActualDressedStaticFeedback.actual_feedback_null_spatial_return

elab "checked_actual_feedback_null_source_priceContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualDressedStaticFeedback.actual_feedback_null_source_price).type
theorem checked_actual_feedback_null_source_price : checked_actual_feedback_null_source_priceContract := @LowEnergy.GaussComposite.ActualDressedStaticFeedback.actual_feedback_null_source_price

elab "checked_actual_longrange_coefficient_balanceContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualDressedStaticFeedback.actual_longrange_coefficient_balance).type
theorem checked_actual_longrange_coefficient_balance : checked_actual_longrange_coefficient_balanceContract := @LowEnergy.GaussComposite.ActualDressedStaticFeedback.actual_longrange_coefficient_balance

end LowEnergy.GaussComposite.ActualDressedStaticFeedbackFullAudit

