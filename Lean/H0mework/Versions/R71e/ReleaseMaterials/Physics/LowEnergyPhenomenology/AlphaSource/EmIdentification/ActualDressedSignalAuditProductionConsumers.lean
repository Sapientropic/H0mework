import H0mework.Versions.R71e.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualDressedSignalOperator
import H0mework.Versions.R71e.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualDressedSignalPrice
import H0mework.Versions.R71e.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualDressedSignalCausal
import H0mework.Versions.R71e.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualDressedSignalTensor

import Lean.Elab.Command
import Lean.Util.FoldConsts
import Lean.Util.CollectAxioms
set_option autoImplicit false
set_option maxHeartbeats 12000000
set_option maxRecDepth 32768
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.GaussComposite.ActualDressedSignalAudit
elab "checked_dressed_euler_observer_priceContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualDressedSignal.dressed_euler_observer_price).type
theorem checked_dressed_euler_observer_price : checked_dressed_euler_observer_priceContract := @LowEnergy.GaussComposite.ActualDressedSignal.dressed_euler_observer_price

elab "checked_dressed_signal_operator_actualContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualDressedSignal.dressed_signal_operator_actual).type
theorem checked_dressed_signal_operator_actual : checked_dressed_signal_operator_actualContract := @LowEnergy.GaussComposite.ActualDressedSignal.dressed_signal_operator_actual

elab "checked_dressed_signal_operator_continuousContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualDressedSignal.dressed_signal_operator_continuous).type
theorem checked_dressed_signal_operator_continuous : checked_dressed_signal_operator_continuousContract := @LowEnergy.GaussComposite.ActualDressedSignal.dressed_signal_operator_continuous

elab "checked_dressed_signal_quadrature_actualContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualDressedSignal.dressed_signal_quadrature_actual).type
theorem checked_dressed_signal_quadrature_actual : checked_dressed_signal_quadrature_actualContract := @LowEnergy.GaussComposite.ActualDressedSignal.dressed_signal_quadrature_actual

elab "checked_dressed_signal_quadrature_continuousContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualDressedSignal.dressed_signal_quadrature_continuous).type
theorem checked_dressed_signal_quadrature_continuous : checked_dressed_signal_quadrature_continuousContract := @LowEnergy.GaussComposite.ActualDressedSignal.dressed_signal_quadrature_continuous

elab "checked_dressed_signal_quadrature_phaseContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualDressedSignal.dressed_signal_quadrature_phase).type
theorem checked_dressed_signal_quadrature_phase : checked_dressed_signal_quadrature_phaseContract := @LowEnergy.GaussComposite.ActualDressedSignal.dressed_signal_quadrature_phase

elab "checked_dressed_signal_duration_positiveContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualDressedSignal.dressed_signal_duration_positive).type
theorem checked_dressed_signal_duration_positive : checked_dressed_signal_duration_positiveContract := @LowEnergy.GaussComposite.ActualDressedSignal.dressed_signal_duration_positive

elab "checked_dressed_signal_nonlinear_generatedContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualDressedSignal.dressed_signal_nonlinear_generated).type
theorem checked_dressed_signal_nonlinear_generated : checked_dressed_signal_nonlinear_generatedContract := @LowEnergy.GaussComposite.ActualDressedSignal.dressed_signal_nonlinear_generated

elab "checked_dressed_signal_coefficient_nonnegativeContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualDressedSignal.dressed_signal_coefficient_nonnegative).type
theorem checked_dressed_signal_coefficient_nonnegative : checked_dressed_signal_coefficient_nonnegativeContract := @LowEnergy.GaussComposite.ActualDressedSignal.dressed_signal_coefficient_nonnegative

elab "checked_dressed_signal_operator_priceContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualDressedSignal.dressed_signal_operator_price).type
theorem checked_dressed_signal_operator_price : checked_dressed_signal_operator_priceContract := @LowEnergy.GaussComposite.ActualDressedSignal.dressed_signal_operator_price

elab "checked_dressed_signal_quadrature_priceContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualDressedSignal.dressed_signal_quadrature_price).type
theorem checked_dressed_signal_quadrature_price : checked_dressed_signal_quadrature_priceContract := @LowEnergy.GaussComposite.ActualDressedSignal.dressed_signal_quadrature_price

elab "checked_dressed_signal_weighted_priceContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualDressedSignal.dressed_signal_weighted_price).type
theorem checked_dressed_signal_weighted_price : checked_dressed_signal_weighted_priceContract := @LowEnergy.GaussComposite.ActualDressedSignal.dressed_signal_weighted_price

elab "checked_dressed_signal_weighted_continuousContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualDressedSignal.dressed_signal_weighted_continuous).type
theorem checked_dressed_signal_weighted_continuous : checked_dressed_signal_weighted_continuousContract := @LowEnergy.GaussComposite.ActualDressedSignal.dressed_signal_weighted_continuous

elab "checked_dressed_signal_weighted_integrableContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualDressedSignal.dressed_signal_weighted_integrable).type
theorem checked_dressed_signal_weighted_integrable : checked_dressed_signal_weighted_integrableContract := @LowEnergy.GaussComposite.ActualDressedSignal.dressed_signal_weighted_integrable

elab "checked_dressed_signal_window_actualContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualDressedSignal.dressed_signal_window_actual).type
theorem checked_dressed_signal_window_actual : checked_dressed_signal_window_actualContract := @LowEnergy.GaussComposite.ActualDressedSignal.dressed_signal_window_actual

elab "checked_dressed_signal_window_noetherContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualDressedSignal.dressed_signal_window_noether).type
theorem checked_dressed_signal_window_noether : checked_dressed_signal_window_noetherContract := @LowEnergy.GaussComposite.ActualDressedSignal.dressed_signal_window_noether

elab "checked_dressed_signal_window_operator_normContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualDressedSignal.dressed_signal_window_operator_norm).type
theorem checked_dressed_signal_window_operator_norm : checked_dressed_signal_window_operator_normContract := @LowEnergy.GaussComposite.ActualDressedSignal.dressed_signal_window_operator_norm

elab "checked_dressed_signal_half_operator_tailContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualDressedSignal.dressed_signal_half_operator_tail).type
theorem checked_dressed_signal_half_operator_tail : checked_dressed_signal_half_operator_tailContract := @LowEnergy.GaussComposite.ActualDressedSignal.dressed_signal_half_operator_tail

elab "checked_dressed_signal_complex_originalContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualDressedSignal.dressed_signal_complex_original).type
theorem checked_dressed_signal_complex_original : checked_dressed_signal_complex_originalContract := @LowEnergy.GaussComposite.ActualDressedSignal.dressed_signal_complex_original

elab "checked_dressed_signal_matrix_actualContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualDressedSignal.dressed_signal_matrix_actual).type
theorem checked_dressed_signal_matrix_actual : checked_dressed_signal_matrix_actualContract := @LowEnergy.GaussComposite.ActualDressedSignal.dressed_signal_matrix_actual

elab "checked_dressed_signal_raw_euler_generatedContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualDressedSignal.dressed_signal_raw_euler_generated).type
theorem checked_dressed_signal_raw_euler_generated : checked_dressed_signal_raw_euler_generatedContract := @LowEnergy.GaussComposite.ActualDressedSignal.dressed_signal_raw_euler_generated

open SaturationMonoid.PhysicsCore SaturationMonoid.PhysicsCore.LowEnergy
open CanonicalGradedSpatialSource GaussCoreHilbert
open PreparationVacuumMixedFieldReturn PreparationVacuumPhysicalFeedback
open PreparationVacuumActionFieldLift PreparationVacuumGaugeSourceInjection
open PreparationVacuumCurrentSignalOperator PreparationVacuumCurrentSignalRealization
open SourcePropagationMotherEulerKernel SourcePropagationNativeEulerHistory SourcePropagationNoetherTime
open SourcePropagationMotherResidualDirections
open ActualDressedFullCoulomb ActualDressedNoether ActualDressedSourcePreparation
open PreparationVacuumSourcePreparedResponse
open SourceGraph MeasureTheory Filter Set
open PreparationVacuumMixedFieldReturn
open PreparationVacuumJointFieldResponse PreparationVacuumRawJointFeedback PreparationVacuumPropagationPencil
open PreparationVacuumPhysicalFeedback PreparationVacuumActionFieldLift
open PreparationVacuumCurrentSignalOperator PreparationVacuumGaugeSourceInjection
open ActualDressedFullCoulomb ActualDressedNoether
open SourceFiniteUnitary PreparationVacuumPhysicalTailPrice
open CanonicalGradedSpatialSource PreparationVacuumPhysicalFeedback PreparationVacuumGaugeSourceInjection
open PreparationVacuumActionFieldLift PreparationVacuumOriginalGreenFeedback
open PreparationVacuumPhysicalHalfAxis
open SourcePropagationMotherEulerKernel
open Filter Set MeasureTheory
open SaturationMonoid.PhysicsCore StageNineHolonomicField ProofFreeRicherAnholonomicSource
open CanonicalGradedSpatialSource PreparationVacuumMixedFieldReturn PreparationVacuumPhysicalFeedback
open PreparationVacuumGaugeSourceInjection PreparationVacuumActionFieldLift
open SourcePropagationMotherEulerKernel SourcePropagationMotherResidualDirections
open SourcePropagationNativeActionHessian
open ActualDressedSignal
open scoped Matrix BigOperators Topology InnerProductSpace Interval
attribute [local irreducible] dressedSignalOperator dressedSignalQuadrature dressedSignalNonlinear
  dressedSignalComplexOperator dressedSignalMatrix dressedEulerObserver dressedNoetherJet
  dressedSignalRawEuler nativeHessian

theorem actual_signal_window_nonempty (event : DressedEvent) (transfer : PhysicalMomentum)
    (p : Fin 4→ℂ) (a : SignalAmplitude) :
    ∃ T : ℝ,0<T ∧ T<dressedSignalDuration event transfer p a := by
  exact ⟨dressedSignalDuration event transfer p a/2,
    half_pos (dressed_signal_duration_positive event transfer p a),
    half_lt_self (dressed_signal_duration_positive event transfer p a)⟩

theorem actual_zero_amplitude (event : DressedEvent) (transfer : PhysicalMomentum)
    (p : Fin 4→ℂ) (t : ℝ) : dressedSignalQuadrature event transfer p t 0=0 :=
  map_zero (dressedSignalQuadrature event transfer p t)

theorem actual_zero_window (event : DressedEvent) (transfer : PhysicalMomentum)
    (p : Fin 4→ℂ) (lambda : ℂ) : dressedSignalWindow event transfer p lambda 0=0 := by
  simp only [dressedSignalWindow,intervalIntegral.integral_same]

theorem actual_amplitude_tail_price (event : DressedEvent) (transfer : PhysicalMomentum)
    (p : Fin 4→ℂ) (lambda : ℂ) (off : sourceClockGrowth p<lambda.re)
    (T : ℝ) (future : 0≤T) (a : SignalAmplitude) :
    ‖dressedSignalHalfOperator event transfer p lambda a-dressedSignalWindow event transfer p lambda T a‖ ≤
      dressedSignalTailPrice event transfer p lambda T*‖a‖ := by
  calc
    _=‖(dressedSignalHalfOperator event transfer p lambda-dressedSignalWindow event transfer p lambda T) a‖ := by
      rw [sub_apply]
    _≤‖dressedSignalHalfOperator event transfer p lambda-dressedSignalWindow event transfer p lambda T‖*‖a‖ :=
      (dressedSignalHalfOperator event transfer p lambda-dressedSignalWindow event transfer p lambda T).le_opNorm a
    _≤dressedSignalTailPrice event transfer p lambda T*‖a‖ :=
      mul_le_mul_of_nonneg_right (dressed_signal_half_operator_tail event transfer p lambda off T future) (norm_nonneg a)

end LowEnergy.GaussComposite.ActualDressedSignalAudit

