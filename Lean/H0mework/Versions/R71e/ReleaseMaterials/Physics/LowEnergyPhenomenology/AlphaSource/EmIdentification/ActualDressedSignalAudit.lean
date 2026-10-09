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

elab "#audit_dressed_signal" : command => do
  let env ← getEnv
  let modules := env.header.moduleNames
  let owner := fun name => (env.getModuleIdxFor? name).map fun i => modules[i.toNat]!
  let candidates := #[`H0mework.Versions.R71e.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualDressedSignalOperator,`H0mework.Versions.R71e.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualDressedSignalPrice,`H0mework.Versions.R71e.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualDressedSignalCausal,`H0mework.Versions.R71e.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualDressedSignalTensor]
  let owned := env.constants.toList.filterMap fun (name, _) =>
    if (owner name).any candidates.contains then some name else none
  let mouths := #[
    ``LowEnergy.GaussComposite.ActualDressedSignal.dressed_euler_observer_price,
    ``LowEnergy.GaussComposite.ActualDressedSignal.dressedSignalOperator,
    ``LowEnergy.GaussComposite.ActualDressedSignal.dressed_signal_operator_actual,
    ``LowEnergy.GaussComposite.ActualDressedSignal.dressed_signal_operator_continuous,
    ``LowEnergy.GaussComposite.ActualDressedSignal.dressedSignalQuadrature,
    ``LowEnergy.GaussComposite.ActualDressedSignal.dressed_signal_quadrature_actual,
    ``LowEnergy.GaussComposite.ActualDressedSignal.dressed_signal_quadrature_continuous,
    ``LowEnergy.GaussComposite.ActualDressedSignal.dressed_signal_quadrature_phase,
    ``LowEnergy.GaussComposite.ActualDressedSignal.dressedSignalDuration,
    ``LowEnergy.GaussComposite.ActualDressedSignal.dressed_signal_duration_positive,
    ``LowEnergy.GaussComposite.ActualDressedSignal.dressedSignalNonlinear,
    ``LowEnergy.GaussComposite.ActualDressedSignal.dressed_signal_nonlinear_generated,
    ``LowEnergy.GaussComposite.ActualDressedSignal.dressedSignalLinearCoefficient,
    ``LowEnergy.GaussComposite.ActualDressedSignal.dressedSignalConstantCoefficient,
    ``LowEnergy.GaussComposite.ActualDressedSignal.dressed_signal_coefficient_nonnegative,
    ``LowEnergy.GaussComposite.ActualDressedSignal.dressed_signal_operator_price,
    ``LowEnergy.GaussComposite.ActualDressedSignal.dressed_signal_quadrature_price,
    ``LowEnergy.GaussComposite.ActualDressedSignal.dressedSignalCausalCoefficient,
    ``LowEnergy.GaussComposite.ActualDressedSignal.dressedSignalWeighted,
    ``LowEnergy.GaussComposite.ActualDressedSignal.dressed_signal_weighted_price,
    ``LowEnergy.GaussComposite.ActualDressedSignal.dressed_signal_weighted_continuous,
    ``LowEnergy.GaussComposite.ActualDressedSignal.dressed_signal_weighted_integrable,
    ``LowEnergy.GaussComposite.ActualDressedSignal.dressedSignalWindow,
    ``LowEnergy.GaussComposite.ActualDressedSignal.dressedSignalHalfOperator,
    ``LowEnergy.GaussComposite.ActualDressedSignal.dressed_signal_window_actual,
    ``LowEnergy.GaussComposite.ActualDressedSignal.dressed_signal_window_noether,
    ``LowEnergy.GaussComposite.ActualDressedSignal.dressed_signal_window_operator_norm,
    ``LowEnergy.GaussComposite.ActualDressedSignal.dressedSignalTailPrice,
    ``LowEnergy.GaussComposite.ActualDressedSignal.dressed_signal_half_operator_tail,
    ``LowEnergy.GaussComposite.ActualDressedSignal.dressedSignalComplexOperator,
    ``LowEnergy.GaussComposite.ActualDressedSignal.dressed_signal_complex_original,
    ``LowEnergy.GaussComposite.ActualDressedSignal.dressedSignalMatrix,
    ``LowEnergy.GaussComposite.ActualDressedSignal.dressed_signal_matrix_actual,
    ``LowEnergy.GaussComposite.ActualDressedSignal.dressedSignalRawEuler,
    ``LowEnergy.GaussComposite.ActualDressedSignal.dressed_signal_raw_euler_generated]
  for name in mouths do
    unless owned.contains name do throwError m!"MISSING_MOUTH {name}"
  let tests := #[
    ``LowEnergy.GaussComposite.ActualDressedSignalAudit.checked_dressed_euler_observer_price,
    ``LowEnergy.GaussComposite.ActualDressedSignalAudit.checked_dressed_signal_operator_actual,
    ``LowEnergy.GaussComposite.ActualDressedSignalAudit.checked_dressed_signal_operator_continuous,
    ``LowEnergy.GaussComposite.ActualDressedSignalAudit.checked_dressed_signal_quadrature_actual,
    ``LowEnergy.GaussComposite.ActualDressedSignalAudit.checked_dressed_signal_quadrature_continuous,
    ``LowEnergy.GaussComposite.ActualDressedSignalAudit.checked_dressed_signal_quadrature_phase,
    ``LowEnergy.GaussComposite.ActualDressedSignalAudit.checked_dressed_signal_duration_positive,
    ``LowEnergy.GaussComposite.ActualDressedSignalAudit.checked_dressed_signal_nonlinear_generated,
    ``LowEnergy.GaussComposite.ActualDressedSignalAudit.checked_dressed_signal_coefficient_nonnegative,
    ``LowEnergy.GaussComposite.ActualDressedSignalAudit.checked_dressed_signal_operator_price,
    ``LowEnergy.GaussComposite.ActualDressedSignalAudit.checked_dressed_signal_quadrature_price,
    ``LowEnergy.GaussComposite.ActualDressedSignalAudit.checked_dressed_signal_weighted_price,
    ``LowEnergy.GaussComposite.ActualDressedSignalAudit.checked_dressed_signal_weighted_continuous,
    ``LowEnergy.GaussComposite.ActualDressedSignalAudit.checked_dressed_signal_weighted_integrable,
    ``LowEnergy.GaussComposite.ActualDressedSignalAudit.checked_dressed_signal_window_actual,
    ``LowEnergy.GaussComposite.ActualDressedSignalAudit.checked_dressed_signal_window_noether,
    ``LowEnergy.GaussComposite.ActualDressedSignalAudit.checked_dressed_signal_window_operator_norm,
    ``LowEnergy.GaussComposite.ActualDressedSignalAudit.checked_dressed_signal_half_operator_tail,
    ``LowEnergy.GaussComposite.ActualDressedSignalAudit.checked_dressed_signal_complex_original,
    ``LowEnergy.GaussComposite.ActualDressedSignalAudit.checked_dressed_signal_matrix_actual,
    ``LowEnergy.GaussComposite.ActualDressedSignalAudit.checked_dressed_signal_raw_euler_generated,
    ``LowEnergy.GaussComposite.ActualDressedSignalAudit.actual_signal_window_nonempty,
    ``LowEnergy.GaussComposite.ActualDressedSignalAudit.actual_zero_amplitude,
    ``LowEnergy.GaussComposite.ActualDressedSignalAudit.actual_zero_window,
    ``LowEnergy.GaussComposite.ActualDressedSignalAudit.actual_amplitude_tail_price]
  let direct := #[
    (``LowEnergy.GaussComposite.ActualDressedSignal.dressed_euler_observer_price,#[
    ``LowEnergy.GaussComposite.ActualDressedSourcePreparation.source_dressed_unit_norm,
    ``LowEnergy.GaussComposite.ActualDressedNoether.dressed_euler_observer_original]),
    (``LowEnergy.GaussComposite.ActualDressedSignal.dressed_signal_operator_actual,#[
    ``LowEnergy.PreparationVacuumCurrentSignalOperator.sourceHistoryOperator_actual,
    ``LowEnergy.GaussComposite.ActualDressedNoether.dressed_noether_jet_original]),
    (``LowEnergy.GaussComposite.ActualDressedSignal.dressed_signal_operator_continuous,#[
    ``LowEnergy.GaussComposite.ActualDressedNoether.dressed_noether_jet_continuous]),
    (``LowEnergy.GaussComposite.ActualDressedSignal.dressed_signal_quadrature_actual,#[
    ``LowEnergy.GaussComposite.ActualDressedSignal.dressed_signal_operator_actual]),
    (``LowEnergy.GaussComposite.ActualDressedSignal.dressed_signal_duration_positive,#[
    ``LowEnergy.PreparationVacuumCurrentSignalRealization.sourceSignalDuration_positive]),
    (``LowEnergy.GaussComposite.ActualDressedSignal.dressed_signal_nonlinear_generated,#[
    ``LowEnergy.GaussComposite.ActualDressedNoether.dressed_nonlinear_source_generated,
    ``LowEnergy.GaussComposite.ActualDressedSignal.dressed_signal_quadrature_actual]),
    (``LowEnergy.GaussComposite.ActualDressedSignal.dressed_signal_operator_price,#[
    ``LowEnergy.GaussComposite.ActualDressedSignal.dressed_euler_observer_price,
    ``LowEnergy.PreparationVacuumCurrentSignalOperator.sourceHistoryOperator_price]),
    (``LowEnergy.GaussComposite.ActualDressedSignal.dressed_signal_quadrature_price,#[
    ``LowEnergy.GaussComposite.ActualDressedSignal.dressed_signal_operator_price]),
    (``LowEnergy.GaussComposite.ActualDressedSignal.dressed_signal_weighted_price,#[
    ``LowEnergy.GaussComposite.ActualDressedSignal.dressed_signal_quadrature_price,
    ``LowEnergy.GaussComposite.ActualDressedSignal.dressed_signal_coefficient_nonnegative]),
    (``LowEnergy.GaussComposite.ActualDressedSignal.dressed_signal_weighted_integrable,#[
    ``LowEnergy.GaussComposite.ActualDressedSignal.dressed_signal_weighted_price,
    ``LowEnergy.GaussComposite.ActualDressedSignal.dressed_signal_weighted_continuous]),
    (``LowEnergy.GaussComposite.ActualDressedSignal.dressed_signal_window_noether,#[
    ``LowEnergy.GaussComposite.ActualDressedSignal.dressed_signal_window_actual,
    ``LowEnergy.GaussComposite.ActualDressedSignal.dressed_signal_quadrature_actual]),
    (``LowEnergy.GaussComposite.ActualDressedSignal.dressed_signal_window_operator_norm,#[
    ``LowEnergy.GaussComposite.ActualDressedSignal.dressed_signal_weighted_integrable]),
    (``LowEnergy.GaussComposite.ActualDressedSignal.dressed_signal_half_operator_tail,#[
    ``LowEnergy.GaussComposite.ActualDressedSignal.dressed_signal_weighted_price,
    ``LowEnergy.GaussComposite.ActualDressedSignal.dressed_signal_weighted_integrable]),
    (``LowEnergy.GaussComposite.ActualDressedSignal.dressedSignalComplexOperator,#[
    ``LowEnergy.GaussComposite.ActualDressedSignal.dressed_signal_quadrature_phase]),
    (``LowEnergy.GaussComposite.ActualDressedSignal.dressed_signal_matrix_actual,#[
    ``LowEnergy.GaussComposite.ActualDressedSignal.dressedSignalComplexOperator]),
    (``LowEnergy.GaussComposite.ActualDressedSignal.dressed_signal_raw_euler_generated,#[
    ``LowEnergy.PreparationVacuumCurrentSignalRealization.sourceRealSignal_originalEuler,
    ``LowEnergy.SourcePropagationMotherResidualDirections.nativeHolonomicEuler_raw_near,
    ``LowEnergy.GaussComposite.ActualDressedSignal.dressed_signal_nonlinear_generated,
    ``LowEnergy.GaussComposite.ActualDressedSignal.dressed_signal_matrix_actual])]
  for (mouth,required) in direct do packageCertRequire env mouth required
  let testProducers := #[
    ``LowEnergy.GaussComposite.ActualDressedSignal.dressed_euler_observer_price,
    ``LowEnergy.GaussComposite.ActualDressedSignal.dressed_signal_operator_actual,
    ``LowEnergy.GaussComposite.ActualDressedSignal.dressed_signal_operator_continuous,
    ``LowEnergy.GaussComposite.ActualDressedSignal.dressed_signal_quadrature_actual,
    ``LowEnergy.GaussComposite.ActualDressedSignal.dressed_signal_quadrature_continuous,
    ``LowEnergy.GaussComposite.ActualDressedSignal.dressed_signal_quadrature_phase,
    ``LowEnergy.GaussComposite.ActualDressedSignal.dressed_signal_duration_positive,
    ``LowEnergy.GaussComposite.ActualDressedSignal.dressed_signal_nonlinear_generated,
    ``LowEnergy.GaussComposite.ActualDressedSignal.dressed_signal_coefficient_nonnegative,
    ``LowEnergy.GaussComposite.ActualDressedSignal.dressed_signal_operator_price,
    ``LowEnergy.GaussComposite.ActualDressedSignal.dressed_signal_quadrature_price,
    ``LowEnergy.GaussComposite.ActualDressedSignal.dressed_signal_weighted_price,
    ``LowEnergy.GaussComposite.ActualDressedSignal.dressed_signal_weighted_continuous,
    ``LowEnergy.GaussComposite.ActualDressedSignal.dressed_signal_weighted_integrable,
    ``LowEnergy.GaussComposite.ActualDressedSignal.dressed_signal_window_actual,
    ``LowEnergy.GaussComposite.ActualDressedSignal.dressed_signal_window_noether,
    ``LowEnergy.GaussComposite.ActualDressedSignal.dressed_signal_window_operator_norm,
    ``LowEnergy.GaussComposite.ActualDressedSignal.dressed_signal_half_operator_tail,
    ``LowEnergy.GaussComposite.ActualDressedSignal.dressed_signal_complex_original,
    ``LowEnergy.GaussComposite.ActualDressedSignal.dressed_signal_matrix_actual,
    ``LowEnergy.GaussComposite.ActualDressedSignal.dressed_signal_raw_euler_generated]
  for i in [:testProducers.size] do packageCertRequire env tests[i]! #[testProducers[i]!]
  let all ← packageCertClosure env (owned ++ tests.toList)
  let anchors := #[
    ``SaturationMonoid.PhysicsCore.StageNineEnrichedProofFreeSource.positiveSmoothUnifiedSource,
    ``SaturationMonoid.PhysicsCore.Stage9C.Material.SpinPair.actual,
    ``LowEnergy.GaussComposite.ActualDressedSourcePreparation.sourceDressedUnit,
    ``LowEnergy.PreparationVacuumSourcePreparedResponse.sourceProfile,
    ``LowEnergy.GaussComposite.ActualDressedNoether.dressedEulerObserver,
    ``LowEnergy.SourcePropagationNoetherTime.noetherHistoryOperatorJet,
    ``LowEnergy.SourcePropagationNativeEulerHistory.actualPreparedHistoryKernel,
    ``LowEnergy.PreparationVacuumCurrentSignalOperator.sourceHistoryOperator,
    ``LowEnergy.SourcePropagationMotherResidualDirections.actualMotherEulerRead,
    ``LowEnergy.SourcePropagationMotherResidualDirections.motherResidualPullback,
    ``LowEnergy.SourcePropagationNativeActionHessian.nativeHessian,
    ``LowEnergy.PreparationVacuumJointFieldResponse.jointResolvent]
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
  if let some path ← liftIO (IO.getEnv "ALPHA_DRESSED_SIGNAL_AUDIT_OUTPUT") then
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
  logInfo m!"DRESSED_SIGNAL_PASS public={mouths.size} owned={owned.length} tests={tests.size} nodes={all.size} anchors={anchors.size} direct={direct.size} opaque_all_read={opaques} axioms={axioms} unknown=0 unsafe=0 partial=0"
#audit_dressed_signal
#print axioms LowEnergy.GaussComposite.ActualDressedSignal.dressed_euler_observer_price
#print axioms LowEnergy.GaussComposite.ActualDressedSignal.dressed_signal_operator_actual
#print axioms LowEnergy.GaussComposite.ActualDressedSignal.dressed_signal_operator_continuous
#print axioms LowEnergy.GaussComposite.ActualDressedSignal.dressed_signal_quadrature_actual
#print axioms LowEnergy.GaussComposite.ActualDressedSignal.dressed_signal_quadrature_continuous
#print axioms LowEnergy.GaussComposite.ActualDressedSignal.dressed_signal_quadrature_phase
#print axioms LowEnergy.GaussComposite.ActualDressedSignal.dressed_signal_duration_positive
#print axioms LowEnergy.GaussComposite.ActualDressedSignal.dressed_signal_nonlinear_generated
#print axioms LowEnergy.GaussComposite.ActualDressedSignal.dressed_signal_coefficient_nonnegative
#print axioms LowEnergy.GaussComposite.ActualDressedSignal.dressed_signal_operator_price
#print axioms LowEnergy.GaussComposite.ActualDressedSignal.dressed_signal_quadrature_price
#print axioms LowEnergy.GaussComposite.ActualDressedSignal.dressed_signal_weighted_price
#print axioms LowEnergy.GaussComposite.ActualDressedSignal.dressed_signal_weighted_continuous
#print axioms LowEnergy.GaussComposite.ActualDressedSignal.dressed_signal_weighted_integrable
#print axioms LowEnergy.GaussComposite.ActualDressedSignal.dressed_signal_window_actual
#print axioms LowEnergy.GaussComposite.ActualDressedSignal.dressed_signal_window_noether
#print axioms LowEnergy.GaussComposite.ActualDressedSignal.dressed_signal_window_operator_norm
#print axioms LowEnergy.GaussComposite.ActualDressedSignal.dressed_signal_half_operator_tail
#print axioms LowEnergy.GaussComposite.ActualDressedSignal.dressed_signal_complex_original
#print axioms LowEnergy.GaussComposite.ActualDressedSignal.dressed_signal_matrix_actual
#print axioms LowEnergy.GaussComposite.ActualDressedSignal.dressed_signal_raw_euler_generated
