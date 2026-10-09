import H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualDressedPreparedTimePrice
import H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualDressedPreparedSlopePrice
import H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualDressedPreparedSlopeGrowth
import H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualDressedFiniteStaticRead

import Lean.Elab.Command
import Lean.Util.FoldConsts
import Lean.Util.CollectAxioms
set_option autoImplicit false
set_option maxHeartbeats 12000000
set_option maxRecDepth 32768
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.GaussComposite.ActualDressedPreparedStaticAudit
elab "checked_occupationPrice_nonnegContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualDressedPreparedPrice.occupationPrice_nonneg).type
theorem checked_occupationPrice_nonneg : checked_occupationPrice_nonnegContract := @LowEnergy.GaussComposite.ActualDressedPreparedPrice.occupationPrice_nonneg

elab "checked_occupationPrice_monoContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualDressedPreparedPrice.occupationPrice_mono).type
theorem checked_occupationPrice_mono : checked_occupationPrice_monoContract := @LowEnergy.GaussComposite.ActualDressedPreparedPrice.occupationPrice_mono

elab "checked_actual_time_N2_returnContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualDressedPreparedPrice.actual_time_N2_return).type
theorem checked_actual_time_N2_return : checked_actual_time_N2_returnContract := @LowEnergy.GaussComposite.ActualDressedPreparedPrice.actual_time_N2_return

elab "checked_actual_time_N2_priceContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualDressedPreparedPrice.actual_time_N2_price).type
theorem checked_actual_time_N2_price : checked_actual_time_N2_priceContract := @LowEnergy.GaussComposite.ActualDressedPreparedPrice.actual_time_N2_price

elab "checked_actual_created_time_priceContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualDressedPreparedPrice.actual_created_time_price).type
theorem checked_actual_created_time_price : checked_actual_created_time_priceContract := @LowEnergy.GaussComposite.ActualDressedPreparedPrice.actual_created_time_price

elab "checked_actual_background_time_priceContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualDressedPreparedPrice.actual_background_time_price).type
theorem checked_actual_background_time_price : checked_actual_background_time_priceContract := @LowEnergy.GaussComposite.ActualDressedPreparedPrice.actual_background_time_price

elab "checked_actual_timeSlope_N2_rangeContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualDressedPreparedPrice.actual_timeSlope_N2_range).type
theorem checked_actual_timeSlope_N2_range : checked_actual_timeSlope_N2_rangeContract := @LowEnergy.GaussComposite.ActualDressedPreparedPrice.actual_timeSlope_N2_range

elab "checked_actual_timeSlope_N2_priceContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualDressedPreparedPrice.actual_timeSlope_N2_price).type
theorem checked_actual_timeSlope_N2_price : checked_actual_timeSlope_N2_priceContract := @LowEnergy.GaussComposite.ActualDressedPreparedPrice.actual_timeSlope_N2_price

elab "checked_actual_created_timeSlope_priceContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualDressedPreparedPrice.actual_created_timeSlope_price).type
theorem checked_actual_created_timeSlope_price : checked_actual_created_timeSlope_priceContract := @LowEnergy.GaussComposite.ActualDressedPreparedPrice.actual_created_timeSlope_price

elab "checked_occupationPrice_twoContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualDressedPreparedPrice.occupationPrice_two).type
theorem checked_occupationPrice_two : checked_occupationPrice_twoContract := @LowEnergy.GaussComposite.ActualDressedPreparedPrice.occupationPrice_two

elab "checked_occupationPrice_two_growthContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualDressedPreparedPrice.occupationPrice_two_growth).type
theorem checked_occupationPrice_two_growth : checked_occupationPrice_two_growthContract := @LowEnergy.GaussComposite.ActualDressedPreparedPrice.occupationPrice_two_growth

elab "checked_actual_timeSlope_N2_polynomial_priceContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualDressedPreparedPrice.actual_timeSlope_N2_polynomial_price).type
theorem checked_actual_timeSlope_N2_polynomial_price : checked_actual_timeSlope_N2_polynomial_priceContract := @LowEnergy.GaussComposite.ActualDressedPreparedPrice.actual_timeSlope_N2_polynomial_price

elab "checked_actual_created_timeSlope_polynomial_priceContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualDressedPreparedPrice.actual_created_timeSlope_polynomial_price).type
theorem checked_actual_created_timeSlope_polynomial_price : checked_actual_created_timeSlope_polynomial_priceContract := @LowEnergy.GaussComposite.ActualDressedPreparedPrice.actual_created_timeSlope_polynomial_price

elab "checked_finite_constant_field_slope_actualContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualDressedFiniteStaticRead.finite_constant_field_slope_actual).type
theorem checked_finite_constant_field_slope_actual : checked_finite_constant_field_slope_actualContract := @LowEnergy.GaussComposite.ActualDressedFiniteStaticRead.finite_constant_field_slope_actual

elab "checked_finite_static_integrand_integrableContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualDressedFiniteStaticRead.finite_static_integrand_integrable).type
theorem checked_finite_static_integrand_integrable : checked_finite_static_integrand_integrableContract := @LowEnergy.GaussComposite.ActualDressedFiniteStaticRead.finite_static_integrand_integrable

elab "checked_dressed_static_polarization_finiteContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualDressedFiniteStaticRead.dressed_static_polarization_finite).type
theorem checked_dressed_static_polarization_finite : checked_dressed_static_polarization_finiteContract := @LowEnergy.GaussComposite.ActualDressedFiniteStaticRead.dressed_static_polarization_finite

elab "checked_finite_static_polarization_tailContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualDressedFiniteStaticRead.finite_static_polarization_tail).type
theorem checked_finite_static_polarization_tail : checked_finite_static_polarization_tailContract := @LowEnergy.GaussComposite.ActualDressedFiniteStaticRead.finite_static_polarization_tail

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



open ActualDressedPreparedPrice ActualDressedFiniteStaticRead MeasureTheory
open scoped Interval

theorem same_actual_created_slope_price (event : DressedEvent) (force : Field289) (t : ℝ) :
    ‖timeSlope force event.momentum event.frame t (sourceDressedUnit event.epsilon event.precision)‖ ≤
      (‖jointCurrent event.momentum event.frame 0 0 force‖*(1+‖actualA event.momentum event.frame‖)^4)*(1+|t|)^5 :=
  actual_created_timeSlope_polynomial_price event.momentum event.frame force event.epsilon event.precision t

theorem same_actual_finite_static_entry (event : DressedEvent) (transfer : PhysicalMomentum)
    (lambda : ℂ) (positive : 0<lambda.re) (i j : Fin 289) :
    ActualDressedSylvester.dressedStaticPolarization event transfer lambda i j=
      ∫t in Set.Ioi (0:ℝ),PreparationVacuumGaugeSourceInjection.laplaceWeight lambda t*
        finiteConstantFieldSlope event transfer (PreparationVacuumActionFieldLift.fieldUnit j) t i :=
  dressed_static_polarization_finite event transfer lambda positive i j

theorem same_actual_finite_static_tail (event : DressedEvent) (transfer : PhysicalMomentum)
    (p : Fin 4→ℂ) (static : p 0=0) (lambda : ℂ) (positive : 0<lambda.re)
    (T : ℝ) (future : 0≤T) (i j : Fin 289) :
    ‖(∫t in Set.Ioi (0:ℝ),PreparationVacuumGaugeSourceInjection.laplaceWeight lambda t*
        finiteConstantFieldSlope event transfer (PreparationVacuumActionFieldLift.fieldUnit j) t i)-
      ActualDressedPencil.dressedWindowPolarization event transfer p lambda T i j‖ ≤
        ActualDressedSignal.dressedSignalTailPrice event transfer p lambda T :=
  finite_static_polarization_tail event transfer p static lambda positive T future i j
end LowEnergy.GaussComposite.ActualDressedPreparedStaticAudit

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

elab "#audit_dressed_prepared_static" : command => do
  let env ← getEnv
  let modules := env.header.moduleNames
  let owner := fun name => (env.getModuleIdxFor? name).map fun i => modules[i.toNat]!
  let candidates := #[`H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualDressedPreparedTimePrice,`H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualDressedPreparedSlopePrice,`H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualDressedPreparedSlopeGrowth,`H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualDressedFiniteStaticRead]
  let owned := env.constants.toList.filterMap fun (name, _) =>
    if (owner name).any candidates.contains then some name else none
  let mouths := #[
    ``LowEnergy.GaussComposite.ActualDressedPreparedPrice.occupationPrice,
    ``LowEnergy.GaussComposite.ActualDressedPreparedPrice.occupationPrice_nonneg,
    ``LowEnergy.GaussComposite.ActualDressedPreparedPrice.occupationPrice_mono,
    ``LowEnergy.GaussComposite.ActualDressedPreparedPrice.actual_time_N2_return,
    ``LowEnergy.GaussComposite.ActualDressedPreparedPrice.actual_time_N2_price,
    ``LowEnergy.GaussComposite.ActualDressedPreparedPrice.actual_created_time_price,
    ``LowEnergy.GaussComposite.ActualDressedPreparedPrice.actual_background_time_price,
    ``LowEnergy.GaussComposite.ActualDressedPreparedPrice.actual_timeSlope_N2_range,
    ``LowEnergy.GaussComposite.ActualDressedPreparedPrice.actual_timeSlope_N2_price,
    ``LowEnergy.GaussComposite.ActualDressedPreparedPrice.actual_created_timeSlope_price,
    ``LowEnergy.GaussComposite.ActualDressedPreparedPrice.occupationPrice_two,
    ``LowEnergy.GaussComposite.ActualDressedPreparedPrice.occupationPrice_two_growth,
    ``LowEnergy.GaussComposite.ActualDressedPreparedPrice.actual_timeSlope_N2_polynomial_price,
    ``LowEnergy.GaussComposite.ActualDressedPreparedPrice.actual_created_timeSlope_polynomial_price,
    ``LowEnergy.GaussComposite.ActualDressedFiniteStaticRead.finiteConstantFieldSlope,
    ``LowEnergy.GaussComposite.ActualDressedFiniteStaticRead.finite_constant_field_slope_actual,
    ``LowEnergy.GaussComposite.ActualDressedFiniteStaticRead.finite_static_integrand_integrable,
    ``LowEnergy.GaussComposite.ActualDressedFiniteStaticRead.dressed_static_polarization_finite,
    ``LowEnergy.GaussComposite.ActualDressedFiniteStaticRead.finite_static_polarization_tail]
  for name in mouths do
    unless owned.contains name do throwError m!"MISSING_MOUTH {name}"
  let tests := #[
    ``LowEnergy.GaussComposite.ActualDressedPreparedStaticAudit.checked_occupationPrice_nonneg,
    ``LowEnergy.GaussComposite.ActualDressedPreparedStaticAudit.checked_occupationPrice_mono,
    ``LowEnergy.GaussComposite.ActualDressedPreparedStaticAudit.checked_actual_time_N2_return,
    ``LowEnergy.GaussComposite.ActualDressedPreparedStaticAudit.checked_actual_time_N2_price,
    ``LowEnergy.GaussComposite.ActualDressedPreparedStaticAudit.checked_actual_created_time_price,
    ``LowEnergy.GaussComposite.ActualDressedPreparedStaticAudit.checked_actual_background_time_price,
    ``LowEnergy.GaussComposite.ActualDressedPreparedStaticAudit.checked_actual_timeSlope_N2_range,
    ``LowEnergy.GaussComposite.ActualDressedPreparedStaticAudit.checked_actual_timeSlope_N2_price,
    ``LowEnergy.GaussComposite.ActualDressedPreparedStaticAudit.checked_actual_created_timeSlope_price,
    ``LowEnergy.GaussComposite.ActualDressedPreparedStaticAudit.checked_occupationPrice_two,
    ``LowEnergy.GaussComposite.ActualDressedPreparedStaticAudit.checked_occupationPrice_two_growth,
    ``LowEnergy.GaussComposite.ActualDressedPreparedStaticAudit.checked_actual_timeSlope_N2_polynomial_price,
    ``LowEnergy.GaussComposite.ActualDressedPreparedStaticAudit.checked_actual_created_timeSlope_polynomial_price,
    ``LowEnergy.GaussComposite.ActualDressedPreparedStaticAudit.checked_finite_constant_field_slope_actual,
    ``LowEnergy.GaussComposite.ActualDressedPreparedStaticAudit.checked_finite_static_integrand_integrable,
    ``LowEnergy.GaussComposite.ActualDressedPreparedStaticAudit.checked_dressed_static_polarization_finite,
    ``LowEnergy.GaussComposite.ActualDressedPreparedStaticAudit.checked_finite_static_polarization_tail,
    ``LowEnergy.GaussComposite.ActualDressedPreparedStaticAudit.actual_event_nonempty,
    ``LowEnergy.GaussComposite.ActualDressedPreparedStaticAudit.actual_unit_nonzero,
    ``LowEnergy.GaussComposite.ActualDressedPreparedStaticAudit.same_actual_created_slope_price,
    ``LowEnergy.GaussComposite.ActualDressedPreparedStaticAudit.same_actual_finite_static_entry,
    ``LowEnergy.GaussComposite.ActualDressedPreparedStaticAudit.same_actual_finite_static_tail]
  let direct := #[
    (``LowEnergy.GaussComposite.ActualDressedPreparedPrice.actual_time_N2_return,#[
    ``LowEnergy.GaussComposite.ActualDressedNumberSector.actual_time_N2_projection_return]),
    (``LowEnergy.GaussComposite.ActualDressedPreparedPrice.actual_time_N2_price,#[
    ``LowEnergy.GaussComposite.ActualDressedPreparedPrice.actual_time_N2_return,
    ``LowEnergy.FullYSourceCutoffVolterra.partialEvolution_bound]),
    (``LowEnergy.GaussComposite.ActualDressedPreparedPrice.actual_created_time_price,#[
    ``LowEnergy.GaussComposite.ActualDressedPreparedPrice.actual_time_N2_price,
    ``LowEnergy.GaussComposite.ActualDressedSourcePreparation.source_dressed_unit_norm]),
    (``LowEnergy.GaussComposite.ActualDressedPreparedPrice.actual_background_time_price,#[
    ``LowEnergy.GaussComposite.ActualDressedNumberZero.actual_time_background,
    ``LowEnergy.FullYSourceCutoffVolterra.partialEvolution_bound]),
    (``LowEnergy.GaussComposite.ActualDressedPreparedPrice.actual_timeSlope_N2_range,#[
    ``LowEnergy.GaussComposite.ActualDressedNumberField.actual_joint_current_number_two,
    ``LowEnergy.GaussComposite.ActualDressedNumberField.actual_joint_time_number_two_range]),
    (``LowEnergy.GaussComposite.ActualDressedPreparedPrice.actual_timeSlope_N2_price,#[
    ``LowEnergy.GaussComposite.ActualDressedPreparedPrice.actual_time_N2_price,
    ``LowEnergy.GaussComposite.ActualDressedNumberField.actual_joint_current_number_two]),
    (``LowEnergy.GaussComposite.ActualDressedPreparedPrice.actual_created_timeSlope_price,#[
    ``LowEnergy.GaussComposite.ActualDressedPreparedPrice.actual_timeSlope_N2_price,
    ``LowEnergy.GaussComposite.ActualDressedSourcePreparation.source_dressed_unit_norm]),
    (``LowEnergy.GaussComposite.ActualDressedPreparedPrice.actual_timeSlope_N2_polynomial_price,#[
    ``LowEnergy.GaussComposite.ActualDressedPreparedPrice.actual_timeSlope_N2_price,
    ``LowEnergy.GaussComposite.ActualDressedPreparedPrice.occupationPrice_two_growth]),
    (``LowEnergy.GaussComposite.ActualDressedPreparedPrice.actual_created_timeSlope_polynomial_price,#[
    ``LowEnergy.GaussComposite.ActualDressedPreparedPrice.actual_timeSlope_N2_polynomial_price,
    ``LowEnergy.GaussComposite.ActualDressedSourcePreparation.source_dressed_unit_norm]),
    (``LowEnergy.GaussComposite.ActualDressedFiniteStaticRead.finite_constant_field_slope_actual,#[
    ``LowEnergy.GaussComposite.ActualDressedFieldTime.actual_finite_number_field_quantum_derivative]),
    (``LowEnergy.GaussComposite.ActualDressedFiniteStaticRead.finite_static_integrand_integrable,#[
    ``LowEnergy.GaussComposite.ActualDressedFiniteStaticRead.finite_constant_field_slope_actual,
    ``LowEnergy.GaussComposite.ActualDressedSylvester.noether_static_half_integrable]),
    (``LowEnergy.GaussComposite.ActualDressedFiniteStaticRead.dressed_static_polarization_finite,#[
    ``LowEnergy.GaussComposite.ActualDressedFiniteStaticRead.finite_constant_field_slope_actual,
    ``LowEnergy.GaussComposite.ActualDressedSylvester.noether_static_half_integrable]),
    (``LowEnergy.GaussComposite.ActualDressedFiniteStaticRead.finite_static_polarization_tail,#[
    ``LowEnergy.GaussComposite.ActualDressedFiniteStaticRead.dressed_static_polarization_finite,
    ``LowEnergy.GaussComposite.ActualDressedSylvester.dressed_static_polarization_tail])]
  for (mouth,required) in direct do packageCertRequire env mouth required
  let testProducers := #[
    ``LowEnergy.GaussComposite.ActualDressedPreparedPrice.occupationPrice_nonneg,
    ``LowEnergy.GaussComposite.ActualDressedPreparedPrice.occupationPrice_mono,
    ``LowEnergy.GaussComposite.ActualDressedPreparedPrice.actual_time_N2_return,
    ``LowEnergy.GaussComposite.ActualDressedPreparedPrice.actual_time_N2_price,
    ``LowEnergy.GaussComposite.ActualDressedPreparedPrice.actual_created_time_price,
    ``LowEnergy.GaussComposite.ActualDressedPreparedPrice.actual_background_time_price,
    ``LowEnergy.GaussComposite.ActualDressedPreparedPrice.actual_timeSlope_N2_range,
    ``LowEnergy.GaussComposite.ActualDressedPreparedPrice.actual_timeSlope_N2_price,
    ``LowEnergy.GaussComposite.ActualDressedPreparedPrice.actual_created_timeSlope_price,
    ``LowEnergy.GaussComposite.ActualDressedPreparedPrice.occupationPrice_two,
    ``LowEnergy.GaussComposite.ActualDressedPreparedPrice.occupationPrice_two_growth,
    ``LowEnergy.GaussComposite.ActualDressedPreparedPrice.actual_timeSlope_N2_polynomial_price,
    ``LowEnergy.GaussComposite.ActualDressedPreparedPrice.actual_created_timeSlope_polynomial_price,
    ``LowEnergy.GaussComposite.ActualDressedFiniteStaticRead.finite_constant_field_slope_actual,
    ``LowEnergy.GaussComposite.ActualDressedFiniteStaticRead.finite_static_integrand_integrable,
    ``LowEnergy.GaussComposite.ActualDressedFiniteStaticRead.dressed_static_polarization_finite,
    ``LowEnergy.GaussComposite.ActualDressedFiniteStaticRead.finite_static_polarization_tail]
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
  if let some path ← liftIO (IO.getEnv "ALPHA_DRESSED_PREPARED_STATIC_AUDIT_OUTPUT") then
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
  logInfo m!"DRESSED_PREPARED_STATIC_PASS public={mouths.size} owned={owned.length} tests={tests.size} nodes={all.size} anchors={anchors.size} direct={direct.size} opaque_all_read={opaques} axioms={axioms} unknown=0 unsafe=0 partial=0"
#audit_dressed_prepared_static
#print axioms LowEnergy.GaussComposite.ActualDressedPreparedPrice.occupationPrice_nonneg
#print axioms LowEnergy.GaussComposite.ActualDressedPreparedPrice.occupationPrice_mono
#print axioms LowEnergy.GaussComposite.ActualDressedPreparedPrice.actual_time_N2_return
#print axioms LowEnergy.GaussComposite.ActualDressedPreparedPrice.actual_time_N2_price
#print axioms LowEnergy.GaussComposite.ActualDressedPreparedPrice.actual_created_time_price
#print axioms LowEnergy.GaussComposite.ActualDressedPreparedPrice.actual_background_time_price
#print axioms LowEnergy.GaussComposite.ActualDressedPreparedPrice.actual_timeSlope_N2_range
#print axioms LowEnergy.GaussComposite.ActualDressedPreparedPrice.actual_timeSlope_N2_price
#print axioms LowEnergy.GaussComposite.ActualDressedPreparedPrice.actual_created_timeSlope_price
#print axioms LowEnergy.GaussComposite.ActualDressedPreparedPrice.occupationPrice_two
#print axioms LowEnergy.GaussComposite.ActualDressedPreparedPrice.occupationPrice_two_growth
#print axioms LowEnergy.GaussComposite.ActualDressedPreparedPrice.actual_timeSlope_N2_polynomial_price
#print axioms LowEnergy.GaussComposite.ActualDressedPreparedPrice.actual_created_timeSlope_polynomial_price
#print axioms LowEnergy.GaussComposite.ActualDressedFiniteStaticRead.finite_constant_field_slope_actual
#print axioms LowEnergy.GaussComposite.ActualDressedFiniteStaticRead.finite_static_integrand_integrable
#print axioms LowEnergy.GaussComposite.ActualDressedFiniteStaticRead.dressed_static_polarization_finite
#print axioms LowEnergy.GaussComposite.ActualDressedFiniteStaticRead.finite_static_polarization_tail
