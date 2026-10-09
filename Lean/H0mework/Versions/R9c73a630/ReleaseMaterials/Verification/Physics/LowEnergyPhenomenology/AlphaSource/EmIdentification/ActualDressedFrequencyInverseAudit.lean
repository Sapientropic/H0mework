import H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualDressedFrequencyMemory
import H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualDressedFrequencyConvolution
import H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualDressedPlaneInverse
import H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualDressedFourierInverse
import H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualDressedRationalFourier

import Lean.Elab.Command
import Lean.Util.FoldConsts
import Lean.Util.CollectAxioms
set_option autoImplicit false
set_option maxHeartbeats 12000000
set_option maxRecDepth 32768
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.GaussComposite.ActualDressedFrequencyInverseAudit
elab "checked_noether_memory_convolutionContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualDressedFrequencyInverse.noether_memory_convolution).type
theorem checked_noether_memory_convolution : checked_noether_memory_convolutionContract := @LowEnergy.GaussComposite.ActualDressedFrequencyInverse.noether_memory_convolution

elab "checked_source_inverse_applied_integrableContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualDressedFrequencyInverse.source_inverse_applied_integrable).type
theorem checked_source_inverse_applied_integrable : checked_source_inverse_applied_integrableContract := @LowEnergy.GaussComposite.ActualDressedFrequencyInverse.source_inverse_applied_integrable

elab "checked_source_inverse_applied_readContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualDressedFrequencyInverse.source_inverse_applied_read).type
theorem checked_source_inverse_applied_read : checked_source_inverse_applied_readContract := @LowEnergy.GaussComposite.ActualDressedFrequencyInverse.source_inverse_applied_read

elab "checked_noether_memory_weightedContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualDressedFrequencyInverse.noether_memory_weighted).type
theorem checked_noether_memory_weighted : checked_noether_memory_weightedContract := @LowEnergy.GaussComposite.ActualDressedFrequencyInverse.noether_memory_weighted

elab "checked_plane_noether_memory_integrableContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualDressedFrequencyInverse.plane_noether_memory_integrable).type
theorem checked_plane_noether_memory_integrable : checked_plane_noether_memory_integrableContract := @LowEnergy.GaussComposite.ActualDressedFrequencyInverse.plane_noether_memory_integrable

elab "checked_plane_noether_memory_inverseContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualDressedFrequencyInverse.plane_noether_memory_inverse).type
theorem checked_plane_noether_memory_inverse : checked_plane_noether_memory_inverseContract := @LowEnergy.GaussComposite.ActualDressedFrequencyInverse.plane_noether_memory_inverse

elab "checked_plane_noether_operator_integrableContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualDressedFrequencyInverse.plane_noether_operator_integrable).type
theorem checked_plane_noether_operator_integrable : checked_plane_noether_operator_integrableContract := @LowEnergy.GaussComposite.ActualDressedFrequencyInverse.plane_noether_operator_integrable

elab "checked_plane_noether_operator_inverseContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualDressedFrequencyInverse.plane_noether_operator_inverse).type
theorem checked_plane_noether_operator_inverse : checked_plane_noether_operator_inverseContract := @LowEnergy.GaussComposite.ActualDressedFrequencyInverse.plane_noether_operator_inverse

elab "checked_plane_noether_observerContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualDressedFrequencyInverse.plane_noether_observer).type
theorem checked_plane_noether_observer : checked_plane_noether_observerContract := @LowEnergy.GaussComposite.ActualDressedFrequencyInverse.plane_noether_observer

elab "checked_dressed_plane_history_generatedContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualDressedFrequencyInverse.dressed_plane_history_generated).type
theorem checked_dressed_plane_history_generated : checked_dressed_plane_history_generatedContract := @LowEnergy.GaussComposite.ActualDressedFrequencyInverse.dressed_plane_history_generated

elab "checked_dressed_frequency_half_inverseContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualDressedFrequencyInverse.dressed_frequency_half_inverse).type
theorem checked_dressed_frequency_half_inverse : checked_dressed_frequency_half_inverseContract := @LowEnergy.GaussComposite.ActualDressedFrequencyInverse.dressed_frequency_half_inverse

elab "checked_damped_fourier_polarization_inverseContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualDressedFrequencyInverse.damped_fourier_polarization_inverse).type
theorem checked_damped_fourier_polarization_inverse : checked_damped_fourier_polarization_inverseContract := @LowEnergy.GaussComposite.ActualDressedFrequencyInverse.damped_fourier_polarization_inverse

elab "checked_damped_physical_response_inverseContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualDressedFrequencyInverse.damped_physical_response_inverse).type
theorem checked_damped_physical_response_inverse : checked_damped_physical_response_inverseContract := @LowEnergy.GaussComposite.ActualDressedFrequencyInverse.damped_physical_response_inverse

elab "checked_plane_response_denominator_nonzeroContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualDressedFrequencyInverse.plane_response_denominator_nonzero).type
theorem checked_plane_response_denominator_nonzero : checked_plane_response_denominator_nonzeroContract := @LowEnergy.GaussComposite.ActualDressedFrequencyInverse.plane_response_denominator_nonzero

elab "checked_plane_noether_inverse_rationalContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualDressedFrequencyInverse.plane_noether_inverse_rational).type
theorem checked_plane_noether_inverse_rational : checked_plane_noether_inverse_rationalContract := @LowEnergy.GaussComposite.ActualDressedFrequencyInverse.plane_noether_inverse_rational

elab "checked_dressed_frequency_polarization_rationalContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualDressedFrequencyInverse.dressed_frequency_polarization_rational).type
theorem checked_dressed_frequency_polarization_rational : checked_dressed_frequency_polarization_rationalContract := @LowEnergy.GaussComposite.ActualDressedFrequencyInverse.dressed_frequency_polarization_rational

elab "checked_dressed_frequency_response_rationalContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualDressedFrequencyInverse.dressed_frequency_response_rational).type
theorem checked_dressed_frequency_response_rational : checked_dressed_frequency_response_rationalContract := @LowEnergy.GaussComposite.ActualDressedFrequencyInverse.dressed_frequency_response_rational

elab "checked_plane_static_denominatorContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualDressedFrequencyInverse.plane_static_denominator).type
theorem checked_plane_static_denominator : checked_plane_static_denominatorContract := @LowEnergy.GaussComposite.ActualDressedFrequencyInverse.plane_static_denominator

elab "checked_actual_zero_transfer_denominatorContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualDressedFrequencyInverse.actual_zero_transfer_denominator).type
theorem checked_actual_zero_transfer_denominator : checked_actual_zero_transfer_denominatorContract := @LowEnergy.GaussComposite.ActualDressedFrequencyInverse.actual_zero_transfer_denominator

open CanonicalGradedSpatialSource PreparationVacuumMixedFieldReturn PreparationVacuumPhysicalFeedback
open PreparationVacuumGaugeSourceInjection PreparationVacuumActionFieldLift
open PreparationVacuumCurrentSignalOperator PreparationVacuumCurrentSignalRealization
open PreparationVacuumPhysicalCharacteristic SourcePropagationResolvent SourcePropagationAlgebraicResponse
open ActualDressedFullCoulomb ActualDressedNoether ActualDressedHistoryKernel
open ActualDressedFrequencyHalf ActualDressedFrequencyInverse ActualDressedSylvester
open Filter Set MeasureTheory
open scoped Topology Matrix BigOperators Interval

theorem actual_event_nonempty : Nonempty DressedEvent := by
  exact ⟨{
    epsilon:=1
    precision:=by norm_num
    momentum:=0
    frame:=Classical.choice inferInstance
    cut:=0
    energy:=Complex.I
    nonreal:=by simp}⟩

theorem actual_nonzero_clock_denominator (event : DressedEvent) :
    planeResponseDenominator (dressedKinematicPoint event 0) (-Complex.I) (2-Complex.I)≠0 := by
  apply plane_response_denominator_nonzero
  · norm_num
  · norm_num

theorem actual_original_memory_order (event : DressedEvent) :
    noetherMemoryMap (dressedKinematicPoint event 0) (fieldUnit 20) 2 1 (fieldUnit 20)=
      twoTimeMap (dressedKinematicPoint event 0) 1
        (PreparationVacuumPropagationPencil.driveOperator (dressedKinematicPoint event 0) (fieldUnit 20)
          (twoTimeMap (dressedKinematicPoint event 0) (2-1)
            (PreparationVacuumPropagationPencil.rawInitial (dressedKinematicPoint event 0) (fieldUnit 20)))) :=
  noether_memory_convolution (dressedKinematicPoint event 0) (fieldUnit 20) (fieldUnit 20) 2 1

theorem actual_physical_field_rational (event : DressedEvent) :
    frequencyResponsePencil event 0 (physicalFrequencyMomentum 1 0) (dampedFourierClock 1 2) 20 20=
      ActualEMAction.emOriginalJacobi (physicalFrequencyMomentum 1 0) 20 20-
        (dampedFourierClock 1 2-physicalFrequencyMomentum 1 0 0)*
          (dressedFrequencyNumerator event 0 (physicalFrequencyMomentum 1 0) (dampedFourierClock 1 2) 20 20/
            planeResponseDenominator (dressedKinematicPoint event 0) (physicalFrequencyMomentum 1 0 0) (dampedFourierClock 1 2)) :=
  dressed_frequency_response_rational event 0 _ _ (damped_fourier_source_domain 1 2 0 (by norm_num)) 20 20

theorem actual_zero_clock_denominator_fails (event : DressedEvent) :
    ¬planeResponseDenominator (dressedKinematicPoint event 0) 0 0≠0 := by
  rw [actual_zero_transfer_denominator]
  simp

end LowEnergy.GaussComposite.ActualDressedFrequencyInverseAudit

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

elab "#audit_dressed_frequency_inverse" : command => do
  let env ← getEnv
  let modules := env.header.moduleNames
  let owner := fun name => (env.getModuleIdxFor? name).map fun i => modules[i.toNat]!
  let candidates := #[`H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualDressedFrequencyMemory,`H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualDressedFrequencyConvolution,`H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualDressedPlaneInverse,`H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualDressedFourierInverse,`H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualDressedRationalFourier]
  let owned := env.constants.toList.filterMap fun (name, _) =>
    if (owner name).any candidates.contains then some name else none
  let mouths := #[
    ``LowEnergy.GaussComposite.ActualDressedFrequencyInverse.noether_memory_convolution,
    ``LowEnergy.GaussComposite.ActualDressedFrequencyInverse.source_inverse_applied_integrable,
    ``LowEnergy.GaussComposite.ActualDressedFrequencyInverse.source_inverse_applied_read,
    ``LowEnergy.GaussComposite.ActualDressedFrequencyInverse.noether_memory_weighted,
    ``LowEnergy.GaussComposite.ActualDressedFrequencyInverse.planeNoetherMemory,
    ``LowEnergy.GaussComposite.ActualDressedFrequencyInverse.plane_noether_memory_integrable,
    ``LowEnergy.GaussComposite.ActualDressedFrequencyInverse.plane_noether_memory_inverse,
    ``LowEnergy.GaussComposite.ActualDressedFrequencyInverse.planeNoetherOperator,
    ``LowEnergy.GaussComposite.ActualDressedFrequencyInverse.planeNoetherInverse,
    ``LowEnergy.GaussComposite.ActualDressedFrequencyInverse.plane_noether_operator_integrable,
    ``LowEnergy.GaussComposite.ActualDressedFrequencyInverse.plane_noether_operator_inverse,
    ``LowEnergy.GaussComposite.ActualDressedFrequencyInverse.plane_noether_observer,
    ``LowEnergy.GaussComposite.ActualDressedFrequencyInverse.dressed_plane_history_generated,
    ``LowEnergy.GaussComposite.ActualDressedFrequencyInverse.dressed_frequency_half_inverse,
    ``LowEnergy.GaussComposite.ActualDressedFrequencyInverse.damped_fourier_polarization_inverse,
    ``LowEnergy.GaussComposite.ActualDressedFrequencyInverse.damped_physical_response_inverse,
    ``LowEnergy.GaussComposite.ActualDressedFrequencyInverse.planeResponseDenominator,
    ``LowEnergy.GaussComposite.ActualDressedFrequencyInverse.planeResponseNumerator,
    ``LowEnergy.GaussComposite.ActualDressedFrequencyInverse.plane_response_denominator_nonzero,
    ``LowEnergy.GaussComposite.ActualDressedFrequencyInverse.plane_noether_inverse_rational,
    ``LowEnergy.GaussComposite.ActualDressedFrequencyInverse.dressedFrequencyNumerator,
    ``LowEnergy.GaussComposite.ActualDressedFrequencyInverse.dressed_frequency_polarization_rational,
    ``LowEnergy.GaussComposite.ActualDressedFrequencyInverse.dressed_frequency_response_rational,
    ``LowEnergy.GaussComposite.ActualDressedFrequencyInverse.plane_static_denominator,
    ``LowEnergy.GaussComposite.ActualDressedFrequencyInverse.actual_zero_transfer_denominator]
  for name in mouths do
    unless owned.contains name do throwError m!"MISSING_MOUTH {name}"
  let tests := #[
    ``LowEnergy.GaussComposite.ActualDressedFrequencyInverseAudit.checked_noether_memory_convolution,
    ``LowEnergy.GaussComposite.ActualDressedFrequencyInverseAudit.checked_source_inverse_applied_integrable,
    ``LowEnergy.GaussComposite.ActualDressedFrequencyInverseAudit.checked_source_inverse_applied_read,
    ``LowEnergy.GaussComposite.ActualDressedFrequencyInverseAudit.checked_noether_memory_weighted,
    ``LowEnergy.GaussComposite.ActualDressedFrequencyInverseAudit.checked_plane_noether_memory_integrable,
    ``LowEnergy.GaussComposite.ActualDressedFrequencyInverseAudit.checked_plane_noether_memory_inverse,
    ``LowEnergy.GaussComposite.ActualDressedFrequencyInverseAudit.checked_plane_noether_operator_integrable,
    ``LowEnergy.GaussComposite.ActualDressedFrequencyInverseAudit.checked_plane_noether_operator_inverse,
    ``LowEnergy.GaussComposite.ActualDressedFrequencyInverseAudit.checked_plane_noether_observer,
    ``LowEnergy.GaussComposite.ActualDressedFrequencyInverseAudit.checked_dressed_plane_history_generated,
    ``LowEnergy.GaussComposite.ActualDressedFrequencyInverseAudit.checked_dressed_frequency_half_inverse,
    ``LowEnergy.GaussComposite.ActualDressedFrequencyInverseAudit.checked_damped_fourier_polarization_inverse,
    ``LowEnergy.GaussComposite.ActualDressedFrequencyInverseAudit.checked_damped_physical_response_inverse,
    ``LowEnergy.GaussComposite.ActualDressedFrequencyInverseAudit.checked_plane_response_denominator_nonzero,
    ``LowEnergy.GaussComposite.ActualDressedFrequencyInverseAudit.checked_plane_noether_inverse_rational,
    ``LowEnergy.GaussComposite.ActualDressedFrequencyInverseAudit.checked_dressed_frequency_polarization_rational,
    ``LowEnergy.GaussComposite.ActualDressedFrequencyInverseAudit.checked_dressed_frequency_response_rational,
    ``LowEnergy.GaussComposite.ActualDressedFrequencyInverseAudit.checked_plane_static_denominator,
    ``LowEnergy.GaussComposite.ActualDressedFrequencyInverseAudit.checked_actual_zero_transfer_denominator,
    ``LowEnergy.GaussComposite.ActualDressedFrequencyInverseAudit.actual_event_nonempty,
    ``LowEnergy.GaussComposite.ActualDressedFrequencyInverseAudit.actual_nonzero_clock_denominator,
    ``LowEnergy.GaussComposite.ActualDressedFrequencyInverseAudit.actual_original_memory_order,
    ``LowEnergy.GaussComposite.ActualDressedFrequencyInverseAudit.actual_physical_field_rational,
    ``LowEnergy.GaussComposite.ActualDressedFrequencyInverseAudit.actual_zero_clock_denominator_fails]
  let direct := #[
    (``LowEnergy.GaussComposite.ActualDressedFrequencyInverse.noether_memory_convolution,#[
    ``LowEnergy.SourceFiniteUnitary.time_add,
    ``LowEnergy.GaussComposite.ActualDressedHistoryKernel.noetherMemoryMap,
    ``LowEnergy.SourcePropagationResolvent.twoTimeMap]),
    (``LowEnergy.GaussComposite.ActualDressedFrequencyInverse.source_inverse_applied_integrable,#[
    ``LowEnergy.SourcePropagationResolvent.sourceInverse_integrable]),
    (``LowEnergy.GaussComposite.ActualDressedFrequencyInverse.source_inverse_applied_read,#[
    ``LowEnergy.SourcePropagationResolvent.sourceInverse_integrable,
    ``LowEnergy.SourcePropagationResolvent.sourceInverse]),
    (``LowEnergy.GaussComposite.ActualDressedFrequencyInverse.noether_memory_weighted,#[
    ``LowEnergy.GaussComposite.ActualDressedFrequencyInverse.noether_memory_convolution]),
    (``LowEnergy.GaussComposite.ActualDressedFrequencyInverse.plane_noether_memory_integrable,#[
    ``LowEnergy.GaussComposite.ActualDressedFrequencyInverse.source_inverse_applied_integrable,
    ``LowEnergy.GaussComposite.ActualDressedFrequencyInverse.noether_memory_weighted]),
    (``LowEnergy.GaussComposite.ActualDressedFrequencyInverse.plane_noether_memory_inverse,#[
    ``MeasureTheory.integral_posConvolution,
    ``LowEnergy.GaussComposite.ActualDressedFrequencyInverse.source_inverse_applied_read,
    ``LowEnergy.GaussComposite.ActualDressedFrequencyInverse.noether_memory_weighted]),
    (``LowEnergy.GaussComposite.ActualDressedFrequencyInverse.plane_noether_operator_integrable,#[
    ``LowEnergy.GaussComposite.ActualDressedFrequencyInverse.plane_noether_memory_integrable]),
    (``LowEnergy.GaussComposite.ActualDressedFrequencyInverse.plane_noether_operator_inverse,#[
    ``LowEnergy.GaussComposite.ActualDressedFrequencyInverse.plane_noether_memory_inverse,
    ``LowEnergy.GaussComposite.ActualDressedFrequencyInverse.source_inverse_applied_read]),
    (``LowEnergy.GaussComposite.ActualDressedFrequencyInverse.dressed_plane_history_generated,#[
    ``LowEnergy.GaussComposite.ActualDressedClockMoment.dressed_signal_history_matrix,
    ``LowEnergy.GaussComposite.ActualDressedFrequencyInverse.plane_noether_observer]),
    (``LowEnergy.GaussComposite.ActualDressedFrequencyInverse.dressed_frequency_half_inverse,#[
    ``LowEnergy.GaussComposite.ActualDressedFrequencyHalf.frequency_half_polarization_integral,
    ``LowEnergy.GaussComposite.ActualDressedFrequencyInverse.plane_noether_operator_inverse]),
    (``LowEnergy.GaussComposite.ActualDressedFrequencyInverse.damped_fourier_polarization_inverse,#[
    ``LowEnergy.GaussComposite.ActualDressedFrequencyInverse.dressed_frequency_half_inverse,
    ``LowEnergy.GaussComposite.ActualDressedFrequencyHalf.damped_fourier_source_domain]),
    (``LowEnergy.GaussComposite.ActualDressedFrequencyInverse.damped_physical_response_inverse,#[
    ``LowEnergy.GaussComposite.ActualDressedFrequencyHalf.damped_fourier_response,
    ``LowEnergy.GaussComposite.ActualDressedFrequencyInverse.damped_fourier_polarization_inverse]),
    (``LowEnergy.GaussComposite.ActualDressedFrequencyInverse.plane_response_denominator_nonzero,#[
    ``LowEnergy.SourcePropagationAlgebraicResponse.propagationPolynomial_offAxis]),
    (``LowEnergy.GaussComposite.ActualDressedFrequencyInverse.plane_noether_inverse_rational,#[
    ``LowEnergy.SourcePropagationAlgebraicResponse.polynomialResolvent_future,
    ``LowEnergy.SourcePropagationAlgebraicResponse.propagationPolynomial_offAxis]),
    (``LowEnergy.GaussComposite.ActualDressedFrequencyInverse.dressed_frequency_polarization_rational,#[
    ``LowEnergy.GaussComposite.ActualDressedFrequencyInverse.plane_noether_inverse_rational,
    ``LowEnergy.GaussComposite.ActualDressedFrequencyInverse.dressed_frequency_half_inverse]),
    (``LowEnergy.GaussComposite.ActualDressedFrequencyInverse.dressed_frequency_response_rational,#[
    ``LowEnergy.GaussComposite.ActualDressedFrequencyHalf.frequency_input_normalizer_generated,
    ``LowEnergy.GaussComposite.ActualDressedFrequencyInverse.dressed_frequency_polarization_rational]),
    (``LowEnergy.GaussComposite.ActualDressedFrequencyInverse.actual_zero_transfer_denominator,#[
    ``LowEnergy.SourcePropagationConstrainedPoleReturn.zero_transfer_sourcePole,
    ``LowEnergy.GaussComposite.ActualDressedFrequencyInverse.plane_static_denominator])]
  for (mouth,required) in direct do packageCertRequire env mouth required
  let testProducers := #[
    ``LowEnergy.GaussComposite.ActualDressedFrequencyInverse.noether_memory_convolution,
    ``LowEnergy.GaussComposite.ActualDressedFrequencyInverse.source_inverse_applied_integrable,
    ``LowEnergy.GaussComposite.ActualDressedFrequencyInverse.source_inverse_applied_read,
    ``LowEnergy.GaussComposite.ActualDressedFrequencyInverse.noether_memory_weighted,
    ``LowEnergy.GaussComposite.ActualDressedFrequencyInverse.plane_noether_memory_integrable,
    ``LowEnergy.GaussComposite.ActualDressedFrequencyInverse.plane_noether_memory_inverse,
    ``LowEnergy.GaussComposite.ActualDressedFrequencyInverse.plane_noether_operator_integrable,
    ``LowEnergy.GaussComposite.ActualDressedFrequencyInverse.plane_noether_operator_inverse,
    ``LowEnergy.GaussComposite.ActualDressedFrequencyInverse.plane_noether_observer,
    ``LowEnergy.GaussComposite.ActualDressedFrequencyInverse.dressed_plane_history_generated,
    ``LowEnergy.GaussComposite.ActualDressedFrequencyInverse.dressed_frequency_half_inverse,
    ``LowEnergy.GaussComposite.ActualDressedFrequencyInverse.damped_fourier_polarization_inverse,
    ``LowEnergy.GaussComposite.ActualDressedFrequencyInverse.damped_physical_response_inverse,
    ``LowEnergy.GaussComposite.ActualDressedFrequencyInverse.plane_response_denominator_nonzero,
    ``LowEnergy.GaussComposite.ActualDressedFrequencyInverse.plane_noether_inverse_rational,
    ``LowEnergy.GaussComposite.ActualDressedFrequencyInverse.dressed_frequency_polarization_rational,
    ``LowEnergy.GaussComposite.ActualDressedFrequencyInverse.dressed_frequency_response_rational,
    ``LowEnergy.GaussComposite.ActualDressedFrequencyInverse.plane_static_denominator,
    ``LowEnergy.GaussComposite.ActualDressedFrequencyInverse.actual_zero_transfer_denominator]
  for i in [:testProducers.size] do packageCertRequire env tests[i]! #[testProducers[i]!]
  let all ← packageCertClosure env (owned ++ tests.toList)
  let anchors := #[
    ``SaturationMonoid.PhysicsCore.StageNineEnrichedProofFreeSource.positiveSmoothUnifiedSource,
    ``SaturationMonoid.PhysicsCore.Stage9C.Material.SpinPair.actual,
    ``LowEnergy.GaussComposite.ActualDressedSourcePreparation.sourceDressedUnit,
    ``LowEnergy.PreparationVacuumSourcePreparedResponse.sourceProfile,
    ``LowEnergy.GaussComposite.ActualDressedNoether.dressedEulerObserver,
    ``LowEnergy.GaussComposite.ActualDressedHistoryKernel.noetherMemoryMap,
    ``LowEnergy.PreparationVacuumPropagationPencil.rawInitial,
    ``LowEnergy.PreparationVacuumCurrentSignalOperator.sourceMaterialMap,
    ``LowEnergy.PreparationVacuumCurrentSignalOperator.sourceContactMap,
    ``LowEnergy.SourcePropagationResolvent.twoTimeMap,
    ``LowEnergy.SourcePropagationResolvent.sourceInverse,
    ``LowEnergy.SourcePropagationAlgebraicResponse.propagationPolynomial,
    ``LowEnergy.SourcePropagationAlgebraicResponse.propagationNumerator]
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
  if let some path ← liftIO (IO.getEnv "ALPHA_DRESSED_FREQUENCY_INVERSE_AUDIT_OUTPUT") then
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
  logInfo m!"DRESSED_FREQUENCY_INVERSE_PASS public={mouths.size} owned={owned.length} tests={tests.size} nodes={all.size} anchors={anchors.size} direct={direct.size} opaque_all_read={opaques} axioms={axioms} unknown=0 unsafe=0 partial=0"
#audit_dressed_frequency_inverse
#print axioms LowEnergy.GaussComposite.ActualDressedFrequencyInverse.noether_memory_convolution
#print axioms LowEnergy.GaussComposite.ActualDressedFrequencyInverse.source_inverse_applied_integrable
#print axioms LowEnergy.GaussComposite.ActualDressedFrequencyInverse.source_inverse_applied_read
#print axioms LowEnergy.GaussComposite.ActualDressedFrequencyInverse.noether_memory_weighted
#print axioms LowEnergy.GaussComposite.ActualDressedFrequencyInverse.plane_noether_memory_integrable
#print axioms LowEnergy.GaussComposite.ActualDressedFrequencyInverse.plane_noether_memory_inverse
#print axioms LowEnergy.GaussComposite.ActualDressedFrequencyInverse.plane_noether_operator_integrable
#print axioms LowEnergy.GaussComposite.ActualDressedFrequencyInverse.plane_noether_operator_inverse
#print axioms LowEnergy.GaussComposite.ActualDressedFrequencyInverse.plane_noether_observer
#print axioms LowEnergy.GaussComposite.ActualDressedFrequencyInverse.dressed_plane_history_generated
#print axioms LowEnergy.GaussComposite.ActualDressedFrequencyInverse.dressed_frequency_half_inverse
#print axioms LowEnergy.GaussComposite.ActualDressedFrequencyInverse.damped_fourier_polarization_inverse
#print axioms LowEnergy.GaussComposite.ActualDressedFrequencyInverse.damped_physical_response_inverse
#print axioms LowEnergy.GaussComposite.ActualDressedFrequencyInverse.plane_response_denominator_nonzero
#print axioms LowEnergy.GaussComposite.ActualDressedFrequencyInverse.plane_noether_inverse_rational
#print axioms LowEnergy.GaussComposite.ActualDressedFrequencyInverse.dressed_frequency_polarization_rational
#print axioms LowEnergy.GaussComposite.ActualDressedFrequencyInverse.dressed_frequency_response_rational
#print axioms LowEnergy.GaussComposite.ActualDressedFrequencyInverse.plane_static_denominator
#print axioms LowEnergy.GaussComposite.ActualDressedFrequencyInverse.actual_zero_transfer_denominator
