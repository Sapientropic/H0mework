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

