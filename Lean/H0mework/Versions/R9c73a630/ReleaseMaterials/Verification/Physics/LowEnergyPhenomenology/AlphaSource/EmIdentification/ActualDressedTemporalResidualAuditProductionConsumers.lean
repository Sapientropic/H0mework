import H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualDressedPreparationWardResidual
import H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualDressedTemporalHalfResidual
import H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualDressedTemporalQuantumResidual
import H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualDressedStaticPoleWard

import Lean.Elab.Command
import Lean.Util.FoldConsts
import Lean.Util.CollectAxioms
set_option autoImplicit false
set_option maxHeartbeats 12000000
set_option maxRecDepth 32768
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.GaussComposite.ActualDressedTemporalResidualAudit
elab "checked_preparation_ward_residual_returnContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualDressedTemporalResidual.preparation_ward_residual_return).type
theorem checked_preparation_ward_residual_return : checked_preparation_ward_residual_returnContract := @LowEnergy.GaussComposite.ActualDressedTemporalResidual.preparation_ward_residual_return

elab "checked_preparation_ward_observer_priceContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualDressedTemporalResidual.preparation_ward_observer_price).type
theorem checked_preparation_ward_observer_price : checked_preparation_ward_observer_priceContract := @LowEnergy.GaussComposite.ActualDressedTemporalResidual.preparation_ward_observer_price

elab "checked_preparation_ward_observer_limitContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualDressedTemporalResidual.preparation_ward_observer_limit).type
theorem checked_preparation_ward_observer_limit : checked_preparation_ward_observer_limitContract := @LowEnergy.GaussComposite.ActualDressedTemporalResidual.preparation_ward_observer_limit

elab "checked_physical_preparation_returnContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualDressedTemporalResidual.physical_preparation_return).type
theorem checked_physical_preparation_return : checked_physical_preparation_returnContract := @LowEnergy.GaussComposite.ActualDressedTemporalResidual.physical_preparation_return

elab "checked_temporal_half_physical_actionContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualDressedTemporalResidual.temporal_half_physical_action).type
theorem checked_temporal_half_physical_action : checked_temporal_half_physical_actionContract := @LowEnergy.GaussComposite.ActualDressedTemporalResidual.temporal_half_physical_action

elab "checked_temporal_half_preparation_returnContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualDressedTemporalResidual.temporal_half_preparation_return).type
theorem checked_temporal_half_preparation_return : checked_temporal_half_preparation_returnContract := @LowEnergy.GaussComposite.ActualDressedTemporalResidual.temporal_half_preparation_return

elab "checked_temporal_half_preparation_priceContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualDressedTemporalResidual.temporal_half_preparation_price).type
theorem checked_temporal_half_preparation_price : checked_temporal_half_preparation_priceContract := @LowEnergy.GaussComposite.ActualDressedTemporalResidual.temporal_half_preparation_price

elab "checked_temporal_half_preparation_limitContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualDressedTemporalResidual.temporal_half_preparation_limit).type
theorem checked_temporal_half_preparation_limit : checked_temporal_half_preparation_limitContract := @LowEnergy.GaussComposite.ActualDressedTemporalResidual.temporal_half_preparation_limit

elab "checked_temporal_quantum_physical_actionContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualDressedTemporalResidual.temporal_quantum_physical_action).type
theorem checked_temporal_quantum_physical_action : checked_temporal_quantum_physical_actionContract := @LowEnergy.GaussComposite.ActualDressedTemporalResidual.temporal_quantum_physical_action

elab "checked_temporal_quantum_preparation_returnContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualDressedTemporalResidual.temporal_quantum_preparation_return).type
theorem checked_temporal_quantum_preparation_return : checked_temporal_quantum_preparation_returnContract := @LowEnergy.GaussComposite.ActualDressedTemporalResidual.temporal_quantum_preparation_return

elab "checked_temporal_quantum_preparation_priceContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualDressedTemporalResidual.temporal_quantum_preparation_price).type
theorem checked_temporal_quantum_preparation_price : checked_temporal_quantum_preparation_priceContract := @LowEnergy.GaussComposite.ActualDressedTemporalResidual.temporal_quantum_preparation_price

elab "checked_temporal_quantum_preparation_limitContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualDressedTemporalResidual.temporal_quantum_preparation_limit).type
theorem checked_temporal_quantum_preparation_limit : checked_temporal_quantum_preparation_limitContract := @LowEnergy.GaussComposite.ActualDressedTemporalResidual.temporal_quantum_preparation_limit

elab "checked_source_leading_pencil_zeroContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualDressedTemporalResidual.source_leading_pencil_zero).type
theorem checked_source_leading_pencil_zero : checked_source_leading_pencil_zeroContract := @LowEnergy.GaussComposite.ActualDressedTemporalResidual.source_leading_pencil_zero

elab "checked_source_leading_physical_actionContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualDressedTemporalResidual.source_leading_physical_action).type
theorem checked_source_leading_physical_action : checked_source_leading_physical_actionContract := @LowEnergy.GaussComposite.ActualDressedTemporalResidual.source_leading_physical_action

elab "checked_static_pole_physical_actionContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualDressedTemporalResidual.static_pole_physical_action).type
theorem checked_static_pole_physical_action : checked_static_pole_physical_actionContract := @LowEnergy.GaussComposite.ActualDressedTemporalResidual.static_pole_physical_action

elab "checked_static_pole_preparation_returnContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualDressedTemporalResidual.static_pole_preparation_return).type
theorem checked_static_pole_preparation_return : checked_static_pole_preparation_returnContract := @LowEnergy.GaussComposite.ActualDressedTemporalResidual.static_pole_preparation_return

elab "checked_static_pole_preparation_priceContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualDressedTemporalResidual.static_pole_preparation_price).type
theorem checked_static_pole_preparation_price : checked_static_pole_preparation_priceContract := @LowEnergy.GaussComposite.ActualDressedTemporalResidual.static_pole_preparation_price

elab "checked_static_pole_preparation_limitContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualDressedTemporalResidual.static_pole_preparation_limit).type
theorem checked_static_pole_preparation_limit : checked_static_pole_preparation_limitContract := @LowEnergy.GaussComposite.ActualDressedTemporalResidual.static_pole_preparation_limit

open CanonicalGradedSpatialSource GaussCoreHilbert
open PreparationVacuumMixedFieldReturn PreparationVacuumActionFieldLift
open PreparationVacuumPhysicalFeedback PreparationVacuumGaugeSourceInjection PreparationVacuumNoetherOrdinaryWard
open PreparationVacuumSourcePreparedState PreparationVacuumPreparedCurrent
open ActualDressedFullCoulomb ActualDressedNoether ActualDressedSylvester ActualDressedStaticResponse
open ActualDressedTemporalHalf ActualDressedTemporalResidual ActualDressedStaticPole ActualDressedPreparationEnergy
open Filter
open scoped Topology Matrix

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

theorem actual_nonreal_not_variational_energy (event : DressedEvent) : event.energy≠(sourceEnergy:ℂ) := by
  intro same
  apply event.nonreal
  rw [same]
  exact Complex.ofReal_im _

theorem actual_all289_temporal_quantum (event : DressedEvent) (a : Fin 12) (j : Fin 289) :
    (staticQuantumCorrection event 0 1*ᵥ(fun k=>(fieldUnit j k:ℂ))) (gaugeSlot 0 a)-
      dressedEulerObserver event (temporalGaussInitialJet (dressedKinematicPoint event 0) a (fieldUnit j))-
      Complex.I*dressedEulerObserver event (temporalPhysicalDrive (dressedKinematicPoint event 0) a (fieldUnit j) 1)-
      Complex.I*physicalPreparationMismatch event 0
        (temporalGaussHalfJet (dressedKinematicPoint event 0) a (fieldUnit j) 1)=
      Complex.I*preparationWardObserver event
        (temporalGaussHalfJet (dressedKinematicPoint event 0) a (fieldUnit j) 1) :=
  temporal_quantum_preparation_return event 0 a (fieldUnit j) 1 (by norm_num)

theorem actual_all289_pole_preparation (event : DressedEvent) (i j : Fin 289) :
    physicalPreparationMismatch event 0
      (staticPoleLeadingOperator (dressedKinematicPoint event 0) (fieldUnit i) (fieldUnit j))=
      -preparationWardObserver event
        (staticPoleLeadingOperator (dressedKinematicPoint event 0) (fieldUnit i) (fieldUnit j)) :=
  static_pole_preparation_return event (fieldUnit i) (fieldUnit j)

theorem actual_all289_pole_preparation_limit (event : DressedEvent) (i j : Fin 289) :
    Tendsto (fun n : ℕ=>physicalPreparationMismatch (preparationEventSequence event n) 0
      (staticPoleLeadingOperator (dressedKinematicPoint (preparationEventSequence event n) 0) (fieldUnit i) (fieldUnit j)))
      atTop (𝓝 0) :=
  static_pole_preparation_limit event (fieldUnit i) (fieldUnit j)
end LowEnergy.GaussComposite.ActualDressedTemporalResidualAudit

