import H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualDressedFieldTimeFull
import H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualDressedFieldTimeSector
import H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualDressedFieldTimeConsumer

import Lean.Elab.Command
import Lean.Util.FoldConsts
import Lean.Util.CollectAxioms
set_option autoImplicit false
set_option maxHeartbeats 12000000
set_option maxRecDepth 32768
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.GaussComposite.ActualDressedFieldTimeAudit
elab "checked_actual_field_C_gradeContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualDressedFieldTime.actual_field_C_grade).type
theorem checked_actual_field_C_grade : checked_actual_field_C_gradeContract := @LowEnergy.GaussComposite.ActualDressedFieldTime.actual_field_C_grade

elab "checked_actual_field_generator_sourceContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualDressedFieldTime.actual_field_generator_source).type
theorem checked_actual_field_generator_source : checked_actual_field_generator_sourceContract := @LowEnergy.GaussComposite.ActualDressedFieldTime.actual_field_generator_source

elab "checked_actual_field_prefix_terminalContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualDressedFieldTime.actual_field_prefix_terminal).type
theorem checked_actual_field_prefix_terminal : checked_actual_field_prefix_terminalContract := @LowEnergy.GaussComposite.ActualDressedFieldTime.actual_field_prefix_terminal

elab "checked_actual_field_prefix_derivativeContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualDressedFieldTime.actual_field_prefix_derivative).type
theorem checked_actual_field_prefix_derivative : checked_actual_field_prefix_derivativeContract := @LowEnergy.GaussComposite.ActualDressedFieldTime.actual_field_prefix_derivative

elab "checked_actual_field_time_finitePrefixContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualDressedFieldTime.actual_field_time_finitePrefix).type
theorem checked_actual_field_time_finitePrefix : checked_actual_field_time_finitePrefixContract := @LowEnergy.GaussComposite.ActualDressedFieldTime.actual_field_time_finitePrefix

elab "checked_actual_field_interaction_N2G0_rangeContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualDressedFieldTime.actual_field_interaction_N2G0_range).type
theorem checked_actual_field_interaction_N2G0_range : checked_actual_field_interaction_N2G0_rangeContract := @LowEnergy.GaussComposite.ActualDressedFieldTime.actual_field_interaction_N2G0_range

elab "checked_actual_field_interaction_N2G1_rangeContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualDressedFieldTime.actual_field_interaction_N2G1_range).type
theorem checked_actual_field_interaction_N2G1_range : checked_actual_field_interaction_N2G1_rangeContract := @LowEnergy.GaussComposite.ActualDressedFieldTime.actual_field_interaction_N2G1_range

elab "checked_actual_field_interaction_N2G2_zeroContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualDressedFieldTime.actual_field_interaction_N2G2_zero).type
theorem checked_actual_field_interaction_N2G2_zero : checked_actual_field_interaction_N2G2_zeroContract := @LowEnergy.GaussComposite.ActualDressedFieldTime.actual_field_interaction_N2G2_zero

elab "checked_actual_field_ordered_N2G2_zeroContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualDressedFieldTime.actual_field_ordered_N2G2_zero).type
theorem checked_actual_field_ordered_N2G2_zero : checked_actual_field_ordered_N2G2_zeroContract := @LowEnergy.GaussComposite.ActualDressedFieldTime.actual_field_ordered_N2G2_zero

elab "checked_actual_field_ordered_N2G1_high_zeroContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualDressedFieldTime.actual_field_ordered_N2G1_high_zero).type
theorem checked_actual_field_ordered_N2G1_high_zero : checked_actual_field_ordered_N2G1_high_zeroContract := @LowEnergy.GaussComposite.ActualDressedFieldTime.actual_field_ordered_N2G1_high_zero

elab "checked_actual_field_ordered_N2G0_high_zeroContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualDressedFieldTime.actual_field_ordered_N2G0_high_zero).type
theorem checked_actual_field_ordered_N2G0_high_zero : checked_actual_field_ordered_N2G0_high_zeroContract := @LowEnergy.GaussComposite.ActualDressedFieldTime.actual_field_ordered_N2G0_high_zero

elab "checked_actual_field_prefix_N2_high_zeroContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualDressedFieldTime.actual_field_prefix_N2_high_zero).type
theorem checked_actual_field_prefix_N2_high_zero : checked_actual_field_prefix_N2_high_zeroContract := @LowEnergy.GaussComposite.ActualDressedFieldTime.actual_field_prefix_N2_high_zero

elab "checked_actual_field_time_N2_grade_returnContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualDressedFieldTime.actual_field_time_N2_grade_return).type
theorem checked_actual_field_time_N2_grade_return : checked_actual_field_time_N2_grade_returnContract := @LowEnergy.GaussComposite.ActualDressedFieldTime.actual_field_time_N2_grade_return

elab "checked_actual_field_time_N2_projection_returnContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualDressedFieldTime.actual_field_time_N2_projection_return).type
theorem checked_actual_field_time_N2_projection_return : checked_actual_field_time_N2_projection_returnContract := @LowEnergy.GaussComposite.ActualDressedFieldTime.actual_field_time_N2_projection_return

elab "checked_actual_field_time_created_unitContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualDressedFieldTime.actual_field_time_created_unit).type
theorem checked_actual_field_time_created_unit : checked_actual_field_time_created_unitContract := @LowEnergy.GaussComposite.ActualDressedFieldTime.actual_field_time_created_unit

elab "checked_actual_field_interaction_N1G0_rangeContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualDressedFieldTime.actual_field_interaction_N1G0_range).type
theorem checked_actual_field_interaction_N1G0_range : checked_actual_field_interaction_N1G0_rangeContract := @LowEnergy.GaussComposite.ActualDressedFieldTime.actual_field_interaction_N1G0_range

elab "checked_actual_field_interaction_N1G1_zeroContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualDressedFieldTime.actual_field_interaction_N1G1_zero).type
theorem checked_actual_field_interaction_N1G1_zero : checked_actual_field_interaction_N1G1_zeroContract := @LowEnergy.GaussComposite.ActualDressedFieldTime.actual_field_interaction_N1G1_zero

elab "checked_actual_field_ordered_N1G1_zeroContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualDressedFieldTime.actual_field_ordered_N1G1_zero).type
theorem checked_actual_field_ordered_N1G1_zero : checked_actual_field_ordered_N1G1_zeroContract := @LowEnergy.GaussComposite.ActualDressedFieldTime.actual_field_ordered_N1G1_zero

elab "checked_actual_field_ordered_N1G0_high_zeroContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualDressedFieldTime.actual_field_ordered_N1G0_high_zero).type
theorem checked_actual_field_ordered_N1G0_high_zero : checked_actual_field_ordered_N1G0_high_zeroContract := @LowEnergy.GaussComposite.ActualDressedFieldTime.actual_field_ordered_N1G0_high_zero

elab "checked_actual_field_prefix_N1G0_high_zeroContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualDressedFieldTime.actual_field_prefix_N1G0_high_zero).type
theorem checked_actual_field_prefix_N1G0_high_zero : checked_actual_field_prefix_N1G0_high_zeroContract := @LowEnergy.GaussComposite.ActualDressedFieldTime.actual_field_prefix_N1G0_high_zero

elab "checked_actual_field_prefix_N1G1_high_zeroContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualDressedFieldTime.actual_field_prefix_N1G1_high_zero).type
theorem checked_actual_field_prefix_N1G1_high_zero : checked_actual_field_prefix_N1G1_high_zeroContract := @LowEnergy.GaussComposite.ActualDressedFieldTime.actual_field_prefix_N1G1_high_zero

elab "checked_actual_field_prefix_N1_high_zeroContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualDressedFieldTime.actual_field_prefix_N1_high_zero).type
theorem checked_actual_field_prefix_N1_high_zero : checked_actual_field_prefix_N1_high_zeroContract := @LowEnergy.GaussComposite.ActualDressedFieldTime.actual_field_prefix_N1_high_zero

elab "checked_actual_field_time_N1_projection_returnContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualDressedFieldTime.actual_field_time_N1_projection_return).type
theorem checked_actual_field_time_N1_projection_return : checked_actual_field_time_N1_projection_returnContract := @LowEnergy.GaussComposite.ActualDressedFieldTime.actual_field_time_N1_projection_return

elab "checked_actual_field_time_backgroundContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualDressedFieldTime.actual_field_time_background).type
theorem checked_actual_field_time_background : checked_actual_field_time_backgroundContract := @LowEnergy.GaussComposite.ActualDressedFieldTime.actual_field_time_background

elab "checked_actual_finite_number_field_readContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualDressedFieldTime.actual_finite_number_field_read).type
theorem checked_actual_finite_number_field_read : checked_actual_finite_number_field_readContract := @LowEnergy.GaussComposite.ActualDressedFieldTime.actual_finite_number_field_read

elab "checked_actual_finite_noether_field_germContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualDressedFieldTime.actual_finite_noether_field_germ).type
theorem checked_actual_finite_noether_field_germ : checked_actual_finite_noether_field_germContract := @LowEnergy.GaussComposite.ActualDressedFieldTime.actual_finite_noether_field_germ

elab "checked_actual_finite_number_field_quantum_derivativeContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualDressedFieldTime.actual_finite_number_field_quantum_derivative).type
theorem checked_actual_finite_number_field_quantum_derivative : checked_actual_finite_number_field_quantum_derivativeContract := @LowEnergy.GaussComposite.ActualDressedFieldTime.actual_finite_number_field_quantum_derivative

elab "checked_actual_finite_created_time_directionContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualDressedFieldTime.actual_finite_created_time_direction).type
theorem checked_actual_finite_created_time_direction : checked_actual_finite_created_time_directionContract := @LowEnergy.GaussComposite.ActualDressedFieldTime.actual_finite_created_time_direction

elab "checked_actual_finite_background_time_directionContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualDressedFieldTime.actual_finite_background_time_direction).type
theorem checked_actual_finite_background_time_direction : checked_actual_finite_background_time_directionContract := @LowEnergy.GaussComposite.ActualDressedFieldTime.actual_finite_background_time_direction

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


theorem same_actual_field_time_carriers (p : PhysicalMomentum) (F : GaussUnitaryHistory.Index) (h : Field289) (t : ℝ) :
    physicalTime p F t h*numberTwoProjection=
      FullYSourceCutoffVolterra.partialEvolution (jointCompression p F h)
        (jointY (PreparationVacuumYukawaTransport.finiteRetainer p F) h) 2 t*numberTwoProjection ∧
    physicalTime p F t h*sourceN1Projection=
      FullYSourceCutoffVolterra.partialEvolution (jointCompression p F h)
        (jointY (PreparationVacuumYukawaTransport.finiteRetainer p F) h) 1 t*sourceN1Projection :=
  ⟨actual_field_time_N2_projection_return p F h t,actual_field_time_N1_projection_return p F h t⟩

theorem same_actual_finite_noether_zero (event : DressedEvent) (transfer : PhysicalMomentum)
    (age : ℝ) (reader : Field289) :
    dressedEulerObserver event (dressedNoetherKernel event transfer reader age 0)=
      finiteNumberFieldRead event transfer reader age 0 :=
  (actual_finite_noether_field_germ event transfer).self_of_nhds age reader

theorem same_actual_finite_quantum_response (event : DressedEvent) (transfer : PhysicalMomentum)
    (force : Field289) (age : ℝ) (i : Fin 289) :
    deriv (fun r : ℝ=>finiteNumberFieldRead event transfer
      (PreparationVacuumActionFieldLift.fieldUnit i) age (r • force)) 0=
      (dressedNoetherJet event transfer (fun _=>⟨force,0,0⟩) age i).value :=
  (actual_finite_number_field_quantum_derivative event transfer force age i).deriv
end LowEnergy.GaussComposite.ActualDressedFieldTimeAudit

