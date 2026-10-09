import H0mework.Versions.R9c73a630.ReleaseMaterials.DomainProofs.CPS1ResourceExecution.CPS1AddressedBondRenewal.NativeSource

set_option autoImplicit false
set_option maxHeartbeats 200000

namespace CPS1AddressedBondRenewal
noncomputable section
open CPS1Deformation CPS1AddressedTransfer CPS1PositivePulse CPS1AddressedBondResponse
open CPS1ElectronicSource (ElectronIndex SpinSpace electronCount)
open scoped BigOperators
variable {frame : CPS1Recycling.Frame}

namespace NativeSource

def stepFields {current : Source.Occurrence frame} (admission : Admission current) (index : Nat) :
    ElectronIndex (trajectory (initial admission) index).material.reference.geometry → SpinSpace :=
  responseFields (trajectory (initial admission) index).material (timeAt (initial admission) index)

def stepSiteFields {current : Source.Occurrence frame} (admission : Admission current) (index : Nat) :
    ElectronIndex (trajectory (initial admission) index).material.reference.geometry → SpinSpace :=
  fun slot => siteProjection (trajectory (initial admission) index).material.reference
    ((trajectory (initial admission) index).material.movedPositions (timeAt (initial admission) index))
    (trajectory (initial admission) index).site.phosphate.nuclear (stepFields admission index slot)

def stepComplementFields {current : Source.Occurrence frame} (admission : Admission current) (index : Nat) :
    ElectronIndex (trajectory (initial admission) index).material.reference.geometry → SpinSpace :=
  fun slot => stepFields admission index slot-stepSiteFields admission index slot

theorem generated_step_fields_actual {current : Source.Occurrence frame} (admission : Admission current) (index : Nat) :
    HEq (stepFields admission index) (trajectory (initial admission) (index+1)).material.currentFields := HEq.rfl

theorem generated_step_whole_fields {current : Source.Occurrence frame} (admission : Admission current) (index : Nat) :
    HEq (fun slot => stepSiteFields admission index slot+stepComplementFields admission index slot)
      (trajectory (initial admission) (index+1)).material.currentFields := by
  have same : (fun slot => stepSiteFields admission index slot+stepComplementFields admission index slot) =
      stepFields admission index := funext (fun _ => add_sub_cancel _ _)
  rw [same]
  exact generated_step_fields_actual admission index

theorem generated_step_electron_number {current : Source.Occurrence frame} (admission : Admission current) (index : Nat) :
    (∑ slot, ‖stepSiteFields admission index slot‖^2)+(∑ slot, ‖stepComplementFields admission index slot‖^2) =
      electronCount frame (trajectory (initial admission) index).material.reference.geometry.originJoint :=
  response_partition_number (trajectory (initial admission) index).material
    (trajectory (initial admission) index).site.phosphate.nuclear (timeAt (initial admission) index)
    (advance_normalized (trajectory (initial admission) index))

end NativeSource

structure SeriesProperties {current : Source.Occurrence frame}
    (admission : NativeSource.Admission current) (depth : Nat) : Prop where
  sourceProgram : type_of% (NativeSource.generated_program admission depth)
  fullPrefix : type_of% (NativeSource.prefix_paid admission depth)
  fullSuffix : type_of% (NativeSource.fired_prefix_and_suffix admission depth)
  actualExecution : type_of% (NativeSource.continued_execution admission depth)
  finalStock : type_of% (NativeSource.continued_final_stock admission depth)
  pending : type_of% (NativeSource.continued_pending admission depth)
  wholeInventory : type_of% (NativeSource.continued_whole_inventory admission depth)
  actualCut : type_of% (NativeSource.continued_cut admission depth)
  terminalReady : type_of% (NativeSource.terminal_ready admission depth)
  terminalActive : type_of% (NativeSource.terminal_active admission depth)
  terminalSite : type_of% (NativeSource.terminal_site admission depth)
  terminalSource : type_of% (NativeSource.terminal_source admission depth)
  terminalPayment : type_of% (NativeSource.terminal_payment admission depth)
  signedSteps : type_of% (NativeSource.generated_step_signed admission)
  actualStepFields : type_of% (NativeSource.generated_step_fields_actual admission)
  wholeStepFields : type_of% (NativeSource.generated_step_whole_fields admission)
  stepElectronNumber : type_of% (NativeSource.generated_step_electron_number admission)
  signedDistances : type_of% (NativeSource.generated_step_signed_distance admission)
  nextVelocity : type_of% (NativeSource.generated_step_nonzero_velocity admission)
  terminalDrive : type_of% (NativeSource.terminal_driven admission depth)
  sourceP28 : type_of% (trajectory_same_atom_slot (NativeSource.initial admission))
  sourceO25 : type_of% (trajectory_same_oxygen_slot (NativeSource.initial admission))
  positiveSteps : type_of% (NativeSource.generated_time_positive admission)
  goodStock : type_of% (NativeSource.continued_stock_good admission depth)
  noGuardStock : type_of% (NativeSource.continued_stock_noGuard admission depth)
  samePrevious : type_of% (NativeSource.continued_previous admission depth)

theorem series_properties {current : Source.Occurrence frame}
    (admission : NativeSource.Admission current) (depth : Nat) : SeriesProperties admission depth :=
  ⟨NativeSource.generated_program admission depth,NativeSource.prefix_paid admission depth,
   NativeSource.fired_prefix_and_suffix admission depth,NativeSource.continued_execution admission depth,
   NativeSource.continued_final_stock admission depth,NativeSource.continued_pending admission depth,
   NativeSource.continued_whole_inventory admission depth,NativeSource.continued_cut admission depth,
   NativeSource.terminal_ready admission depth,NativeSource.terminal_active admission depth,
   NativeSource.terminal_site admission depth,NativeSource.terminal_source admission depth,
   NativeSource.terminal_payment admission depth,NativeSource.generated_step_signed admission,
   NativeSource.generated_step_fields_actual admission,NativeSource.generated_step_whole_fields admission,
   NativeSource.generated_step_electron_number admission,NativeSource.generated_step_signed_distance admission,
   NativeSource.generated_step_nonzero_velocity admission,NativeSource.terminal_driven admission depth,
   trajectory_same_atom_slot (NativeSource.initial admission),trajectory_same_oxygen_slot (NativeSource.initial admission),
   NativeSource.generated_time_positive admission,
   NativeSource.continued_stock_good admission depth,NativeSource.continued_stock_noGuard admission depth,
   NativeSource.continued_previous admission depth⟩

def CurrentResult (current : Source.Occurrence frame) (depth : Nat) : Prop :=
  match CPS1AddressedBondResponse.NativeSource.autoBondResponse? current with
  | none => NativeSource.next current depth = Source.resume frame current [] []
  | some admission => NativeSource.next current depth = NativeSource.continued admission depth ∧
      SeriesProperties admission depth

theorem current_result (current : Source.Occurrence frame) (depth : Nat) : CurrentResult current depth := by
  cases generated : CPS1AddressedBondResponse.NativeSource.autoBondResponse? current with
  | none => simp only [CurrentResult,generated,NativeSource.next,NativeSource.autoContinue?,Option.map_none,Option.getD_none]
  | some admission =>
    simp only [CurrentResult,generated,NativeSource.next,NativeSource.autoContinue?,Option.map_some,Option.getD_some,true_and]
    exact series_properties admission depth

structure BondRenewalContract : Prop where
  sourceBridge : type_of% @selected_bridge_source
  originalBridge : type_of% @selected_bridge_bond
  actualMotion : type_of% @relative_motion
  actualDistance : type_of% @distance_response
  exactDrive : type_of% @distance_polynomial_none
  actualNextVelocity : type_of% @renewed_relative_velocity
  generatedNextVelocity : type_of% @renewed_velocity_eventually_nonzero
  generatedNextDrive : type_of% @velocity_generates_leading
  sourceSite : type_of% @renewed_bridge_site
  actualRenewal : type_of% @bridge_response_eventually_renewing
  generatedDyadic : type_of% @renewing_index_spec
  generatedMinimum : type_of% @renewing_index_minimal
  actualStep : type_of% @advance_actual
  actualTrajectory : type_of% @trajectory_actual
  sourceTrajectory : type_of% @trajectory_same_reference
  sourceComponent : type_of% @trajectory_same_component
  sourcePhosphate : type_of% @trajectory_same_atom_slot
  sourceOxygen : type_of% @trajectory_same_oxygen_slot
  elapsedProgress : type_of% @elapsed_strict
  currentResult : type_of% @current_result
  nativeNext : type_of% @NativeSource.next_previous

theorem sourceGeneratedBondRenewal : BondRenewalContract :=
  ⟨@selected_bridge_source,@selected_bridge_bond,@relative_motion,@distance_response,@distance_polynomial_none,
   @renewed_relative_velocity,@renewed_velocity_eventually_nonzero,@velocity_generates_leading,@renewed_bridge_site,
   @bridge_response_eventually_renewing,@renewing_index_spec,@renewing_index_minimal,@advance_actual,@trajectory_actual,
   @trajectory_same_reference,@trajectory_same_component,@trajectory_same_atom_slot,@trajectory_same_oxygen_slot,
   @elapsed_strict,@current_result,@NativeSource.next_previous⟩

end
end CPS1AddressedBondRenewal
