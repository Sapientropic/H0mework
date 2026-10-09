import H0mework.Versions.R9c73a630.ReleaseMaterials.DomainProofs.CPS1ResourceExecution.CPS1AddressedBondResponse.Emission

set_option autoImplicit false
set_option maxHeartbeats 200000

namespace CPS1AddressedBondResponse
noncomputable section
open CPS1Deformation NativeSource
variable {frame : CPS1Recycling.Frame}

structure EmissionProperties {current : CPS1Deformation.Source.Occurrence frame}
    (emission : Emission current) : Prop where
  sourceBridge : type_of% (selected_bridge_source emission.selected.reference emission.site emission.sourceSite)
  sourceBond : type_of% (selected_bridge_bond emission.selected.reference emission.site emission.sourceSite)
  distinctSlots : type_of% (selected_bridge_distinct_slots emission.selected.reference emission.site emission.sourceSite)
  distinctNuclei : type_of% (selected_bridge_distinct_nuclei emission.selected.reference emission.site emission.sourceSite)
  samePhosphate : type_of% (emission_same_phosphate emission)
  relativeMotion : type_of% (relative_motion emission.selected emission.site emission.time)
  exactDistance : type_of% (distance_response emission.selected emission.site emission.time)
  actualPair : type_of% (emission_actual_pair emission)
  signedDistance : type_of% (emission_signed_distance emission)
  signedElectrons : type_of% (emission_signed_electrons emission)
  generatedMinimum : type_of% (emission_minimal emission)
  actualPulse : type_of% (emission_actual emission)
  renewedMaterial : type_of% (emission_ready emission)
  normalizedSeed : type_of% (emission_normalized emission)
  sourceForce : type_of% (pulse_force_generated emission.selected emission.response emission.time (emission_actual emission))
  nuclearWork : type_of% (pulse_nuclear_work emission.selected emission.response emission.time (emission_actual emission))
  sameMaterial : type_of% (pulse_same_source emission.selected emission.response emission.time (emission_actual emission))
  groundedMaterial : type_of% (pulse_grounded emission.selected emission.response emission.time (emission_actual emission))
  payment : type_of% (emission_paid emission)
  seedActual : type_of% (emission_seed_actual emission)
  actualFields : type_of% (emission_fields_actual emission)
  wholeFields : type_of% (emission_whole_fields emission)
  electronNumber : type_of% (emission_electron_number emission)
  complementaryTransfer : type_of% (emission_complementary_transfer emission)
  sourceProgram : type_of% (emission_program emission)
  actualFire : type_of% (emission_fire emission)
  firstFired : type_of% (emission_first_fired emission)
  completeSuffix : type_of% (emission_fired_suffix emission)
  nativeExecution : type_of% (emission_execution emission)
  finalStock : type_of% (emission_final_stock emission)
  pending : type_of% (emission_pending emission)
  wholeInventory : type_of% (emission_whole_inventory emission)
  actualCut : type_of% (emission_cut emission)
  goodStock : type_of% (emission_stock_good emission)
  noGuardStock : type_of% (emission_stock_noGuard emission)
  samePrevious : type_of% (emission_previous emission)

theorem emission_properties {current : CPS1Deformation.Source.Occurrence frame}
    (emission : Emission current) : EmissionProperties emission :=
  ⟨selected_bridge_source emission.selected.reference emission.site emission.sourceSite,
   selected_bridge_bond emission.selected.reference emission.site emission.sourceSite,
   selected_bridge_distinct_slots emission.selected.reference emission.site emission.sourceSite,
   selected_bridge_distinct_nuclei emission.selected.reference emission.site emission.sourceSite,
   emission_same_phosphate emission,relative_motion emission.selected emission.site emission.time,
   distance_response emission.selected emission.site emission.time,emission_actual_pair emission,
   emission_signed_distance emission,emission_signed_electrons emission,emission_minimal emission,
   emission_actual emission,emission_ready emission,emission_normalized emission,
   pulse_force_generated emission.selected emission.response emission.time (emission_actual emission),
   pulse_nuclear_work emission.selected emission.response emission.time (emission_actual emission),
   pulse_same_source emission.selected emission.response emission.time (emission_actual emission),
   pulse_grounded emission.selected emission.response emission.time (emission_actual emission),
   emission_paid emission,emission_seed_actual emission,emission_fields_actual emission,emission_whole_fields emission,
   emission_electron_number emission,emission_complementary_transfer emission,emission_program emission,
   emission_fire emission,emission_first_fired emission,emission_fired_suffix emission,emission_execution emission,
   emission_final_stock emission,emission_pending emission,emission_whole_inventory emission,emission_cut emission,
   emission_stock_good emission,emission_stock_noGuard emission,emission_previous emission⟩

def CurrentResult (current : CPS1Deformation.Source.Occurrence frame) : Prop :=
  match autoBondResponse? current with
  | none => next current = CPS1Deformation.Source.resume frame current [] []
  | some emission => next current = emission.next ∧ EmissionProperties emission

theorem current_result (current : CPS1Deformation.Source.Occurrence frame) : CurrentResult current := by
  cases generated : autoBondResponse? current with
  | none => simp only [CurrentResult,generated,next]
  | some emission =>
    simp only [CurrentResult,generated,next,true_and]
    exact emission_properties emission

structure AddressedBondResponseContract : Prop where
  sourceBridge : type_of% @selected_bridge_source
  sourceBond : type_of% @selected_bridge_bond
  distinctSlots : type_of% @selected_bridge_distinct_slots
  distinctNuclei : type_of% @selected_bridge_distinct_nuclei
  relativeMotion : type_of% @relative_motion
  euclideanDistance : type_of% @squared_distance_norm
  exactDistancePolynomial : type_of% @distance_response
  signedNeighborhood : type_of% @distance_eventually_signed
  generatedDyadic : type_of% @bond_index_spec
  generatedMinimum : type_of% @bond_index_minimal
  nativePulse : type_of% @emission_actual
  actualPair : type_of% @emission_actual_pair
  currentResult : type_of% @current_result
  nativeNext : type_of% @NativeSource.next_previous

theorem sourceGeneratedAddressedBondResponse : AddressedBondResponseContract :=
  ⟨@selected_bridge_source,@selected_bridge_bond,@selected_bridge_distinct_slots,@selected_bridge_distinct_nuclei,
   @relative_motion,@squared_distance_norm,@distance_response,@distance_eventually_signed,
   @bond_index_spec,@bond_index_minimal,@emission_actual,@emission_actual_pair,@current_result,@NativeSource.next_previous⟩

end
end CPS1AddressedBondResponse
