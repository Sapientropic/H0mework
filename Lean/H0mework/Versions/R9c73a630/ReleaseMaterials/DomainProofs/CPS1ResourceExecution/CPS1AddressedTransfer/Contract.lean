import H0mework.Versions.R9c73a630.ReleaseMaterials.DomainProofs.CPS1ResourceExecution.CPS1AddressedTransfer.Emission

set_option autoImplicit false
set_option maxHeartbeats 200000

namespace CPS1AddressedTransfer
noncomputable section
open NativeSource
variable {frame : CPS1Recycling.Frame}

structure EmissionProperties {current : CPS1Deformation.Source.Occurrence frame}
    (emission : Emission current) : Prop where
  siteSource : type_of% (emission_source_site emission)
  actualPulse : type_of% (emission_actual emission)
  normalizedSeed : type_of% (emission_normalized emission)
  exactPopulation : type_of% (response_population emission.selected emission.site.nuclear emission.time)
  signedTransfer : type_of% (emission_nonzero emission)
  renewedMaterial : type_of% (emission_ready emission)
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
  wholeInventory : type_of% (emission_whole_inventory emission)
  actualCut : type_of% (emission_cut emission)
  goodStock : type_of% (emission_stock_good emission)
  noGuardStock : type_of% (emission_stock_noGuard emission)
  samePrevious : type_of% (emission_previous emission)

theorem emission_properties {current : CPS1Deformation.Source.Occurrence frame}
    (emission : Emission current) : EmissionProperties emission :=
  ⟨emission_source_site emission,emission_actual emission,emission_normalized emission,
   response_population emission.selected emission.site.nuclear emission.time,
   emission_nonzero emission,emission_ready emission,emission_paid emission,emission_seed_actual emission,
   emission_fields_actual emission,emission_whole_fields emission,emission_electron_number emission,
   emission_complementary_transfer emission,emission_program emission,emission_fire emission,
   emission_first_fired emission,emission_fired_suffix emission,emission_execution emission,
   emission_final_stock emission,emission_whole_inventory emission,emission_cut emission,
   emission_stock_good emission,emission_stock_noGuard emission,emission_previous emission⟩

def CurrentResult (current : CPS1Deformation.Source.Occurrence frame) : Prop :=
  match autoTransfer? current with
  | none => next current = CPS1Deformation.Source.resume frame current [] []
  | some emission => next current = emission.next ∧ EmissionProperties emission

theorem current_result (current : CPS1Deformation.Source.Occurrence frame) : CurrentResult current := by
  cases generated : autoTransfer? current with
  | none => simp only [CurrentResult,generated,next]
  | some emission =>
    simp only [CurrentResult,generated,next,true_and]
    exact emission_properties emission

structure AddressedTransferContract : Prop where
  sourceSite : type_of% @selected_site_source
  rawSiteSpan : type_of% @site_basis_span
  orthogonalSite : type_of% @site_projection_apply
  exactElectronicPulse : type_of% @response_midpoint
  exactPopulation : type_of% @response_population
  fluxContinuity : type_of% @response_flux_continuousAt_zero
  sourceSeed : type_of% @response_seed_actual
  currentResult : type_of% @current_result
  nativeNext : type_of% @NativeSource.next_previous

theorem sourceGeneratedAddressedTransfer : AddressedTransferContract :=
  ⟨@selected_site_source,@site_basis_span,@site_projection_apply,@response_midpoint,@response_population,
   @response_flux_continuousAt_zero,@response_seed_actual,@current_result,@NativeSource.next_previous⟩

end
end CPS1AddressedTransfer
