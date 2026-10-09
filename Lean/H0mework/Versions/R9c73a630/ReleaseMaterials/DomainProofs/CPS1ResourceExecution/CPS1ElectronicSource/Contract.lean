import H0mework.Versions.R9c73a630.ReleaseMaterials.DomainProofs.CPS1ResourceExecution.CPS1ElectronicSource.Closure

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace CPS1ElectronicSource

structure ElectronicContract : Prop where
  actualSource : type_of% @actual_electronic_source
  sourceNormalizer : type_of% @normalized_synthesis
  sourceOccupation : type_of% @CPS1ElectronicEvolution.Source.source_occupation
  nuclearDomain : type_of% @normalized_nuclear_integrable
  pairDomain : type_of% @normalized_pair_integrable
  sourceHamiltonian : type_of% @source_hamiltonian_hermitian
  boundedProjection : type_of% @continuous_action_exact
  projectedEquation : type_of% @actual_continuous_midpoint
  sourceFields : type_of% @current_continuous_fields
  nativeNetCharge : type_of% @same_native_net_charge
  nativeResponse : type_of% @actual_native_response
  nativeCurrent : type_of% @actual_native_current
  actualCapture : type_of% @Actual.prepare_actual
  capturePayment : type_of% @capture_paid
  energyReplacement : type_of% @capture_price_actual
  pulsePayment : type_of% @pulse_paid
  depositPayment : type_of% @deposit_paid
  generatedInventory : type_of% @execution_safe
  inventory : type_of% @whole_inventory
  potential : type_of% @whole_potential
  cut : type_of% @actual_cut
  guardCut : type_of% @true_guard_cut
  legacyPhaseCut : type_of% @legacy_requireCarrier_cut
  pending : type_of% @Actual.raw_cut_suffix
  sourceResume : type_of% @Source.source_preserved
  continuationFields : type_of% @resume_safe

theorem sourceGeneratedElectronic : ElectronicContract :=
  ⟨actual_electronic_source,normalized_synthesis,CPS1ElectronicEvolution.Source.source_occupation,
    normalized_nuclear_integrable,normalized_pair_integrable,source_hamiltonian_hermitian,
    continuous_action_exact,actual_continuous_midpoint,current_continuous_fields,same_native_net_charge,
    actual_native_response,actual_native_current,Actual.prepare_actual,capture_paid,capture_price_actual,
    pulse_paid,deposit_paid,execution_safe,whole_inventory,whole_potential,actual_cut,true_guard_cut,
    legacy_requireCarrier_cut,Actual.raw_cut_suffix,Source.source_preserved,resume_safe⟩

end CPS1ElectronicSource
