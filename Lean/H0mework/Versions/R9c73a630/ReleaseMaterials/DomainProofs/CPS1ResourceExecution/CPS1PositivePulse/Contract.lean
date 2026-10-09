import H0mework.Versions.R9c73a630.ReleaseMaterials.DomainProofs.CPS1ResourceExecution.CPS1PositivePulse.NativeSource

set_option autoImplicit false
set_option maxHeartbeats 200000

namespace CPS1PositivePulse
noncomputable section

structure PositivePulseContract : Prop where
  canonicalFieldContinuity : type_of% @canonical_gs_continuousAt.{0,0,0,0}
  canonicalCoefficientContinuity : type_of% @canonical_coefficients_continuousAt.{0,0,0,0}
  canonicalNormalizationContinuity : type_of% @total_normalization_continuousAt.{0,0,0,0}
  canonicalRankNeighborhood : type_of% @canonical_eventually_full_rank.{0,0,0,0}
  occupiedNormalization : type_of% @normalized_occupation_candidate_eq
  occupiedContinuity : type_of% @normalized_occupation_candidate_continuousAt.{0}
  generatedNormalization : type_of% @normalize_eventually_success.{0}
  basisReadback : type_of% @physical_fock_response_fixed
  basisUnitNeighborhood : type_of% @basis_unit_eventually.{0}
  physicalFockContinuity : type_of% @physical_fock_continuousAt.{0}
  physicalResponseContinuity : type_of% @physical_fock_response_continuousAt.{0}
  candidateZero : type_of% @continuous_pulse_candidate_zero
  candidateEnergy : type_of% @candidate_energy_continuousAt_zero
  affordableNeighborhood : type_of% @candidate_price_eventually_affordable
  sameRows : type_of% @current_rows_transport
  generatedGather : type_of% @current_gather_transport
  currentReadyNeighborhood : type_of% @current_ready_eventually
  nuclearReadyNeighborhood : type_of% @nuclear_ready_eventually
  successfulNeighborhood : type_of% @pulse_eventually_success
  dyadicExistence : type_of% @exists_successful_dyadic
  generatedIndex : type_of% @generated_dyadic_success
  generatedMinimum : type_of% @generated_dyadic_minimal
  generatedResponse : type_of% @generated_dyadic_actual
  publicEmitter : type_of% @NativeSource.auto_pulse_generated
  positiveTime : type_of% @NativeSource.emission_time_positive
  actualPulse : type_of% @NativeSource.emission_actual
  minimumTimeIndex : type_of% @NativeSource.emission_minimal
  pulseGood : type_of% @NativeSource.emission_good
  pulsePayment : type_of% @NativeSource.emission_paid
  carrierAvailable : type_of% @NativeSource.emission_held_available
  carrierMembership : type_of% @NativeSource.emission_carrier_mem
  clockMembership : type_of% @NativeSource.emission_clock_mem
  actualProgram : type_of% @NativeSource.emission_program
  actualFire : type_of% @NativeSource.emission_fire
  firstFired : type_of% @NativeSource.emission_first_fired
  fullFiredSuffix : type_of% @NativeSource.emission_fired_suffix
  nativeExecution : type_of% @NativeSource.emission_execution
  wholeInventory : type_of% @NativeSource.emission_whole_inventory
  actualCut : type_of% @NativeSource.emission_cut
  samePrevious : type_of% @NativeSource.emission_previous
  nativeNext : type_of% @NativeSource.next_previous
  generatedStock : type_of% @NativeSource.emission_stock_good
  generatedNoGuard : type_of% @NativeSource.emission_stock_noGuard

theorem sourceGeneratedPositivePulse : PositivePulseContract :=
  ⟨canonical_gs_continuousAt,
   canonical_coefficients_continuousAt,
   total_normalization_continuousAt,
   canonical_eventually_full_rank,
   normalized_occupation_candidate_eq,
   normalized_occupation_candidate_continuousAt,
   normalize_eventually_success,
   physical_fock_response_fixed,
   basis_unit_eventually,
   physical_fock_continuousAt,
   physical_fock_response_continuousAt,
   continuous_pulse_candidate_zero,
   candidate_energy_continuousAt_zero,
   candidate_price_eventually_affordable,
   current_rows_transport,
   current_gather_transport,
   current_ready_eventually,
   nuclear_ready_eventually,
   pulse_eventually_success,
   exists_successful_dyadic,
   generated_dyadic_success,
   generated_dyadic_minimal,
   generated_dyadic_actual,
   NativeSource.auto_pulse_generated,
   NativeSource.emission_time_positive,
   NativeSource.emission_actual,
   NativeSource.emission_minimal,
   NativeSource.emission_good,
   NativeSource.emission_paid,
   NativeSource.emission_held_available,
   NativeSource.emission_carrier_mem,
   NativeSource.emission_clock_mem,
   NativeSource.emission_program,
   NativeSource.emission_fire,
   NativeSource.emission_first_fired,
   NativeSource.emission_fired_suffix,
   NativeSource.emission_execution,
   NativeSource.emission_whole_inventory,
   NativeSource.emission_cut,
   NativeSource.emission_previous,
   NativeSource.next_previous,
   NativeSource.emission_stock_good,
   NativeSource.emission_stock_noGuard⟩

end
end CPS1PositivePulse
