import H0mework.Versions.R9c73a630.ReleaseMaterials.DomainProofs.CPS1ResourceExecution.CPS1Deformation.Closure
import H0mework.Versions.R9c73a630.ReleaseMaterials.DomainProofs.CPS1ResourceExecution.CPS1Deformation.Provenance
import H0mework.Versions.R9c73a630.ReleaseMaterials.DomainProofs.CPS1ResourceExecution.CPS1Deformation.Guards
import H0mework.Versions.R9c73a630.ReleaseMaterials.DomainProofs.CPS1ResourceExecution.CPS1Deformation.JointVariation

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace CPS1Deformation
noncomputable section

structure DeformationContract : Prop where
  actualSource : type_of% @actual_execution_source
  sourceField : type_of% @raw_jet_source
  fieldFrechet : type_of% @basis_hasFDerivAt
  frameFrechet : type_of% @frame_hasFDerivAt
  gramFrechet : type_of% @gram_hasFDerivAt
  sourceUnit : type_of% @source_gram_unit
  covariantTangent : type_of% @covariant_tangent_apply
  tangentGram : type_of% @occupied_connection_tangent
  fullLift : type_of% @full_source_frame_lift
  nuclearEnergy : type_of% @nuclear_energy_source
  nuclearFrechet : type_of% @nuclear_energy_hasFDerivAt
  fullFrechet : type_of% @energy_hasFDerivAt
  currentMomentumFrechet : type_of% @energy_with_momenta_hasFDerivAt
  electronicFrechet : type_of% @occupied_physical_hasFDerivAt
  electronicGradient : type_of% @occupied_physical_differential_apply
  electronicFullJoint : type_of% @occupied_physical_joint_apply
  physicalFock : type_of% @physical_fock_hermitian
  normalizationRank : type_of% @occupied_rank_full
  canonicalNormalization : type_of% @normalized_fields
  normalizationGood : type_of% @normalize_generated
  normalizationSpan : type_of% @normalization_span_exact
  currentNormalization : type_of% @normalization_current_fields
  wholeBasis : type_of% @normed_basis_complete
  wholeBasisReadback : type_of% @canonical_readback_fields
  fockResponse : type_of% @physical_fock_response_equation
  fockAction : type_of% @physical_action_fields
  fockMidpoint : type_of% @physical_fock_midpoint
  adoption : type_of% @adopt_actual
  adoptionGood : type_of% @adopt_good
  adoptionPayment : type_of% @adopt_paid
  adoptionGrounded : type_of% @adopt_grounded
  adoptionSource : type_of% @adopt_source
  generatedAdoption : type_of% @adopt_at_generated_current
  actualPulse : type_of% @pulse_actual
  pulseGood : type_of% @pulse_good
  pulsePayment : type_of% @pulse_paid
  pulseGrounded : type_of% @pulse_grounded
  wholeSource : type_of% @pulse_same_source
  force : type_of% @pulse_force_generated
  nuclearWork : type_of% @pulse_nuclear_work
  actualMidpoint : type_of% @actual_midpoint
  zeroTime : type_of% @pulse_zero_time
  actualDeposit : type_of% @deposit_actual
  depositPayment : type_of% @deposit_paid
  generatedStock : type_of% @source_stock
  currentFields : type_of% @current_fields
  nativeCharge : type_of% @current_charge
  wholeAddresses : type_of% @current_joint_addresses
  wholeJoint : type_of% @current_joint_source
  inventory : type_of% @whole_inventory
  cut : type_of% @actual_cut
  trueGuardCut : type_of% @true_guard_cut
  inheritedGuardCut : type_of% @inherited_guard_cut
  failedCannotFire : type_of% @failed_reaction_cannot_fire
  legacyPhase : type_of% @legacy_phase_cut
  pending : type_of% @pending_same
  sourceResume : type_of% @Source.source_preserved
  continuationGood : type_of% @resume_good
  continuationNoGuard : type_of% @resume_noGuard

theorem sourceGeneratedDeformation : DeformationContract :=
  ⟨actual_execution_source,
   raw_jet_source,
   basis_hasFDerivAt,
   frame_hasFDerivAt,
   gram_hasFDerivAt,
   source_gram_unit,
   covariant_tangent_apply,
   occupied_connection_tangent,
   full_source_frame_lift,
   nuclear_energy_source,
   nuclear_energy_hasFDerivAt,
   energy_hasFDerivAt,
   energy_with_momenta_hasFDerivAt,
   occupied_physical_hasFDerivAt,
   occupied_physical_differential_apply,
   occupied_physical_joint_apply,
   physical_fock_hermitian,
   occupied_rank_full,
   normalized_fields,
   normalize_generated,
   normalization_span_exact,
   normalization_current_fields,
   normed_basis_complete,
   canonical_readback_fields,
   physical_fock_response_equation,
   physical_action_fields,
   physical_fock_midpoint,
   adopt_actual,
   adopt_good,
   adopt_paid,
   adopt_grounded,
   adopt_source,
   adopt_at_generated_current,
   pulse_actual,
   pulse_good,
   pulse_paid,
   pulse_grounded,
   pulse_same_source,
   pulse_force_generated,
   pulse_nuclear_work,
   actual_midpoint,
   pulse_zero_time,
   deposit_actual,
   deposit_paid,
   source_stock,
   current_fields,
   current_charge,
   current_joint_addresses,
   current_joint_source,
   whole_inventory,
   actual_cut,
   true_guard_cut,
   inherited_guard_cut,
   failed_reaction_cannot_fire,
   legacy_phase_cut,
   pending_same,
   Source.source_preserved,
   resume_good,
   resume_noGuard⟩

end
end CPS1Deformation

