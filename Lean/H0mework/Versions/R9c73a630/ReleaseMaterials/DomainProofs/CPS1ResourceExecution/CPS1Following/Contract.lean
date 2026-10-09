import H0mework.Versions.R9c73a630.ReleaseMaterials.DomainProofs.CPS1ResourceExecution.CPS1Following.Closure
import H0mework.Versions.R9c73a630.ReleaseMaterials.DomainProofs.CPS1ResourceExecution.CPS1Following.Provenance
import H0mework.Versions.R9c73a630.ReleaseMaterials.DomainProofs.CPS1ResourceExecution.CPS1Following.Integrals
import H0mework.Versions.R9c73a630.ReleaseMaterials.DomainProofs.CPS1ResourceExecution.CPS1Following.Dynamics
import H0mework.Versions.R9c73a630.ReleaseMaterials.DomainProofs.CPS1ResourceExecution.CPS1Following.Guards

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace CPS1Following

structure FollowingContract : Prop where
  actualSource : type_of% @actual_execution_source
  relocation : type_of% @relocate_actual
  relocationPayment : type_of% @relocate_paid
  relocationGrounded : type_of% @relocate_grounded
  relativeSource : type_of% @relative_source
  relativeParticles : type_of% @relative_particles
  kinetic : type_of% @physical_kinetic_exact
  nuclearIntegral : type_of% @moving_nuclear_integral
  pairIntegral : type_of% @moving_pair_integral
  physicalEnergy : type_of% @physical_energy_exact
  physicalFock : type_of% @physical_fock_exact
  basisMotion : type_of% @moving_basis_curve
  slaterMap : type_of% @translate_slater_map
  momentumHermitian : type_of% @source_momentum_hermitian
  movingMidpoint : type_of% @moving_midpoint
  forceFormula : type_of% @actual_source_force
  forceDerivative : type_of% @pulse_lab_energy_line
  actualPulse : type_of% @pulse_actual
  payment : type_of% @pulse_paid
  wholeSource : type_of% @pulse_source
  actualRows : type_of% @pulse_node_rows
  coverage : type_of% @pulse_gather
  rowMomentum : type_of% @pulse_row_momentum
  mass : type_of% @pulse_mass
  actualCentre : type_of% @pulse_centre
  actualVelocity : type_of% @pulse_centre_velocity
  generatedStock : type_of% @source_stock
  currentFields : type_of% @current_fields
  nativeCharge : type_of% @current_charge
  inventory : type_of% @whole_inventory
  cut : type_of% @actual_cut
  trueGuardCut : type_of% @true_guard_cut
  inheritedGuardCut : type_of% @inherited_guard_cut
  pending : type_of% @pending_same
  sourceResume : type_of% @Source.source_preserved
  continuationGood : type_of% @resume_good
  continuationNoGuard : type_of% @resume_noGuard

theorem sourceGeneratedFollowing : FollowingContract :=
  ⟨actual_execution_source,relocate_actual,relocate_paid,relocate_grounded,relative_source,relative_particles,
   physical_kinetic_exact,moving_nuclear_integral,moving_pair_integral,physical_energy_exact,physical_fock_exact,moving_basis_curve,
   translate_slater_map,source_momentum_hermitian,moving_midpoint,actual_source_force,pulse_lab_energy_line,pulse_actual,
   pulse_paid,pulse_source,pulse_node_rows,pulse_gather,pulse_row_momentum,pulse_mass,
   pulse_centre,pulse_centre_velocity,source_stock,current_fields,current_charge,whole_inventory,
   actual_cut,true_guard_cut,inherited_guard_cut,pending_same,Source.source_preserved,resume_good,
   resume_noGuard⟩

end CPS1Following
