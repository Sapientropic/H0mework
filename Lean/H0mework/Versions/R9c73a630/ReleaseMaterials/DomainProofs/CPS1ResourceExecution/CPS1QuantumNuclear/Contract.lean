import H0mework.Versions.R9c73a630.ReleaseMaterials.DomainProofs.CPS1ResourceExecution.CPS1QuantumNuclear.Closure

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace CPS1QuantumNuclear

structure NuclearContract : Prop where
  actualSource : type_of% @actual_execution_source
  sourceIntegral : type_of% @normalized_integral_expansion
  sourceDerivative : type_of% @normalized_nuclear_line
  originalEnergy : type_of% @original_total_energy
  sourceForce : type_of% @actual_source_force
  currentGrounded : type_of% @pulse_grounded
  actualPulse : type_of% @nuclear_actual
  payment : type_of% @pulse_paid
  wholeSource : type_of% @pulse_source
  atomsBonds : type_of% @pulse_atoms_and_bonds
  occupation : type_of% @pulse_good
  currentFields : type_of% @current_fields
  generatedStock : type_of% @source_stock
  inventory : type_of% @whole_inventory
  cut : type_of% @actual_cut
  trueGuardCut : type_of% @true_guard_cut
  inheritedGuardCut : type_of% @inherited_guard_cut
  legacyCut : type_of% @legacy_requireCarrier_cut
  pending : type_of% @pending_same
  sourceResume : type_of% @Source.source_preserved
  continuationGood : type_of% @resume_good
  continuationNoGuard : type_of% @resume_noGuard

theorem sourceGeneratedNuclear : NuclearContract :=
  ⟨actual_execution_source,normalized_integral_expansion,normalized_nuclear_line,original_total_energy,
    actual_source_force,pulse_grounded,nuclear_actual,pulse_paid,pulse_source,pulse_atoms_and_bonds,pulse_good,
    current_fields,source_stock,whole_inventory,actual_cut,true_guard_cut,inherited_guard_cut,legacy_requireCarrier_cut,
    pending_same,Source.source_preserved,resume_good,resume_noGuard⟩

end CPS1QuantumNuclear
