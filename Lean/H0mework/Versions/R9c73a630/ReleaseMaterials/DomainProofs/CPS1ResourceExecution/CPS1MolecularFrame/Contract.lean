import H0mework.Versions.R9c73a630.ReleaseMaterials.DomainProofs.CPS1ResourceExecution.CPS1MolecularFrame.Closure
import H0mework.Versions.R9c73a630.ReleaseMaterials.DomainProofs.CPS1ResourceExecution.CPS1MolecularFrame.Projection
import H0mework.Versions.R9c73a630.ReleaseMaterials.DomainProofs.CPS1ResourceExecution.CPS1MolecularFrame.Provenance
import H0mework.Versions.R9c73a630.ReleaseMaterials.DomainProofs.CPS1ResourceExecution.CPS1MolecularFrame.Guards

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace CPS1MolecularFrame
noncomputable section
variable {frame : CPS1Recycling.Frame}

theorem normalized_span (state : CPS1ElectronicSource.State frame) :
    Submodule.span ℂ (Set.range (FiniteNormed.field (𝕜 := ℂ) (rawField state))) =
      Submodule.span ℂ (Set.range (rawField state)) := FiniteNormed.span_exact (rawField state)

theorem source_coefficient_gram (state : CPS1ElectronicSource.State frame) :
    (FiniteNormed.coefficients (𝕜 := ℂ) (rawField state)).conjTranspose * Matrix.gram ℂ (rawField state) *
      FiniteNormed.coefficients (𝕜 := ℂ) (rawField state) = 1 := FiniteNormed.coefficient_gram (rawField state)

structure MolecularContract : Prop where
  actualSource : type_of% @actual_execution_source
  allNuclei : type_of% @actual_nuclei_complete
  rawSource : type_of% @raw_field_source
  rawRate : type_of% @raw_jet_curve_derivative
  sourceIndependence : type_of% @nucleus_fields_independent
  wholeSpan : type_of% @normalized_span
  rank : type_of% @generated_enough
  canonicalCoefficients : type_of% @FiniteNormed.gs_coefficients_step.{0,0,0}
  coefficientGram : type_of% @source_coefficient_gram
  basis : type_of% @basis_jet_zero
  basisValue : type_of% @basis_jet_value
  kinetic : type_of% @kinetic_integral_expansion
  nuclearIntegrable : type_of% @basis_nuclear_integrable
  pairIntegrable : type_of% @basis_pair_integrable
  nuclearIntegral : type_of% @nuclear_integral_expansion
  pairIntegral : type_of% @pair_integral_expansion
  physicalFock : type_of% @fock_hermitian
  frameRate : type_of% @frame_curve_derivative
  frameUnit : type_of% @current_frame_unit
  spatialHamiltonian : type_of% @spatial_hamiltonian_selfadjoint
  projection : type_of% @source_projection_controlled
  wholeLift : type_of% @source_frame_lift
  vertical : type_of% @source_vertical_gram_rate
  adoption : type_of% @adopt_actual
  adoptionGood : type_of% @adopt_good
  adoptionPayment : type_of% @adopt_paid
  adoptionGrounded : type_of% @adopt_grounded
  adoptionSource : type_of% @adopted_source
  actualPulse : type_of% @pulse_actual
  pulsePayment : type_of% @pulse_paid
  wholeSource : type_of% @pulse_source
  midpoint : type_of% @actual_midpoint
  generatedStock : type_of% @source_stock
  currentFields : type_of% @current_fields
  nativeCharge : type_of% @current_charge
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

theorem sourceGeneratedMolecular : MolecularContract :=
  ⟨actual_execution_source,actual_nuclei_complete,raw_field_source,raw_jet_curve_derivative,nucleus_fields_independent,
   normalized_span,generated_enough,FiniteNormed.gs_coefficients_step.{0,0,0},source_coefficient_gram,basis_jet_zero,
   basis_jet_value,kinetic_integral_expansion,basis_nuclear_integrable,basis_pair_integrable,nuclear_integral_expansion,
   pair_integral_expansion,fock_hermitian,frame_curve_derivative,current_frame_unit,spatial_hamiltonian_selfadjoint,
   source_projection_controlled,source_frame_lift,source_vertical_gram_rate,adopt_actual,adopt_good,
   adopt_paid,adopt_grounded,adopted_source,pulse_actual,pulse_paid,
   pulse_source,actual_midpoint,source_stock,current_fields,current_charge,
   whole_inventory,actual_cut,true_guard_cut,inherited_guard_cut,failed_reaction_cannot_fire,
   legacy_phase_cut,pending_same,Source.source_preserved,resume_good,resume_noGuard⟩

end
end CPS1MolecularFrame
