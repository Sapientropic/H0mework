import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.CPS1Personalized2025.Longitudinal.Response

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.CPS1Personalized2025.Longitudinal

structure LongitudinalClosure : Prop where
  inventory : type_of% Source.complete_inventory
  residualsAllAbsent : type_of% Source.residuals_complete
  sourceIdentity : type_of% Source.same_source_identity
  parentValues : type_of% Source.parent_values_used_not_rewritten
  ruleSatisfaction : type_of% Feedback.recorded_measurements_satisfy_day22_escalation_rule
  minimumInterval : type_of% Feedback.redose_respects_minimum_interval
  restoreTrigger : type_of% Feedback.glutamine_restore_trigger_recorded
  liberalizationWindow : type_of% Feedback.liberalization_window_and_sick_day
  steroidSparing : type_of% Feedback.steroid_sparing_rule_recorded
  quotesPresent : type_of% Feedback.quotes_present
  executedEvents : type_of% Execution.executed_events
  eventOrder : type_of% Execution.event_order
  halveArithmetic : type_of% Execution.halve_day_arithmetic
  restoreMatchesParent : type_of% Execution.restore_matches_parent_first_taper
  bothInfusions : type_of% Execution.both_infusions_executed
  planNotExecuted : type_of% Execution.plan_not_executed
  ammoniaNonMonotone : type_of% Response.ammonia_course_non_monotone
  halvedRatio : type_of% Response.halved_medication_ratio
  weightImprovement : type_of% Response.weight_percentile_improvement
  illnessStressTest : type_of% Response.illness_stress_test_passed
  capabilityCarried : type_of% Response.capability_carried_forward
  nominalMass : type_of% Response.nominal_dose_one_mass
  formulationResiduals : type_of% Response.formulation_responses_and_residuals
  supplyOpen : type_of% Response.physical_supply_connection_open

theorem sourceGeneratedLongitudinalMaintenance : LongitudinalClosure :=
  ⟨Source.complete_inventory,Source.residuals_complete,Source.same_source_identity,
   Source.parent_values_used_not_rewritten,
   Feedback.recorded_measurements_satisfy_day22_escalation_rule,
   Feedback.redose_respects_minimum_interval,Feedback.glutamine_restore_trigger_recorded,
   Feedback.liberalization_window_and_sick_day,Feedback.steroid_sparing_rule_recorded,
   Feedback.quotes_present,Execution.executed_events,Execution.event_order,
   Execution.halve_day_arithmetic,Execution.restore_matches_parent_first_taper,
   Execution.both_infusions_executed,Execution.plan_not_executed,
   Response.ammonia_course_non_monotone,
   Response.halved_medication_ratio,Response.weight_percentile_improvement,
   Response.illness_stress_test_passed,Response.capability_carried_forward,
   Response.nominal_dose_one_mass,Response.formulation_responses_and_residuals,
   Response.physical_supply_connection_open⟩

noncomputable abbrev parentRuntime := Ngs.afterParent
abbrev ParentN := Root.N
abbrev ParentV := Root.V
noncomputable abbrev ParentBase := Ngs.authoritySource
noncomputable abbrev ParentLedger := ParentBase.restructuringSource.toLedgerSource

theorem complete_parent : Ngs.InstalledJointAlleles :=
  Ngs.sourceGeneratedCPS1JointAllelesAtNext

end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.CPS1Personalized2025.Longitudinal
