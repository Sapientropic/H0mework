import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Characterization.Support.Law

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Characterization.Support

open Source.Program Source.ProgrammeControl
noncomputable section
variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  (input : Root.ProgrammeSource.Input Party Good Port Technology Instrument)
  (endpoint : History.Visit input)

/-- The old access origin and its current exclusion are both read from
the same original history, even after holder or operator changes. -/
theorem every_historical_capital_exposes_its_original_and_current_bearing_failure
    (capital : History.Capital input endpoint) :
    (type_of% (capital.original_origins_and_actual_before input endpoint)) ∧
    PrivatePhase input.law (capital.access.access.raw input).before capital.access.port capital.access.recipient ∧
    (∃ person ∈ History.parties input endpoint,
      PrivatePhase input.law (History.target input endpoint) capital.access.port person) ∧
    ¬ NoAsymmetry input.law ∧
    (type_of% (capital.exact_original_rows_and_current_relation input endpoint)) ∧
    (type_of% (capital.original_actor_survives_every_cross_word_successor input endpoint)) := by
  have atAccess := capital.checked.1.2.2.1
  obtain ⟨controller,person,present,denied⟩ := capital.private_relation_at_current_phase input endpoint
  exact ⟨capital.original_origins_and_actual_before input endpoint,atAccess,
    ⟨person,present,controller,denied⟩,
    every_private_phase_refutes_the_exact_permission_support input.law _ _ _ atAccess,
    capital.exact_original_rows_and_current_relation input endpoint,
    capital.original_actor_survives_every_cross_word_successor input endpoint⟩

omit [DecidableEq Port] [DecidableEq Instrument] in
theorem a_fresh_control_use_exposes_the_actual_affected_subject
    (port : Port) (item : ExecutionItem Party Good Port Technology Instrument)
    (fresh : History.FreshControl input port item) :
    input.law.Valid item.before item.request ∧ port ∈ input.law.requiredPorts item.before item.request ∧
    (∃ person ∈ History.affectedSubjects input item, PrivatePhase input.law item.before port person) ∧
    ¬ NoAsymmetry input.law := by
  obtain ⟨accepted,required,person,present,phase⟩ := fresh
  exact ⟨accepted,required,⟨person,present,phase⟩,
    every_private_phase_refutes_the_exact_permission_support input.law _ _ _ phase⟩

theorem minimal_permission_support_blocks_every_historical_reproduction
    (shared : NoAsymmetry input.law) : ¬ Nonempty (History.Capital input endpoint) := by
  rintro ⟨capital⟩
  exact (every_historical_capital_exposes_its_original_and_current_bearing_failure input endpoint capital).2.2.2.1 shared

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Characterization.Support
