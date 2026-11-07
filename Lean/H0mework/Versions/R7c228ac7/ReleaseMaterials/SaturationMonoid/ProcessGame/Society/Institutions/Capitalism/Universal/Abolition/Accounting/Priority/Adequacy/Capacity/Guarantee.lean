import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Priority.Adequacy.Capacity.Routing
import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Priority.Completeness.Selection

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Priority.Adequacy.Capacity

open Source.Program Innovation
open Exit.Necessity

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Instrument]
  [DecidableEq Technology] [DecidableEq Port]
  {source : Trials.Mechanism Party Good Port Technology Instrument}
  {past : List (RawEvent Party Good Port Technology Instrument)} {nature : source.Nature}
  {response : Control.HistoryResponse (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument)}
  (claim : Responsibility.Family.Claim source past nature response)
  (state : Responsibility.Family.State claim) (law : RawLaw Party Good Port Technology Instrument)
  (members : List Party) (word : RawEvent Party Good Port Technology Instrument)

/-- Every debit, delivery and consumed necessity is included. This primitive
net inequality is physical capacity, not an actual settlement certificate. -/
def NetCapacity : Prop := ∀ key ∈ Responsibility.Family.positiveScope source past nature response,
  state.remaining key ≤ Primitive.net law (Primitive.execute law state.raw 0 word).items key.1 key.2

instance : Decidable (NetCapacity claim state law word) := by unfold NetCapacity; infer_instance

/-- All tests concern the current source recipe, primitive lots and authority.
No Valid, AllNeedsPaid, Permit, target current or payment is a field. -/
structure Resources : Prop where
  recipe : RecipeFacts law (Primitive.execute law state.raw 0 word).items
  startup : Startup law state.raw word
  routing : Routing claim state law members word
  bills : Needs law state.raw members word
  net : NetCapacity claim state law word

instance : Decidable (Resources claim state law members word) :=
  decidable_of_iff (RecipeFacts law (Primitive.execute law state.raw 0 word).items ∧ Startup law state.raw word ∧
    Routing claim state law members word ∧ Needs law state.raw members word ∧ NetCapacity claim state law word)
    ⟨fun facts => ⟨facts.1,facts.2.1,facts.2.2.1,facts.2.2.2.1,facts.2.2.2.2⟩,
      fun facts => ⟨facts.recipe,facts.startup,facts.routing,facts.bills,facts.net⟩⟩

omit [DecidableEq Technology] [DecidableEq Port] in
theorem sufficient_primitive_resources_force_the_gate_to_execute_every_request
    (declared : state.declared = true) (resources : Resources claim state law members word) :
    (Policy.evaluate claim state law members word).stop = none ∧
    (Policy.evaluate claim state law members word).executableWord = word := by
  have conditions := primitive_resources_generate_the_complete_conditions law state.raw word resources.recipe resources.startup
  have noStop : (Policy.evaluate claim state law members word).stop = none := by
    cases stopped : (Policy.evaluate claim state law members word).stop with
    | none => rfl
    | some issue =>
      obtain ⟨known,material,valid,amount,control⟩ := original_request_conditions_are_generated
        claim state law members issue.front issue.request word conditions resources.routing issue.suffix issue.original
      cases issue.denied with
      | declaration pending => exact (pending declared).elim
      | standing unknown => exact (unknown known).elim
      | material foreign => exact (foreign material).elim
      | authority invalid => exact (invalid valid).elim
      | quantity overdraw => exact (overdraw amount).elim
      | control newControl => exact (newControl control).elim
  refine ⟨noStop,?_⟩
  have empty := (Policy.evaluate claim state law members word).complete_when_noStop noStop
  simpa only [empty,List.append_nil] using (Policy.evaluate claim state law members word).original.symm

structure ActualSuccess : Prop where
  complete : (Policy.evaluate claim state law members word).executableWord = word
  noStop : (Policy.evaluate claim state law members word).stop = none
  needs : AllNeedsPaid law state.raw members (Policy.evaluate claim state law members word).actualWord
  paid : Responsibility.Family.State.isPaid claim (Policy.evaluate claim state law members word).updated
  originalClaims : (Policy.evaluate claim state law members word).updated.raw.claims = state.raw.claims

omit [DecidableEq Technology] [DecidableEq Port] in
theorem sufficient_source_resources_generate_actual_success
    (declared : state.declared = true) (resources : Resources claim state law members word) :
    ActualSuccess claim state law members word := by
  obtain ⟨noStop,complete⟩ := sufficient_primitive_resources_force_the_gate_to_execute_every_request claim state law members word declared resources
  have conditions := primitive_resources_generate_the_complete_conditions law state.raw word resources.recipe resources.startup
  have material := routing_retains_the_original_material_source claim state law members word resources.routing
  have actualWord := Policy.evaluation_actual_word_is_the_original_executable_word claim state law members (Policy.evaluate claim state law members word)
  rw [complete] at actualWord
  refine ⟨complete,noStop,?_,?_,?_⟩
  · rw [actualWord]
    intro actor member
    have bills := resources.bills actor member
    have same := raw_bill_becomes_actual_paid_service law state.raw word
      (original_inventory_is_valid law state.raw word conditions) actor
    exact ⟨(same _ .necessity).mpr bills.1,(same _ .maintenance).mpr bills.2⟩
  · change Responsibility.Family.State.isPaid claim (Responsibility.Family.State.advance claim state law _)
    rw [complete]
    intro key member
    rw [primitive_residual_is_the_original_actual_remaining claim state law word conditions material key]
    apply max_eq_left
    have bound := (resources.net key member).trans (le_max_right 0 _)
    change state.remaining key - max 0 _ ≤ 0
    linarith
  · exact Responsibility.Family.State.actual_advance_retains_every_original_financial_claim claim state law _

omit [DecidableEq Technology] [DecidableEq Port] in
theorem source_resources_generate_a_selected_actual_admission
    (declared : state.declared = true) (unpaid : ¬ Responsibility.Family.State.isPaid claim state)
    (resources : Resources claim state law members word) :
    ∃ permit, Selection.renewalVerdict claim state law members word = .admitted permit := by
  have success := sufficient_source_resources_generate_actual_success claim state law members word declared resources
  have targetZero := (Progress.zero_budget_exactly_when_all_original_cells_are_paid claim _).mpr success.paid
  have sourcePositive : 0 < Progress.budget claim state := by
    apply Nat.pos_of_ne_zero
    exact fun zero => unpaid ((Progress.zero_budget_exactly_when_all_original_cells_are_paid claim state).mp zero)
  apply Completeness.a_generated_permit_forces_the_actual_selected_branch
  exact ⟨declared,success.noStop,success.needs,by rw [targetZero]; exact sourcePositive⟩

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Priority.Adequacy.Capacity
