import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Priority.Adequacy.Compiler.Menu

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Priority.Adequacy.Compiler

open Source.Program Innovation

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
  (members : List Party)

/-- This is a source resource condition over generated primitive recipes.
It contains neither a successful actual execution nor its endpoint. -/
def Enough : Prop := ∃ word ∈ plans claim state law members, Capacity.Resources claim state law members word

structure Plan : Type where
  word : RawEvent Party Good Port Technology Instrument
  original : word ∈ plans claim state law members
  resources : Capacity.Resources claim state law members word

private def chooseFrom : (candidates : List (RawEvent Party Good Port Technology Instrument)) →
    Option {word // word ∈ candidates ∧ Capacity.Resources claim state law members word}
  | [] => none
  | word :: rest =>
    if resources : Capacity.Resources claim state law members word then some ⟨word,⟨List.mem_cons_self,resources⟩⟩
    else match chooseFrom rest with
      | none => none
      | some plan => some ⟨plan.val,⟨List.mem_cons_of_mem _ plan.property.1,plan.property.2⟩⟩

private theorem chooseFrom_is_complete (candidates : List (RawEvent Party Good Port Technology Instrument))
    (available : ∃ word ∈ candidates, Capacity.Resources claim state law members word) :
    (chooseFrom claim state law members candidates).isSome = true := by
  induction candidates with
  | nil => obtain ⟨word,impossible,_⟩ := available; cases impossible
  | cons word rest inherited =>
    simp only [chooseFrom]
    split
    · rfl
    next missing =>
      have later : ∃ next ∈ rest, Capacity.Resources claim state law members next := by
        obtain ⟨next,member,ready⟩ := available
        rcases List.mem_cons.mp member with same | inside
        · exact (missing (same ▸ ready)).elim
        · exact ⟨next,inside,ready⟩
      have selected := inherited later
      cases same : chooseFrom claim state law members rest with
      | none => rw [same] at selected; cases selected
      | some plan => rfl

/-- The compiler is fixed before its source current. It selects the first raw
resource-adequate source plan, without an external chooser or controller veto. -/
def compile : Option (Plan claim state law members) :=
  match chooseFrom claim state law members (plans claim state law members) with
  | none => none
  | some plan => some ⟨plan.val,plan.property.1,plan.property.2⟩

def word : RawEvent Party Good Port Technology Instrument :=
  match compile claim state law members with | none => [] | some plan => plan.word

theorem enough_source_resources_force_a_generated_plan (enough : Enough claim state law members) :
    ∃ plan, compile claim state law members = some plan := by
  have selected := chooseFrom_is_complete claim state law members _ enough
  unfold compile
  cases same : chooseFrom claim state law members (plans claim state law members) with
  | none => rw [same] at selected; cases selected
  | some plan => exact ⟨_,rfl⟩

theorem no_compiled_plan_is_an_exact_menu_inspection_blocker
    (missing : compile claim state law members = none) :
    ∀ candidate ∈ plans claim state law members, ¬ Capacity.Resources claim state law members candidate := by
  intro candidate original resources
  obtain ⟨plan,selected⟩ := enough_source_resources_force_a_generated_plan claim state law members ⟨candidate,original,resources⟩
  rw [missing] at selected
  cases selected

theorem the_compiled_word_is_exactly_the_source_selected_plan
    (plan : Plan claim state law members) (selected : compile claim state law members = some plan) :
    word claim state law members = plan.word := by simp only [word,selected]

theorem enough_resources_force_the_compiled_word_to_actually_pay_every_original_cell
    (declared : state.declared = true) (enough : Enough claim state law members) :
    Capacity.ActualSuccess claim state law members (word claim state law members) := by
  obtain ⟨plan,selected⟩ := enough_source_resources_force_a_generated_plan claim state law members enough
  rw [the_compiled_word_is_exactly_the_source_selected_plan claim state law members plan selected]
  exact Capacity.sufficient_source_resources_generate_actual_success claim state law members plan.word declared plan.resources

theorem enough_resources_force_actual_renewal_selection
    (declared : state.declared = true) (unpaid : ¬ Responsibility.Family.State.isPaid claim state)
    (enough : Enough claim state law members) :
    ∃ permit, Selection.renewalVerdict claim state law members (word claim state law members) = .admitted permit := by
  obtain ⟨plan,selected⟩ := enough_source_resources_force_a_generated_plan claim state law members enough
  rw [the_compiled_word_is_exactly_the_source_selected_plan claim state law members plan selected]
  exact Capacity.source_resources_generate_a_selected_actual_admission claim state law members plan.word declared unpaid plan.resources

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Priority.Adequacy.Compiler
