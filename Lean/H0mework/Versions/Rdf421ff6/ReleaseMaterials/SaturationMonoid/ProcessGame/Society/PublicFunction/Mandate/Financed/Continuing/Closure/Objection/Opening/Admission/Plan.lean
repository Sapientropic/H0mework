import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.Exit.Source

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 6000000

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.Admission

open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root

inductive Method where
  | direct | productive
  deriving DecidableEq

structure Choice where
  sponsor : Bool
  candidate : Bool
  method : Method
  deriving DecidableEq

def choices : List Choice :=
  (Delegation.members task).eraseDups.flatMap fun sponsor =>
    [false, true].flatMap fun candidate => [.direct, .productive].map fun method => ⟨sponsor, candidate, method⟩

def Choice.prefix (choice : Choice) : List Action :=
  match choice.method with
  | .direct => []
  | .productive => [Exit.production choice.sponsor] ++
      if choice.candidate = choice.sponsor then [] else [Exit.production choice.candidate]

def beforeProposal (current : Current) (choice : Choice) := (law.execute current 0 choice.prefix).final

def proposal (current : Current) (choice : Choice) :=
  request scope (beforeProposal current choice) choice.sponsor (.propose choice.candidate)

def beforeAcceptance (current : Current) (choice : Choice) := law.step (beforeProposal current choice) (proposal current choice)

def acceptance (current : Current) (choice : Choice) := request scope (beforeAcceptance current choice) choice.candidate .accept

def candidate (current : Current) (choice : Choice) := choice.prefix ++ [proposal current choice, acceptance current choice]

def Legal (current : Current) (choice : Choice) : Prop :=
  ∀ item ∈ law.rawItems current (candidate current choice), law.Valid item.before item.request

instance (current : Current) (choice : Choice) : Decidable (Legal current choice) := by unfold Legal; infer_instance

structure Ready (current : Current) where
  private mk ::
  choice : Choice
  included : choice ∈ choices
  legal : Legal current choice

def choose (current : Current) : Option (Ready current) :=
  match found : choices.find? (fun choice => decide (Legal current choice)) with
  | some choice => some ⟨choice, List.mem_of_find?_eq_some found,
      of_decide_eq_true (List.find?_some (p := fun choice => decide (Legal current choice)) found)⟩
  | none => none

theorem no_choice_refuses_every_generated_pair (current : Current) (blocked : choose current = none)
    (choice : Choice) (inside : choice ∈ choices) : ¬ Legal current choice := by
  unfold choose at blocked
  split at blocked
  · cases blocked
  · rename_i absent
    intro legal
    have denied := List.find?_eq_none.mp absent choice inside
    have accepted : decide (Legal current choice) = true := decide_eq_true legal
    rw [accepted] at denied
    exact denied rfl

def selected (current : Current) : Choice :=
  match choose current with
  | some ready => ready.choice
  | none => ⟨false, false, if current.clock ≤ task.deadline then .productive else .direct⟩

theorem selected_is_generated (current : Current) : selected current ∈ choices := by
  unfold selected
  split
  · rename_i ready _; exact ready.included
  · split <;> decide +kernel

def core (current : Current) := candidate current (selected current)

theorem blocked_core_has_a_real_refusal (current : Current) (blocked : choose current = none) :
    ∃ item ∈ law.rawItems current (core current), ¬ law.Valid item.before item.request := by
  by_contra absent
  apply no_choice_refuses_every_generated_pair current blocked (selected current) (selected_is_generated current)
  intro item included
  by_contra refused
  exact absent ⟨item, included, refused⟩

def proposalItem (current : Current) (choice : Choice) : ExecutionItem Bool Good Mandate.Source.Port (State Bool Unit) Unit :=
  ⟨choice.prefix.length, beforeProposal current choice, proposal current choice⟩

def acceptanceItem (current : Current) (choice : Choice) : ExecutionItem Bool Good Mandate.Source.Port (State Bool Unit) Unit :=
  ⟨choice.prefix.length + 1, beforeAcceptance current choice, acceptance current choice⟩

theorem actual_pair (current : Current) (choice : Choice) :
    proposalItem current choice ∈ law.rawItems current (candidate current choice) ∧
    acceptanceItem current choice ∈ law.rawItems current (candidate current choice) := by
  unfold candidate RawLaw.rawItems
  rw [law.execute_append]
  simp only [RawLaw.execute, Nat.zero_add]
  exact ⟨List.mem_append_right _ (by simp [proposalItem, beforeProposal]),
    List.mem_append_right _ (by simp [acceptanceItem, beforeAcceptance, beforeProposal])⟩

end SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.Admission
