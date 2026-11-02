import H0mework.Versions.R59df7e39.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.SourceExposure

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.RootExposure

open Distributed

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Instrument]
  (source : Source Party Good Port Technology Instrument) (ports : Fin source.code.sites → Port)

def affectedFromOutcome : source.code.Outcome source.reference → Option (Finset (Fin source.code.sites))
  | .blocked _ => none
  | .selected choice => some (SourceExposure.affectedThrough source.code ports choice.policy.policy
      (source.code.historyCurrent source.history) source.events source.events.length)

def budgetFromOutcome (outcome : source.code.Outcome source.reference) : Option Nat :=
  (affectedFromOutcome source ports outcome).map Finset.card

def generatedAffected := affectedFromOutcome source ports source.answer
def generatedBudget : Option Nat := budgetFromOutcome source ports source.answer

def rootedAffected : Option (Finset (Fin source.code.sites)) :=
  match (Distributed.Runtime.facade source).readoutAt
      (Distributed.Runtime.activated source (source.history.length + 1)) .synthesis with
  | .inl outcome => affectedFromOutcome source ports outcome.2
  | .inr impossible => nomatch impossible

def rootedBudget : Option Nat := (rootedAffected source ports).map Finset.card

theorem rooted_affected_eq_generated : rootedAffected source ports = generatedAffected source ports := rfl
theorem rooted_budget_eq_generated : rootedBudget source ports = generatedBudget source ports := rfl

theorem budget_of_selected (choice : source.code.Selection source.reference)
    (selected : source.answer = .selected choice) : rootedBudget source ports =
    some (SourceExposure.budget source.code ports choice.policy.policy
      (source.code.historyCurrent source.history) source.events source.events.length) := by
  rw [rooted_budget_eq_generated]
  unfold generatedBudget budgetFromOutcome
  rw [selected]
  rfl

theorem blocked_reception_has_no_budget
    (interface : Interface source.code) (receiver : Fin source.code.sites)
    (incoming : Nat → Option (Envelope source.code))
    (blocked : RootConsumer.rooted source interface receiver incoming = .blocked) :
    rootedBudget source ports = none := by
  rw [RootConsumer.rooted_eq_generated] at blocked
  unfold RootConsumer.generate RootConsumer.fromOutcome at blocked
  rw [rooted_budget_eq_generated]
  unfold generatedBudget budgetFromOutcome
  cases actual : source.answer with
  | blocked _ => rfl
  | selected _ => rw [actual] at blocked; contradiction

theorem available_reception_has_generated_keys
    (interface : Interface source.code) (receiver : Fin source.code.sites)
    (incoming : Nat → Option (Envelope source.code)) (state : ReceiverState source.code)
    (available : RootConsumer.rooted source interface receiver incoming = .available state) :
    ∃ keys : Finset (Fin source.code.sites), rootedAffected source ports = some keys ∧
      rootedBudget source ports = some keys.card := by
  rw [RootConsumer.rooted_eq_generated] at available
  unfold RootConsumer.generate RootConsumer.fromOutcome at available
  cases generated : source.answer with
  | blocked _ => rw [generated] at available; contradiction
  | selected choice =>
    refine ⟨SourceExposure.affectedThrough source.code ports choice.policy.policy
      (source.code.historyCurrent source.history) source.events source.events.length, ?_, ?_⟩
    · rw [rooted_affected_eq_generated]
      unfold generatedAffected
      rw [generated]
      rfl
    · exact budget_of_selected source ports choice generated

theorem rooted_agreement_from_source_budget
    (interface : Interface source.code) (leftSite rightSite : Fin source.code.sites)
    (leftInput rightInput : Nat → Option (Envelope source.code))
    (left right : ReceiverState source.code)
    (leftActual : RootConsumer.rooted source interface leftSite leftInput = .available left)
    (rightActual : RootConsumer.rooted source interface rightSite rightInput = .available right)
    (b threshold : Nat) (scope : Scope) (a c : Fin source.code.signals)
    (actualBudget : rootedBudget source ports = some b)
    (enough : source.code.sites + b < threshold + threshold)
    (one : Quorum.readout source.code left scope threshold = .decided a)
    (two : Quorum.readout source.code right scope threshold = .decided c) : a = c := by
  rw [RootConsumer.rooted_eq_generated] at leftActual rightActual
  rw [rooted_budget_eq_generated] at actualBudget
  unfold RootConsumer.generate RootConsumer.fromOutcome at leftActual rightActual
  unfold generatedBudget budgetFromOutcome affectedFromOutcome at actualBudget
  cases generated : source.answer with
  | blocked obstruction => simp only [generated] at actualBudget; contradiction
  | selected choice =>
    simp only [generated, Option.map_some] at leftActual rightActual actualBudget
    have leftSame := RootConsumer.ReceptionData.available.inj leftActual
    have rightSame := RootConsumer.ReceptionData.available.inj rightActual
    have budgetSame := Option.some.inj actualBudget
    subst left; subst right; subst b
    exact SourceExposure.agreement_of_source_generated_budget source.code ports choice.policy.policy
      (source.code.historyCurrent source.history) interface source.events leftSite rightSite leftInput rightInput
      source.events.length threshold scope a c one two enough

/-- A changed capability is attached to the selected source's actual response,
not to a caller-selected affected set. The original law still generates next. -/
theorem counted_root_key_has_actual_change_and_next
    (keys : Finset (Fin source.code.sites))
    (actualKeys : rootedAffected source ports = some keys)
    (key : Fin source.code.sites) (counted : key ∈ keys) :
    ∃ choice : source.code.Selection source.reference,
      source.answer = .selected choice ∧
      (∃ n < source.events.length, SourceExposure.viewAt source.code ports choice.policy.policy
        (source.code.historyCurrent source.history) source.events n key ≠
        SourceExposure.viewAt source.code ports choice.policy.policy
          (source.code.historyCurrent source.history) source.events (n + 1) key) ∧
      source.currentAt (source.history.length + 2) = source.code.law.next
        (source.code.historyCurrent source.history)
        (source.code.executed choice.policy.policy (source.history, source.events)).word := by
  rw [rooted_affected_eq_generated] at actualKeys
  unfold generatedAffected affectedFromOutcome at actualKeys
  split at actualKeys
  · contradiction
  · rename_i choice generated
    have same := Option.some.inj actualKeys
    rw [← same] at counted
    exact ⟨choice, generated,
      (SourceExposure.affected_iff_actual_change source.code ports choice.policy.policy
        (source.code.historyCurrent source.history) source.events source.events.length key).mp counted,
      (source.selected_plan_is_paid_on_its_own_root choice generated).2.2.1⟩

end SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.RootExposure
