import H0mework.Versions.R7e013edd.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.AdaptiveRejectionInventory

set_option autoImplicit false
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.AdaptiveRejectionHistory
open Distributed Reaction Reaction.Feedback
open Distributed.Recall.Information.Agency.Protocol Continuation

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Technology] [DecidableEq Instrument]
  {code : Code Party Good Port (Mandate.State Party Technology) Instrument}

abbrev Stages := List (EventHistory.Stage (code := code))
abbrev slot (past : Stages (code := code)) (n : Nat) := past[n]?.getD (SilentWindow.quiet, EventStep.fixed none)
abbrev protocols (past : Stages (code := code)) (n : Nat) := (slot past n).1
abbrev rivals (past : Stages (code := code)) (n : Nat) := (slot past n).2

omit [DecidableEq Port] [DecidableEq Technology] in
theorem reconstructed_stages_are_the_literal_actual_prefix (past : Stages (code := code)) (n : Nat)
    (bounded : n ≤ past.length) : AdaptiveDeliveryTrace.stages (protocols past) (rivals past) n = past.take n := by
  have mapped : ∀ k, AdaptiveDeliveryTrace.stages (protocols past) (rivals past) k = (List.range k).map (slot past) := by
    intro k
    induction k with
    | zero => rfl
    | succ k ih => rw [AdaptiveDeliveryTrace.stages, ih, List.range_succ, List.map_append]; rfl
  rw [mapped]
  apply List.ext_getElem
  · simp only [List.length_map, List.length_range, List.length_take]; omega
  · intro i left right
    have before : i < past.length := by simp only [List.length_map, List.length_range] at left; omega
    simp only [List.getElem_map, List.getElem_range, slot, List.getElem?_eq_getElem before,
      Option.getD_some, List.getElem_take]

variable (start : Cursor code)
  (vocabulary : OwnedAttestation.Vocabulary (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument))
  (encoding : StageTransport.Encoding (code := code)) (law : StageReception.Law code)

-- A condition on each actual callback and its original prefix, not a supplied bound.
abbrev Compliant (allowance : Nat) (past : Stages (code := code)) := ∀ n < past.length,
  InterferenceEnvelope.intake (EventHistory.execute start (past.take n)) (rivals past n) ∈
    InterferenceEnvelope.choices start (past.take n) allowance

def check (allowance : Nat) (past : Stages (code := code)) : Bool := (List.range past.length).all fun n =>
  decide (InterferenceEnvelope.intake (EventHistory.execute start (past.take n)) (rivals past n) ∈
    InterferenceEnvelope.choices start (past.take n) allowance)

theorem check_iff (allowance : Nat) (past : Stages (code := code)) :
    check start allowance past = true ↔ Compliant start allowance past := by
  simp only [check, List.all_eq_true, List.mem_range, decide_eq_true_eq, Compliant]

theorem the_actual_history_generates_its_own_rejection_capacity
    (allowance : Nat) (past : Stages (code := code)) (compliant : Compliant start allowance past) :
    (AdaptiveRejectionInventory.identities start vocabulary encoding law past).card ≤
      AdaptiveReceptionBudget.capacity (code := code) := by
  have trace : AdaptiveDeliveryDeadline.Compliant start (protocols past) (rivals past) allowance past.length := by
    intro n bounded
    have actual := compliant n bounded
    rw [← reconstructed_stages_are_the_literal_actual_prefix past n (by omega), AdaptiveDeliveryTrace.execute_stages] at actual
    exact actual
  have counted := AdaptiveRejectionInventory.actual_rejection_identities_fit_the_source_reception_budget
    start vocabulary encoding law (protocols past) (rivals past) allowance past.length trace past.length (Nat.le_refl _)
  simpa only [reconstructed_stages_are_the_literal_actual_prefix past past.length (Nat.le_refl _), List.take_length] using counted

end SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.AdaptiveRejectionHistory
