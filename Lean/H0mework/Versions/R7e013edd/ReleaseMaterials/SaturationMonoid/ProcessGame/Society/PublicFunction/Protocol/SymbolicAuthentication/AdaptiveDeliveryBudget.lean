import H0mework.Versions.R7e013edd.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.AdaptiveDeliveryDeadline

set_option autoImplicit false
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.AdaptiveDeliveryBudget
open Distributed Reaction Reaction.Feedback
open Distributed.Recall.Information.Agency.Protocol Continuation
open AdaptiveDeliveryTrace AdaptiveDeliveryDeadline

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Technology] [DecidableEq Instrument]
  {code : Code Party Good Port (Mandate.State Party Technology) Instrument}
  (start : Cursor code) (protocols : Nat → Rule code) (rivals : Nat → Opponent code)

theorem a_charged_actual_callback_needs_unspent_source_capacity (allowance n : Nat)
    (chosen : InterferenceEnvelope.intake (cursorAt start protocols rivals n) (rivals n) ∈
      InterferenceEnvelope.choices start (stages protocols rivals n) allowance)
    (charged : InterferenceEnvelope.interference start (row start protocols rivals n) = true) :
    InterferenceEnvelope.spent start (stages protocols rivals n) < code.eventLimit := by
  unfold InterferenceEnvelope.interference at charged
  cases called : (row start protocols rivals n).call <;> simp only [called] at charged <;> try contradiction
  rename_i move
  have retained := StageTrace.external_callback_is_retained_before_admission _ (protocols n) (rivals n) move called
  have intake : InterferenceEnvelope.intake (cursorAt start protocols rivals n) (rivals n) =
      Distributed.Recall.Information.Agency.externalChoice code move := by
    simp only [CompletionEnvelope.intake, CompletionEnvelope.raw, retained.2.1, Option.isSome_none,
      Bool.false_eq_true, if_false, EventStep.selected, retained.2.2]
  cases normalized : Distributed.Recall.Information.Agency.externalChoice code move with
  | none => simp only [normalized, Option.isSome_none, Bool.false_and, Bool.false_eq_true] at charged
  | some event =>
    have absent : event ∉ InterferenceEnvelope.fresh start (cursorAt start protocols rivals n) := by
      simp only [normalized, Option.isSome_some, Bool.true_and, InterferenceEnvelope.progresses, called] at charged
      intro member
      have fresh : decide (event ∈ InterferenceEnvelope.fresh start (cursorAt start protocols rivals n)) = true := decide_eq_true member
      change (!decide (event ∈ InterferenceEnvelope.fresh start (cursorAt start protocols rivals n))) = true at charged
      rw [fresh] at charged; contradiction
    apply InterferenceEnvelope.a_nonfresh_generated_choice_needs_unspent_source_capacity start
      (stages protocols rivals n) allowance event
    · simpa only [intake, normalized] using chosen
    · rw [execute_stages]; exact absent

theorem every_actual_prefix_keeps_the_one_source_interface_budget
    (allowance stop : Nat) (compliant : Compliant start protocols rivals allowance stop) :
    ∀ n ≤ stop, InterferenceEnvelope.spent start (stages protocols rivals n) ≤ code.eventLimit := by
  intro n bounded
  induction n with
  | zero => simp [InterferenceEnvelope.spent, stages, StageTrace.records]
  | succ n ih =>
    have previous := ih (by omega)
    have counts : InterferenceEnvelope.spent start (stages protocols rivals (n + 1)) =
        InterferenceEnvelope.spent start (stages protocols rivals n) +
          if InterferenceEnvelope.interference start (row start protocols rivals n) then 1 else 0 := by
      simp only [InterferenceEnvelope.spent, records_succ, List.filter_append, List.length_append]
      split <;> simp_all
    rw [counts]
    split
    · have capacity := a_charged_actual_callback_needs_unspent_source_capacity start protocols rivals allowance n
        (compliant n (by omega)) (by assumption)
      omega
    · omega

end SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.AdaptiveDeliveryBudget
