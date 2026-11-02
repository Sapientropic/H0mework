import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Computation.Search.Runtime
import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Budget.Programme.Debt.Information.Inquiry.Replay.Suffix.Window.Whole.Observation

set_option autoImplicit false
set_option maxRecDepth 65536
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Computation.Search.Deployment
open Distributed Distributed.Reaction Distributed.Reaction.Feedback
open Distributed.Recall.Information.Agency.Protocol
open Distributed.Recall.Information.Agency.Protocol.Continuation
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root
open Budget.Programme.Debt Budget.Programme.Debt.Information Budget.Programme.Debt.Information.Inquiry
open Budget.Programme.Debt.Information.Inquiry.Replay.Suffix.Window.Whole

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Technology] [DecidableEq Instrument]
  (model : Native.Authority.Bound (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument))
  (domain : List (Cursor model.source.code))
  (original : Distributed.Recall.Information.Agency.Protocol.Rule model.source.code)
  (reference : Program model.source.code (horizon domain))
  (worker : Fin model.source.code.sites)
  (quote : Charge.Quote (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument))

variable (point : View (code := model.source.code)) (rival : Opponent model.source.code)

def install (ordinal : Nat) : Cursor model.source.code :=
  match (Runtime.read model domain original reference worker quote point rival ordinal).1 with
  | some (.searched _ (.selected choice)) =>
      Splice.install (Charge.final quote model worker point rival) rival (choice.policy.protocol.controls.drop 1)
  | _ => Charge.final quote model worker point rival

variable (ordinal : Nat) (funded : Gate model domain worker quote)
  (choice : Prefix.Choice model domain original (past model original worker quote) reference)
  (released : (Runtime.read model domain original reference worker quote point rival ordinal).1 =
    some (.searched funded (.selected choice)))

include released in
private theorem charge_is_paid : Charge.paid quote model worker point rival ordinal := by
  obtain ⟨paid,_⟩ := Search.every_released_search_is_generated_after_its_own_actual_payment model domain original reference worker quote point rival ordinal
    (.searched funded (.selected choice)) released
  exact paid

include released in
private theorem charge_final : Charge.final quote model worker point rival =
    point.point.after (feeRule model original worker quote) rival := by
  obtain ⟨checked,arrived⟩ := charge_is_paid model domain original reference worker quote point rival ordinal funded choice released
  have finished : (Charge.trace quote worker point rival).result = some (.accepted checked) := by
    change (if Charge.endAt quote model worker point rival ≤ ordinal then
      (Charge.trace quote worker point rival).result else none) = some (.accepted checked) at arrived
    split at arrived
    · exact arrived
    · cases arrived
  have rules := Charge.completed_charge_is_exactly_the_precommitted_rule quote model worker point rival original (.accepted checked) finished
  have actual := (Charge.trace quote worker point rival).final_is_generated_only_by_its_actual_single_cut_rules
  rw [rules] at actual
  simpa only [List.foldl_cons,List.foldl_nil] using actual

include released in
theorem the_selected_installed_source_is_exactly_the_searched_complete_programme :
    install model domain original reference worker quote point rival ordinal =
      Splice.install point.point rival choice.policy.protocol.controls := by
  have retained :=  Search.every_selected_plan_keeps_its_paid_fee_prefix model domain original reference worker quote funded choice
  have whole := List.take_append_drop 1 choice.policy.protocol.controls
  rw [retained] at whole
  simp only [install,released]
  rw [charge_final model domain original reference worker quote point rival ordinal funded choice released]
  rw [←whole]
  rfl

include released in
theorem the_actual_paid_tail_is_the_original_complete_evaluated_input :
    (install model domain original reference worker quote point rival ordinal).source.input =
      (Budget.Programme.Debt.Information.Inquiry.Replay.Suffix.Window.Whole.source point.point original choice.policy.protocol rival).input := by
  rw [the_selected_installed_source_is_exactly_the_searched_complete_programme model domain original reference worker quote point rival ordinal funded choice released]
  have retained :=  Search.every_selected_plan_keeps_its_paid_fee_prefix model domain original reference worker quote funded choice
  have nonempty : choice.policy.protocol.controls ≠ [] := by
    intro empty
    rw [empty] at retained
    cases retained
  rw [Splice.input_assembly point.point rival original choice.policy.protocol.controls nonempty]
  rfl

theorem the_searched_plan_protects_every_covered_actual_source
    (covered : Continuation.Covered domain point.point) :
    Synthesis.accepts model.source.code (economicAxes point.point.source point.point.cut)
      (actualEvaluation model point.point original choice.policy.protocol rival)
      (actualEvaluation model point.point original reference rival) :=
  Observation.public_domain_acceptance_protects_every_covered_actual_source model point.point original choice.policy.protocol rival
    domain covered reference choice.policy.accepted

abbrev bound (ordinal : Nat) := Replanning.native model (install model domain original reference worker quote point rival ordinal)
abbrev facade (ordinal : Nat) := Native.AuthorityRuntime.facade (bound model domain original reference worker quote point rival ordinal)
abbrev activated (ordinal : Nat) := Inquiry.Runtime.readState (bound model domain original reference worker quote point rival ordinal)
  (depth (install model domain original reference worker quote point rival ordinal))

theorem the_deployed_search_is_consumed_with_its_original_whole_ledger_and_actual_next (ordinal : Nat) :
    let current := activated model domain original reference worker quote point rival ordinal
    HEq ((facade model domain original reference worker quote point rival ordinal).readoutAt current .responsibilities)
      (current.tick.generated.projectionOutcome (.component ())) ∧
    HEq current.tick.generated.wholeLedgerWriteBack
      (current.current.root.toAuthoritativeRoot.toLedgerRoot.generatedLedgerAt current.current.visit.current) ∧
    current.tick.nextCurrent = (facade model domain original reference worker quote point rival ordinal).process.stateAt
      ((facade model domain original reference worker quote point rival ordinal).process.successor current.state) := by
  have rooted := (facade model domain original reference worker quote point rival ordinal).readoutAt_factorizes
    (activated model domain original reference worker quote point rival ordinal) .responsibilities
  exact ⟨rooted.2.2.2.1,rooted.2.2.1,rooted.2.2.2.2⟩

end SaturationMonoid.ProcessGame.Society.PublicFunction.Computation.Search.Deployment
