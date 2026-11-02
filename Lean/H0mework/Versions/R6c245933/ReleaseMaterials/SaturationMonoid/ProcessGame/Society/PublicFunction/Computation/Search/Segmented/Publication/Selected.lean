import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Computation.Search.Segmented.Publication.Plan

set_option autoImplicit false
set_option maxRecDepth 65536
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Computation.Search.Segmented.Publication.Selected
open Distributed Distributed.Reaction Distributed.Reaction.Feedback
open Distributed.Recall.Information.Agency.Protocol Continuation
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root
open Budget.Programme.Debt Budget.Programme.Debt.Information Budget.Programme.Debt.Information.Inquiry
open Budget.Programme.Debt.Information.Inquiry.Replay.Suffix.Window.Whole

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Technology] [DecidableEq Instrument]
  (model : Native.Authority.Bound (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument))
  (domain : List (Cursor model.source.code)) (original : Prefix.Rule model.source.code)
  (reference : Program model.source.code (horizon domain))
  (worker receiver : Fin model.source.code.sites)
  (quote : Charge.Quote (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument)) (quotas : List Nat) (slots : Nat)
  (point : View (code := model.source.code)) (rival : Opponent model.source.code) (ordinal : Nat)

/-- The shared material occurrence carries no classifier cache or cache-completion claim. -/
structure Plan where
  announcements : List (Prefix.Rule model.source.code)
  registered : Publication.Plan.layout model worker receiver slots = some announcements
  within : quotas.length+announcements.length ≤ Deployment.actualHorizon model point
  choice : Prefix.Choice model domain original (reserved model original worker quote quotas) reference
  publicationPrefix : Publication.Plan.eligible model domain original reference worker quote quotas announcements choice.policy = true
  complete : (Segmented.trace model domain original reference worker quote quotas point rival).remaining = []
  room : quotas.length ≤ horizon domain
  payments : List (PaidSlot model worker quote rival)
  payments_exact : payments = (Segmented.trace model domain original reference worker quote quotas point rival).payments
  closing : PaidSlot model worker quote rival
  sealed : (Segmented.trace model domain original reference worker quote quotas point rival).closingReceipt = some closing
  arrived : arrival (Segmented.trace model domain original reference worker quote quotas point rival).final.point ≤ ordinal

variable (plan : Plan model domain original reference worker receiver quote quotas slots point rival ordinal)

include plan in
theorem paid_prefix :
    Deployment.paidFinal model domain original reference worker quote quotas point rival =
      Splice.install point.point rival (reserved model original worker quote quotas) ∧ quotas.length ≤ horizon domain := by
  obtain ⟨actual,rules,_⟩ := (Segmented.trace model domain original reference worker quote quotas point rival).the_actual_source_contains_exactly_the_executed_fee_prefix
  have same : (Segmented.trace model domain original reference worker quote quotas point rival).rules = reserved model original worker quote quotas := by
    simpa only [plan.complete,List.length_nil,Nat.sub_zero] using rules
  exact ⟨by simpa only [same] using actual,plan.room⟩

/-- Ordinals are read from each original before-cut, never zipped onto a filtered list. -/
def indexedPayments := plan.payments.map (fun payment => (payment.before.point.cut-point.point.cut,payment))

theorem indexing_preserves_every_original_actual_payment :
    (indexedPayments model domain original reference worker receiver quote quotas slots point rival ordinal plan).map Prod.snd =
      (Segmented.trace model domain original reference worker quote quotas point rival).payments := by
  have erased : (indexedPayments model domain original reference worker receiver quote quotas slots point rival ordinal plan).map Prod.snd = plan.payments := by
    unfold indexedPayments
    rw [List.map_map]
    exact List.map_id _
  exact erased.trans plan.payments_exact

private theorem legacy_execution_exact
    (legacy : Publication.Plan.Selection model domain original reference worker receiver quote quotas slots point rival ordinal) :
    legacy.execution = Segmented.trace model domain original reference worker quote quotas point rival := by
  have released := legacy.arrived
  rw [Runtime.read_is_the_arrived_source_generated_outcome] at released
  unfold Runtime.available at released
  dsimp only at released
  split at released
  · exact (congrArg Prod.fst (Option.some.inj released)).symm
  · cases released

private theorem legacy_complete
    (legacy : Publication.Plan.Selection model domain original reference worker receiver quote quotas slots point rival ordinal) :
    (Segmented.trace model domain original reference worker quote quotas point rival).remaining = [] ∧ quotas.length ≤ horizon domain := by
  have made := Deployment.released_result_is_the_same_source_generated_cache model domain original reference worker quote quotas point rival ordinal
    legacy.execution legacy.finished legacy.arrived
  refine ⟨?_,(Segmented.a_released_result_has_executed_the_entire_fixed_fee_plan model domain original reference worker quote quotas point rival legacy.finished made).2.2⟩
  unfold Segmented.result Segmented.close at made
  split at made
  · rename_i ready
    exact ready.2.1
  · cases made

private theorem legacy_has_closing
    (legacy : Publication.Plan.Selection model domain original reference worker receiver quote quotas slots point rival ordinal) :
    ∃ closing, legacy.execution.closingReceipt = some closing := by
  have made := Deployment.released_result_is_the_same_source_generated_cache model domain original reference worker quote quotas point rival ordinal
    legacy.execution legacy.finished legacy.arrived
  have present := (Segmented.a_released_finished_cache_is_its_actual_payment_replay_and_has_a_closing_receipt
    model domain original reference worker quote quotas point rival legacy.finished made).2
  rw [←legacy_execution_exact model domain original reference worker receiver quote quotas slots point rival ordinal legacy] at present
  exact present

private def legacyClosing
    (legacy : Publication.Plan.Selection model domain original reference worker receiver quote quotas slots point rival ordinal) : PaidSlot model worker quote rival :=
  match closed : legacy.execution.closingReceipt with
  | some closing => closing
  | none => False.elim (by
    have present := legacy_has_closing model domain original reference worker receiver quote quotas slots point rival ordinal legacy
    rw [closed] at present
    obtain ⟨_,impossible⟩ := present
    cases impossible)

private theorem legacyClosing_exact
    (legacy : Publication.Plan.Selection model domain original reference worker receiver quote quotas slots point rival ordinal) :
    legacy.execution.closingReceipt = some (legacyClosing model domain original reference worker receiver quote quotas slots point rival ordinal legacy) := by
  unfold legacyClosing
  split
  · assumption
  · have present := legacy_has_closing model domain original reference worker receiver quote quotas slots point rival ordinal legacy
    rename_i closed
    rw [closed] at present
    obtain ⟨_,impossible⟩ := present
    cases impossible

/-- The data projections stay literal so existing consumers retain their selected occurrence. -/
def ofLegacy (legacy : Publication.Plan.Selection model domain original reference worker receiver quote quotas slots point rival ordinal) :
    Plan model domain original reference worker receiver quote quotas slots point rival ordinal where
  announcements := legacy.announcements
  registered := legacy.registered
  within := legacy.within
  choice := legacy.choice
  publicationPrefix := legacy.publicationPrefix
  complete := (legacy_complete model domain original reference worker receiver quote quotas slots point rival ordinal legacy).1
  room := (legacy_complete model domain original reference worker receiver quote quotas slots point rival ordinal legacy).2
  payments := legacy.execution.payments
  payments_exact := congrArg Scan.payments (legacy_execution_exact model domain original reference worker receiver quote quotas slots point rival ordinal legacy)
  closing := legacyClosing model domain original reference worker receiver quote quotas slots point rival ordinal legacy
  sealed := by
    rw [←legacy_execution_exact model domain original reference worker receiver quote quotas slots point rival ordinal legacy]
    exact legacyClosing_exact model domain original reference worker receiver quote quotas slots point rival ordinal legacy
  arrived := by
    have released := legacy.arrived
    rw [Runtime.read_is_the_arrived_source_generated_outcome] at released
    unfold Runtime.available at released
    dsimp only at released
    split at released
    · assumption
    · cases released

instance : Coe (Publication.Plan.Selection model domain original reference worker receiver quote quotas slots point rival ordinal)
    (Plan model domain original reference worker receiver quote quotas slots point rival ordinal) :=
  ⟨ofLegacy model domain original reference worker receiver quote quotas slots point rival ordinal⟩

end SaturationMonoid.ProcessGame.Society.PublicFunction.Computation.Search.Segmented.Publication.Selected
