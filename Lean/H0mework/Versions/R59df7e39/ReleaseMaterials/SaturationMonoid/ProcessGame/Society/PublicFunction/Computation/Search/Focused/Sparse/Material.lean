import H0mework.Versions.R59df7e39.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Computation.Search.Focused.Sparse.Scan

set_option autoImplicit false
set_option maxRecDepth 65536
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Computation.Search.Focused.Sparse.Material
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
  (domain : List (Cursor model.source.code)) (original : Rule model.source.code)
  (reference : Program model.source.code (horizon domain)) (worker : Fin model.source.code.sites)
  (quote : Charge.Quote (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument)) (quotas : List Nat)
  (rival : Opponent model.source.code)

private theorem stopped_has_no_actual_rule (point : View (code := model.source.code))
    (reason : Segmented.Halt model quote point) : (Charge.trace quote worker point rival).rules = [] := by
  cases reason with
  | exhausted empty => simp only [Charge.trace,dif_pos empty,Cut.Trace.rules]
  | unsupported outside =>
    by_cases empty : (Cut.seed point.point).remaining = 0
    · simp only [Charge.trace,dif_pos empty,Cut.Trace.rules]
    · have inspected : Replay.inspect worker ((Charge.tariff quote).word () 1) point rival = .unsupported (by
          simpa only [Charge.tariff,Tariff.word,List.append_nil] using outside) := by
        unfold Replay.inspect
        rw [dif_neg (by simpa only [Charge.tariff,Tariff.word,List.append_nil] using outside)]
      simp only [Charge.trace,dif_neg empty,inspected,Cut.Trace.rules,Replay.Attempt.rule,Option.toList_none]

private theorem sparse_stopped_has_no_actual_rule (point : View (code := model.source.code))
    (reason : Sparse.Halt model quote point) : (Charge.trace quote worker point rival).rules = [] := by
  cases reason with
  | exhausted empty => exact stopped_has_no_actual_rule model worker quote rival point (.exhausted empty)
  | unsupported outside => exact stopped_has_no_actual_rule model worker quote rival point (.unsupported outside)

/-- Both classifiers are restrictions of the same actual fee-step occurrence.
No equality of their cache contents or their selected futures is asserted. -/
theorem both_scans_have_the_same_entire_physical_prefix
    {point : View (code := model.source.code)} {jobs : List Nat}
    {firstCache : Option (Segmented.Cache model domain original reference worker quote quotas)}
    {secondCache : Option (Sparse.Cache model domain original reference worker quote quotas)}
    (first : Segmented.Scan model domain original reference worker quote quotas rival point firstCache jobs)
    (second : Sparse.Scan model domain original reference worker quote quotas rival point secondCache jobs) :
    first.final = second.final ∧ first.rules = second.rules ∧ first.remaining = second.remaining ∧
      first.closingReceipt = second.closingReceipt ∧ first.payments = second.payments := by
  induction first generalizing secondCache with
  | empty point cache => cases second;exact ⟨rfl,rfl,rfl,rfl,rfl⟩
  | stopped point cache quota rest reason =>
    cases second with
    | stopped => exact ⟨rfl,rfl,rfl,rfl,rfl⟩
    | next _ _ _ _ consumed _ =>
      have empty := stopped_has_no_actual_rule model worker quote rival point reason
      rw [empty] at consumed
      cases consumed
  | next point cache quota rest consumed later ih =>
    cases second with
    | stopped _ _ _ _ reason =>
      have empty := sparse_stopped_has_no_actual_rule model worker quote rival point reason
      rw [empty] at consumed
      cases consumed
    | next _ _ _ _ _ tail =>
      obtain ⟨final,rules,remaining,closing,payments⟩ := ih tail
      refine ⟨final,congrArg (Charge.feeRule quote model worker original :: ·) rules,remaining,?_,?_⟩
      · cases rest with
        | nil => rfl
        | cons => exact closing
      · exact congrArg (fun receipts : List (Segmented.PaidSlot model worker quote rival) =>
          match seen : (Charge.read quote model worker point rival (Charge.endAt quote model worker point rival)).1 with
          | some (.accepted checked) =>
              (⟨point,quota,⟨checked,seen⟩⟩ : Segmented.PaidSlot model worker quote rival) :: receipts
          | _ => receipts) payments

end SaturationMonoid.ProcessGame.Society.PublicFunction.Computation.Search.Focused.Sparse.Material
