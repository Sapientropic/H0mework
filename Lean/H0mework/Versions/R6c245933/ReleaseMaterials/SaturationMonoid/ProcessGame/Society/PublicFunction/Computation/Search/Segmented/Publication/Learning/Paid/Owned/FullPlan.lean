import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Computation.Search.Segmented.Publication.Learning.Paid.Owned.Planner

set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 400000

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Computation.Search.Segmented.Publication.Learning.Paid.Owned.FullPlan
open Distributed Reaction Reaction.Feedback
open Distributed.Recall.Information Agency.Protocol Continuation
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root
open Budget.Programme.Debt Budget.Programme.Debt.Information Budget.Programme.Debt.Information.Inquiry
open Budget.Programme.Debt.Information.Inquiry.Replay.Suffix.Window.Whole
open PublicFunction.Protocol.SymbolicAuthentication

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Technology] [DecidableEq Instrument]
  (input : Task (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument))

def Full (cache : Cache input) : Prop := cache.programme.controls.length = horizon input.domain

theorem progress (cache : Cache input) (full : Full input cache) : Full input (Driving.Progress.next cache) := by
  unfold Full Driving.Progress.next
  split
  · exact Prefix.Commitment.padded_length _ _
  · exact full

theorem advance (cache : Cache input) (full : Full input cache) : Full input (Owned.advance input cache) := by
  exact progress input cache full

theorem commit (cache : Cache input) (full : Full input cache) (reader : Fin input.model.source.code.sites)
    (reading : Fin input.model.source.code.signals) (decision : cache.Decision reader) :
    Full input (cache.commit reader reading decision) := by
  cases decision with
  | refused => exact full
  | admitted accepted =>
      change (cache.proposal reader).controls.length = horizon input.domain
      have length : cache.programme.controls.length = horizon input.domain := full
      simp only [Paid.State.proposal,Prefix.extension,Continuation.Whole.Complete.clip,Splice.word,
        List.length_take,List.length_append,List.length_cons,List.length_drop,length]
      omega

theorem walk {cache : Cache input} (event : Walk input cache) (full : Full input cache) : Full input event.final := by
  induction event with
  | exhausted | terminal => exact full
  | @learned state live owned decision =>
      exact advance input _ (commit input state full _ _ decision)
  | waiting live foreign later ih => exact ih (advance input _ full)

theorem turn {cache : Cache input} (event : Turn input cache) (full : Full input cache) : Full input event.final := by
  cases event with
  | unsupported => exact full
  | unreserved =>
      change Full input (if input.continueUnreserved then Owned.advance input cache else cache)
      split
      · exact advance input _ full
      · exact full
  | unpaid => exact full
  | paid supported booked receipt later => exact walk input later full

theorem run (rounds : Nat) (cache : Cache input) (full : Full input cache) : Full input (Owned.run input rounds cache) := by
  induction rounds generalizing cache with
  | zero => exact full
  | succ rounds ih => exact ih _ (turn input _ full)

theorem every_source_generated_plan_retains_its_full_extent
    (initial : input.baseline.controls.length = horizon input.domain) (rounds : Nat) :
    match Source.response input rounds with
    | .inl _ => True
    | .inr cache => Full input cache := by
  unfold Source.response Source.generate
  cases Source.seed input with
  | rejected => trivial
  | accepted cache empty programme beliefs =>
      change Full input (trace input rounds cache).1
      rw [trace_is_the_original_run_and_reports]
      apply run input rounds cache
      change cache.programme.controls.length = horizon input.domain
      rw [programme]
      exact initial

theorem every_emitted_plan_retains_its_full_extent
    (initial : input.baseline.controls.length = horizon input.domain) (rounds : Nat) (made : Source.Occurrence input rounds) :
    match made.response with
    | .inl _ => True
    | .inr cache => Full input cache := by
  have same : made.response = Source.response input rounds := by
    unfold Source.Occurrence.response Source.response
    rw [made.exact_generation]
  rw [same]
  exact every_source_generated_plan_retains_its_full_extent input initial rounds

end SaturationMonoid.ProcessGame.Society.PublicFunction.Computation.Search.Segmented.Publication.Learning.Paid.Owned.FullPlan
