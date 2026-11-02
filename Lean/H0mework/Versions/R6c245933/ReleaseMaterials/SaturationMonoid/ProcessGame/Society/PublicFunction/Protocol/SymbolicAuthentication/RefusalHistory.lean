import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.JournalWithdrawal

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.RefusalHistory

open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root
open ResponsibilityLifecycle
open Mandate.Challenge

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Technology] [DecidableEq Instrument]
  {base : RawLaw Party Good Port Technology Instrument}
  {scope : Mandate.Scope (Party := Party) (Good := Good) (Port := Port)}
  {Index : Type} (bound : ProgrammeFamily base scope Index) (inputs : Index)

theorem a_refused_actual_item_preserves_the_existing_status
    (original : Claim bound inputs) (history : History bound inputs original)
    (position : Position bound inputs)
    (denied : ¬ (Mandate.law base scope).Valid (position.item bound inputs).before (position.item bound inputs).request) :
    (history.receive bound inputs position).isPending bound inputs = history.isPending bound inputs := by
  cases history with
  | closed state archive slots => rfl
  | pending target state slots =>
    cases renewed : readReconfirmation bound inputs original position with
    | some receipt =>
      simp only [History.receive, renewed]
      split <;> rfl
    | none =>
      cases attempted : readAttempt bound inputs (target.claim bound inputs) position with
      | none => simp only [History.receive, renewed, attempted, History.isPending]
      | some receipt =>
        have same : receipt.position = position := by
          unfold readAttempt at attempted
          split at attempted
          · cases Option.some.inj attempted
            rfl
          · contradiction
        have refused : ¬ (Mandate.law base scope).Valid
            (receipt.position.item bound inputs).before (receipt.position.item bound inputs).request := by
          rw [same]
          exact denied
        simp only [History.receive, renewed, attempted, dif_neg refused, History.isPending]

theorem an_all_refused_visit_preserves_the_complete_previous_history
    (original : Claim bound inputs) (ordinal : Nat)
    (denied : ∀ position ∈ positionsAt bound inputs ordinal,
      ¬ (Mandate.law base scope).Valid (position.item bound inputs).before (position.item bound inputs).request) :
    (through bound inputs original (ordinal + 1)).isPending bound inputs =
      (through bound inputs original ordinal).isPending bound inputs := by
  rw [through]
  generalize positionsAt bound inputs ordinal = items at *
  generalize through bound inputs original ordinal = history
  induction items generalizing history with
  | nil => rfl
  | cons position rest ih =>
    rw [List.foldl_cons, ih (fun p inside => denied p (List.mem_cons_of_mem _ inside)) _]
    exact a_refused_actual_item_preserves_the_existing_status bound inputs original history position
      (denied position (List.mem_cons_self))

end SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.RefusalHistory

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.RefusalHistory

open Distributed Reaction Reaction.Feedback
open Distributed.Recall.Information.Agency.Protocol Continuation IncidentWithdrawalNative

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Technology] [DecidableEq Instrument]
  (model : Native.Authority.Bound (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument))
  (start : Cursor model.source.code) (past : List (EventHistory.Stage (code := model.source.code)))
  (vocabulary : OwnedAttestation.Vocabulary (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument))
  (encoding : StageTransport.Encoding (code := model.source.code)) (law : StageReception.Law model.source.code)
  (ready : IncidentWithdrawal.Ready model start past vocabulary encoding law)
  (rival : Opponent model.source.code) (more : List (EventHistory.Stage (code := model.source.code)))

-- The cut is the actual refusal visit; later valid events can settle a still-live claim.
theorem the_common_refusal_preserves_every_native_claim_at_its_actual_visit
    (denied : ¬ model.source.code.law.Valid (attemptItem model start past vocabulary encoding law ready).before
      (attemptItem model start past vocabulary encoding law ready).request)
    (original : Native.Authority.Challenge (native model start past vocabulary encoding law ready rival more)) :
    (Mandate.Challenge.through (family model start past vocabulary encoding law ready rival more)
      (sourceIndex model start past vocabulary encoding law ready rival more) original
      ((attemptPosition model start past vocabulary encoding law ready rival more).ordinal + 1)).isPending _ _ =
    (Mandate.Challenge.through (family model start past vocabulary encoding law ready rival more)
      (sourceIndex model start past vocabulary encoding law ready rival more) original
      (attemptPosition model start past vocabulary encoding law ready rival more).ordinal).isPending _ _ := by
  let bound := family model start past vocabulary encoding law ready rival more
  let inputs := sourceIndex model start past vocabulary encoding law ready rival more
  let attempt := attemptPosition model start past vocabulary encoding law ready rival more
  have refused : ¬ (Mandate.law model.base model.scope).Valid
      (attempt.item bound inputs).before (attempt.item bound inputs).request := by
    rw [attempt_position_item_is_original, ← model.law_exact]
    exact denied
  have single := IncidentChallenge.actual_trace_items model start (full model start past vocabulary encoding law ready rival more)
    (attemptRow model start past vocabulary encoding law ready rival)
    (attempt_is_in_the_same_final_source model start past vocabulary encoding law ready rival more)
  have singleton : Mandate.Challenge.positionsAt bound inputs attempt.ordinal = [attempt] :=
    WithdrawalHistory.a_single_item_visit_has_its_unique_actual_position _ _ _
      ((congrArg List.length single).trans (by rw [attempt_items_are_original]; rfl))
  apply an_all_refused_visit_preserves_the_complete_previous_history
  intro position inside
  rw [singleton] at inside
  rw [List.mem_singleton.mp inside]
  exact refused

end SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.RefusalHistory
