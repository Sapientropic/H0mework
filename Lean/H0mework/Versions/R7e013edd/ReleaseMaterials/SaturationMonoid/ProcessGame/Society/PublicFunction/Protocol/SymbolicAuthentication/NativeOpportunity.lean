import H0mework.Versions.R7e013edd.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.RetryBudgetConsumer

set_option autoImplicit false
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.NativeOpportunity
open Distributed Reaction Reaction.Feedback
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root
open Distributed.Recall.Information.Agency.Protocol Continuation

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Technology] [DecidableEq Instrument]
  (model : Native.Authority.Bound (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument))
  (start : Cursor model.source.code) (past : NativeReviewRun.Stages model)

abbrev full (ready : NativeReview.Ready model start past) := NativeReviewRun.attempted model start past ready
abbrev originalType (ready : NativeReview.Ready model start past) :=
  Native.Authority.Challenge (NativeReviewHistory.native model start past ready (OriginQueue.environment start))
def originals (ready : NativeReview.Ready model start past) : List (originalType model start past ready) :=
  (NativeReview.inventory model start (full model start past ready)).map Sigma.fst
abbrev beforePending (ready : NativeReview.Ready model start past) (original : originalType model start past ready) :=
  (Mandate.Challenge.through (NativeReviewHistory.family model start past ready (OriginQueue.environment start))
    (NativeReviewHistory.sourceIndex model start past ready (OriginQueue.environment start)) original
    (NativeReviewHistory.position model start past ready (OriginQueue.environment start)).ordinal).isPending _ _
def eligible (ready : NativeReview.Ready model start past) (original : originalType model start past ready) : Bool :=
  beforePending model start past ready original &&
    NativeReviewHistory.targetReady model start past ready (OriginQueue.environment start) original

structure Attempt where
  private mk ::
  ready : NativeReview.Ready model start past
  accepted : model.source.code.law.Valid (EventStep.seed (NativeReview.current model start past)).current
    (NativeReview.action model start past ready.receiver)
  selected : NativeReview.produce model start past = .paid ready accepted
  original : originalType model start past ready
  member : original ∈ originals model start past ready
  pending : beforePending model start past ready original = true
  aligned : NativeReviewHistory.targetReady model start past ready (OriginQueue.environment start) original = true

-- A valid current revoke is selected only when it actually discharges an original pending target.
def probe : Option (Attempt model start past) :=
  match selected : NativeReview.produce model start past with
  | .paid ready accepted =>
    match found : (originals model start past ready).find? (eligible model start past ready) with
    | none => none
    | some original =>
      have checked : beforePending model start past ready original = true ∧
          NativeReviewHistory.targetReady model start past ready (OriginQueue.environment start) original = true := by
        have actual := List.find?_some found
        simpa only [eligible, Bool.and_eq_true] using actual
      some ⟨ready, accepted, selected, original, List.mem_of_find?_eq_some found, checked.1, checked.2⟩
  | _ => none

theorem every_selected_opportunity_closes_a_real_previously_pending_original
    (answer : Attempt model start past) :
    answer.original ∈ originals model start past answer.ready ∧
    beforePending model start past answer.ready answer.original = true ∧
    (NativeReviewHistory.history model start past answer.ready (OriginQueue.environment start) answer.original).isPending _ _ = false ∧
    (NativeReviewHistory.history model start past answer.ready (OriginQueue.environment start) answer.original).state.current.history =
      (NativeReviewHistory.history model start past answer.ready (OriginQueue.environment start) answer.original).state.generated.events :=
  ⟨answer.member, answer.pending,
    NativeReviewHistory.a_paid_actual_attempt_closes_every_ready_original model start past answer.ready
      (OriginQueue.environment start) answer.original answer.accepted answer.aligned,
    NativeReviewHistory.every_original_has_its_complete_native_history model start past answer.ready
      (OriginQueue.environment start) answer.original⟩

theorem probe_exposes_the_actual_native_selection :
    (probe model start past).isSome =
      match NativeReview.produce model start past with
      | .paid ready _ => ((originals model start past ready).find? (eligible model start past ready)).isSome
      | _ => false := by
  unfold probe
  split <;> split <;> simp_all only [Option.isSome]
  rename_i impossible actual
  exact False.elim (impossible _ _ rfl)

theorem no_opportunity_at_a_paid_cut_is_exactly_the_absence_of_an_aligned_pending_target
    (ready : NativeReview.Ready model start past)
    (accepted : model.source.code.law.Valid (EventStep.seed (NativeReview.current model start past)).current
      (NativeReview.action model start past ready.receiver))
    (selected : NativeReview.produce model start past = .paid ready accepted) :
    probe model start past = none ↔ ∀ original ∈ originals model start past ready,
      eligible model start past ready original = false := by
  rw [← Option.not_isSome_iff_eq_none, probe_exposes_the_actual_native_selection, selected,
    Option.not_isSome_iff_eq_none, List.find?_eq_none]
  simp only [Bool.not_eq_true]

theorem every_selected_opportunity_terminates_the_actual_original_inventory_row
    (answer : Attempt model start past) :
    ∃ row ∈ NativeReview.inventory model start (full model start past answer.ready),
      row.1 = answer.original ∧ row.2.isPending _ _ = false := by
  obtain ⟨row, member, same⟩ := List.mem_map.mp answer.member
  have closed := (every_selected_opportunity_closes_a_real_previously_pending_original model start past answer).2.2.1
  rw [← same] at closed
  refine ⟨row, member, same, ?_⟩
  obtain ⟨birth, birthInside, mapped⟩ := List.mem_flatMap.mp member
  obtain ⟨claim, claimInside, identity⟩ := List.mem_map.mp mapped
  cases identity
  exact closed

end SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.NativeOpportunity
