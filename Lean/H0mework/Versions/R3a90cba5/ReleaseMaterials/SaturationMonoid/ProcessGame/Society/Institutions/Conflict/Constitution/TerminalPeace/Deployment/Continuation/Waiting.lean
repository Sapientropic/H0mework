import H0mework.Versions.R3a90cba5.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Deployment.Continuation

set_option autoImplicit false
set_option maxRecDepth 8192

namespace SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.Deployment

open Capitalism.Universal.Source.Program
open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot RootInquiryCompletion
open Clearance.Joint.Reinterpreted
open Clearance.Joint.Reinterpreted.OriginalConsumer
open FixedPoint.OpenPeace
open FixedPoint.OpenPeace.Network
open FixedPoint.OpenPeace.Network.Runtime (ReadOn)
open FixedPoint.OpenPeace.Network.Runtime.Decision
open private literal missing completedLaw completedWord from H0mework.Versions.R3a90cba5.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Deployment.Continuation

noncomputable section

private abbrev At := type_of% reached.2

private abbrev renewFrom (state : At) (n : Nat) :=
  (Runtime.history home namedReplies state renewPolicy n).1

abbrev waiting (n : Nat) := renewFrom reached.2 n

abbrev waitedPath (n : Nat) :=
  path.trans (Runtime.historyReads home namedReplies reached.2 renewPolicy n)

private theorem waitingLanguage (n : Nat) : (waiting n).base.language = reached.2.base.language := by
  induction n with
  | zero => rfl
  | succ n kept =>
    change (Runtime.advance home namedReplies (waiting n) quiet).next.base.language = _
    exact (Runtime.unpaid_keeps_the_language home namedReplies (waiting n) quiet rfl).trans kept

private theorem waitingScope (n : Nat) : ((waitedPath n).carry pending.pending).read = {terms} :=
  (((waitedPath n).keeps pending.pending).trans pending.exactScope).trans originalScope

private theorem stillMissing (n : Nat) :
    ¬ ((waitedPath n).carry pending.pending).read ⊆ (waiting n).base.language.covered := by
  rw [waitingScope n, waitingLanguage n, ← literal]
  exact missing

def completedAfterWaiting (n : Nat) := pending.completeAlong (waiting n) (waitedPath n) (.isFalse (stillMissing n))

theorem received_evidence_writes_on_the_reached_resident (n : Nat) :
    let prior := (waiting n).current.ledger
    let scope := ((waitedPath n).carry pending.pending).read
    let generated := (revised prior (waiting n).base.language scope (waiting n).u7 (stillMissing n)).generate
    let completed := completedAfterWaiting n
    completed.write.isSome = true ∧ scope = {terms} ∧
      (⟨generated.NewN, generated.newLivingRoot.generatedNextCurrentAt
        (.finite generated.newRoot.toRoot.initialVisit)⟩ : AnyAuthoritativeRootCurrent) =
      completed.next.current.ledger.resident.erase :=
  ⟨rfl, waitingScope n, revisedLedger_is_the_generated_first_write _ _ _ _ _⟩

theorem already_received_evidence_keeps_the_same_resident (n : Nat) :
    let completed := completedAfterWaiting n
    ∃ covered, let retried := pending.completeAlong completed.next ((waitedPath n).trans completed.reads) (.isTrue covered)
      retried.write = none ∧ retried.next = completed.next := by
  intro completed
  have covered : (((waitedPath n).trans completed.reads).carry pending.pending).read ⊆
      completed.next.base.language.covered := by
    change (completed.reads.carry ((waitedPath n).carry pending.pending)).read ⊆ _
    rw [completed.reads.keeps, completed.coverage]
    exact Set.subset_union_right
  exact ⟨covered, pending.covered_paid_scope_does_not_write_twice completed.next
    ((waitedPath n).trans completed.reads) covered⟩

abbrev afterWaiting (n m : Nat) := renewFrom (completedAfterWaiting n).next m

private theorem reads_from (start : At) (offset : Nat)
    (initial : start.current.physical.raw = renewStock offset ∧ start.current.programme = revised ∧
      start.current.recipe.move.word = jointWord) (n : Nat) :
    (renewFrom start n).current.physical.raw = renewStock (offset + n) ∧
    (renewFrom start n).current.programme = revised ∧ (renewFrom start n).current.recipe.move.word = jointWord := by
  induction n with
  | zero => exact initial
  | succ n earlier =>
    let prior := renewFrom start n
    let actual := Runtime.source home namedReplies prior quiet
    let next := (Runtime.advance home namedReplies prior quiet).next
    have law := (Runtime.same_programme home namedReplies prior quiet).trans actual.same_programme
    have word := Runtime.same_recipe_word home namedReplies prior quiet
    have stock := (Runtime.same_physical home namedReplies prior quiet).trans actual.same_physical_successor
    change next.current.physical.raw = _ ∧ next.current.programme = revised ∧ next.current.recipe.move.word = jointWord
    refine ⟨?_, law.trans earlier.2.1, word.trans earlier.2.2⟩
    rw [stock]
    have native : actual.source.next.physical.raw = prior.current.move.next := by
      change (FixedPoint.productiveRound prior.current .renew .renewed prior.current.programme prior.current.recipe).next.physical.raw = _
      exact (FixedPoint.productiveRound_reads_selected_production prior.current .renew .renewed prior.current.programme prior.current.recipe).2.1
    rw [native]
    change prior.current.programme.law.next prior.current.physical.raw prior.current.move.word = _
    have exactWord := (prior.current.recipe.moveAt_word prior.current.physical.raw prior.current.reserved).trans earlier.2.2
    rw [exactWord, earlier.1, earlier.2.1]
    rfl

theorem waitingRead (n : Nat) :
    (waiting n).current.physical.raw = renewStock n ∧
    (waiting n).current.programme = revised ∧ (waiting n).current.recipe.move.word = jointWord := by
  simpa only [Nat.zero_add] using reads_from reached.2 0 ⟨reachedStock, completedLaw, completedWord⟩ n

theorem afterWaitingRead (n m : Nat) :
    (afterWaiting n m).current.physical.raw = renewStock (n + m) ∧
    (afterWaiting n m).current.programme = revised ∧ (afterWaiting n m).current.recipe.move.word = jointWord := by
  have wait := waitingRead n
  exact reads_from (completedAfterWaiting n).next n
    ⟨(congrArg (fun physical => physical.raw) (completedAfterWaiting n).samePhysical).trans wait.1,
      wait.2.1, wait.2.2⟩ m

theorem waitingRows (n : Nat) :
    (waiting n).current.ledger.stack.balances = opening.paid.next.ledger.stack.balances :=
  (Runtime.history_keeps_rows home namedReplies reached.2 renewPolicy n).trans rebaseRows

theorem afterWaitingRows (n m : Nat) :
    (afterWaiting n m).current.ledger.stack.balances = opening.paid.next.ledger.stack.balances :=
  (Runtime.history_keeps_rows home namedReplies (completedAfterWaiting n).next renewPolicy m).trans (waitingRows n)

theorem every_waiting_and_following_period_pays (n m : Nat) :
    Runtime.LivingVisitAt home namedReplies reached.2 renewPolicy n ∧
      Runtime.LivingVisitAt home namedReplies (completedAfterWaiting n).next renewPolicy m :=
  ⟨Runtime.history_is_living_and_peaceful home namedReplies reached.2 renewPolicy n,
   Runtime.history_is_living_and_peaceful home namedReplies (completedAfterWaiting n).next renewPolicy m⟩

theorem the_revision_and_its_actual_suffix_keep_the_source_audit (n m : Nat) :
    ∃ audit : ReadOn reached.2.current.ledger.resident (Runtime.RefreshEvidence pending.live menu),
      let waitingReads := Runtime.historyReads home namedReplies reached.2 renewPolicy n
      let later := Runtime.historyReads home namedReplies (completedAfterWaiting n).next renewPolicy m
      (later.carry ((completedAfterWaiting n).reads.carry (waitingReads.carry audit))).read = replacement.record := by
  obtain ⟨audit, exactRead, _⟩ := the_original_joint_refusals_follow_the_material_successor 0
  let waitingReads := Runtime.historyReads home namedReplies reached.2 renewPolicy n
  let arrival := (completedAfterWaiting n).reads
  let later := Runtime.historyReads home namedReplies (completedAfterWaiting n).next renewPolicy m
  exact ⟨audit, (later.keeps _).trans ((arrival.keeps _).trans ((waitingReads.keeps audit).trans exactRead))⟩

theorem the_revised_actual_clock_is_cofinal (waits start : Nat) (bound : ℚ) :
    ∃ n ≥ start, bound < (afterWaiting waits n).current.physical.raw.clock :=
  Runtime.history_clock_is_cofinal home namedReplies (completedAfterWaiting waits).next renewPolicy start bound

end

end SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.Deployment
