import H0mework.Versions.R3a90cba5.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Deployment.Replacement
import H0mework.Versions.R3a90cba5.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.FixedPoint.OpenPeace.Network.Runtime.Rebase.Privacy

set_option autoImplicit false
set_option maxRecDepth 8192

namespace SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.Deployment

open Capitalism.Universal.Source.Program
open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot RootInquiryCompletion
open Clearance.Joint.Reinterpreted
open Clearance.Joint.Reinterpreted.OriginalConsumer
open FixedPoint.OpenPeace
open FixedPoint.OpenPeace.Network
open FixedPoint.OpenPeace.Network.Runtime (ReadOn ReadAt)
open FixedPoint.OpenPeace.Network.Runtime.Decision
open private replaceCatalogue from H0mework.Versions.R3a90cba5.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Deployment.Replacement

noncomputable section

private theorem literal : (path.carry pending.pending).read = {terms} :=
  ((path.keeps pending.pending).trans pending.exactScope).trans originalScope

private theorem missing : ¬ (path.carry pending.pending).read ⊆ reached.2.base.language.covered := by
  have absent : terms ∉ reached.2.base.language.covered := by
    rw [reachedFromPending]
    change terms ∉ replacement.joint.actual.next.base.language.covered
    rw [replacement.joint.actual.language, pending.language, opening.network.initialLanguage]
    exact Set.notMem_empty _
  rw [literal, Set.singleton_subset_iff]
  exact absent

def completed := pending.completeAfterRebases replaceCatalogue policy 1 (.isFalse missing)

theorem sameOriginalScope :
    (completed.reads.carry (path.carry pending.pending)).read = {terms} ∧
      terms ∈ completed.next.base.language.covered := by
  have exact := pending.the_mixed_schedule_retains_the_original_paid_scope replaceCatalogue policy 1 (.isFalse missing)
  refine ⟨exact.1.trans originalScope, exact.2 ?_⟩
  rw [originalScope]
  exact Set.mem_singleton _

theorem the_generated_revision_is_the_live_next :
    let prior := reached.2.current.ledger
    let generated := (revised prior reached.2.base.language (path.carry pending.pending).read reached.2.u7 missing).generate
    completed.write.isSome = true ∧
      (⟨generated.NewN, generated.newLivingRoot.generatedNextCurrentAt
        (.finite generated.newRoot.toRoot.initialVisit)⟩ : AnyAuthoritativeRootCurrent) =
      completed.next.current.ledger.resident.erase :=
  ⟨rfl, revisedLedger_is_the_generated_first_write _ _ _ _ _⟩

theorem noSecondWrite :
    ∃ covered, (pending.completeAlong completed.next (path.trans completed.reads) (.isTrue covered)).write = none := by
  have covered : ((path.trans completed.reads).carry pending.pending).read ⊆ completed.next.base.language.covered := by
    change (completed.reads.carry (path.carry pending.pending)).read ⊆ _
    rw [sameOriginalScope.1, Set.singleton_subset_iff]
    exact sameOriginalScope.2
  exact ⟨covered, (pending.covered_paid_scope_does_not_write_twice completed.next (path.trans completed.reads) covered).1⟩

theorem completedStock : completed.next.current.physical.raw = rebaseStock :=
  (congrArg (fun physical => physical.raw) completed.samePhysical).trans reachedStock

private theorem completedLaw : completed.next.current.programme = revised := by
  change reached.2.current.programme = _
  rw [reachedFromPending]
  exact replacement.joint.actual.programme.trans pendingLaw

private theorem completedWord : completed.next.current.recipe.move.word = jointWord := by
  change reached.2.current.recipe.move.word = _
  rw [reachedFromPending]
  exact replacement.word

theorem pendingRows : pending.live.current.ledger.stack.balances = opening.paid.next.ledger.stack.balances := by
  have chargedRows : pending.live.current.ledger.stack.balances = visit.source.next.ledger.stack.balances := by
    change visit.next.native.ledger.stack.balances = _
    generalize visit = posted
    cases posted <;> rfl
  exact chargedRows.trans (visit.source.rows.trans opening.network.rows)

theorem rebaseRows : reached.2.current.ledger.stack.balances = opening.paid.next.ledger.stack.balances :=
  ((Runtime.RebaseHistory.every_interleaving_keeps_the_original_rows_and_orders home namedReplies
    replaceCatalogue initial policy 1).1).trans pendingRows

theorem completedRows : completed.next.current.ledger.stack.balances = opening.paid.next.ledger.stack.balances :=
  rebaseRows

abbrev quiet : Input Bool Bool Bool Unit Unit := .native ⟨none, []⟩

def renewPolicy : Policy Bool Bool Bool Unit Unit := nativeSchedule fun _ => ⟨none, []⟩

abbrev running (n : Nat) := (Runtime.history home namedReplies completed.next renewPolicy n).1

theorem the_revision_drives_the_next_paid_material (n : Nat) :
    let ledger := (running n).current.ledger
    let round := (Runtime.source home namedReplies (running n) quiet).source.round
    (⟨ledger.world, (Installation.Live.action ledger round.visit.read true).target.targetAnswerAndNext.nextCurrent⟩ :
      AnyAuthoritativeRootCurrent) = round.next.ledger.resident.erase ∧
    Runtime.LivingVisitAt home namedReplies completed.next renewPolicy n := by
  intro ledger round
  exact ⟨round.wholeNext, Runtime.history_is_living_and_peaceful home namedReplies completed.next renewPolicy n⟩

theorem the_deployment_continues_cofinally (start : Nat) (bound : ℚ) :
    ∃ n ≥ start, bound < (running n).current.physical.raw.clock :=
  Runtime.history_clock_is_cofinal home namedReplies completed.next renewPolicy start bound

theorem runningRows (n : Nat) :
    (running n).current.ledger.stack.balances = opening.paid.next.ledger.stack.balances :=
  (Runtime.history_keeps_rows home namedReplies completed.next renewPolicy n).trans completedRows

theorem the_original_joint_refusals_follow_the_material_successor (n : Nat) :
    ∃ audit : ReadOn reached.2.current.ledger.resident (Runtime.RefreshEvidence pending.live menu),
      audit.read = replacement.record ∧
      ((Runtime.historyReads home namedReplies completed.next renewPolicy n).carry
        (completed.reads.carry audit)).read = replacement.record := by
  let published := Runtime.RebaseHistory.refreshAudit home namedReplies initial replaceCatalogue
  have exactRead : published.map ReadAt.read = some replacement.record := by
    exact (Runtime.RebaseHistory.refresh_audit_is_the_selected_decision home namedReplies initial replaceCatalogue).trans
      (congrArg Runtime.RefreshDecision.evidence replacement.selected)
  cases found : published with
  | none => rw [found] at exactRead; cases exactRead
  | some audit =>
    rw [found] at exactRead
    have evidence : audit.read = replacement.record := Option.some.inj exactRead
    exact ⟨audit, evidence,
      ((Runtime.historyReads home namedReplies completed.next renewPolicy n).keeps (completed.reads.carry audit)).trans
        ((completed.reads.keeps audit).trans evidence)⟩

def renewStock : Nat → Original.Raw
  | 0 => rebaseStock
  | n + 1 => revised.law.next (renewStock n) jointWord

theorem runningRead (n : Nat) :
    (running n).current.physical.raw = renewStock n ∧
    (running n).current.programme = revised ∧ (running n).current.recipe.move.word = jointWord := by
  induction n with
  | zero => exact ⟨completedStock, completedLaw, completedWord⟩
  | succ n earlier =>
    let prior := running n
    let actual := Runtime.source home namedReplies prior quiet
    let next := (Runtime.advance home namedReplies prior quiet).next
    have law := (Runtime.same_programme home namedReplies prior quiet).trans actual.same_programme
    have word := Runtime.same_recipe_word home namedReplies prior quiet
    have stock := (Runtime.same_physical home namedReplies prior quiet).trans actual.same_physical_successor
    change next.current.physical.raw = _ ∧ next.current.programme = revised ∧ next.current.recipe.move.word = jointWord
    refine ⟨?_, law.trans earlier.2.1, word.trans earlier.2.2⟩
    rw [stock]
    have native :
        actual.source.next.physical.raw = prior.current.move.next := by
      change (FixedPoint.productiveRound prior.current .renew .renewed prior.current.programme prior.current.recipe).next.physical.raw = _
      exact (FixedPoint.productiveRound_reads_selected_production prior.current .renew .renewed
        prior.current.programme prior.current.recipe).2.1
    rw [native]
    change prior.current.programme.law.next prior.current.physical.raw prior.current.move.word = _
    have exactWord := (prior.current.recipe.moveAt_word prior.current.physical.raw prior.current.reserved).trans earlier.2.2
    rw [exactWord, earlier.1, earlier.2.1]
    rfl

end

end SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.Deployment
