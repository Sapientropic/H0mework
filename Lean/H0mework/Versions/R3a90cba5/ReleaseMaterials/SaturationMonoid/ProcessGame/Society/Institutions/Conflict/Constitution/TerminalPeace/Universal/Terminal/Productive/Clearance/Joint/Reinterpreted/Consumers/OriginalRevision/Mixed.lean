import H0mework.Versions.R3a90cba5.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.Productive.Clearance.Joint.Reinterpreted.Consumers.OriginalDue
import H0mework.Versions.R3a90cba5.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.Productive.Clearance.Joint.Reinterpreted.Consumers.OriginalRevision.Deferred
import H0mework.Versions.R3a90cba5.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.Productive.Clearance.Joint.Reinterpreted.Consumers.OriginalRevision.Rebase
import H0mework.Versions.R3a90cba5.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.FixedPoint.OpenPeace.Network.Runtime.Decision.Deferred.Transport

set_option autoImplicit false
set_option maxRecDepth 8192

namespace SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.Clearance.Joint.Reinterpreted.OriginalConsumer

open Capitalism.Universal.Source.Program
open FixedPoint.OpenPeace
open FixedPoint.OpenPeace.Network
open FixedPoint.OpenPeace.Network.Runtime.Decision
open FixedPoint.OpenPeace.Operational (RecipeConditions)
open private start home submit scope first_ready first_scope termsEffect from H0mework.Versions.R3a90cba5.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.Productive.Clearance.Joint.Reinterpreted.Consumers.OriginalRevision
open private job from H0mework.Versions.R3a90cba5.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.Productive.Clearance.Joint.Reinterpreted.Consumers.OriginalRevision.Deferred
open private afterReview reviewedStock from H0mework.Versions.R3a90cba5.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.Productive.Clearance.Joint.Reinterpreted.Consumers.OriginalRevision.Rebase

noncomputable section

private abbrev initial := Sigma.mk actualNetwork.paid.next.physical.raw job.live
private abbrev At := type_of% initial

private def mixedPolicy (n : Nat) (_ : At) : Runtime.RebaseHistory.Command Bool Bool Bool Unit Unit :=
  if n = 0 then .refresh else .scheduled (.native ⟨none, []⟩)

private abbrev reached := Runtime.RebaseHistory.history home namedReplies catalogue initial mixedPolicy 1
private abbrev path := Runtime.RebaseHistory.historyReads home namedReplies catalogue initial mixedPolicy 1

private theorem paidLaw : job.live.current.programme = revised :=
  (Runtime.same_programme home namedReplies start (submit 0)).symm.trans first_ready.1

private theorem paidStock : job.live.current.physical.raw = afterReview :=
  (congrArg (fun p : TerminalPeace.Universal.Runtime.Native Bool Bool Bool Unit Unit => p.raw)
    (job.physical.trans (Runtime.same_physical home namedReplies start (submit 0)).symm)).trans reviewedStock

private theorem viable : ∃ i : Fin (catalogue job.live.current.programme job.live.current.physical.raw).length,
    RecipeConditions job.live.current.programme (originalRaw loss) job.live.current.physical.raw (people loss front)
      (catalogue job.live.current.programme job.live.current.physical.raw)[i] := by
  let input := job.live.current.programme
  let raw := job.live.current.physical.raw
  have present : codeFor input paidLaw raw ∈ catalogue input raw := by
    rw [catalogue_at input paidLaw]
    exact List.mem_cons_self
  obtain ⟨i, code⟩ := List.mem_iff_get.mp present
  refine ⟨i, ?_⟩
  change RecipeConditions input (originalRaw loss) raw (people loss front) ((catalogue input raw).get i)
  rw [code]
  have stock : raw = afterReview := paidStock
  apply checksFor
  · rw [stock]; decide +kernel
  · intro person
    rw [stock]
    cases person <;> decide +kernel
  · rw [stock]; decide +kernel
  · rw [stock]; decide +kernel

private theorem clockBound :
    actualNetwork.paid.next.programme.law.duration actualNetwork.paid.next.physical.raw ≤
      job.live.current.programme.law.duration job.live.current.physical.raw := by
  have old : actualNetwork.paid.next.programme.law.duration actualNetwork.paid.next.physical.raw = 1 := by
    rw [actualNetwork.paid.sameProgramme.trans actualTrial.revisedProgramme, payment_lands_at_the_actual_stock]
    decide +kernel
  have now : 1 ≤ job.live.current.programme.law.duration job.live.current.physical.raw := by
    rw [paidLaw, paidStock]
    decide +kernel
  exact old.le.trans now

private theorem reachedByWrite : ∃ replacement,
    Runtime.chooseReplacement job.live (catalogue job.live.current.programme job.live.current.physical.raw)
      home namedReplies = .inr replacement ∧
    reached = ⟨job.live.current.physical.raw, replacement.next⟩ := by
  obtain ⟨i, checked⟩ := viable
  obtain ⟨replacement, selected⟩ := Runtime.chooseReplacement_uses_an_available_registered_recipe job.live
    (catalogue job.live.current.programme job.live.current.physical.raw) home namedReplies clockBound i checked
  refine ⟨replacement, selected, ?_⟩
  exact Runtime.RebaseHistory.refresh_uses_the_generated_replacement home namedReplies initial catalogue selected

/-- At an actual replacement of the reserve, the old review can finish
on the new resident and cannot be written twice once covered. -/
theorem the_original_charged_scope_survives_a_real_reserve_change :
    ∃ (check : Decidable ((path.carry job.pending).read ⊆ reached.2.base.language.covered)),
      let done := job.completeAfterRebases catalogue mixedPolicy 1 check
      reached.1 ≠ initial.1 ∧ done.write.isSome = true ∧
      done.next.current.physical = reached.2.current.physical ∧
      HEq done.next.current.ledger.stack initial.2.current.ledger.stack ∧
      (done.reads.carry (path.carry job.pending)).read = {termsEffect} ∧
      ∃ covered, (job.completeAlong done.next (path.trans done.reads) (.isTrue covered)).write = none := by
  obtain ⟨replacement, _, actual⟩ := reachedByWrite
  have literal : (path.carry job.pending).read = {termsEffect} :=
    ((path.keeps job.pending).trans job.exactScope).trans first_scope
  have fresh : termsEffect ∉ reached.2.base.language.covered := by
    rw [actual, replacement.language, job.language, actualNetwork.network.initialLanguage]
    exact Set.notMem_empty _
  have novel : ¬ (path.carry job.pending).read ⊆ reached.2.base.language.covered := by
    rw [literal, Set.singleton_subset_iff]
    exact fresh
  let done := job.completeAfterRebases catalogue mixedPolicy 1 (.isFalse novel)
  have known := job.the_mixed_schedule_retains_the_original_paid_scope catalogue mixedPolicy 1 (.isFalse novel)
  have entire := (Runtime.RebaseHistory.whole_stack_and_language home namedReplies catalogue initial mixedPolicy 1).1
  refine ⟨.isFalse novel, ?_, rfl, done.samePhysical, done.sameStack.trans entire, known.1.trans first_scope, ?_⟩
  · intro same
    have measured := (congrArg (fun raw : Original.Raw => raw.stock true false) same)
    rw [actual] at measured
    change job.live.current.physical.raw.stock true false = actualNetwork.paid.next.physical.raw.stock true false at measured
    rw [paidStock, payment_lands_at_the_actual_stock] at measured
    exact (by decide +kernel : afterReview.stock true false ≠ afterClear.stock true false) measured
  · have covered : ((path.trans done.reads).carry job.pending).read ⊆ done.next.base.language.covered := by
      change (done.reads.carry (path.carry job.pending)).read ⊆ _
      rw [known.1]
      exact known.2
    exact ⟨covered, (job.covered_paid_scope_does_not_write_twice done.next (path.trans done.reads) covered).1⟩

end

end SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.Clearance.Joint.Reinterpreted.OriginalConsumer
