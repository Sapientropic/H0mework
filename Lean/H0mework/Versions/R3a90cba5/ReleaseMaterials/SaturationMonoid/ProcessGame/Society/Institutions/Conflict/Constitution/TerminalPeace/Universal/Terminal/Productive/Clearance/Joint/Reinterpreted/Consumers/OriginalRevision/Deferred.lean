import H0mework.Versions.R3a90cba5.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.Productive.Clearance.Joint.Reinterpreted.Consumers.OriginalRevision
import H0mework.Versions.R3a90cba5.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.FixedPoint.OpenPeace.Network.Runtime.Decision.Deferred.Finish
import H0mework.Versions.R3a90cba5.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.FixedPoint.OpenPeace.Network.Runtime.Decision.Deferred.Native

set_option autoImplicit false
set_option maxRecDepth 8192

namespace SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.Clearance.Joint.Reinterpreted.OriginalConsumer

open Capitalism.Universal.Source.Program
open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot RootInquiryCompletion
open FixedPoint.OpenPeace
open FixedPoint.OpenPeace.Network
open FixedPoint.OpenPeace.Network.Runtime (ReadAt)
open FixedPoint.OpenPeace.Network.Runtime.Decision
open private start home packet submit visit scope paid_wire initial_reads initial_ready first_scope first_novel termsEffect
  from H0mework.Versions.R3a90cba5.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.Productive.Clearance.Joint.Reinterpreted.Consumers.OriginalRevision
open private Reader.mk from H0mework.Versions.R3a90cba5.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.FixedPoint.OpenPeace.Network.Runtime.Decision.Run
open private defer from H0mework.Versions.R3a90cba5.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.FixedPoint.OpenPeace.Network.Runtime.Decision.Deferred.Start

noncomputable section

private def reader : Reader start :=
  Reader.mk (fun point => match point with
    | .inl word => some (.isFalse (fun impossible =>
        (Set.notMem_empty (Sum.inl word : Effect Bool Bool Bool Unit Unit)) (by
          rw [← actualNetwork.network.initialLanguage]
          exact impossible)))
    | .inr _ => none) (fun _ => rfl)

private theorem charged : (visit start 0).source.paidWire = some (packet 0).wire :=
  paid_wire initial_reads initial_ready

private abbrev answer : Result home namedReplies start (submit 0) := .needsEvidence (packet 0).wire charged

private def job : Deferred home namedReplies start (submit 0) := defer (packet 0).wire charged

private def due (_ : Nat) : FixedPoint.NoFreeProbe.Due Bool Bool Bool Unit Unit := ⟨none, []⟩

private abbrev schedule := nativeSchedule due
private abbrev reached (n : Nat) := (job.run schedule n).1

private theorem observed (n : Nat) : termsEffect ∈ (job.readAt schedule n).read := by
  rw [job.readAt_is_the_original_paid_scope]
  change termsEffect ∈ scope start 0
  rw [first_scope]
  exact Set.mem_singleton _

private theorem fresh (n : Nat) : termsEffect ∉ (reached n).base.language.covered := by
  have same := native_language home namedReplies job.live due n
  change termsEffect ∉ (Runtime.history home namedReplies job.live schedule n).1.base.language.covered
  rw [same, job.language, actualNetwork.network.initialLanguage]
  exact Set.notMem_empty _

private def finish (n : Nat) := job.completeAtWitness schedule n termsEffect (observed n) (fresh n)

/-- The original paid term gap really enters the pending path. Every
waiting period still has an executable ordinary decision on that same history. -/
theorem the_original_pending_u8_pays_during_every_waiting_round (n : Nat) :
    Runtime.Decision.advance home namedReplies start (submit 0) reader (Advice.raw start (submit 0)) [] = answer ∧
      answer.beginDeferred = some job ∧
      Runtime.LivingVisitAt home namedReplies job.live schedule n ∧
      (∃ r step same next,
        Runtime.Decision.advance home namedReplies (reached n) (.native (due n)) r (Advice.raw (reached n) (.native (due n))) [] =
          .committed step same next ∧ step.write = none) ∧
      ∀ first : Nat, ∀ bound : ℚ, ∃ k ≥ first, bound < (reached k).current.physical.raw.clock := by
  refine ⟨?_, rfl, job.every_waiting_round_pays schedule n,
    native_wait_is_checked home namedReplies job.live due (job.reader reader) n,
    job.waiting_clock_is_cofinal schedule⟩
  apply advance_retains_an_unreadable_paid_scope _ _ _ _ _ _ _ _ charged first_novel
  intro point member
  change point ∈ scope start 0 at member
  rw [first_scope, Set.mem_singleton_iff] at member
  subst point
  rfl

/-- The later evidence consumes the original paid scope on the reached
resident, with no material debit. Its first whole write supplies the next
actual paid round, with the original paid rows still in place. -/
theorem the_original_late_u8_is_the_next_material_input (n : Nat) :
    let done := finish n
    done.write.isSome = true ∧ done.next.current.physical = (reached n).current.physical ∧
      (done.reads.carry (job.readAt schedule n)).read = {termsEffect} ∧
      done.next.current.ledger.stack.balances = actualNetwork.paid.next.ledger.stack.balances ∧
      termsEffect ∈ done.next.base.language.covered ∧
      (let round := (Runtime.source home namedReplies done.next (.native (due n))).source.round
       let ledger := done.next.current.ledger
       (⟨ledger.world, (Installation.Live.action ledger round.visit.read true).target.targetAnswerAndNext.nextCurrent⟩ :
         AnyAuthoritativeRootCurrent) = round.next.ledger.resident.erase) := by
  intro done
  have exact := job.completion_reads_the_original_request schedule n
    (.isFalse fun covered => fresh n (covered (observed n)))
  have rows := Runtime.history_keeps_rows home namedReplies job.live schedule n
  have kept : done.next.current.ledger.stack.balances = (reached n).current.ledger.stack.balances := rfl
  have postedRows := (visit start 0).source.rows
  have landing : job.live.current.ledger.stack.balances = (visit start 0).source.next.ledger.stack.balances := by
    change (visit start 0).next.native.ledger.stack.balances = _
    generalize visit start 0 = posted
    cases posted <;> rfl
  refine ⟨rfl, done.samePhysical, exact.1.trans first_scope, ?_, ?_, ?_⟩
  · exact kept.trans (rows.trans (landing.trans (postedRows.trans actualNetwork.network.rows)))
  · apply exact.2
    change termsEffect ∈ scope start 0
    rw [first_scope]
    exact Set.mem_singleton _
  · exact (Runtime.source home namedReplies done.next (.native (due n))).source.round.wholeNext

end

end SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.Clearance.Joint.Reinterpreted.OriginalConsumer
