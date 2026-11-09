import H0mework.Versions.R71cb159f.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.Productive.Clearance.Joint.Reinterpreted.Dispatch
import H0mework.Versions.R71cb159f.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.Productive.Clearance.Joint.Reinterpreted.Consumers.OriginalSource

set_option autoImplicit false
set_option maxRecDepth 8192

namespace SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.Clearance.Joint.Reinterpreted.OriginalConsumer

open Capitalism.Universal.Source.Program
open Capitalism.Universal.Abolition.Material.Continuation
open Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening
open Conflict.Consumers.Evolving (compact)
open FixedPoint.OpenPeace.Operational (RecipeIssue)
open Supply.Consumers (refillWord)

noncomputable section

def afterTrial : Original.Raw :=
  { Original.snapshot 115 117 with
    stock := fun person good => if good then 2 else if person then 117 else 115
    clock := 5
    round := 5 }

structure Trial where
  before : Current loss front
  entered : enter loss nativeAnswers front = .ok before
  source : before.programme = compact
  originalStock : before.physical.raw = Original.snapshot 111 113
  originalDebt : before.ledger.stack.balances = [(loss, Original.balance)]
  actual : TrialWrite before (reviseReplies true) offer
  selected : revise before (reviseReplies true) offer (repeatAt before source) = .inr actual
  revisedProgramme : actual.period.next.programme = revised
  revisedStock : actual.period.next.physical.raw = afterTrial

set_option maxHeartbeats 750000 in
theorem the_new_interpreter_posts_before_clearing : Nonempty Trial := by
  obtain ⟨before, entered, source, raw, debt⟩ := the_unsettled_original_cut_is_generated
  have checks := the_new_trial_checks before source raw
  cases result : tryRevision before (reviseReplies true) offer (repeatAt before source) with
  | error issue =>
    exfalso
    cases issue with
    | denied person _ denied =>
      have yes : reviseReplies true before.ledger.resident.erase before.physical.raw offer person = true := by
        cases person <;> rfl
      exact Bool.false_ne_true (denied.symm.trans yes)
    | differentPilot missing => exact missing rfl
    | unpaid missing => exact (missing.refutes _ _ _ _ _ checks)
  | ok actual =>
    refine ⟨⟨before, entered, source, raw, debt, actual, by simp only [revise, result],
      actual.period.programmeNext.trans (congrArg (fun input => FixedPoint.reviseProgramme input offer) source), ?_⟩⟩
    rw [actual.period.exactStock, actual.pilot, raw, source]
    change revised.law.next (Original.snapshot 111 113) refillWord = afterTrial
    apply RawCurrent.ext
    · funext person good
      cases person <;> cases good <;> decide +kernel
    · funext instrument debtor creditor
      cases instrument
      cases debtor <;> cases creditor <;> decide +kernel
    · exact Subsingleton.elim _ _
    · decide +kernel
    · decide +kernel

def actualTrial : Trial := Classical.choice the_new_interpreter_posts_before_clearing

theorem the_unrevised_interpreter_cannot_replay_this_material_successor :
    compact.law.next actualTrial.before.physical.raw refillWord ≠ actualTrial.actual.period.next.physical.raw := by
  rw [actualTrial.originalStock, actualTrial.revisedStock]
  intro same
  have observed := congrArg (fun raw : Original.Raw => raw.stock true true) same
  exact (by decide +kernel : ¬ (compact.law.next (Original.snapshot 111 113) refillWord).stock true true =
    afterTrial.stock true true) observed

end

end SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.Clearance.Joint.Reinterpreted.OriginalConsumer
