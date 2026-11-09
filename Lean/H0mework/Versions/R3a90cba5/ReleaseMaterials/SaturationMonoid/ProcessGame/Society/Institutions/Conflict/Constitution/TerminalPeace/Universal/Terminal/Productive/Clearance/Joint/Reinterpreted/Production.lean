import H0mework.Versions.R3a90cba5.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.Productive.Clearance.Joint.Reinterpreted.Current
import H0mework.Versions.R3a90cba5.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Supply.Native
import H0mework.Versions.R3a90cba5.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.FixedPoint.Revision

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.Clearance.Joint.Reinterpreted

open Capitalism.Universal.Source.Program
open Capitalism.Universal.Root
open Capitalism.Universal.Abolition.Root.Registered
open Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening
open Capitalism.Universal.Abolition.Material (inspectList)
open Quantities.Execution (endAt)
open Reparation.Actual (PostedMaterial Script)
open FixedPoint (KeepsPublicTerms Recipe RevisionAnswers RevisionApproval reviseProgramme)
open FixedPoint.OpenPeace.Operational (RepeatCode RecipeIssue checkRecipe)
open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot RootInquiryCompletion
open private Current.mk from H0mework.Versions.R3a90cba5.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.Productive.Clearance.Joint.Reinterpreted.Current

noncomputable section

variable {Party Good Port Technology Instrument Community : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  [DecidableEq Community]
  {seed : Conflict.Root.Cut Party Good Port Technology Instrument} {community : Party → Community}
  {loss : Reparation.Actual.Occurrence seed community} {front : Script Party Good Port Technology Instrument}

local notation "Prog" => ProgrammeSource.Input Party Good Port Technology Instrument
local notation "Word" => RawEvent Party Good Port Technology Instrument
local notation "Raw" => RawCurrent Party Good Technology Instrument

variable (before : Current loss front) (programme : ProgrammeSource.Input Party Good Port Technology Instrument)

structure PeriodWrite where
  visit : Installation.Core.Landed seed community (endAt seed (anchor loss front))
    (PostedMaterial Party Good Port Technology Instrument)
  next : Current loss front
  programmeAt : visit.read.programme = programme
  programmeNext : next.programme = programme
  materialNext : next.physical = visit.read.effect.next
  ledgerNext : next.ledger = visit.state
  ownClock : next.ordinal = before.ordinal + 1
  word : Word
  exactCommand : visit.read.command = .execute word
  beforeAt : visit.read.before = before.physical
  accepted : visit.read.effect.isAccepted = true
  exactStock : next.physical.raw = programme.law.next before.physical.raw word
  exactItems : visit.read.effect.execution.items = programme.law.rawItems before.physical.raw word
  rows : next.ledger.stack.balances = before.ledger.stack.balances
  noDamage : ∀ item ∈ visit.read.effect.execution.items, ∀ key, Reparation.loss programme.law community item key = 0
  life : Supply.Period programme (originalRaw loss) before.physical.raw (people loss front) word
  exits : ∀ person ∈ people loss front, ∃ exitWord,
    Supply.Registered programme before.physical.raw exitWord ∧
      Supply.Period programme (originalRaw loss) before.physical.raw [person] exitWord
  canonical : (⟨before.ledger.world,
    (Installation.Core.action before.ledger visit.read true).target.targetAnswerAndNext.nextCurrent⟩ :
      AnyAuthoritativeRootCurrent) = next.ledger.resident.erase

/-- An accepted replacement actually spends its trial on the original
ledger. This phase does not use revision votes as debt receipts. -/
def writePeriod (keeps : KeepsPublicTerms before.programme programme)
    (move : Runtime.Viability.Move programme (originalRaw loss) (people loss front) before.physical.raw) :
    PeriodWrite before programme := by
  let read : PostedMaterial Party Good Port Technology Instrument :=
    ⟨before.ordinal, programme, before.physical, .execute move.word, fun _ => false⟩
  let visit := Installation.Core.publish before.ledger read true
  have exactRead : visit.read = read := Installation.Core.publish_reads_the_exact_payload _ _ _
  let effect := move.paid.native_write before.physical
  let next : Current loss front :=
    Current.mk visit.state read.effect.next programme (before.ordinal + 1)
      (before.afterAnchor.trans (Nat.le_succ _)) (before.terms.trans keeps) before.origins before.inherited
  refine ⟨visit, next, ?_, rfl, ?_, rfl, rfl, move.word, ?_, ?_, ?_, ?_, ?_, rfl, ?_,
    move.paid, move.personal, ?_⟩
  · rw [exactRead]
  · rw [exactRead]
  · rw [exactRead]
  · rw [exactRead]
  · rw [exactRead]
    exact effect.1
  · exact congrArg (fun native : Runtime.Native Party Good Port Technology Instrument => native.raw) effect.2.2
  · rw [exactRead]
    exact congrArg ExecutionResult.items effect.2.1
  · intro item listed key
    rw [exactRead] at listed
    exact (move.paid.each_native_item_has_exact_original_ownership before.physical item listed).opens_no_coercive_loss
      community key
  · rw [exactRead]
    exact Installation.Core.the_canonical_write_is_the_published_whole_state _ _ _

variable [DecidableEq (Request Party Good Port Technology Instrument)]
  (approvals : RevisionAnswers Party Good Port Technology Instrument)
  (offer : ProductionOffer Party Good Port Technology Instrument)
  (code : RepeatCode (reviseProgramme before.programme offer) before.physical.raw)

inductive TrialIssue
  | denied (person : Party) (present : person ∈ people loss front)
      (refused : approvals before.ledger.resident.erase before.physical.raw offer person = false)
  | differentPilot (different : code.production ≠ offer.pilot)
  | unpaid (issue : RecipeIssue (reviseProgramme before.programme offer)
      (originalRaw loss) before.physical.raw (people loss front) code)

structure TrialWrite where
  period : PeriodWrite before (reviseProgramme before.programme offer)
  approved : RevisionApproval approvals before.ledger.resident.erase before.physical.raw (people loss front) offer
  pilot : period.word = offer.pilot

structure PreparedTrial where
  approved : RevisionApproval approvals before.ledger.resident.erase before.physical.raw (people loss front) offer
  recipe : FixedPoint.Recipe (reviseProgramme before.programme offer) (originalRaw loss) (people loss front)
    before.physical.raw ((reviseProgramme before.programme offer).law.duration before.physical.raw)
  pilot : recipe.move.word = offer.pilot

def inspectTrial : Except (TrialIssue before approvals offer code) (PreparedTrial before approvals offer) :=
  match inspectList (fun person =>
    approvals before.ledger.resident.erase before.physical.raw offer person = true) (people loss front) with
  | .failure person present refused => .error (.denied person present (Bool.eq_false_of_not_eq_true refused))
  | .clear approved =>
    if samePilot : code.production = offer.pilot then
      match checkRecipe (reviseProgramme before.programme offer) (originalRaw loss) before.physical.raw
          (people loss front) code with
      | .inl issue => .error (.unpaid issue)
      | .inr recipe =>
        .ok ⟨approved, recipe.val, recipe.property.trans samePilot⟩
    else .error (.differentPilot samePilot)


def tryRevision : Except (TrialIssue before approvals offer code)
    (TrialWrite before approvals offer) :=
  match inspectTrial before approvals offer code with
  | .error issue => .error issue
  | .ok ready =>
    .ok ⟨writePeriod before (reviseProgramme before.programme offer)
      (FixedPoint.reviseProgramme_keeps_public_terms _ _) ready.recipe.move,
      ready.approved, ready.pilot⟩

end

end SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.Clearance.Joint.Reinterpreted
