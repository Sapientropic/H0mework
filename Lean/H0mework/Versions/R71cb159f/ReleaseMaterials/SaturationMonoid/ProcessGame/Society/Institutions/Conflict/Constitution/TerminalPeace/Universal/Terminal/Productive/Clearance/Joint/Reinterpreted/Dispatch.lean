import H0mework.Versions.R71cb159f.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.Productive.Clearance.Joint.Reinterpreted.Production
import H0mework.Versions.R3a90cba5.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.Productive.Clearance.Joint.Reinterpreted.Payment

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.Clearance.Joint.Reinterpreted

open Capitalism.Universal.Source.Program
open Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening
open Quantities.Execution (endAt)
open Reparation (Key)
open Reparation.Actual (Script)
open FixedPoint (RevisionAnswers reviseProgramme)
open FixedPoint.OpenPeace.Operational (RepeatCode)
open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot RootInquiryCompletion
open private Current.mk from H0mework.Versions.R3a90cba5.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.Productive.Clearance.Joint.Reinterpreted.Current

noncomputable section

variable {Party Good Port Technology Instrument Community : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  [DecidableEq Community]
  {seed : Conflict.Root.Cut Party Good Port Technology Instrument} {community : Party → Community}
  {loss : Reparation.Actual.Occurrence seed community} {front : Script Party Good Port Technology Instrument}

variable (before : Current loss front)

structure Refused (Issue : Type) where
  visit : Installation.Core.Landed seed community (endAt seed (anchor loss front)) Issue
  next : Current loss front
  keepsPhysical : next.physical = before.physical
  keepsProgramme : next.programme = before.programme
  keepsRows : next.ledger.stack.balances = before.ledger.stack.balances
  exactOrdinal : next.ordinal = before.ordinal + 1
  canonical : (⟨before.ledger.world,
    (Installation.Core.action before.ledger visit.read true).target.targetAnswerAndNext.nextCurrent⟩ :
      AnyAuthoritativeRootCurrent) = next.ledger.resident.erase

def refuse {Issue : Type} (issue : Issue) : Refused before Issue :=
  let visit := Installation.Core.publish before.ledger issue true
  let next := Current.mk visit.state before.physical before.programme (before.ordinal + 1)
    (before.afterAnchor.trans (Nat.le_succ _)) before.terms before.origins before.inherited
  ⟨visit, next, rfl, rfl, rfl, rfl, Installation.Core.the_canonical_write_is_the_published_whole_state _ _ _⟩

section Payment

variable (answers : DeliveryAnswers Party Good Port Technology Instrument)
  (key : Key Party Good) (quantity : ℚ)
  (addresses : List (Party × Good)) (covered : ∀ address, address ∈ addresses)

def pay : Refused before (PaymentIssue before answers key quantity) ⊕ PaidWrite before answers key quantity :=
  match checkFunding before answers key quantity addresses covered with
  | .error issue => .inl (refuse before issue)
  | .ok funding => .inr (writeFunded before answers key quantity funding.down)

theorem pays_exactly_at_a_funded_position :
    (∃ actual, pay before answers key quantity addresses covered = .inr actual) ↔ Funding before answers key quantity := by
  unfold pay
  cases checkFunding before answers key quantity addresses covered with
  | error issue =>
    constructor
    · rintro ⟨_, impossible⟩
      cases impossible
    · exact fun funded => (issue.refutes before answers key quantity funded).elim
  | ok accepted => exact ⟨fun _ => accepted.down, fun _ => ⟨_, rfl⟩⟩

end Payment

variable [DecidableEq (Request Party Good Port Technology Instrument)]
  (approvals : RevisionAnswers Party Good Port Technology Instrument)
  (offer : ProductionOffer Party Good Port Technology Instrument)
  (code : RepeatCode (reviseProgramme before.programme offer) before.physical.raw)

def revise : Refused before (TrialIssue before approvals offer code) ⊕ TrialWrite before approvals offer :=
  match tryRevision before approvals offer code with
  | .error issue => .inl (refuse before issue)
  | .ok actual => .inr actual

end

end SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.Clearance.Joint.Reinterpreted
