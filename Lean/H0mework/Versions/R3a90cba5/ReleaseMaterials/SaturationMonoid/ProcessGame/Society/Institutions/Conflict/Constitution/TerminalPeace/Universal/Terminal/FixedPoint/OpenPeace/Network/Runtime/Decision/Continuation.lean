import H0mework.Versions.R3a90cba5.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.FixedPoint.OpenPeace.Boundary

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.FixedPoint.OpenPeace.Network.Runtime.Decision

open Capitalism.Universal.Source.Program
open Capitalism.Universal.Root
open Capitalism.Universal.Abolition.Material (inspectList)
open Capitalism.Universal.Abolition.Material.Migration (sourceAlphabet)
open private continuationAt from H0mework.Versions.R3a90cba5.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.FixedPoint.OpenPeace.Boundary

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Instrument]

variable (origin before : RawCurrent Party Good Technology Instrument)
  (programme : ProgrammeSource.Input Party Good Port Technology Instrument)
  (claim : Claim Party Good Port Technology Instrument)

/-- A failed continuation names either an unregistered instruction in
the original word or its first source execution issue. -/
inductive ContinuationIssue : Type
  | unregistered (request : Request Party Good Port Technology Instrument)
      (original : request ∈ claim.2) (absent : request ∉ sourceAlphabet programme before)
  | execution (issue : Supply.Issue programme origin before claim.1 claim.2)

theorem ContinuationIssue.refutes (issue : ContinuationIssue origin before programme claim) :
    ¬ continuationAt origin before programme claim := by
  intro retained
  cases issue with
  | unregistered request original absent =>
    exact absent (retained.1 request original)
  | execution issue => exact issue.refutes _ _ _ _ _ retained.2

variable [DecidableEq (Request Party Good Port Technology Instrument)]

/-- Execute any submitted finite word at the paid before-state. The
membership check reads the literal registered alphabet at that state. -/
def inspectContinuation :
    ContinuationIssue origin before programme claim ⊕ PLift (continuationAt origin before programme claim) :=
  match inspectList (fun request => request ∈ sourceAlphabet programme before) claim.2 with
  | .failure request original absent => .inl (.unregistered request original absent)
  | .clear registered =>
    match Supply.inspect programme origin before claim.1 claim.2 with
    | .inl issue => .inl (.execution issue)
    | .inr paid => .inr ⟨⟨registered, paid.down⟩⟩

def continuationDecision : Decidable (continuationAt origin before programme claim) :=
  match inspectContinuation origin before programme claim with
  | .inl issue => .isFalse (issue.refutes _ _ _ _)
  | .inr paid => .isTrue paid.down

variable (candidate : ProgrammeSource.Input Party Good Port Technology Instrument)

def lossDecision :
    Decidable (continuationAt origin before programme claim ∧
      ¬ continuationAt origin before candidate claim) :=
  match continuationDecision origin before programme claim, continuationDecision origin before candidate claim with
  | .isFalse failed, _ => .isFalse (fun lost => failed lost.1)
  | _, .isTrue kept => .isFalse (fun lost => lost.2 kept)
  | .isTrue prior, .isFalse lost => .isTrue ⟨prior, lost⟩

end SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.FixedPoint.OpenPeace.Network.Runtime.Decision
