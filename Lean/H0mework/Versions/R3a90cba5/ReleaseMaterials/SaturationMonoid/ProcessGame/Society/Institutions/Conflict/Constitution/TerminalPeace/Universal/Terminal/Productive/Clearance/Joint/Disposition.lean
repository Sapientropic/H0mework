import H0mework.Versions.R3a90cba5.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.Productive.Clearance.Joint.Compiler

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.Clearance.Joint

open Capitalism.Universal.Source.Program
open Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Execution (endAt)
open Reparation (Key)
open Reparation.Actual (ReceiptAnswers Script)
open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot RootInquiryCompletion

noncomputable section

variable {Party Good Port Technology Instrument Community : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Instrument] [DecidableEq Community]
  {seed : Conflict.Root.Cut Party Good Port Technology Instrument} {community : Party → Community}
  (loss : Reparation.Actual.Occurrence seed community) (answers : ReceiptAnswers seed)
  (reserve : Party → Good → ℚ) (front : Script Party Good Port Technology Instrument)
  (purpose : Port) (key : Key Party Good) (quantity : ℚ)

local notation "Here" => (endAt seed (Occurrence.history loss ++ front))
local notation "Issue" => InstallmentIssue loss answers reserve front purpose key quantity

/-- A local failure writes the named refusal on the current ledger.
There is no transfer or debit on this branch. -/
def publishInstallmentIssue (issue : Issue) :=
  Installation.Core.publish (Occurrence.reached answers loss front) issue true

theorem a_refusal_preserves_the_original_rows_and_generates_next (issue : Issue) :
    let original := Occurrence.reached answers loss front
    let written := publishInstallmentIssue loss answers reserve front purpose key quantity issue
    written.read = issue ∧
      written.state.stack.balances = original.stack.balances ∧
      (⟨original.world, (Installation.Core.action original issue true).target.targetAnswerAndNext.nextCurrent⟩ :
        AnyAuthoritativeRootCurrent) = written.state.resident.erase :=
  ⟨rfl, rfl, Installation.Core.the_canonical_write_is_the_published_whole_state _ _ _⟩

inductive InstallmentOutcome
  | written (paid : PaidInstallment loss answers reserve front purpose key quantity)
  | refused (issue : Issue) (visit : Installation.Core.Landed seed community Here Issue)
      (same : visit = publishInstallmentIssue loss answers reserve front purpose key quantity issue)

def compileInstallment (safe : Occurrence.Eligible answers loss front) (ready : ReadyEntry loss front)
    (nonnegative : 0 ≤ reserve key.2.1 key.2.2) :
    InstallmentOutcome loss answers reserve front purpose key quantity :=
  match inspectInstallment loss answers reserve front purpose key quantity ready nonnegative with
  | .inl issue =>
    .refused issue (publishInstallmentIssue loss answers reserve front purpose key quantity issue) rfl
  | .inr paid =>
    .written (writeInstallment loss answers reserve front purpose key quantity safe ready nonnegative paid.down)

end

end SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.Clearance.Joint
