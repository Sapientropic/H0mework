import H0mework.Versions.R3a90cba5.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.FixedPoint.NoFreeProbe.Compiler
import H0mework.Versions.R3a90cba5.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.FixedPoint.NoFreeProbe.Prepayment.Invariants
import H0mework.Versions.R3a90cba5.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.FixedPoint.NoFreeProbe.Prepayment.Privacy
import H0mework.Versions.R3a90cba5.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.FixedPoint.NoFreeProbe.Prepayment.Registered

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.FixedPoint.NoFreeProbe.Prepayment

open Capitalism.Universal.Source.Program
open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot RootInquiryCompletion
open Reparation.Actual (ReceiptAnswers Script)
open Clearance

noncomputable section

variable {Party Good Port Technology Instrument Community : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Instrument] [DecidableEq Community]
  {seed : Conflict.Root.Cut Party Good Port Technology Instrument} {community : Party → Community}
  (loss : Reparation.Actual.Occurrence seed community) (answers : ReceiptAnswers seed)
  (reserve : Party → Good → ℚ) (body : RawEvent Party Good Port Technology Instrument)
  (offers : ProductionMenu Party Good Port Technology Instrument)
  (replies : Replies Party Good Port Technology Instrument)
  (tariff : Tariff Party Good Port Technology Instrument)
  (orders : PaymentOrders Party Good Port Technology Instrument)

structure PrepaidOpening (orders : PaymentOrders Party Good Port Technology Instrument) where
  private mk ::
  source : ProtectedOpening loss answers reserve body offers replies tariff

namespace PrepaidOpening

variable {loss answers reserve body offers replies tariff orders}
  (opening : PrepaidOpening loss answers reserve body offers replies tariff orders)

/-- Install the independent payment input at the existing tariff-bearing
entrance. The one registration anchor remains fixed after private answers. -/
def installation :=
  Installation.Live.publish opening.source.current.ledger orders true

def current :=
  { opening.source.current with ledger := opening.installation.state }

def home : AnyAuthoritativeRootCurrent :=
  opening.current.ledger.resident.erase

theorem canonical_installation :
    let before := opening.source.current
    let actual := Installation.Live.action before.ledger orders true
    (⟨before.ledger.world, actual.target.targetAnswerAndNext.nextCurrent⟩ : AnyAuthoritativeRootCurrent) =
      opening.home :=
  Installation.Live.the_canonical_write_is_the_published_whole_state _ _ _

theorem installation_keeps_the_original_stack :
    opening.current.ledger.stack = opening.source.source.entry.current.ledger.stack :=
  rfl

def run (policy : AdaptivePolicy
    (RawLaw Party Good Port Technology Instrument × RawEvent Party Good Port Technology Instrument)
    Party Good Port Technology Instrument) :=
  registeredHistory opening.source.installation.read opening.home opening.installation.read replies opening.current policy

theorem run_reads_the_same_original_scheduler (policy : AdaptivePolicy
    (RawLaw Party Good Port Technology Instrument × RawEvent Party Good Port Technology Instrument)
    Party Good Port Technology Instrument) :
    opening.run policy = history opening.source.installation.read (fun current => registeredTerms current)
      opening.home opening.installation.read replies opening.current policy :=
  registered_run_is_the_exact_private_history _ _ _ _ _ _

theorem run_keeps_the_original_stack (policy : AdaptivePolicy
    (RawLaw Party Good Port Technology Instrument × RawEvent Party Good Port Technology Instrument)
    Party Good Port Technology Instrument) (n : Nat) :
    HEq (opening.run policy n).1.ledger.stack opening.source.source.entry.current.ledger.stack := by
  rw [opening.run_reads_the_same_original_scheduler]
  exact (history_keeps_the_entire_stack opening.source.installation.read (fun current => registeredTerms current)
    opening.home opening.installation.read replies opening.current policy n).trans
    (heq_of_eq opening.installation_keeps_the_original_stack)

end PrepaidOpening

inductive PrepaidOutcome
  | jointFailure (diagnostic : Joint.JointOutcome loss answers reserve body offers)
  | noProductiveOpening (joint : Joint.PaidFrontier loss answers reserve (Joint.firstProduction loss body) offers)
      (excluded : ∀ word : Script Party Good Port Technology Instrument,
        ¬ Nonempty (OpeningAt loss answers reserve body offers word))
  | installed (original : Joint.ProductionWrite answers loss (Joint.openingDrain loss) body)
      (actualProduction : Joint.ProducesAtFirstWrite loss body)
      (opening : PrepaidOpening loss answers reserve body offers replies tariff orders)

def compilePrepaidPeace : PrepaidOutcome loss answers reserve body offers replies tariff orders :=
  match compileProtectedPeace loss answers reserve body offers replies tariff with
  | .jointFailure failure => .jointFailure failure
  | .noProductiveOpening frontier excluded => .noProductiveOpening frontier excluded
  | .installed original production prior => .installed original production ⟨prior⟩

theorem installs_on_the_same_jointly_cleared_entrance
    {original : Joint.ProductionWrite answers loss (Joint.openingDrain loss) body}
    {production : Joint.ProducesAtFirstWrite loss body}
    {prior : ProtectedOpening loss answers reserve body offers replies tariff}
    (actual : compileProtectedPeace loss answers reserve body offers replies tariff = .installed original production prior) :
    ∃ opening, compilePrepaidPeace loss answers reserve body offers replies tariff orders =
      .installed original production opening ∧ opening.source = prior := by
  exact ⟨⟨prior⟩, by simp only [compilePrepaidPeace, actual], rfl⟩

end

end SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.FixedPoint.NoFreeProbe.Prepayment
