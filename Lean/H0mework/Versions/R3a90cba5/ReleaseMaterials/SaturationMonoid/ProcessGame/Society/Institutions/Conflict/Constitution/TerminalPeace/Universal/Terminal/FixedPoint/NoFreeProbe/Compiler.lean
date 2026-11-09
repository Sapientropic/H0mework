import H0mework.Versions.R3a90cba5.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.FixedPoint.Compiler
import H0mework.Versions.R3a90cba5.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.FixedPoint.NoFreeProbe.Influence
import H0mework.Versions.R3a90cba5.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.FixedPoint.NoFreeProbe.Invariants
import H0mework.Versions.R3a90cba5.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.FixedPoint.NoFreeProbe.RepeatedCharges

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.FixedPoint.NoFreeProbe

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

structure ProtectedOpening (tariff : Tariff Party Good Port Technology Instrument) where
  private mk ::
  source : SettledOpening loss answers reserve body offers replies

namespace ProtectedOpening

variable {loss answers reserve body offers replies tariff}
  (opening : ProtectedOpening loss answers reserve body offers replies tariff)

/-- The tariff is installed as a dependent face of the actual cleared
entrance. The due dispatcher reads the installation on this same root. -/
def installation :=
  Installation.Live.publish opening.source.entry.current.ledger tariff true

def current :=
  { opening.source.entry.current with ledger := opening.installation.state }

theorem reads_the_installed_tariff : opening.installation.read = tariff :=
  rfl

theorem canonical_installation :
    let before := opening.source.entry.current
    let actual := Installation.Live.action before.ledger tariff true
    (⟨before.ledger.world, actual.target.targetAnswerAndNext.nextCurrent⟩ : AnyAuthoritativeRootCurrent) =
      opening.current.ledger.resident.erase :=
  Installation.Live.the_canonical_write_is_the_published_whole_state _ _ _

theorem installation_keeps_the_original_stack :
    opening.current.ledger.stack = opening.source.entry.current.ledger.stack :=
  rfl

def run (policy : CoalitionPolicy Party Good Port Technology Instrument) :=
  history opening.installation.read replies opening.current policy

theorem every_cut_retains_the_original_paid_addresses (policy : CoalitionPolicy Party Good Port Technology Instrument)
    (n : Nat) :
    (opening.run policy n).1.ledger.stack.balances.map Prod.fst =
      (Occurrence.originState loss).stack.balances.map Prod.fst ∧
    ∀ row ∈ (opening.run policy n).1.ledger.stack.balances, row.2.remaining = 0 := by
  have rows := (history_keeps_original_accounts opening.installation.read replies opening.current policy n).1
  refine ⟨(congrArg (List.map Prod.fst) rows).trans opening.source.entry.every_old_address_is_retained, ?_⟩
  intro row listed
  exact opening.source.fixed.oldPaid row (rows ▸ listed)

end ProtectedOpening

inductive ProtectedOutcome
  | jointFailure (diagnostic : Joint.JointOutcome loss answers reserve body offers)
  | noProductiveOpening (joint : Joint.PaidFrontier loss answers reserve (Joint.firstProduction loss body) offers)
      (excluded : ∀ word : Script Party Good Port Technology Instrument,
        ¬ Nonempty (OpeningAt loss answers reserve body offers word))
  | installed (original : Joint.ProductionWrite answers loss (Joint.openingDrain loss) body)
      (actualProduction : Joint.ProducesAtFirstWrite loss body)
      (opening : ProtectedOpening loss answers reserve body offers replies tariff)

/-- Extend the existing joint producer at its actual settled cut with
the tariff and the protected due dispatcher. -/
def compileProtectedPeace : ProtectedOutcome loss answers reserve body offers replies tariff :=
  match compilePeace loss answers reserve body offers replies with
  | .jointFailure failure => .jointFailure failure
  | .noProductiveOpening frontier excluded => .noProductiveOpening frontier excluded
  | .installed original production peace => .installed original production ⟨peace.settled loss answers reserve body offers replies⟩

theorem installs_at_the_same_original_entrance
    {original : Joint.ProductionWrite answers loss (Joint.openingDrain loss) body}
    {production : Joint.ProducesAtFirstWrite loss body}
    {peace : FixedOpening loss answers reserve body offers replies}
    (actual : compilePeace loss answers reserve body offers replies = .installed original production peace) :
    ∃ opening, compileProtectedPeace loss answers reserve body offers replies tariff =
      .installed original production opening ∧ opening.source = peace.settled loss answers reserve body offers replies := by
  exact ⟨⟨peace.settled loss answers reserve body offers replies⟩, by simp only [compileProtectedPeace, actual], rfl⟩

end

end SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.FixedPoint.NoFreeProbe
