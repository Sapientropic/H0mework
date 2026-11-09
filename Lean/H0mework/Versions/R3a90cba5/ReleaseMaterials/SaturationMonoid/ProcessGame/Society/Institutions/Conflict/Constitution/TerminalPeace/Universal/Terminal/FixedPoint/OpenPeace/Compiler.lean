import H0mework.Versions.R3a90cba5.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.FixedPoint.OpenPeace.History
import H0mework.Versions.R3a90cba5.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.FixedPoint.AdaptivePeace.Compiler

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.FixedPoint.OpenPeace

open Capitalism.Universal.Source.Program
open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot RootInquiryCompletion
open NoFreeProbe
open NoFreeProbe.Prepayment (PaymentOrders)
open Reparation.Actual (ReceiptAnswers Script)
open Clearance
open private State.start from H0mework.Versions.R3a90cba5.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.FixedPoint.OpenPeace.Dispatch
open private AdaptivePeace.State.mk from H0mework.Versions.R3a90cba5.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.FixedPoint.AdaptivePeace.Dispatch

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
  (openOrders : OpenOrders Party Good Port Technology Instrument)

structure Opening (openOrders : OpenOrders Party Good Port Technology Instrument) where
  private mk ::
  source : AdaptivePeace.AdaptiveOpening loss answers reserve body offers replies tariff orders

namespace Opening

variable {loss answers reserve body offers replies tariff orders openOrders}
  (opening : Opening loss answers reserve body offers replies tariff orders openOrders)

def installation :=
  Installation.Live.publish opening.source.initial.native.ledger openOrders true

def initial :=
  let prior := opening.source.initial
  State.start (AdaptivePeace.State.mk { prior.native with ledger := opening.installation.state } prior.amendment)

def home : AnyAuthoritativeRootCurrent :=
  opening.source.source.home

theorem installation_is_the_canonical_original_write :
    let prior := opening.source.initial.native.ledger
    let action := Installation.Live.action prior openOrders true
    (⟨prior.world, action.target.targetAnswerAndNext.nextCurrent⟩ : AnyAuthoritativeRootCurrent) =
      opening.initial.adaptive.native.ledger.resident.erase :=
  Installation.Live.the_canonical_write_is_the_published_whole_state _ _ _

theorem no_future_expressions_are_installed : opening.initial.language.covered = ∅ :=
  Language.covered_initial

end Opening

inductive Outcome
  | jointFailure (diagnostic : Joint.JointOutcome loss answers reserve body offers)
  | noProductiveOpening (joint : Joint.PaidFrontier loss answers reserve (Joint.firstProduction loss body) offers)
      (excluded : ∀ word : Script Party Good Port Technology Instrument,
        ¬ Nonempty (OpeningAt loss answers reserve body offers word))
  | installed (original : Joint.ProductionWrite answers loss (Joint.openingDrain loss) body)
      (actualProduction : Joint.ProducesAtFirstWrite loss body)
      (opening : Opening loss answers reserve body offers replies tariff orders openOrders)

/-- The original joint compiler pays the original addresses. The new
signed ingress is a dependent face of that same productive entrance. -/
def compileOpenPeace : Outcome loss answers reserve body offers replies tariff orders openOrders :=
  match AdaptivePeace.compileAdaptivePeace loss answers reserve body offers replies tariff orders with
  | .jointFailure failure => .jointFailure failure
  | .noProductiveOpening frontier excluded => .noProductiveOpening frontier excluded
  | .installed original production prior => .installed original production ⟨prior⟩

theorem installs_at_the_same_original_entrance
    {original : Joint.ProductionWrite answers loss (Joint.openingDrain loss) body}
    {production : Joint.ProducesAtFirstWrite loss body}
    {prior : AdaptivePeace.AdaptiveOpening loss answers reserve body offers replies tariff orders}
    (actual : AdaptivePeace.compileAdaptivePeace loss answers reserve body offers replies tariff orders =
      .installed original production prior) :
    ∃ opening, compileOpenPeace loss answers reserve body offers replies tariff orders openOrders =
      .installed original production opening ∧ opening.source = prior := by
  exact ⟨⟨prior⟩, by simp only [compileOpenPeace, actual], rfl⟩

end

end SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.FixedPoint.OpenPeace
