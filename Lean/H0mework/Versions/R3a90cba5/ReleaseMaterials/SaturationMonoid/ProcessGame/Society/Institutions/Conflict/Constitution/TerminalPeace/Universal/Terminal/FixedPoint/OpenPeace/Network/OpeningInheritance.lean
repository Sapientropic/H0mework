import H0mework.Versions.R3a90cba5.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.FixedPoint.OpenPeace.Network.Settlement
import H0mework.Versions.R3a90cba5.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.FixedPoint.OpenPeace.Compiler

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.FixedPoint.OpenPeace

open Capitalism.Universal.Source.Program
open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot RootInquiryCompletion
open Reparation.Actual (ReceiptAnswers)
open NoFreeProbe
open NoFreeProbe.Prepayment (PaymentOrders)

noncomputable section

variable {Party Good Port Technology Instrument Community : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Instrument] [DecidableEq Community]
  {seed : Conflict.Root.Cut Party Good Port Technology Instrument} {community : Party → Community}
  {loss : Reparation.Actual.Occurrence seed community} {answers : ReceiptAnswers seed}
  {reserve : Party → Good → ℚ} {body : RawEvent Party Good Port Technology Instrument}
  {offers : ProductionMenu Party Good Port Technology Instrument}
  {replies : Replies Party Good Port Technology Instrument} {tariff : Tariff Party Good Port Technology Instrument}
  {orders : PaymentOrders Party Good Port Technology Instrument}
  {openOrders : OpenOrders Party Good Port Technology Instrument}

section Runtime

variable {cut : Conflict.Root.Cut Party Good Port Technology Instrument}
  {origin : RawCurrent Party Good Technology Instrument} {people : List Party} {quantum : ℚ}
  {reserveBase : RawCurrent Party Good Technology Instrument}
  {home : AnyAuthoritativeRootCurrent.{0}}
  {before : AdaptivePeace.State (seed := seed) (cut := cut) (community := community) origin people quantum (reserveBase := reserveBase)}

theorem adaptiveKeepsWorld (step : AdaptivePeace.Step tariff home orders replies before) :
    step.next.native.ledger.world = before.native.ledger.world := by
  have original : step.source.round.next.ledger.world = before.native.ledger.world :=
    (congrArg AnyAuthoritativeRootCurrent.N step.source.round.wholeNext).symm
  refine Eq.trans ?_ original
  cases step with
  | ordinary base _ =>
    cases base with
    | ordinary due _ => cases due <;> rfl
    | prepaid _ _ _ => rfl
  | refused _ _ _ _ _ | amended _ _ _ _ => rfl

theorem next_world_eq (home : AnyAuthoritativeRootCurrent.{0})
    (before : State (seed := seed) (cut := cut) (community := community) origin people quantum (reserveBase := reserveBase))
    (input : Input Party Good Port Technology Instrument) :
    (next tariff home orders openOrders replies before input).adaptive.native.ledger.world =
      before.adaptive.native.ledger.world := by
  classical
  have same := adaptiveKeepsWorld (source tariff home orders openOrders replies before input)
  by_cases covered : scope tariff home orders openOrders replies before input ⊆ before.language.covered
  · simpa only [next, amendment, if_pos covered] using same
  · simp only [next, amendment, if_neg covered, languageWrite]
    exact same

end Runtime

namespace Opening

variable (opening : Opening loss answers reserve body offers replies tariff orders openOrders)

/-- Start the full inherited calculus at the exact installed paid cut.
Each entrance coface preserves the world index of the clearing writer. -/
def inherited : Network.InheritedCalculus opening.initial.adaptive.native.ledger.world :=
  Network.inheritedReached loss answers opening.source.source.source.source.word

end Opening

end

end SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.FixedPoint.OpenPeace
