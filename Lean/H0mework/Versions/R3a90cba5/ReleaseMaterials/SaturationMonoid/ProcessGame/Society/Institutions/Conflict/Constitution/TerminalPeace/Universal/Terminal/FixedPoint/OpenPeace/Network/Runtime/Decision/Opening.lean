import H0mework.Versions.R3a90cba5.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.FixedPoint.OpenPeace.Network.Runtime.Decision.Pending
import H0mework.Versions.R3a90cba5.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.FixedPoint.OpenPeace.Network.Compile

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.FixedPoint.OpenPeace.Opening

open Capitalism.Universal.Source.Program
open Reparation.Actual (ReceiptAnswers)
open NoFreeProbe
open NoFreeProbe.Prepayment (PaymentOrders)
open Network.Runtime.Decision (Reader Advice)

noncomputable section

variable {Party Good Port Technology Instrument Community : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Instrument] [DecidableEq Community]
  {seed : Conflict.Root.Cut Party Good Port Technology Instrument} {community : Party → Community}
  {loss : Reparation.Actual.Occurrence seed community} {answers : ReceiptAnswers seed}
  {reserve : Party → Good → ℚ} {body : RawEvent Party Good Port Technology Instrument}
  {offers : ProductionMenu Party Good Port Technology Instrument}
  {replies : Replies Party Good Port Technology Instrument}
  {tariff : Tariff Party Good Port Technology Instrument}
  {orders : PaymentOrders Party Good Port Technology Instrument}
  {openOrders : OpenOrders Party Good Port Technology Instrument}

variable (opening : Opening loss answers reserve body offers replies tariff orders openOrders)

/-- Start the point reader on the original paid opening. Its first
language is precisely the one installed on the live resident. -/
def checkedReader : Reader opening.liveInitial :=
  Reader.start opening.liveInitial rfl

variable [DecidableEq (Request Party Good Port Technology Instrument)]
  (policy : Policy Party Good Port Technology Instrument) (slot : Nat)

local notation "Before" => Prod.fst (opening.liveRun policy slot)
local notation "InputAt" => opening.submitted policy slot
local notation "After" => Prod.fst (opening.liveRun policy (slot + 1))

def checkedVisit (reader : Reader Before) (advice : Advice Before InputAt)
    (witnesses : List (Effect Party Good Port Technology Instrument) := []) :=
  Network.Runtime.Decision.advance opening.home replies Before InputAt reader advice witnesses

/-- A checked commitment is consumed at the next canonical physical
cut, with the same reader transported to its exact resident. -/
def nextCheckedReader {step : Network.Runtime.Step (seed := seed) (community := community)}
    (exactStep : step = Network.Runtime.advance opening.home replies Before InputAt)
    (reader : Reader step.next) : Reader After := by
  have next_eq : step.next = After :=
    (congrArg Network.Runtime.Step.next exactStep).trans
      (Network.Runtime.history_succ opening.home replies opening.liveInitial policy slot).symm
  exact next_eq ▸ reader

end

end SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.FixedPoint.OpenPeace.Opening
