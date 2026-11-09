import H0mework.Versions.R3a90cba5.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.FixedPoint.OpenPeace.Network.Runtime.SignedLanes
import H0mework.Versions.R3a90cba5.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.FixedPoint.OpenPeace.Compiler

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.FixedPoint.OpenPeace.Network.Runtime

open Capitalism.Universal.Source.Program
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
  {replies : Replies Party Good Port Technology Instrument}
  {tariff : Tariff Party Good Port Technology Instrument}
  {orders : PaymentOrders Party Good Port Technology Instrument}
  {openOrders : OpenOrders Party Good Port Technology Instrument}

variable (opening : Opening loss answers reserve body offers replies tariff orders openOrders)

set_option maxHeartbeats 450000 in
/-- Read all three original signer lanes at the opening's actual current.
The later opening writes retain the first two installed projections. -/
def openingLanes :
    SignedLanes Party Good Port Technology Instrument opening.initial.adaptive.native.ledger.resident :=
  let tariffWrite := opening.source.source.source.installation
  let paymentWrite := opening.source.source.installation
  let openWrite := opening.installation
  let quote : ReadOn tariffWrite.state.resident (Tariff Party Good Port Technology Instrument) :=
    ⟨tariffWrite.material, tariffWrite.materialType⟩
  let payment : ReadOn paymentWrite.state.resident (PaymentOrders Party Good Port Technology Instrument) :=
    ⟨paymentWrite.material, paymentWrite.materialType⟩
  let carriedQuote : ReadOn paymentWrite.state.resident (Tariff Party Good Port Technology Instrument) :=
    ReadAt.afterWrite (prior := tariffWrite.state.resident) quote tariffWrite.state.ready orders true
  let carry {Payload : Type} (input : ReadOn paymentWrite.state.resident Payload) :
      ReadOn openWrite.state.resident Payload :=
    ReadAt.afterWrite (prior := paymentWrite.state.resident) input paymentWrite.state.ready openOrders true
  let installed : SignedLanes Party Good Port Technology Instrument openWrite.state.resident :=
    ⟨carry carriedQuote, carry payment, ⟨openWrite.material, openWrite.materialType⟩⟩
  installed

theorem opening_lanes_are_the_original_registrations :
    (openingLanes opening).tariff.read = tariff ∧
    (openingLanes opening).payment.read = orders ∧
    (openingLanes opening).openPayment.read = openOrders :=
  ⟨rfl, rfl, rfl⟩

end

end SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.FixedPoint.OpenPeace.Network.Runtime
