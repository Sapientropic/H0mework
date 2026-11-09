import H0mework.Versions.Rb675168b.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.FixedPoint.OpenPeace.Network.Runtime.Consumers.Orders
import H0mework.Versions.Rb675168b.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.FixedPoint.OpenPeace.Network.Runtime.SignedLanes
import H0mework.Versions.Rb675168b.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.FixedPoint.OpenPeace.Network.Consumers.OriginalBase

set_option autoImplicit false
set_option maxRecDepth 8192

namespace SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.FixedPoint.OpenPeace.Network.Runtime.OriginalFixture

open OriginalOrders
open private OpenPeace.State.start from H0mework.Versions.Rb675168b.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.FixedPoint.OpenPeace.Dispatch
open private AdaptivePeace.State.start from H0mework.Versions.Rb675168b.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.FixedPoint.AdaptivePeace.Dispatch

noncomputable section

private abbrev initial := OriginalReview.initial
private abbrev originalLedger := initial.ledger
private def openingWrite := Installation.Live.publish paymentWrite.state openPayment true

def base : OpenPeace.State (seed := TerminalPeace.Original.seed) (cut := Settlement.settledCut)
    (community := TerminalPeace.Original.community) OriginalReview.origin [false, true] 1 :=
  OpenPeace.State.start (AdaptivePeace.State.start { initial with ledger := openingWrite.state })

/-- All three reads come from the actual consecutive installations on the
settled six-unit occurrence. The registration is the payment write. -/
def lanes : SignedLanes Bool Bool Bool Unit Unit base.adaptive.native.ledger.resident :=
  let quoteLane := ReadAt.ofWrite originalLedger.resident originalLedger.ready quote true
  let paymentLane := ReadAt.ofWrite tariffWrite.state.resident tariffWrite.state.ready payment true
  ⟨(quoteLane.afterWrite tariffWrite.state.ready payment true).afterWrite paymentWrite.state.ready openPayment true,
    paymentLane.afterWrite paymentWrite.state.ready openPayment true,
    ReadAt.ofWrite paymentWrite.state.resident paymentWrite.state.ready openPayment true⟩

def inherited : InheritedCalculus base.adaptive.native.ledger.world :=
  OriginalBase.inherited

theorem reads_the_three_original_installations :
    lanes.tariff.read = quote ∧ lanes.payment.read = payment ∧ lanes.openPayment.read = openPayment :=
  ⟨rfl, rfl, rfl⟩

theorem opening_keeps_the_original_settlement :
    base.adaptive.native.ledger.stack.balances = initial.ledger.stack.balances :=
  rfl

end

end SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.FixedPoint.OpenPeace.Network.Runtime.OriginalFixture
