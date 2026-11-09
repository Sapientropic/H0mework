import H0mework.Versions.R3a90cba5.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.FixedPoint.NoFreeProbe.Pricing.Payment
import H0mework.Versions.R3a90cba5.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.FixedPoint.OpenPeace.Network.Compile

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.FixedPoint.NoFreeProbe.Pricing

open Capitalism.Universal.Source.Program
open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot RootInquiryCompletion
open Reparation.Actual (ReceiptAnswers)
open Prepayment (PaymentOrders)
open OpenPeace (OpenOrders)
open private NoFreeProbe.ProtectedOpening.mk from H0mework.Versions.R3a90cba5.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.FixedPoint.NoFreeProbe.Compiler
open private Prepayment.PrepaidOpening.mk from H0mework.Versions.R3a90cba5.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.FixedPoint.NoFreeProbe.Prepayment.Compiler
open private AdaptivePeace.AdaptiveOpening.mk from H0mework.Versions.R3a90cba5.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.FixedPoint.AdaptivePeace.Compiler
open private OpenPeace.Opening.mk from H0mework.Versions.R3a90cba5.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.FixedPoint.OpenPeace.Compiler

noncomputable section

variable {Party Good Port Technology Instrument Community : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Instrument] [DecidableEq Community]
  {seed : Conflict.Root.Cut Party Good Port Technology Instrument} {community : Party → Community}
  {loss : Reparation.Actual.Occurrence seed community} {answers : ReceiptAnswers seed}
  {reserve : Party → Good → ℚ} {body : RawEvent Party Good Port Technology Instrument}
  {offers : ProductionMenu Party Good Port Technology Instrument}
  {replies : Replies Party Good Port Technology Instrument}
  {worker : Party}

variable (original : SettledOpening loss answers reserve body offers replies)
  (desk : Desk original.entry.current.programme.law original.entry.current.physical.raw worker)
  (orders : PaymentOrders Party Good Port Technology Instrument)
  (openOrders : OpenOrders Party Good Port Technology Instrument)

/-- Publish the metered tariff through the exact original opening. The
existing payment and open-order installations follow on its own resident. -/
def install (ready : desk.filingCheck = true) :
    OpenPeace.Opening loss answers reserve body offers replies (desk.tariff ready) orders openOrders :=
  OpenPeace.Opening.mk (AdaptivePeace.AdaptiveOpening.mk
    (Prepayment.PrepaidOpening.mk (NoFreeProbe.ProtectedOpening.mk original)))

theorem installation_reads_the_same_cost_at_every_epoch
    (ready : desk.filingCheck = true) (policy : OpenPeace.Policy Party Good Port Technology Instrument) (n : Nat)
    (word : RawEvent Party Good Port Technology Instrument) (good : Good) :
    let opening := install original desk orders openOrders ready
    amount Good (((opening.liveRun policy n).1.lanes.tariff.read).parts word).bundle good =
      desk.actualCost word good := by
  dsimp only
  let opening := install original desk orders openOrders ready
  have lane := (OpenPeace.Network.Runtime.history_keeps_original_signatures
    opening.home replies opening.liveInitial policy n).1
  have initial := (OpenPeace.Network.Runtime.opening_lanes_are_the_original_registrations opening).1
  have same : (opening.liveRun policy n).1.lanes.tariff.read = desk.tariff ready := lane.trans initial
  change amount Good (((opening.liveRun policy n).1.lanes.tariff.read).parts word).bundle good = _
  rw [same]
  exact desk.exact_quote ready word good

/-- Opening consumes the measured work through the existing lanes. If the
source supplies no positive filing work, the ordinary productive round
still writes while the proposal acquires no extra review authority. -/
inductive InstallResult
  | opened (ready : desk.filingCheck = true)
      (opening : OpenPeace.Opening loss answers reserve body offers replies
        (desk.tariff ready) orders openOrders)
  | noFiling (zero : ∀ good, amount Good desk.filing.bundle good = 0)
      (round : Round original.entry.current)
      (ordinary : round = dispatch replies original.entry.current .renew)

def installFromWork : InstallResult original desk orders openOrders :=
  if ready : desk.filingCheck = true then .opened ready (install original desk orders openOrders ready)
  else
    .noFiling (desk.no_filing_cost_iff.mp (dif_neg ready))
      (dispatch replies original.entry.current .renew) rfl

theorem no_filing_uses_the_original_productive_round
    (ready : desk.filingCheck ≠ true) :
    installFromWork original desk orders openOrders =
      .noFiling (desk.no_filing_cost_iff.mp (dif_neg ready))
        (dispatch replies original.entry.current .renew) rfl := by
  simp only [installFromWork, dif_neg ready]

end

end SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.FixedPoint.NoFreeProbe.Pricing
