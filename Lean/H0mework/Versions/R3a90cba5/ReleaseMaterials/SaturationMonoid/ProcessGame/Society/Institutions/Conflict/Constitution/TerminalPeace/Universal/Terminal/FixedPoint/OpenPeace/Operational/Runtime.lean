import H0mework.Versions.R3a90cba5.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.FixedPoint.OpenPeace.Operational.Certificate
import H0mework.Versions.R3a90cba5.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.FixedPoint.NoFreeProbe.Pricing.Entrance

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.FixedPoint.OpenPeace.Operational

open Capitalism.Universal.Source.Program
open Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening
open Reparation.Actual (ReceiptAnswers Occurrence Script)
open Quantities.Execution (endAt)
open Clearance Joint.SourceReserve
open NoFreeProbe
open NoFreeProbe.Prepayment (PaymentOrders)

noncomputable section

variable {Party Good Port Technology Instrument Community : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Instrument] [DecidableEq Community]
  [DecidableEq (Request Party Good Port Technology Instrument)]
  {seed : Conflict.Root.Cut Party Good Port Technology Instrument} {community : Party → Community}
  (loss : Occurrence seed community) (answers : ReceiptAnswers seed)
  (body : RawEvent Party Good Port Technology Instrument)
  (replies : Replies Party Good Port Technology Instrument)
  (offers : ProductionMenu Party Good Port Technology Instrument)
  (addresses : List (Party × Good)) (covered : ∀ address, address ∈ addresses)
  (tail : Script Party Good Port Technology Instrument)
  (choice : ProductionChoice offers)
  (code : RepeatCode (productionInput seed loss (Joint.firstProduction loss body ++ tail) choice)
    (prefixRaw loss (Joint.firstProduction loss body ++ tail)))
  (worker : Party)
  (deskAt : ∀ opening : SettledOpening loss answers (openingReserve loss) body offers replies,
    Pricing.Desk opening.entry.current.programme.law opening.entry.current.physical.raw worker)
  (orders : PaymentOrders Party Good Port Technology Instrument)
  (openOrders : OpenOrders Party Good Port Technology Instrument)

/-- A checked word installs the paid work lanes at its literal landing.
A refused word emits its typed failure at the original cut. -/
def openVerified :
    Installation.Core.Landed seed community (endAt seed (Occurrence.history loss))
      (CertificateIssue loss answers body offers tail choice code) ⊕
    ((checked : CheckedCertificate loss answers body replies offers tail) ×
      Pricing.InstallResult checked.opening (deskAt checked.opening) orders openOrders) :=
  match verifyPrepared loss answers body replies offers addresses covered tail choice code with
  | .error issue => .inl (writeCertificateIssue loss answers body offers tail choice code issue)
  | .ok checked =>
    .inr ⟨checked, Pricing.installFromWork checked.opening (deskAt checked.opening) orders openOrders⟩

end

end SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.FixedPoint.OpenPeace.Operational
