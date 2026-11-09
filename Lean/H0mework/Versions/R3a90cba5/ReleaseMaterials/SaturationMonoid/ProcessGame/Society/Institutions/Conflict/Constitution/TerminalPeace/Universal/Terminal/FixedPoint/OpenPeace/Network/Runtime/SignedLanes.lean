import H0mework.Versions.R3a90cba5.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.FixedPoint.OpenPeace.Network.Runtime.Authority
import H0mework.Versions.R3a90cba5.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Installation.Core.ResidentWrite
import H0mework.Versions.R3a90cba5.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.FixedPoint.OpenPeace.Ingress

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.FixedPoint.OpenPeace.Network.Runtime

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot RootInquiryCompletion
open Capitalism.Universal.Abolition.Accounting.Root
open Installation.Core
open Reparation.Actual (Resident)
open NoFreeProbe
open NoFreeProbe.Prepayment (PaymentOrders)

noncomputable section

variable {N M : WorldRelationNetwork}

abbrev ReadOn (resident : Resident N) (Payload : Type) :=
  ReadAt resident.root resident.visit Payload

namespace ReadAt

variable {prior : Resident N} {Payload Emission : Type}

/-- Carry a signer through the exact generated material or semantic write. -/
def afterWrite (input : ReadOn prior Payload) (ready : ResidentWrite.Ready prior)
    (emission : Emission) (writes : Bool) :
    ReadOn (ResidentWrite.landing prior ready emission writes) Payload :=
  input.freezeWrite (Compiler.livingRoot (ResidentWrite.first prior ready writes).flow)
    (ResidentWrite.component prior ready emission writes)
    (ResidentWrite.landing prior ready emission writes).visit

theorem afterWrite_read (input : ReadOn prior Payload) (ready : ResidentWrite.Ready prior)
    (emission : Emission) (writes : Bool) :
    (input.afterWrite ready emission writes).read = input.read :=
  rfl

/-- The new input is a typed read of the write that originally installed it. -/
def ofWrite (prior : Resident N) (ready : ResidentWrite.Ready prior)
    (emission : Payload) (writes : Bool) :
    ReadOn (ResidentWrite.landing prior ready emission writes) Payload :=
  ⟨ResidentWrite.face prior ready emission writes, rfl⟩

theorem ofWrite_read (prior : Resident N) (ready : ResidentWrite.Ready prior)
    (emission : Payload) (writes : Bool) :
    (ofWrite prior ready emission writes).read = emission :=
  rfl

end ReadAt

/-- The three original signer lanes at the live dispatch resident. -/
structure SignedLanes (Party Good Port Technology Instrument : Type) [DecidableEq Good]
    (resident : Resident N) where
  tariff : ReadOn resident (Tariff Party Good Port Technology Instrument)
  payment : ReadOn resident (PaymentOrders Party Good Port Technology Instrument)
  openPayment : ReadOn resident (OpenOrders Party Good Port Technology Instrument)

namespace SignedLanes

variable {Party Good Port Technology Instrument : Type} [DecidableEq Good]
  {prior : Resident N} {target : Resident M}
  (inputs : SignedLanes Party Good Port Technology Instrument prior)

def map (lift : ∀ {Payload : Type}, ReadOn prior Payload → ReadOn target Payload) :
    SignedLanes Party Good Port Technology Instrument target :=
  ⟨lift inputs.tariff, lift inputs.payment, lift inputs.openPayment⟩

theorem map_keeps_reads (lift : ∀ {Payload : Type}, ReadOn prior Payload → ReadOn target Payload)
    (keeps : ∀ {Payload : Type} (input : ReadOn prior Payload), (lift input).read = input.read) :
    (inputs.map lift).tariff.read = inputs.tariff.read ∧
    (inputs.map lift).payment.read = inputs.payment.read ∧
    (inputs.map lift).openPayment.read = inputs.openPayment.read :=
  ⟨keeps inputs.tariff, keeps inputs.payment, keeps inputs.openPayment⟩

end SignedLanes

end

end SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.FixedPoint.OpenPeace.Network.Runtime
