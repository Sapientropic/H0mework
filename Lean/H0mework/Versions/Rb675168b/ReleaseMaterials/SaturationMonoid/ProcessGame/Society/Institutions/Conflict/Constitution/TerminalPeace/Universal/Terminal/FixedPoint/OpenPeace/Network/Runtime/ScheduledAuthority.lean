import H0mework.Versions.Rb675168b.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.FixedPoint.OpenPeace.Network.Runtime.SignedLanes

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.FixedPoint.OpenPeace.Network.Runtime

open Capitalism.Universal.Source.Program
open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot RootInquiryCompletion
open Installation.Core
open Reparation.Actual (Resident)
open NoFreeProbe
open NoFreeProbe.Prepayment (PaymentOrders)

noncomputable section

variable {N M L : WorldRelationNetwork}

/-- Transport through an already selected sequence of exact writes. -/
structure ReadPath (prior : Resident N) (target : Resident M) where
  carry : ∀ {Payload : Type}, ReadOn prior Payload → ReadOn target Payload
  keeps : ∀ {Payload : Type} (input : ReadOn prior Payload), (carry input).read = input.read

namespace ReadPath

variable {prior : Resident N} {middle : Resident M} {target : Resident L}

def write {Emission : Type} (ready : ResidentWrite.Ready prior) (emission : Emission) (writes : Bool) :
    ReadPath prior (ResidentWrite.landing prior ready emission writes) :=
  ⟨fun input => input.afterWrite ready emission writes,
    fun input => input.afterWrite_read ready emission writes⟩

def trans (first : ReadPath prior middle) (next : ReadPath middle target) : ReadPath prior target :=
  ⟨fun input => next.carry (first.carry input),
    fun input => (next.keeps (first.carry input)).trans (first.keeps input)⟩

end ReadPath

variable {Party Good Port Technology Instrument Community : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Instrument] [DecidableEq Community]
  {seed cut : Conflict.Root.Cut Party Good Port Technology Instrument} {community : Party → Community}
  {origin : RawCurrent Party Good Technology Instrument} {people : List Party} {quantum : ℚ}

variable {current : Current (seed := seed) (cut := cut) (community := community) origin people quantum}
  {tariff : Tariff Party Good Port Technology Instrument} {replies : Replies Party Good Port Technology Instrument}
  {home : AnyAuthoritativeRootCurrent.{0}} {orders : PaymentOrders Party Good Port Technology Instrument}
  {View : Type*}
  {see : Current (seed := seed) (cut := cut) (community := community) origin people quantum → View}

def roundReads (round : Round current) :
    ReadPath current.ledger.resident round.next.ledger.resident :=
  round.ledgerNext.symm ▸ ReadPath.write current.ledger.ready round.visit.read true

private def protectedReads (step : NoFreeProbe.Step tariff replies current) :
    ReadPath current.ledger.resident step.next.ledger.resident :=
  match step with
  | .renewed => roundReads (.renewed : NoFreeProbe.Step tariff replies current).round
  | .revised offer kit approved =>
    roundReads (.revised offer kit approved : NoFreeProbe.Step tariff replies current).round
  | .reviewed _ _ paid =>
    (roundReads paid.round).trans (ReadPath.write paid.round.next.ledger.ready paid.answer true)

private def prepaidReads (step : Prepayment.Step tariff replies current see home orders) :
    ReadPath current.ledger.resident step.next.ledger.resident :=
  match step with
  | .ordinary due _ => protectedReads due
  | .prepaid _ _ paid =>
    (roundReads paid.round).trans
      (ReadPath.write paid.round.next.ledger.ready (Prepayment.assessment replies paid).read true)

variable {before : AdaptivePeace.State (seed := seed) (cut := cut) (community := community) origin people quantum}

/-- Consume the scheduler's actual selected branch, including its
post-payment assessment, refusal, or guard write. -/
def adaptiveReads (step : AdaptivePeace.Step tariff home orders replies before) :
    ReadPath before.native.ledger.resident step.next.native.ledger.resident :=
  match step with
  | .ordinary base _ => prepaidReads base
  | .refused _ _ paid _ _ =>
    (roundReads paid.round).trans (ReadPath.write paid.round.next.ledger.ready AdaptivePeace.Reply.refused true)
  | .amended _ _ paid _ =>
    (roundReads paid.round).trans
      (ReadPath.write paid.round.next.ledger.ready (AdaptivePeace.repair before.covered paid).read true)

namespace SignedLanes

variable (lanes : SignedLanes Party Good Port Technology Instrument before.native.ledger.resident)
  (step : AdaptivePeace.Step tariff home orders replies before)

def afterAdaptive : SignedLanes Party Good Port Technology Instrument step.next.native.ledger.resident :=
  lanes.map (adaptiveReads step).carry

theorem afterAdaptive_keeps_reads :
    (lanes.afterAdaptive step).tariff.read = lanes.tariff.read ∧
    (lanes.afterAdaptive step).payment.read = lanes.payment.read ∧
    (lanes.afterAdaptive step).openPayment.read = lanes.openPayment.read :=
  lanes.map_keeps_reads (adaptiveReads step).carry (adaptiveReads step).keeps

end SignedLanes

end

end SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.FixedPoint.OpenPeace.Network.Runtime
