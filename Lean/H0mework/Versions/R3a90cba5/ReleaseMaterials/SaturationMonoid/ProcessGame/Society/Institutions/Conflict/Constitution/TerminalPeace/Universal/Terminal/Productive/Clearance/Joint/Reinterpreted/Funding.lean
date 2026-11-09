import H0mework.Versions.R3a90cba5.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.Productive.Clearance.Joint.Reinterpreted.Current
import H0mework.Versions.R3a90cba5.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.Productive.Clearance.Joint.Reinterpreted.Transfer

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.Clearance.Joint.Reinterpreted

open Capitalism.Universal.Source.Program
open Capitalism.Universal.Abolition.Material (inspectList)
open Reparation (Key)
open Reparation.Actual (Script)
open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot RootInquiryCompletion
open Joint.SourceReserve (atRaw)

noncomputable section

variable {Party Good Port Technology Instrument Community : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  [DecidableEq Community]
  {seed : Conflict.Root.Cut Party Good Port Technology Instrument} {community : Party → Community}
  {loss : Reparation.Actual.Occurrence seed community} {front : Script Party Good Port Technology Instrument}

/-- The independent signer reads the actual resident, its physical stock
and the literal delivery request. A request supplies no replies. -/
abbrev DeliveryAnswers (Party Good Port Technology Instrument : Type) :=
  AnyAuthoritativeRootCurrent.{0} → Nat → RawCurrent Party Good Technology Instrument →
    Request Party Good Port Technology Instrument → Party → Bool

variable (before : Current loss front)
  (answers : DeliveryAnswers Party Good Port Technology Instrument)
  (key : Key Party Good) (quantity : ℚ)

abbrev purpose (before : Current loss front) (key : Key Party Good) : Port :=
  before.programme.law.stockPort before.physical.raw.technology key.2.1 key.2.2

abbrev request := (paymentRequest (purpose before key) key quantity :
  Request Party Good Port Technology Instrument)

abbrev signAt :=
  answers before.ledger.resident.erase before.ordinal before.physical.raw (request before key quantity)

abbrev requiredAt (raw : RawCurrent Party Good Technology Instrument) :=
  atRaw before.programme.law (originalRaw loss) raw

abbrev liveBalance (before : Current loss front) (key : Key Party Good) :=
  dueFor key before.ledger.stack.balances

local notation "Pay" => request before key quantity
local notation "Sign" => signAt before answers key quantity
local notation "StockAfter" => deliveredRaw before.physical.raw key quantity

def ProtectedDelivery : Prop :=
  ∀ person good, requiredAt before StockAfter person good ≤ (StockAfter).stock person good

structure Funding : Prop where
  distinct : key.1 ≠ key.2.1
  positive : 0 < quantity
  within : quantity ≤ liveBalance before key
  legal : before.programme.law.Valid before.physical.raw Pay
  payer : Sign key.2.1 = true
  victim : Sign key.1 = true
  reserve : ProtectedDelivery before key quantity

inductive PaymentIssue
  | sameParty (same : key.1 = key.2.1)
  | nonpositive (amount : quantity ≤ 0)
  | overclaim (amount : liveBalance before key < quantity)
  | notAuthorized (denied : ¬ before.programme.law.Valid before.physical.raw Pay)
  | payerRefused (denied : Sign key.2.1 = false)
  | victimRefused (denied : Sign key.1 = false)
  | shortage (person : Party) (good : Good)
      (missing : (StockAfter).stock person good < requiredAt before StockAfter person good)

theorem PaymentIssue.refutes (issue : PaymentIssue before answers key quantity) :
    ¬ Funding before answers key quantity := by
  intro paid
  cases issue with
  | sameParty same => exact paid.distinct same
  | nonpositive amount => exact amount.not_gt paid.positive
  | overclaim amount => exact amount.not_ge paid.within
  | notAuthorized denied => exact denied paid.legal
  | payerRefused denied => exact Bool.false_ne_true (denied.symm.trans paid.payer)
  | victimRefused denied => exact Bool.false_ne_true (denied.symm.trans paid.victim)
  | shortage person good missing => exact missing.not_ge (paid.reserve person good)

variable (addresses : List (Party × Good)) (covered : ∀ address, address ∈ addresses)

def checkFunding : Except (PaymentIssue before answers key quantity) (PLift (Funding before answers key quantity)) := do
  let distinct ← if same : key.1 = key.2.1 then throw (.sameParty same) else pure (PLift.up same)
  let positive ← if positive : 0 < quantity then pure (PLift.up positive) else throw (.nonpositive (le_of_not_gt positive))
  let within ← if within : quantity ≤ liveBalance before key then pure (PLift.up within) else throw (.overclaim (lt_of_not_ge within))
  let legal ← if legal : before.programme.law.Valid before.physical.raw Pay then pure (PLift.up legal)
    else throw (.notAuthorized legal)
  let payer ← if signed : Sign key.2.1 = true then pure (PLift.up signed)
    else throw (.payerRefused (Bool.eq_false_of_not_eq_true signed))
  let victim ← if signed : Sign key.1 = true then pure (PLift.up signed)
    else throw (.victimRefused (Bool.eq_false_of_not_eq_true signed))
  let fits (address : Party × Good) :=
    requiredAt before StockAfter address.1 address.2 ≤ (StockAfter).stock address.1 address.2
  match inspectList fits addresses with
  | .failure address _ short => throw (.shortage address.1 address.2 (lt_of_not_ge short))
  | .clear all =>
    return ⟨⟨distinct.down, positive.down, within.down, legal.down, payer.down, victim.down,
      fun person good => all (person, good) (covered _)⟩⟩

theorem checkFunding_exact :
    (∃ accepted, checkFunding before answers key quantity addresses covered = .ok accepted) ↔
      Funding before answers key quantity := by
  constructor
  · rintro ⟨accepted, _⟩
    exact accepted.down
  · intro paid
    cases checkFunding before answers key quantity addresses covered with
    | error issue => exact (issue.refutes before answers key quantity paid).elim
    | ok proof => exact ⟨proof, rfl⟩

end

end SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.Clearance.Joint.Reinterpreted
