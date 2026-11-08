import H0mework.Versions.Rf1d58550.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Root.Restitution
import H0mework.Versions.R3b3d24a4.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Transition.Exchange.Slot
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Settlement.NonFinancial

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Root

open PublicFunction.Repayment (Position)
open Capitalism.Universal
open Capitalism.Universal.Source.Program
open Capitalism.Universal.Abolition.Root
open Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening
open Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Transition.Exchange

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]

local notation "C" => Cut Party Good Port Technology Instrument
local notation "Req" => Request Party Good Port Technology Instrument
local notation "Word" => RawEvent Party Good Port Technology Instrument
local notation "Law" => RawLaw Party Good Port Technology Instrument

/-- Read an earmarked one-unit-kind payment from its two adjacent original
instructions. Their amounts and addresses are parsed from the signed word. -/
structure Funding (law : Law) (levy settlement : Req) where
  position : Position Party Instrument
  bearer : Party
  quantity : ℚ
  principal : ℚ
  funded : levy.operation = .transfer bearer position.debtor [(law.settlementUnit position.instrument, quantity)]
  paid : settlement.operation = .settle position.instrument position.debtor position.creditor principal
  exposed : bearer ≠ position.debtor
  distinctPayment : position.debtor ≠ position.creditor
  amount : quantity = principal * law.settlementRate position.instrument
  positive : 0 < quantity

def readFunding (law : Law) (levy settlement : Req) : Option (Funding law levy settlement) :=
  match funded : levy.operation, paid : settlement.operation with
  | .transfer bearer receiver [(good, quantity)], .settle instrument debtor creditor principal =>
      if matched : receiver = debtor ∧ good = law.settlementUnit instrument ∧
          bearer ≠ debtor ∧ debtor ≠ creditor ∧ quantity = principal * law.settlementRate instrument ∧
          0 < quantity then
        some ⟨⟨instrument, debtor, creditor⟩, bearer, quantity, principal,
          by simpa only [matched.1, matched.2.1] using funded, paid,
          matched.2.2.1, matched.2.2.2.1, matched.2.2.2.2.1, matched.2.2.2.2.2⟩
      else none
  | _, _ => none

def SameOldSlot (source : C) (word : Word) (position : Position Party Instrument)
    (index : Nat) (principal : ℚ) : Prop :=
  let after := terminal source word
  NamesOpenSlot source position index ∧
    (slotAt after index).map (slotAddress after) = some (position.instrument, position.debtor) ∧
    principalAt source index position.creditor - principalAt after index position.creditor = principal

instance (source : C) (word : Word) (position : Position Party Instrument) (index : Nat) (principal : ℚ) :
    Decidable (SameOldSlot source word position index principal) := by
  unfold SameOldSlot
  infer_instance

structure Shift (source : C) (front : Word) (levy settlement : Req) (index : Nat) where
  funding : Funding source.native.input.law levy settlement
  prior : Settlement.NonFinancial front
  execution : Paid source (front ++ [levy, settlement])
  oldSlot : SameOldSlot source (front ++ [levy, settlement]) funding.position index funding.principal

inductive Incidence (source : C) (front : Word) (levy settlement : Req) (index : Nat)
  | shifted (shift : Shift source front levy settlement index)
  | noFunding (absent : readFunding source.native.input.law levy settlement = none)
  | otherFinancialInstruction (request : Req) (present : request ∈ front)
      (financial : ¬ Settlement.NonFinancialRequest request)
  | refused (failure : Failure source (front ++ [levy, settlement]))
  | wrongShare (funding : Funding source.native.input.law levy settlement)
      (actual : Paid source (front ++ [levy, settlement]))
      (mismatch : ¬ SameOldSlot source (front ++ [levy, settlement]) funding.position index funding.principal)

/-- Allocation must reach the named old native slot. Nominally matching a
financial address does not decide how much its earlier priority consumes. -/
def readShift (source : C) (front : Word) (levy settlement : Req) (index : Nat) :
    Incidence source front levy settlement index :=
  match found : readFunding source.native.input.law levy settlement with
  | none => .noFunding found
  | some funding =>
      match Settlement.checkFinancial front with
      | .rejected request present financial => .otherFinancialInstruction request present financial
      | .accepted prior =>
          match inspect source (front ++ [levy, settlement]) with
          | .rejected failure => .refused failure
          | .paid execution =>
              if named : SameOldSlot source (front ++ [levy, settlement])
                  funding.position index funding.principal then
                .shifted ⟨funding, prior, execution, named⟩
              else .wrongShare funding execution named

end

end SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Root
