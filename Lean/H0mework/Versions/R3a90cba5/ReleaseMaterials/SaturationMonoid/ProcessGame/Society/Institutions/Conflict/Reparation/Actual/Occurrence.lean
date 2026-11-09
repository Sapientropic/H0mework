import H0mework.Versions.R3a90cba5.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Boundary.Actual.Incidence
import H0mework.Versions.Rf1d58550.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Reparation.Discharge

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Reparation.Actual

open Capitalism.Universal.Source.Program
open Capitalism.Universal.Abolition.Root.Registered
open Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening
open Quantities.Execution (endAt)

noncomputable section

variable {Party Good Port Technology Instrument Community : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Instrument] [DecidableEq Community]

abbrev Input (Party Good Port Technology Instrument : Type) :=
  Option (Compile.RawInput Party Good Port Technology Instrument)

abbrev Script (Party Good Port Technology Instrument : Type) :=
  List (Input Party Good Port Technology Instrument)

local notation "C" => Root.Cut Party Good Port Technology Instrument
local notation "Proposal" => Input Party Good Port Technology Instrument
local notation "History" => Script Party Good Port Technology Instrument

/-- One particular root history, one material occurrence within its next
tick, and the harmed address at that occurrence. -/
structure Occurrence (seed : C) (community : Party → Community) where
  past : History
  input : Proposal
  damage : Boundary.Actual.DamageAt (endAt seed past) input community

namespace Occurrence

variable {seed : Root.Cut Party Good Port Technology Instrument} {community : Party → Community}
  (origin : Occurrence seed community)

abbrev key := origin.damage.key
abbrev quantity := origin.damage.quantity
abbrev address : Nat × Nat × Key Party Good := (origin.past.length, origin.damage.position.val, origin.key)

theorem positive : 0 < origin.quantity := origin.damage.positive

end Occurrence

/-- The credit comes from one original signed physical receipt, keyed by
the original victim, debtor, and good. -/
structure SignedReceipt (seed : C) (key : Key Party Good) where
  past : History
  input : Proposal
  position : Fin (Boundary.Actual.items (endAt seed past) input).length
  positive : 0 < receiptCredit seed.native.input.law
    (Boundary.Actual.items (endAt seed past) input)[position] key

namespace SignedReceipt

variable {seed : Root.Cut Party Good Port Technology Instrument} {key : Key Party Good}
  (receipt : SignedReceipt seed key)

abbrev item := (Boundary.Actual.items (endAt seed receipt.past) receipt.input)[receipt.position]
abbrev quantity := receiptCredit seed.native.input.law receipt.item key
abbrev address : Nat × Nat := (receipt.past.length, receipt.position.val)

theorem is_original_receipt :
    receipt.item ∈ Boundary.Actual.items (endAt seed receipt.past) receipt.input ∧
      receipt.item.request.signer = key.1 :=
  ⟨List.getElem_mem _, (positive_receipt_has_the_original_signature_and_delivery
    seed.native.input.law receipt.item key receipt.positive).1⟩

end SignedReceipt

variable {seed : Root.Cut Party Good Port Technology Instrument} {community : Party → Community}

def later (origin : Occurrence seed community) (receipt : SignedReceipt seed origin.key) : Prop :=
  (origin.past ++ [origin.input]).IsPrefix receipt.past ∨
    origin.past = receipt.past ∧ origin.input = receipt.input ∧
      origin.damage.position.val < receipt.position.val

/-- Local receipt evidence is later than its own damage. The joint
allocator budgets all of its shares together. -/
structure Share (origin : Occurrence seed community) where
  receipt : SignedReceipt seed origin.key
  amount : ℚ
  positive : 0 < amount
  within : amount ≤ receipt.quantity
  afterBirth : later origin receipt

end

end SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Reparation.Actual
