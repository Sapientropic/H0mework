import H0mework.Versions.R3a90cba5.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.Productive.Clearance.Delivery.Native
import H0mework.Versions.R3a90cba5.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Supply.Native

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.Clearance.Joint.Reinterpreted

open Capitalism.Universal.Source.Program
open Capitalism.Universal.Root
open Capitalism.Universal.Abolition.Root.Registered
open Reparation (Key)
open Reparation.Actual (payerCredit)

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]

variable (programme : ProgrammeSource.Input Party Good Port Technology Instrument)
  (before : Capitalism.Universal.Abolition.Root.Actual.Current (Party := Party) (Good := Good)
    (Port := Port) (Technology := Technology) (Instrument := Instrument))
  (purpose : Port) (key : Key Party Good) (quantity : ℚ)

local notation "Send" => (paymentRequest purpose key quantity : Request Party Good Port Technology Instrument)
local notation "Item" => (ExecutionItem.mk 0 before.raw Send : ExecutionItem Party Good Port Technology Instrument)
local notation "Effect" => Physical.Public.compile programme before (Compile.RawInput.primitive Send)
local notation "Law" => programme.law

omit [DecidableEq Port] [DecidableEq Instrument] in
theorem transfer_credit (valid : (Law).Valid before.raw Send) (good : Good) :
    flowAt ((Law).actualCredit before.raw Send) key.1 good = if good = key.2.2 then quantity else 0 := by
  rw [RawLaw.actualCredit, if_pos valid]
  change flowAt (locate key.1 [(key.2.2, quantity)]) key.1 good = _
  rw [singleton_delivery_flow]
  simp

omit [DecidableEq Port] [DecidableEq Instrument] in
theorem transfer_limit (valid : (Law).Valid before.raw Send) (positive : 0 < quantity) (good : Good) :
    Settlement.deliveryLimit Law Item good = if good = key.2.2 then quantity else 0 := by
  change max 0 (flowAt ((Law).actualCredit before.raw Send) key.1 good) = _
  rw [transfer_credit programme before purpose key quantity valid]
  split
  · exact max_eq_right positive.le
  · exact max_self _

omit [DecidableEq Port] [DecidableEq Instrument] in
theorem transfer_payerCredit (valid : (Law).Valid before.raw Send) (distinct : key.1 ≠ key.2.1)
    (positive : 0 < quantity) :
    payerCredit Law Item key = quantity := by
  unfold payerCredit
  rw [if_pos ⟨distinct, rfl, valid⟩]
  change (if key.2.1 = key.2.1 ∧ key.1 = key.1 then
    max 0 (flowAt ((Law).actualCredit before.raw Send) key.1 key.2.2) else 0) = _
  rw [if_pos ⟨rfl, rfl⟩, transfer_credit programme before purpose key quantity valid, if_pos rfl,
    max_eq_right positive.le]

omit [DecidableEq Port] [DecidableEq Instrument] in
theorem transfer_has_only_its_own_key (valid : (Law).Valid before.raw Send) (other : Key Party Good)
    (different : other ≠ key) : payerCredit Law Item other = 0 := by
  unfold payerCredit
  split
  · change (if key.2.1 = other.2.1 ∧ key.1 = other.1 then
      max 0 (flowAt ((Law).actualCredit before.raw Send) other.1 other.2.2) else 0) = _
    split
    · rename_i parties
      have good : other.2.2 ≠ key.2.2 := fun same =>
        different (Prod.ext parties.2.symm (Prod.ext parties.1.symm same))
      rw [← parties.2, transfer_credit programme before purpose key quantity valid, if_neg good, max_self]
    · rfl
  · rfl

omit [DecidableEq Port] in
/-- Use the installed interpreter and its real stock. A primitive
settlement does not create a physical period. -/
theorem transfer_is_the_actual_primitive (valid : (Law).Valid before.raw Send) :
    (Effect).isAccepted = true ∧ (Effect).execution.items = [Item] ∧
      (Effect).next.raw = deliveredRaw before.raw key quantity := by
  have signed : (Send).resign (Send).signer = Send := Request.resign_self _ rfl
  have selected : Physical.Public.wordAt before (.primitive Send) = some [Send] := by
    change some [(Send).resign (Send).signer] = _
    rw [signed]
  have physical : (Physical.Public.interpreter programme).Valid before.raw Send :=
    PublicFunction.valid_physical _ _ _ valid
  cases result : Effect with
  | accepted word actual _ =>
    rw [selected] at actual
    cases Option.some.inj actual
    refine ⟨rfl, rfl, ?_⟩
    change (Physical.Public.interpreter programme).step before.raw Send = _
    rw [RawLaw.step, if_pos physical]
    apply RawCurrent.ext
    · funext person good
      change before.raw.stock person good -
        flowAt (locate key.2.1 [(key.2.2, quantity)]) person good +
        flowAt (locate key.1 [(key.2.2, quantity)]) person good = _
      rw [singleton_delivery_flow, singleton_delivery_flow]
      rfl
    · rfl
    · rfl
    · rfl
    · rfl
  | refused word actual item listed refused =>
    rw [selected] at actual
    cases Option.some.inj actual
    change item ∈ [Item] at listed
    exact (refused (List.mem_singleton.mp listed ▸ physical)).elim
  | metadata none =>
    rw [selected] at none
    cases none

end

end SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.Clearance.Joint.Reinterpreted
