import H0mework.Versions.R3b3d24a4.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Transition.Exchange.Slot
import H0mework.Versions.R3b3d24a4.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Transition.Exchange.Capacity
import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Epoch.Finance.Family.Source

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Transition.Exchange

open ResponsibilityLifecycle Source.Program PublicFunction.Repayment
open Abolition.Root Abolition.Root.Registered Abolition.Root.Epoch
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root
open Innovation.Contribution.Pricing.Root.Runtime
open Quantities.Exit.Redemption (sourceLaw request)

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]

local notation "C" => Evolving.Epoch.Current (Party := Party) (Good := Good) (Port := Port)
  (Technology := Technology) (Instrument := Instrument)
local notation "P" => Plan Party Good Port Technology Instrument
local notation "Pos" => Position Party Instrument

abbrev settlementBody (source : C) (position : Pos) (plan : P) (quantity : ℚ) :=
  afterBody (plan.exchanged source) (request (sourceLaw (plan.exchanged source)) position quantity)

abbrev familyInputs (old body : C) (current : Bool) :=
  Bool.rec (motive := fun _ => ProgrammeSource.Input Party Good Port Technology Instrument)
    old.native.input body.native.input current

abbrev familyDepths (old body : C) (current : Bool) :=
  Bool.rec (motive := fun _ => Nat) old.native.depth body.native.depth current

abbrev familyCounts (old body : C) (current : Bool) :=
  Bool.rec (motive := fun _ => Nat) old.native.count body.native.count current

/-- The receipt is the exact native head of the last original instruction
and is read against the selected claim at its old slot. -/
def NativeReviewed (source : C) (position : Pos) (plan : P) (quantity : ℚ) (index : Nat) : Prop :=
  let body := settlementBody source position plan quantity
  ∃ slot : SlotAt source, ∃ item : HeadAt body,
    slotAt source index = some slot ∧
    item.instruction _ _ _ =
      ⟨0, (plan.exchanged source).raw, request (sourceLaw (plan.exchanged source)) position quantity⟩ ∧
    (Finance.Family.readReview (familyInputs source body) (familyDepths source body) (familyCounts source body)
      ⟨false, Finance.slotClaim _ _ _ slot⟩ ⟨true, item⟩).isSome = true

private theorem reads_settlement (body : C) (item : HeadAt body) (position : Pos) (quantity : ℚ)
    (operation : (item.instruction _ _ _).request.operation =
      .settle position.instrument position.debtor position.creditor quantity)
    (valid : (item.interpreter _ _ _).Valid (item.instruction _ _ _).before (item.instruction _ _ _).request) :
    ∃ movement, Finance.readMovement _ _ _ item = some movement ∧
      movement.instrument = position.instrument ∧ movement.debtor = position.debtor := by
  have found : ∃ movement, Finance.readMovement _ _ _ item = some movement := by
    unfold Finance.readMovement
    rw [dif_pos valid]
    split
    · exact ⟨_, rfl⟩
    · rename_i _ _ _ _ _ mismatch
      rw [operation] at mismatch
      cases mismatch
    · rename_i _ _ notSettlement _
      exact False.elim (notSettlement _ _ _ _ operation)
  obtain ⟨movement, read⟩ := found
  have exactOperation := movement.operation
  rw [operation] at exactOperation
  refine ⟨movement, read, ?_⟩
  cases kind : movement.kind with
  | payment =>
      rw [kind] at exactOperation
      exact ⟨(Operation.settle.inj exactOperation).1.symm, (Operation.settle.inj exactOperation).2.1.symm⟩
  | assignment =>
      rw [kind] at exactOperation
      cases exactOperation

theorem the_original_family_reviews_the_paid_head_at_the_named_slot
    {source : C} {position : Pos} {plan : P} {quantity : ℚ} {index : Nat}
    (payment : FundedPayment source position plan quantity) (named : NamesOpenSlot source position index) :
    NativeReviewed source position plan quantity index := by
  let cut := plan.exchanged source
  let settle := request (sourceLaw cut) position quantity
  let body := settlementBody source position plan quantity
  have valid : (sourceLaw cut).Valid cut.raw settle := payment.settles.safe.2.1
  obtain ⟨item, identity, interpreter, _⟩ :=
    the_paid_primitive_has_one_literal_native_consumer cut settle
      payment.received.ready payment.received.review rfl valid
  have operation : (item.instruction _ _ _).request.operation =
      .settle position.instrument position.debtor position.creditor quantity :=
    congrArg (fun (entry : ExecutionItem Party Good Port Technology Instrument) => entry.request.operation) identity
  have admitted : (item.interpreter _ _ _).Valid (item.instruction _ _ _).before (item.instruction _ _ _).request := by
    rw [interpreter, identity]
    exact valid
  obtain ⟨movement, read, instrument, debtor⟩ := reads_settlement body item position quantity operation admitted
  obtain ⟨slot, present, address⟩ := Option.map_eq_some_iff.mp named.1
  have sameInstrument : movement.instrument =
      (Finance.slotClaim _ _ _ slot).instrument _ _ _ :=
    instrument.trans (congrArg Prod.fst address).symm
  have sameDebtor : movement.debtor = (Finance.slotClaim _ _ _ slot).debtor _ _ _ :=
    debtor.trans (congrArg Prod.snd address).symm
  have input : body.native.input = source.native.input :=
    ((queued cut settle).advance_parameters.1).trans (Quantities.Execution.endAt_input source plan.script)
  refine ⟨slot, item, present, identity, ?_⟩
  have unit : (familyInputs source body true).law.settlementUnit movement.instrument =
      (familyInputs source body false).law.settlementUnit movement.instrument :=
    congrArg (fun law => law.law.settlementUnit movement.instrument) input
  have rate : (familyInputs source body true).law.settlementRate movement.instrument =
      (familyInputs source body false).law.settlementRate movement.instrument :=
    congrArg (fun law => law.law.settlementRate movement.instrument) input
  dsimp only [familyInputs] at unit rate
  dsimp only [Finance.Family.readReview, familyInputs, familyDepths, familyCounts]
  rw [read]
  dsimp only
  rw [dif_pos sameInstrument, dif_pos sameDebtor, dif_pos unit, dif_pos rate]
  rfl

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Transition.Exchange
