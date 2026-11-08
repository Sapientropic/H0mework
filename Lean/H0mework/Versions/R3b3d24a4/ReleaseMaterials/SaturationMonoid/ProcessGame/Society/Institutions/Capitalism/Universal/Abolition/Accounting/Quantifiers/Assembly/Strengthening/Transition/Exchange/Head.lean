import H0mework.Versions.R3b3d24a4.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Transition.Exchange.Delivery

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Transition.Exchange

open Source.Program Abolition.Root Abolition.Root.Registered Abolition.Root.Registered.Macro
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root
open Innovation.Contribution.Pricing.Root.Runtime
open Abolition.Accounting.Quantifiers.Evolution
open Quantities.Exit.Redemption (sourceLaw)

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]

local notation "C" => Evolving.Epoch.Current (Party := Party) (Good := Good) (Port := Port)
  (Technology := Technology) (Instrument := Instrument)
local notation "Q" => Request Party Good Port Technology Instrument
abbrev nativeAccount (cut : C) := cut.native.actual.actual.account

abbrev HeadAt (source : C) :=
  Epoch.Finance.ActualItem source.native.input source.native.depth source.native.count

theorem nativeAccount_heq_of_eq {before after : C} (same : before = after) :
    HEq (nativeAccount before) (nativeAccount after) := by
  cases same
  rfl

set_option maxHeartbeats 800000 in
theorem the_paid_body_keeps_the_native_account (source : C) (instruction : Q) (ready : Ready source) :
    HEq (nativeAccount (afterBody source instruction)) (nativeAccount (source)) := by
  have complete : ¬ Public.Inquiry.HasWork (queued source instruction).native.frame
      (queued source instruction).native.actual.actual := ready
  have next : afterBody source instruction =
      Evolving.Epoch.Transition.next (queued source instruction) complete :=
    Evolving.Epoch.Current.advance_eq_epoch _ complete
  have kept := (Evolving.Epoch.Transition.body_is_not_replayed_or_financially_reset
    (queued source instruction) complete).1
  have keptInBody : HEq (nativeAccount (Evolving.Epoch.Transition.next (queued source instruction) complete))
      (nativeAccount (queued source instruction)) :=
    heq_of_eq kept
  exact (nativeAccount_heq_of_eq next).trans (keptInBody.trans
    (heq_of_eq (queued_keeps_the_original_control_and_complete_account source instruction).2))

set_option maxHeartbeats 900000 in
theorem the_paid_primitive_has_one_literal_native_consumer
    (source : C) (instruction : Q) (ready : Ready source) (review : ReviewAvailable source)
    (noConsents : instruction.consents = []) (valid : (sourceLaw source).Valid source.raw instruction) :
    ∃ item : HeadAt (afterBody source instruction),
      item.instruction _ _ _ = ⟨0, source.raw, instruction⟩ ∧
      item.interpreter _ _ _ = sourceLaw source ∧
      HEq (nativeAccount (afterNative source instruction))
        ((Epoch.Finance.consume _ _ _ item (nativeAccount (afterBody source instruction))).next _ _ _) := by
  obtain ⟨item, single, present⟩ := the_actual_body_has_its_single_original_native_head
    source instruction ready review noConsents valid
  have complete : ¬ Public.Inquiry.HasWork (queued source instruction).native.frame
      (queued source instruction).native.actual.actual := ready
  have readers : (queued source instruction).executionReader = (queued source instruction).native.reader := by
    funext cursor account
    exact the_available_review_forwards_the_actual_requested_primitive source instruction review
  have original := Clearing.the_actual_raw_owns_its_one_original_native_item
    (queued source instruction).native instruction rfl complete noConsents valid
  let body := afterBody source instruction
  have mapped :
      (Public.Accounting.items body.native.input body.native.depth body.native.count
        body.native.prefixLimit body.native.renewalLimit body.native.oldPast body.native.start).map
        (Epoch.Finance.ActualItem.instruction body.native.input body.native.depth body.native.count) =
        [⟨0, source.raw, instruction⟩] := by
    dsimp only [body, afterBody]
    rw [Evolving.Epoch.Current.advance_eq_epoch _ complete]
    change (Public.Accounting.items source.native.input source.native.depth source.native.count
      source.native.prefixLimit source.native.renewalLimit source.native.oldPast
      (Factory.Direct.selectedStart (queued source instruction).native.full
        (queued source instruction).native.sourceActual (queued source instruction).executionReader)).map _ = _
    rw [readers]
    exact original
  have actual : item ∈ Public.Accounting.items body.native.input body.native.depth body.native.count
      body.native.prefixLimit body.native.renewalLimit body.native.oldPast body.native.start := by
    rw [single]
    exact List.mem_cons_self
  have interpreter : item.interpreter _ _ _ = sourceLaw body := by
    unfold Public.Accounting.items Epoch.Finance.inventory at actual
    obtain ⟨position, sourceItem⟩ := List.mem_ofFn.mp actual
    rw [← sourceItem]
    rfl
  have input : body.native.input = source.native.input :=
    (queued source instruction).advance_parameters.1
  rw [single, List.map_singleton] at mapped
  exact ⟨item, List.singleton_inj.mp mapped,
    interpreter.trans (congrArg Physical.Public.interpreter input),
    native_head_uses_the_original_admission_or_consumption _ item present⟩

theorem a_paid_transfer_keeps_the_literal_native_debt_account
    (source : C) (instruction : Q) (ready : Ready source) (review : ReviewAvailable source)
    (noConsents : instruction.consents = []) (valid : (sourceLaw source).Valid source.raw instruction)
    (sender recipient : Party) (goods : Bundle Good)
    (transfer : instruction.operation = .transfer sender recipient goods) :
    HEq (nativeAccount (afterNative source instruction)) (nativeAccount (source)) := by
  obtain ⟨item, identity, interpreter, consumed⟩ :=
    the_paid_primitive_has_one_literal_native_consumer source instruction ready review noConsents valid
  have operation := (congrArg (fun original => original.request.operation) identity).trans transfer
  have issued : Epoch.Finance.readNewClaim _ _ _ item = none := by
    cases found : Epoch.Finance.readNewClaim _ _ _ item with
    | none => rfl
    | some fresh =>
      have same := Epoch.Finance.readNewClaim_origin _ _ _ item fresh found
      have impossible := fresh.operation
      rw [same, operation] at impossible
      cases impossible
  have moved : Epoch.Finance.readMovement _ _ _ item = none := by
    cases found : Epoch.Finance.readMovement _ _ _ item with
    | none => rfl
    | some movement =>
      have impossible := movement.operation
      cases kind : movement.kind <;> rw [operation, kind] at impossible <;> cases impossible
  have paid : (item.interpreter _ _ _).Valid (item.instruction _ _ _).before (item.instruction _ _ _).request := by
    rw [interpreter, identity]
    exact valid
  have retained : (Epoch.Finance.consume _ _ _ item (nativeAccount (afterBody source instruction))).next _ _ _ =
      (nativeAccount (afterBody source instruction)) := by
    unfold Epoch.Finance.consume
    rw [dif_neg (not_not_intro paid)]
    split
    · rename_i fresh found
      rw [issued] at found
      cases found
    · rw [moved]
      rfl
  exact consumed.trans ((heq_of_eq retained).trans (the_paid_body_keeps_the_native_account source instruction ready))

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Transition.Exchange
