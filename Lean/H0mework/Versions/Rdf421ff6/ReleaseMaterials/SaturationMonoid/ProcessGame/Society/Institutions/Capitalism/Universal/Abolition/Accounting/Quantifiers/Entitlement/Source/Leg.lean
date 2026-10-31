import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Source.Program.MarketReadout
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Source.ProgrammeControl.Kernel.Discovery.ReturnIncidence
import Mathlib.Algebra.BigOperators.Group.List.Basic

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Entitlement.Source

open Universal.Source.Program Universal.Source.ProgrammeControl

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  (law : RawLaw Party Good Port Technology Instrument)
  (before : RawCurrent Party Good Technology Instrument)
  (word : RawEvent Party Good Port Technology Instrument)

/-- One occurred transfer and one original material unit. Duplicate bundle
entries are aggregated before they can become a responsibility address. -/
structure Leg where
  private mk ::
  item : OriginalItem law before word
  sender : Party
  recipient : Party
  goods : Bundle Good
  good : Good
  operation : item.val.request.operation = .transfer sender recipient goods
  accepted : law.Valid item.val.before item.val.request
  distinct : sender ≠ recipient
  positive : 0 < amount Good goods good

namespace Leg
variable {law before word} (leg : Leg law before word)

def quantity : ℚ := amount Good leg.goods leg.good

omit [DecidableEq Port] in
theorem quantity_positive : 0 < leg.quantity := leg.positive

omit [DecidableEq Port] in
private theorem own_locate (party : Party) (goods : Bundle Good) (good : Good) :
    flowAt (locate party goods) party good = amount Good goods good := by
  simp only [flowAt,amount,locate,List.map_map]
  apply congrArg List.sum
  apply List.map_congr_left
  intro entry _
  simp only [Function.comp_apply,Prod.mk.injEq,true_and]

omit [DecidableEq Port] in
private theorem other_locate (sender recipient : Party) (different : sender ≠ recipient)
    (goods : Bundle Good) (good : Good) : flowAt (locate sender goods) recipient good = 0 := by
  unfold flowAt amount locate
  rw [List.map_map]
  apply List.sum_eq_zero
  intro quantity member
  obtain ⟨entry,_inside,rfl⟩ := List.mem_map.mp member
  simp [Function.comp_apply,Prod.mk.injEq,different]

omit [DecidableEq Port] in
theorem original_debit_and_credit :
    flowAt (law.actualDebit leg.item.val.before leg.item.val.request) leg.sender leg.good = leg.quantity ∧
    flowAt (law.actualCredit leg.item.val.before leg.item.val.request) leg.recipient leg.good = leg.quantity := by
  simp only [RawLaw.actualDebit,RawLaw.actualCredit,if_pos leg.accepted,
    RawLaw.debit,RawLaw.credit,leg.operation]
  exact ⟨own_locate _ _ _,own_locate _ _ _⟩

omit [DecidableEq Port] in
theorem the_original_victim_and_recipient_have_opposite_actual_stock_changes :
    (law.step leg.item.val.before leg.item.val.request).stock leg.sender leg.good =
      leg.item.val.before.stock leg.sender leg.good - leg.quantity ∧
    (law.step leg.item.val.before leg.item.val.request).stock leg.recipient leg.good =
      leg.item.val.before.stock leg.recipient leg.good + leg.quantity := by
  have debit := leg.original_debit_and_credit.1
  have credit := leg.original_debit_and_credit.2
  have noVictimCredit : flowAt (law.actualCredit leg.item.val.before leg.item.val.request) leg.sender leg.good = 0 := by
    simp only [RawLaw.actualCredit,if_pos leg.accepted,RawLaw.credit,leg.operation]
    exact other_locate _ _ (Ne.symm leg.distinct) _ _
  have noRecipientDebit : flowAt (law.actualDebit leg.item.val.before leg.item.val.request) leg.recipient leg.good = 0 := by
    simp only [RawLaw.actualDebit,if_pos leg.accepted,RawLaw.debit,leg.operation]
    exact other_locate _ _ leg.distinct _ _
  have victim := law.material_step_balance leg.item.val.before leg.item.val.request leg.sender leg.good
  have recipient := law.material_step_balance leg.item.val.before leg.item.val.request leg.recipient leg.good
  rw [debit,noVictimCredit] at victim
  rw [credit,noRecipientDebit] at recipient
  constructor <;> linarith

end Leg

def readLegs (item : OriginalItem law before word) : List (Leg law before word) :=
  match operation : item.val.request.operation with
  | .transfer sender recipient goods =>
      if accepted : law.Valid item.val.before item.val.request then
        if distinct : sender ≠ recipient then
          (goods.map Prod.fst).dedup.filterMap fun good =>
            if positive : 0 < amount Good goods good then
              some ⟨item,sender,recipient,goods,good,operation,accepted,distinct,positive⟩
            else none
        else []
      else []
  | _ => []

def legs : List (Leg law before word) :=
  (law.rawItems before word).attach.flatMap (readLegs law before word)

end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Entitlement.Source
