import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Clearing.Account

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Clearing

open Source.Program
open Abolition.Completion.Actual.Dividend

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Instrument]

private theorem located_amount (owner person : Party) (goods : Bundle Good) (good : Good) :
    flowAt (locate owner goods) person good = if owner = person then amount Good goods good else 0 := by
  by_cases same : owner = person
  · subst owner
    unfold flowAt amount locate
    simp only [List.map_map]
    apply congrArg List.sum
    apply List.map_congr_left
    intro entry _
    simp only [Function.comp_apply,Prod.mk.injEq,true_and]
  · simp [flowAt,amount,locate,List.map_map,Function.comp_def,Prod.mk.injEq,same]

omit [DecidableEq Instrument] in
theorem the_original_transfer_has_its_exact_material_unit_restriction
    (law : RawLaw Party Good Port Technology Instrument)
    (initial : RawCurrent Party Good Technology Instrument)
    (request : Request Party Good Port Technology Instrument)
    (victim controller : Party) (goods : Bundle Good) (good : Good)
    (operation : request.operation = .transfer victim controller goods)
    (accepted : law.Valid initial request) :
    (Financial.fullChange law initial request).filter (fun key => key.2 = good) =
      Finsupp.single (controller,good) (amount Good goods good) -
        Finsupp.single (victim,good) (amount Good goods good) := by
  have effect : Financial.fullChange law initial request =
      Financial.flowVector (locate controller goods) - Financial.flowVector (locate victim goods) := by
    simp only [Financial.fullChange,Financial.materialChange,Financial.claimChange,
      RawLaw.actualDebit,RawLaw.actualCredit,if_pos accepted]
    simp [Financial.rawClaimChange,RawLaw.credit,RawLaw.debit,operation]
  rw [effect]
  ext key
  rcases key with ⟨person,unit⟩
  by_cases same : unit = good
  · subst unit
    simp only [Finsupp.filter_apply,Finsupp.sub_apply,Financial.flowVector_apply,
      located_amount,Finsupp.single_apply,Prod.mk.injEq,eq_self,and_true,ite_true]
  · simp [same,Prod.mk.injEq]

/-- The original transfer's selected material leg and its actual return
cancel for every coalition. The real payment retires the old finite right
and is fully neutral, even when its settlement unit is a different good. -/
theorem every_coalition_has_zero_full_net_change_from_the_original_leg_and_actual_clearing
    (law : RawLaw Party Good Port Technology Instrument)
    (initial current : RawCurrent Party Good Technology Instrument)
    (request : Request Party Good Port Technology Instrument)
    (victim controller : Party) (goods : Bundle Good) (good : Good)
    (operation : request.operation = .transfer victim controller goods)
    (accepted : law.Valid initial request) (instrument : Instrument) (principal : ℚ)
    (resources : Resources law current controller victim good (amount Good goods good) instrument principal)
    (members : Party → Bool) (unit : Good) :
    Coalition.read members unit
      ((Financial.fullChange law initial request).filter (fun key => key.2 = good) +
        Profit.fullIncome (PublicFunction.physicalLaw law)
          ((PublicFunction.physicalLaw law).rawItems current
            (word law controller victim good (amount Good goods good) instrument principal))) = 0 := by
  rw [the_original_transfer_has_its_exact_material_unit_restriction law initial request victim controller goods good operation accepted,
    the_full_actual_clearing_income_is_exactly_the_material_return law current controller victim good
      (amount Good goods good) instrument principal resources]
  have cancelled :
      (Finsupp.single (controller,good) (amount Good goods good) - Finsupp.single (victim,good) (amount Good goods good)) +
        (Finsupp.single (victim,good) (amount Good goods good) - Finsupp.single (controller,good) (amount Good goods good)) =
      (0 : Profit.Vector (Party := Party) (Good := Good)) := by abel
  rw [cancelled,map_zero]

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Clearing
