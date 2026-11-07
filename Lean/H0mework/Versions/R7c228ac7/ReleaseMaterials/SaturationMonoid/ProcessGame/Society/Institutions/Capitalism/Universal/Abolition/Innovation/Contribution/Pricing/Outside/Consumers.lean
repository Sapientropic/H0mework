import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Innovation.Contribution.Pricing.Outside.Complete

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Innovation.Contribution.Pricing.Outside.Consumers

open Source.Program

def law : RawLaw Unit Unit Unit Unit Unit where
  technique := fun _ _ => ⟨[],[],[],[]⟩
  controller := fun _ _ => ()
  allowed := fun _ _ _ => true
  stockPort := fun _ _ _ => ()
  revisionPort := fun _ => ()
  revisionCost := fun _ _ => []
  settlementUnit := fun _ => ()
  settlementRate := fun _ => 1
  issuerPort := fun _ => ()
  necessities := fun _ _ => [((),1)]
  mandatoryMaintenance := fun _ _ => []
  duration := fun _ => 1

def current (stock : ℚ) : RawCurrent Unit Unit Unit Unit where
  stock := fun _ _ => stock
  claims := fun _ _ _ => 0
  technology := ()
  clock := 0
  round := 0

def pay : Request Unit Unit Unit Unit Unit := ⟨(),[],(),[],.use () [((),1)] .necessity⟩

def input : Root.ProgrammeSource.Input Unit Unit Unit Unit Unit where
  law := law
  initial := current 1
  instructions := [pay]

def amountAt (stock : ℚ) : Option ℚ :=
  match sourceOutside input (current stock) [()] 1 () () with
  | some result => some result.amount
  | none => none

theorem a_paid_outside_option_can_have_a_strictly_negative_complete_value :
    amountAt 1 = some (-1) := by decide +kernel

theorem an_unpaid_life_bill_does_not_generate_a_free_zero_outside_option :
    amountAt 0 = none := by decide +kernel

theorem an_empty_action_budget_does_not_silently_remove_standing :
    (sourceOutside input (current 1) [()] 0 () ()).isSome = false := by decide +kernel

end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Innovation.Contribution.Pricing.Outside.Consumers
