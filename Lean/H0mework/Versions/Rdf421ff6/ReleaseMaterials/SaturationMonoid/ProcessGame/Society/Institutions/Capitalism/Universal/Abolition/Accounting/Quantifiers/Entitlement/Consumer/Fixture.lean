import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Entitlement.Source.Demand
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Clearing.Account

set_option autoImplicit false
set_option maxRecDepth 8192

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Entitlement.Consumer

open Universal.Source.Program Universal.Root

def law : RawLaw Bool Bool Bool Unit Unit where
  technique := fun _ _ => ⟨[],[],[],[]⟩
  controller := fun _ _ => true
  allowed := fun _ port actor => if port then actor else true
  stockPort := fun _ _ _ => false
  revisionPort := fun _ => true
  revisionCost := fun _ _ => []
  settlementUnit := fun _ => false
  settlementRate := fun _ => 1
  issuerPort := fun _ => false
  necessities := fun _ _ => [(true,1)]
  mandatoryMaintenance := fun _ _ => []
  duration := fun _ => 1

def initial : RawCurrent Bool Bool Unit Unit where
  stock := fun actor good => if good then 3 else if actor then 1 else 99
  claims := fun _ _ _ => 0
  technology := ()
  clock := 0
  round := 0

def issued : Request Bool Bool Bool Unit Unit := ⟨false,[],false,[],.issue () false true 1⟩
def advanced : Request Bool Bool Bool Unit Unit := ⟨true,[],false,[],.transfer true false [(false,1)]⟩
def need : Request Bool Bool Bool Unit Unit := ⟨false,[true],false,[true],.use false [(true,1)] .necessity⟩
def taking : Request Bool Bool Bool Unit Unit := ⟨true,[],false,[true],.transfer false true [(false,100)]⟩
def retained : Request Bool Bool Bool Unit Unit := ⟨true,[],false,[],.present⟩
def word := [issued,advanced,need,taking,retained]
def before := law.next initial []

def input : ProgrammeSource.Input Bool Bool Bool Unit Unit where
  law := law
  initial := initial
  instructions := word
def window : Source.Window (Party := Bool) (Good := Bool) (Port := Bool) (Technology := Unit) (Instrument := Unit) :=
  ⟨input,0,15⟩

def takingItem := Universal.Source.ProgrammeControl.itemAt law before word ⟨3,by decide +kernel⟩

def takingLeg : Source.Leg law before word :=
  ((Source.readLegs law before word takingItem).head?).get (by decide +kernel)

theorem taking_quantity_is_the_actual_hundred : takingLeg.quantity = 100 := by decide +kernel

theorem the_original_word_has_a_real_advance_and_old_claim :
    (law.next before word).claims () false true = 1 ∧
      (law.next before word).stock false false = 0 ∧ (law.next before word).stock true false = 100 := by
  decide +kernel

theorem the_source_taking_is_an_actual_control_return : Source.ControlledReturn takingLeg := by
  constructor <;> decide +kernel

theorem the_victim_is_not_deleted_from_the_quantity :
    (law.step takingLeg.item.val.before takingLeg.item.val.request).stock takingLeg.sender takingLeg.good =
      takingLeg.item.val.before.stock takingLeg.sender takingLeg.good - 100 := by
  rw [← taking_quantity_is_the_actual_hundred]
  exact takingLeg.the_original_victim_and_recipient_have_opposite_actual_stock_changes.1

end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Entitlement.Consumer
