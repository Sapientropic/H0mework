import H0mework.Versions.R5e4033a6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Recovery.PersonTime.Observation
import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Consumers.CofinalClock

set_option autoImplicit false
set_option maxRecDepth 8192

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Recovery.PersonTime.Consumers.OriginalLife

open Source.Program Abolition.Root Abolition.Root.Registered
open Quantities.Consumers (lifeSource firstPaidPeriod checked_living_period)
open Innovation.Contribution.Pricing.Consumers.Actual (life lifeWord source_ready source_review)
open Innovation.Contribution.Pricing.Root.Runtime (normalise)

noncomputable section

private abbrev law := Physical.Public.interpreter lifeSource.native.input

private def items : List (ExecutionItem Bool Bool Bool Unit Unit) :=
  [⟨0, lifeSource.raw, life false⟩, ⟨1, law.step lifeSource.raw (life false), life true⟩]

private theorem inventory_eq : Execution.inventory lifeSource firstPaidPeriod = items :=
  (Execution.inventory_of_the_original_period_and_accounting lifeSource lifeWord source_ready
    source_review checked_living_period).trans (by rfl)

def index (person : Bool) : Nat := if person then 1 else 0

def slot (person : Bool) : Ordinal lifeSource firstPaidPeriod :=
  ⟨index person, by rw [inventory_eq]; cases person <;> decide⟩

private theorem actual_item (person : Bool) :
    (Execution.timedAt lifeSource firstPaidPeriod (slot person)).1 =
      if person then ⟨1, law.step lifeSource.raw (life false), life true⟩
      else ⟨0, lifeSource.raw, life false⟩ := by
  rw [Execution.timedAt_is_the_same_original_item]
  apply Option.some.inj
  calc
    some ((Execution.inventory lifeSource firstPaidPeriod).get (slot person)) =
        (Execution.inventory lifeSource firstPaidPeriod)[(slot person).val]? :=
      (List.getElem?_eq_getElem (slot person).isLt).symm
    _ = _ := by
      change (Execution.inventory lifeSource firstPaidPeriod)[index person]? = _
      rw [inventory_eq]
      cases person <;> rfl

theorem own_action (person : Bool) : ownAction lifeSource firstPaidPeriod (slot person) person := by
  refine ⟨?_, ?_⟩
  · rw [actual_item]
    cases person <;> rfl
  · apply (checked_living_period.2.2.1 _ ?_).1
    change (Execution.timedAt lifeSource firstPaidPeriod (slot person)).1 ∈
      law.rawItems lifeSource.raw (normalise lifeWord)
    rw [← Execution.inventory_of_the_original_period_and_accounting lifeSource lifeWord source_ready
      source_review checked_living_period, Execution.timedAt_is_the_same_original_item]
    exact List.get_mem _ _

theorem starts_at_original_clock (person : Bool) :
    opensAt lifeSource firstPaidPeriod (slot person) = lifeSource.raw.clock := by
  unfold opensAt
  rw [actual_item]
  cases person
  · rfl
  · change (law.step lifeSource.raw (life false)).clock = lifeSource.raw.clock
    unfold RawLaw.step
    split <;> rfl

theorem commits_at_original_clock (person : Bool) :
    commitsAt lifeSource firstPaidPeriod (slot person) =
      (Execution.endAt lifeSource firstPaidPeriod).raw.clock := by
  let proposal : Option (Compile.RawInput Bool Bool Bool Unit Unit) := some (.execute lifeWord)
  let paid := Execution.next lifeSource proposal
  have terminal : Execution.endAt lifeSource firstPaidPeriod =
      Execution.endAt paid (Execution.drain paid) := rfl
  obtain ⟨_, same, empty, _, _⟩ :=
    Execution.the_first_exhausted_native_cut_is_the_original_paid_drain paid
  have noItems : Execution.timedInventory paid (Execution.drain paid) = [] :=
    List.map_eq_nil_iff.mp ((Execution.timedInventory_is_the_original_inventory paid _).trans empty)
  have occurred := List.get_mem (Execution.timedInventory lifeSource firstPaidPeriod)
    ⟨(slot person).val, by
      rw [← List.length_map Prod.fst, Execution.timedInventory_is_the_original_inventory]
      exact (slot person).isLt⟩
  change Execution.timedAt lifeSource firstPaidPeriod (slot person) ∈
    Execution.timedInventory lifeSource ([proposal] ++ Execution.drain paid) at occurred
  rw [Execution.timedInventory_append, show Execution.endAt lifeSource [proposal] = paid from rfl,
    noItems, List.append_nil] at occurred
  simp only [Execution.timedInventory, List.append_nil] at occurred
  obtain ⟨item, _, actual⟩ := List.mem_map.mp occurred
  change (item, paid.raw.clock) = Execution.timedAt lifeSource firstPaidPeriod (slot person) at actual
  unfold commitsAt
  rw [← actual, terminal, same]

end

end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Recovery.PersonTime.Consumers.OriginalLife
