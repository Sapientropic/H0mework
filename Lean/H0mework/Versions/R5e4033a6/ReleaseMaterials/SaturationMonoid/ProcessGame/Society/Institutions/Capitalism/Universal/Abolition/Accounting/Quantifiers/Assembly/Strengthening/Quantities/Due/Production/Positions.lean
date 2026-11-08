import H0mework.Versions.R3b3d24a4.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Due.Production.Native
import H0mework.Versions.R5e4033a6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Due.Service.Trace
import H0mework.Versions.R3b3d24a4.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Due.Service.Incidence
import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Execution.Witness

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Due.Production

open Source.Program Abolition.Root Abolition.Root.Registered
open Innovation.Contribution.Pricing.Root.Runtime (Trace)
open Abolition.Accounting.Quantifiers.Evolution.Ingress.Joint.Material.Runtime.Retirement.CompleteLedger.Primitive
  (ordinary_steps_preserve_the_original_clock_and_round)

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]

local notation "C" => Evolving.Epoch.Current (Party := Party) (Good := Good) (Port := Port)
  (Technology := Technology) (Instrument := Instrument)
local notation "Word" => RawEvent Party Good Port Technology Instrument
local notation "Law" => RawLaw Party Good Port Technology Instrument

omit [DecidableEq Port] in
private theorem raw_items_keep_the_opening_clock (law : Law) (source : RawCurrent Party Good Technology Instrument)
    (index : Nat) (word : Word) :
    ∀ item ∈ (law.execute source index word).items, item.before.clock = source.clock := by
  induction word generalizing source index with
  | nil => simp [RawLaw.execute]
  | cons request tail ih =>
    intro item listed
    change item ∈ ⟨index, source, request⟩ :: _ at listed
    rcases List.mem_cons.mp listed with rfl | later
    · rfl
    · exact (ih _ _ item later).trans (ordinary_steps_preserve_the_original_clock_and_round law source request).1

theorem paid_word_length {source target : C} {word : Word} (paid : Trace source word target) :
    (Execution.inventory source (Execution.primitiveScript word)).length = word.length := by
  rw [Execution.primitive_inventory paid 0, List.length_map, RawLaw.inventory_length]

def nativePosition {source target : C} {word : Word} (paid : Trace source word target) (position : Fin word.length) :
    Service.Ordinal source (Execution.primitiveScript word) :=
  Fin.cast (paid_word_length paid).symm position

theorem nativePosition_is_injective {source target : C} {word : Word} (paid : Trace source word target) :
    Function.Injective (nativePosition paid) :=
  fun left right same => by
    have position := congrArg (fun (ordinal : Service.Ordinal source (Execution.primitiveScript word)) =>
      ordinal.val) same
    exact Fin.ext position

/-- Every planned use acquires its own committing ordinal in the actual
primitive suffix. The original signing and both clocks survive unchanged. -/
theorem the_native_position_carries_the_exact_submitted_request
    {source target : C} {word : Word} (paid : Trace source word target) (position : Fin word.length) :
    let actual := Execution.timedAt source (Execution.primitiveScript word) (nativePosition paid position)
    actual.1.request = word[position.val] ∧ actual.1.before.clock = source.raw.clock ∧
      actual.2 = source.raw.clock ∧ (interpreter source).Valid actual.1.before actual.1.request := by
  let law := interpreter source
  let items := (law.execute source.raw 0 word).items
  have fits : position.val < items.length := by
    rw [RawLaw.inventory_length]
    exact position.isLt
  let item := items[position.val]
  let script := Execution.primitiveScript word
  let ordinal := nativePosition paid position
  let receipt := Execution.timedAt source script ordinal
  have actual : some receipt = some ({item with index := 0}, source.raw.clock) := by
    calc
      some receipt = (Execution.timedInventory source script)[position.val]? := by
        unfold receipt Execution.timedAt
        exact (List.getElem?_eq_getElem _).symm
      _ = _ := by
        rw [Service.timed_primitives_are_the_original_material_at_the_same_clock paid, List.getElem?_map]
        change items[position.val]?.map _ = _
        rw [List.getElem?_eq_getElem fits]
        rfl
  have stamp := Option.some.inj actual
  have request : item.request = word[position.val] := by
    have same := congrArg (fun requests : Word => requests[position.val]?)
      (law.inventory_requests_exact source.raw 0 word)
    rw [List.getElem?_map, List.getElem?_eq_getElem fits, List.getElem?_eq_getElem position.isLt] at same
    exact Option.some.inj same
  have present : item ∈ items := List.getElem_mem _
  change receipt.1.request = _ ∧ receipt.1.before.clock = _ ∧ receipt.2 = _ ∧
    law.Valid receipt.1.before receipt.1.request
  rw [stamp]
  exact ⟨request, raw_items_keep_the_opening_clock law source.raw 0 word item present, rfl,
    Execution.admitted_items_of_original_trace paid 0 item present⟩

end

end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Due.Production
