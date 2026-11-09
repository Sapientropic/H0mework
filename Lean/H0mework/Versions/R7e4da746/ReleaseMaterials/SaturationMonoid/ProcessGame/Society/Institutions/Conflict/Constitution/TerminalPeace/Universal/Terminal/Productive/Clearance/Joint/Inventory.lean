import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.Productive.Clearance.Payment

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.Clearance.Joint

open Capitalism.Universal.Source.Program
open Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Execution (endAt)
open Reparation.Actual (Occurrence Script)

noncomputable section

variable {Party Good Port Technology Instrument Community : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Instrument] [DecidableEq Community]
  {seed : Conflict.Root.Cut Party Good Port Technology Instrument} {community : Party → Community}
  (loss : Reparation.Actual.Occurrence seed community)

local notation "Word" => Script Party Good Port Technology Instrument
local notation "Raw" => RawCurrent Party Good Technology Instrument

/-- An inventory read keeps both the original visit and, when applicable,
the ordinal of the actual material instruction. -/
structure InventoryRead (Party Good Technology Instrument : Type) where
  visit : Nat
  item : Option (Nat × Bool)
  raw : RawCurrent Party Good Technology Instrument

def inventoryTrace (word : Word) : List (InventoryRead Party Good Technology Instrument) :=
  (List.range (word.length + 1)).flatMap fun visit =>
    let before := endAt seed (Occurrence.history loss ++ word.take visit)
    ⟨visit, none, before.raw⟩ ::
      (if inside : visit < word.length then
        (Boundary.Actual.items before word[visit]).flatMap fun item =>
          [⟨visit, some (item.index, false), item.before⟩,
            ⟨visit, some (item.index, true), (Boundary.Actual.materialLaw before).step item.before item.request⟩]
      else [])

def ProtectedThrough (reserve : Party → Good → ℚ) (word : Word) : Prop :=
  ∀ cut ∈ inventoryTrace loss word, ∀ person good, reserve person good ≤ cut.raw.stock person good

structure InventoryShortage (reserve : Party → Good → ℚ) (word : Word) where
  position : Fin (inventoryTrace loss word).length
  person : Party
  good : Good
  short : ((inventoryTrace loss word)[position.val]'position.isLt).raw.stock person good < reserve person good
  earlier : ∀ i : Fin (inventoryTrace loss word).length, i < position →
    ∀ p g, reserve p g ≤ ((inventoryTrace loss word)[i.val]'i.isLt).raw.stock p g

def InventoryShortage.address {reserve : Party → Good → ℚ} {word : Word}
    (shortage : InventoryShortage loss reserve word) :=
  let cut := (inventoryTrace loss word)[shortage.position]
  (cut.visit, cut.item, shortage.person, shortage.good)

def InventoryShortage.amount {reserve : Party → Good → ℚ} {word : Word}
    (shortage : InventoryShortage loss reserve word) : ℚ :=
  reserve shortage.person shortage.good -
    (inventoryTrace loss word)[shortage.position].raw.stock shortage.person shortage.good

theorem InventoryShortage.amount_pos {reserve : Party → Good → ℚ} {word : Word}
    (shortage : InventoryShortage loss reserve word) :
    0 < shortage.amount loss :=
  sub_pos.mpr shortage.short

theorem InventoryShortage.refutes {reserve : Party → Good → ℚ} {word : Word}
    (shortage : InventoryShortage loss reserve word) :
    ¬ ProtectedThrough loss reserve word :=
  fun safe => (not_le_of_gt shortage.short)
    (safe _ (List.getElem_mem shortage.position.isLt) shortage.person shortage.good)

def inspectInventory (reserve : Party → Good → ℚ) (word : Word) :
    InventoryShortage loss reserve word ⊕ PLift (ProtectedThrough loss reserve word) := by
  classical
  by_cases failed : ∃ n, ∃ inside : n < (inventoryTrace loss word).length,
      ∃ person good, ((inventoryTrace loss word)[n]'inside).raw.stock person good < reserve person good
  · let n := Nat.find failed
    have first := Nat.find_spec failed
    let inside := Classical.choose first
    let pair := Classical.choose_spec first
    let person := Classical.choose pair
    let good := Classical.choose (Classical.choose_spec pair)
    refine .inl ⟨⟨n, inside⟩, person, good, Classical.choose_spec (Classical.choose_spec pair), ?_⟩
    intro i earlier p g
    exact le_of_not_gt (fun short => Nat.find_min failed earlier ⟨i.isLt, p, g, short⟩)
  · refine .inr ⟨?_⟩
    intro cut present person good
    obtain ⟨n, inside, rfl⟩ := List.getElem_of_mem present
    exact le_of_not_gt (fun short => failed ⟨n, inside, person, good, short⟩)

theorem every_literal_opening_is_in_the_inventory_trace (word : Word)
    (ordinal : Nat) (within : ordinal ≤ word.length) :
    (⟨ordinal, none, prefixRaw loss (word.take ordinal)⟩ : InventoryRead Party Good Technology Instrument) ∈
      inventoryTrace loss word := by
  apply List.mem_flatMap.mpr
  exact ⟨ordinal, List.mem_range.mpr (Nat.lt_succ_of_le within), List.mem_cons_self⟩

theorem ProtectedThrough.atEnd {reserve : Party → Good → ℚ} {word : Word}
    (safe : ProtectedThrough loss reserve word) (person : Party) (good : Good) :
    reserve person good ≤ (prefixRaw loss word).stock person good := by
  have seen := every_literal_opening_is_in_the_inventory_trace loss word word.length le_rfl
  rw [List.take_length] at seen
  exact safe _ seen person good

end

end SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.Clearance.Joint
