import H0mework.Versions.R3b3d24a4.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Due.Service.Incidence
import Mathlib.Data.List.Dedup

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Due.Service

open Source.Program Abolition.Root Abolition.Root.Registered PublicFunction

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  {TaskId : Type*} [DecidableEq TaskId]

local notation "C" => Evolving.Epoch.Current (Party := Party) (Good := Good) (Port := Port)
  (Technology := Technology) (Instrument := Instrument)
local notation "Script" => List (Option (Compile.RawInput Party Good Port Technology Instrument))
local notation "Task" => PublicTaskSpec Party Good

private def listed {A : Type*} [DecidableEq A] {carrier : Finset A}
    (original : List A) (same : original.toFinset = carrier) : List { entry // entry ∈ carrier } :=
  original.dedup.attach.map fun entry =>
    ⟨entry.val, same ▸ List.mem_toFinset.mpr (List.mem_dedup.mp entry.property)⟩

private theorem listed_covers {A : Type*} [DecidableEq A] {carrier : Finset A}
    (original : List A) (same : original.toFinset = carrier) (entry : { entry // entry ∈ carrier }) :
    entry ∈ listed original same := by
  have found : entry.val ∈ original.toFinset := same.symm ▸ entry.property
  let attached : { x // x ∈ original.dedup } := ⟨entry.val, List.mem_dedup.mpr (List.mem_toFinset.mp found)⟩
  apply List.mem_map.mpr
  refine ⟨attached, List.mem_attach _ _, ?_⟩
  exact Subtype.ext rfl

def slotList (ids : Finset TaskId) (task : TaskId → Task) (ordered : List TaskId)
    (same : ordered.toFinset = ids) : List (Slot ids task) :=
  (listed ordered same).flatMap fun id =>
    (List.finRange (task id.val).slots.length).map fun ordinal => ⟨id, ordinal⟩

omit [DecidableEq Good] in
theorem slotList_covers (ids : Finset TaskId) (task : TaskId → Task) (ordered : List TaskId)
    (same : ordered.toFinset = ids) (slot : Slot ids task) :
    slot ∈ slotList ids task ordered same := by
  obtain ⟨id, ordinal⟩ := slot
  apply List.mem_flatMap.mpr
  exact ⟨id, listed_covers ordered same id, List.mem_map.mpr ⟨ordinal, by simp, rfl⟩⟩

def needList (ids : Finset TaskId) (task : TaskId → Task) (ordered : List TaskId)
    (same : ordered.toFinset = ids) : List (Need ids task) :=
  (slotList ids task ordered same).flatMap fun slot =>
    (listed (slot.spec.goods.map Prod.fst) (rfl : (slot.spec.goods.map Prod.fst).toFinset = slot.goods)).map
      fun good => ⟨slot, good⟩

theorem needList_covers (ids : Finset TaskId) (task : TaskId → Task) (ordered : List TaskId)
    (same : ordered.toFinset = ids) (line : Need ids task) :
    line ∈ needList ids task ordered same := by
  obtain ⟨slot, good⟩ := line
  apply List.mem_flatMap.mpr
  exact ⟨slot, slotList_covers ids task ordered same slot,
    List.mem_map.mpr ⟨good, listed_covers _ rfl good, rfl⟩⟩

def goodList (ids : Finset TaskId) (task : TaskId → Task) (ordered : List TaskId)
    (same : ordered.toFinset = ids) : List Good :=
  (slotList ids task ordered same).flatMap fun slot => slot.spec.goods.map Prod.fst

theorem goodList_is_the_original_finite_support (ids : Finset TaskId) (task : TaskId → Task)
    (ordered : List TaskId) (same : ordered.toFinset = ids) :
    (goodList ids task ordered same).toFinset = goods ids task := by
  ext good
  simp only [goodList, List.mem_toFinset, List.mem_flatMap, goods, Finset.mem_biUnion,
    Finset.mem_univ, true_and, Slot.goods]
  exact ⟨fun ⟨slot, _, present⟩ => ⟨slot, present⟩,
    fun ⟨slot, present⟩ => ⟨slot, slotList_covers _ _ _ _ slot, present⟩⟩

variable [DecidableEq Party]

def supplyList (source : C) (script : Script) (ids : Finset TaskId) (task : TaskId → Task)
    (ordered : List TaskId) (same : ordered.toFinset = ids) : List (Supply source script ids task) :=
  let originalGoods := listed (goodList ids task ordered same) (goodList_is_the_original_finite_support _ _ _ _)
  (List.finRange (Execution.inventory source script).length).flatMap fun ordinal =>
    originalGoods.map fun good => (ordinal, good)

theorem supplyList_covers (source : C) (script : Script) (ids : Finset TaskId) (task : TaskId → Task)
    (ordered : List TaskId) (same : ordered.toFinset = ids) (receipt : Supply source script ids task) :
    receipt ∈ supplyList source script ids task ordered same := by
  obtain ⟨ordinal, good⟩ := receipt
  apply List.mem_flatMap.mpr
  exact ⟨ordinal, by simp, List.mem_map.mpr ⟨good, listed_covers _ _ good, rfl⟩⟩

end

end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Due.Service
