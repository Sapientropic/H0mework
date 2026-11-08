import H0mework.Versions.R5e4033a6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Due.Service.Mixed.Source
import Mathlib.Data.List.MinMax
import Mathlib.Data.List.Sublists

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Due.Service.Mixed

open Source.Program Abolition.Root Abolition.Root.Registered PublicFunction
open _root_.SaturationMonoid.ProcessGame.Society.UBI.Capacity

section FiniteDeficiency

variable {L R : Type*} [DecidableEq L] [DecidableEq R]

private def countDeficit (geom : CanonicalBipartiteFeasibility L R) (group : Finset L) : Nat :=
  group.card - (geom.rightCarrier.filter fun item => ∃ slot ∈ group, eligibility geom slot item = true).card

omit [DecidableEq L] [DecidableEq R] in
private theorem countDeficit_is_original (geom : CanonicalBipartiteFeasibility L R) (group : Finset L) :
    countDeficit geom group = deficit geom group := by
  have equal : (geom.rightCarrier.filter fun item => ∃ slot ∈ group, eligibility geom slot item = true) =
      neighbours geom group := by
    ext item
    simp only [Finset.mem_filter, eligibility_eq_true, neighbour_iff_original_compatible_edge]
    exact ⟨fun ⟨right, slot, left, allowed⟩ => ⟨slot, left, right, allowed⟩,
      fun ⟨slot, left, right, allowed⟩ => ⟨right, slot, left, allowed⟩⟩
  unfold countDeficit deficit
  rw [equal]

private def groups (slots : List L) : List (Finset L) := slots.sublists.map List.toFinset

private theorem groups_are_exact (slots : List L) (group : Finset L) :
    group ∈ groups slots ↔ group ⊆ slots.toFinset := by
  constructor
  · intro present
    obtain ⟨sublist, listedSublist, rfl⟩ := List.mem_map.mp present
    intro line listed
    exact List.mem_toFinset.mpr ((List.mem_sublists.mp listedSublist).subset (List.mem_toFinset.mp listed))
  · intro included
    let selected := slots.filter fun line => decide (line ∈ group)
    have same : selected.toFinset = group := by
      ext line
      simp only [selected, List.mem_toFinset, List.mem_filter, decide_eq_true_eq]
      exact ⟨And.right, fun inside => ⟨List.mem_toFinset.mp (included inside), inside⟩⟩
    exact List.mem_map.mpr ⟨selected, List.mem_sublists.mpr List.filter_sublist, same⟩

private def worstGroup (geom : CanonicalBipartiteFeasibility L R) (slots : List L) : Finset L :=
  ((groups slots).argmax (countDeficit geom)).getD ∅

omit [DecidableEq R] in
private theorem worstGroup_is_exact (geom : CanonicalBipartiteFeasibility L R) (slots : List L)
    (same : slots.toFinset = geom.leftCarrier) :
    worstGroup geom slots ⊆ geom.leftCarrier ∧ deficit geom (worstGroup geom slots) = maximumDeficit geom := by
  unfold worstGroup
  cases computed : (groups slots).argmax (countDeficit geom) with
  | none =>
    have empty : (∅ : Finset L) ∈ groups slots := (groups_are_exact slots ∅).mpr (Finset.empty_subset _)
    rw [List.argmax_eq_none.mp computed] at empty
    cases empty
  | some group =>
    have best : group ∈ (groups slots).argmax (countDeficit geom) := by rw [computed]; rfl
    have inside : group ⊆ geom.leftCarrier :=
      same ▸ (groups_are_exact slots group).mp (List.argmax_mem best)
    refine ⟨inside, le_antisymm (every_original_group_deficit_is_bounded geom group inside) ?_⟩
    obtain ⟨largest, original, maximum⟩ := the_largest_deficit_is_attained_at_an_original_group geom
    have available : largest ∈ groups slots := (groups_are_exact slots largest).mpr (same.symm ▸ original)
    have greatest := List.le_of_mem_argmax available best
    simpa only [countDeficit_is_original, maximum, Option.getD_some] using greatest

end FiniteDeficiency

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  {TaskId : Type*} [DecidableEq TaskId]

local notation "C" => Evolving.Epoch.Current (Party := Party) (Good := Good) (Port := Port)
  (Technology := Technology) (Instrument := Instrument)
local notation "Script" => List (Option (Compile.RawInput Party Good Port Technology Instrument))
local notation "Task" => PublicTaskSpec Party Good

/-- Exhausting original whole assignments produces the original atomic
Hall deficiency with its tight amount. The group is selected by finite scan. -/
def atomicDeficiency (source : C) (script : Script) (atomic : Finset TaskId) (task : TaskId → Task)
    (ordered : List TaskId) (same : ordered.toFinset = atomic)
    (absent : ¬ Clock.Window.Shared.Assigned source atomic task script) :
    Clock.Window.Shared.Deficiency source atomic task script := by
  let geom := Clock.Window.Shared.geometry source atomic task script
  let slots := atomicSlots source script atomic task ordered same
  let group := worstGroup geom slots
  have exactGroup := worstGroup_is_exact geom slots (atomicSlots_are_the_original_nonempty_slots _ _ _ _ _ _)
  have exactAmount := actual_capacity_plus_the_largest_original_deficit_is_the_full_need geom
  have incomplete : geom.maximumMatchingCapacity ≠ geom.leftCarrier.card :=
    fun full => absent ((full_capacity_iff_there_is_a_complete_matching geom).mp full)
  have positive : 0 < deficit geom group := by
    change 0 < deficit geom (worstGroup geom slots)
    rw [exactGroup.2]
    omega
  exact ⟨group, exactGroup.1, Nat.sub_pos_iff_lt.mp positive, exactGroup.2.symm ▸ exactAmount⟩

end

end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Due.Service.Mixed
