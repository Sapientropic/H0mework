import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Feedback.Cut.Profile

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Feedback.Cut

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Technology] [DecidableEq Instrument]
  (source : Machine Party Good Port Technology Instrument) (input : Input source.code) (cut : Nat)

inductive ValueAxis where
  | material (table : Table source input cut) (metric : Settlement.Material Party Good)
  | unpaid (table : Table source input cut) (index : Nat) (holder : Party)
  | service (table : Table source input cut) (index : Fin source.code.task.slots.length)

def valueAxes : List (ValueAxis source input cut) := (tables source input cut).flatMap fun table =>
  (Settlement.materials source.code).map (.material table) ++
    (List.finRange source.code.task.slots.length).map (.service table) ++
    (List.range (originalSlots source cut)).flatMap fun index =>
      source.code.parties.map (.unpaid table index)

def value (term : Term source input cut) : ValueAxis source input cut → ℚ
  | .material table metric => material source input cut (opponent source input cut table) term metric
  | .unpaid table index holder => remaining source input cut (opponent source input cut table) term index holder
  | .service table index =>
      serviceTime source input cut (opponent source input cut table) term index

inductive Axis where
  | value (axis : ValueAxis source input cut)
  | native (table : Table source input cut) (anchor : Settlement.Profile Party Good Port Technology Instrument)

def axes : List (Axis source input cut) := (valueAxes source input cut).map .value ++
  (tables source input cut).flatMap fun table => (terms source input cut).map fun term =>
    .native table (profile source input cut (opponent source input cut table) term)

def cost (term : Term source input cut) : Axis source input cut → ℚ
  | .value axis => value source input cut term axis
  | .native table anchor => if profile source input cut (opponent source input cut table) term = anchor then 0 else 1

abbrev ValuesNoWorse (new old : Term source input cut) := NoWorse (valueAxes source input cut) (value source input cut) new old
abbrev NonRegression (new old : Term source input cut) := NoWorse (axes source input cut) (cost source input cut) new old
abbrev Better (old new : Term source input cut) := Improves (axes source input cut) (cost source input cut) old new

theorem native_axis_is_generated (term : Term source input cut) (table : Table source input cut)
    (generated : table ∈ tables source input cut) :
    Axis.native table (profile source input cut (opponent source input cut table) term) ∈ axes source input cut := by
  exact List.mem_append_right _ (List.mem_flatMap.mpr ⟨table, generated,
    List.mem_map.mpr ⟨term, List.mem_attach _ _, rfl⟩⟩)

theorem material_axis_is_generated (table : Table source input cut) (generated : table ∈ tables source input cut)
    (metric : Settlement.Material Party Good) (present : metric ∈ Settlement.materials source.code) :
    ValueAxis.material table metric ∈ valueAxes source input cut :=
  List.mem_flatMap.mpr ⟨table, generated, List.mem_append_left _
    (List.mem_append_left _ (List.mem_map.mpr ⟨metric, present, rfl⟩))⟩

theorem service_axis_is_generated (table : Table source input cut) (generated : table ∈ tables source input cut)
    (index : Fin source.code.task.slots.length) : ValueAxis.service table index ∈ valueAxes source input cut :=
  List.mem_flatMap.mpr ⟨table, generated, List.mem_append_left _
    (List.mem_append_right _ (List.mem_map.mpr ⟨index, List.mem_finRange _, rfl⟩))⟩

theorem unpaid_axis_is_generated (table : Table source input cut)
    (generated : table ∈ tables source input cut) (index : Nat)
    (inside : index < originalSlots source cut) (holder : Party) :
    ValueAxis.unpaid table index holder ∈ valueAxes source input cut := by
  exact List.mem_flatMap.mpr ⟨table, generated, List.mem_append_right _
    (List.mem_flatMap.mpr ⟨index, List.mem_range.mpr inside,
      List.mem_map.mpr ⟨holder, source.code.parties_cover holder, rfl⟩⟩)⟩

theorem comparison_iff (new old : Term source input cut) : NonRegression source input cut new old ↔
    ValuesNoWorse source input cut new old ∧ ∀ table ∈ tables source input cut,
      profile source input cut (opponent source input cut table) new = profile source input cut (opponent source input cut table) old := by
  constructor
  · intro bounded
    refine ⟨fun axis inside => bounded (.value axis) (List.mem_append_left _ (List.mem_map.mpr ⟨axis, inside, rfl⟩)), ?_⟩
    intro table generated
    have checked := bounded _ (native_axis_is_generated source input cut old table generated)
    simp only [cost] at checked
    split at checked
    next same => exact same
    next => norm_num at checked
  · rintro ⟨values, natives⟩ axis inside
    rcases List.mem_append.mp inside with valueAxis | nativeAxis
    · obtain ⟨axis, generated, rfl⟩ := List.mem_map.mp valueAxis
      exact values axis generated
    · obtain ⟨table, generated, inner⟩ := List.mem_flatMap.mp nativeAxis
      obtain ⟨term, _, rfl⟩ := List.mem_map.mp inner
      simp only [cost, natives table generated, le_refl]

theorem strictness_comes_from_actual_values (old new : Term source input cut) : Better source input cut old new ↔
    Improves (valueAxes source input cut) (value source input cut) old new ∧ ∀ table ∈ tables source input cut,
      profile source input cut (opponent source input cut table) new = profile source input cut (opponent source input cut table) old := by
  constructor
  · rintro ⟨forward, strict⟩
    obtain ⟨values, same⟩ := (comparison_iff source input cut new old).mp forward
    exact ⟨⟨values, fun backward => strict ((comparison_iff source input cut old new).mpr
      ⟨backward, fun table generated => (same table generated).symm⟩)⟩, same⟩
  · rintro ⟨⟨values, strict⟩, same⟩
    exact ⟨(comparison_iff source input cut new old).mpr ⟨values, same⟩,
      fun backward => strict ((comparison_iff source input cut old new).mp backward).1⟩

theorem lawful_comparison_protects_each_original_holder (new old : Term source input cut)
    (bounded : NonRegression source input cut new old) (table : Table source input cut)
    (generated : table ∈ tables source input cut) (index : Nat)
    (inside : index < originalSlots source cut) (holder : Party) :
    received source input cut (opponent source input cut table) old index holder ≤
      received source input cut (opponent source input cut table) new index holder := by
  obtain ⟨values, profiles⟩ := (comparison_iff source input cut new old).mp bounded
  exact same_rights_and_less_owed_give_more_actual_receipts source input cut _ new old
    (profiles table generated) index holder
    (values (.unpaid table index holder) (unpaid_axis_is_generated source input cut table generated index inside holder))

end SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Feedback.Cut
