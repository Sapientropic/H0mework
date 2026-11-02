import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Settlement.Profile

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 2000000

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Settlement

open Institutions.Capitalism.Universal.Source.Program

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Technology] [DecidableEq Instrument]
  (code : Code Party Good Port Technology Instrument)

inductive Material (Party Good : Type) where
  | debit (party : Party) (good : Good)
  | credit (party : Party) (good : Good)
  | inventory (party : Party) (good : Good)
  | clock | admissibility

def materials : List (Material Party Good) := code.parties.flatMap (fun party =>
  code.goods.flatMap fun good => [.debit party good, .credit party good, .inventory party good]) ++
  [.clock, .admissibility]

def materialMetric : Material Party Good → Metric Party Good Instrument
  | .debit party good => .raw (.debit party good)
  | .credit party good => .raw (.credit party good)
  | .inventory party good => .raw (.inventory party good)
  | .clock => .raw .clock
  | .admissibility => .admissibility

inductive ValueAxis where
  | material (history : OriginalHistory code) (table : Table code) (metric : Material Party Good)
  | unpaid (history : OriginalHistory code) (table : Table code) (index : Nat) (holder : Party)

def valueAxes : List (ValueAxis code) := code.histories.attach.flatMap fun history =>
  (tables code).flatMap fun table =>
    (materials code).map (.material history table) ++ code.policies.attach.flatMap fun program =>
      (List.range (before code program history table).current.slots.length).flatMap fun index =>
        code.parties.map (.unpaid history table index)

def value (program : Program code) : ValueAxis code → ℚ
  | .material history table metric =>
      (machine code program history table).actualScore (materialMetric metric)
  | .unpaid history table index holder => remaining code program history table index holder

inductive Axis where
  | value (axis : ValueAxis code)
  | native (history : OriginalHistory code) (table : Table code)
      (anchor : Profile Party Good Port Technology Instrument)

def axes : List (Axis code) := (valueAxes code).map .value ++
  code.histories.attach.flatMap fun history => (tables code).flatMap fun table =>
    code.policies.attach.map fun program => .native history table (profile code program history table)

def cost (program : Program code) : Axis code → ℚ
  | .value axis => value code program axis
  | .native history table anchor => if profile code program history table = anchor then 0 else 1

abbrev ValuesNoWorse (new old : Program code) := NoWorse (valueAxes code) (value code) new old
abbrev NonRegression (new old : Program code) := NoWorse (axes code) (cost code) new old
abbrev Better (old new : Program code) := Improves (axes code) (cost code) old new

theorem native_axis_is_generated (program : Program code) (history : OriginalHistory code)
    (table : Table code) (generated : table ∈ tables code) :
    Axis.native history table (profile code program history table) ∈ axes code := by
  exact List.mem_append_right _ (List.mem_flatMap.mpr ⟨history, List.mem_attach _ _,
    List.mem_flatMap.mpr ⟨table, generated, List.mem_map.mpr ⟨program, List.mem_attach _ _, rfl⟩⟩⟩)

theorem material_axis_is_generated (history : OriginalHistory code) (table : Table code)
    (generated : table ∈ tables code) (metric : Material Party Good) (present : metric ∈ materials code) :
    ValueAxis.material history table metric ∈ valueAxes code := by
  exact List.mem_flatMap.mpr ⟨history, List.mem_attach _ _, List.mem_flatMap.mpr
    ⟨table, generated, List.mem_append_left _ (List.mem_map.mpr ⟨metric, present, rfl⟩)⟩⟩

theorem unpaid_axis_is_generated (program : Program code) (history : OriginalHistory code)
    (table : Table code) (generated : table ∈ tables code) (index : Nat)
    (inside : index < (before code program history table).current.slots.length) (holder : Party) :
    ValueAxis.unpaid history table index holder ∈ valueAxes code := by
  apply List.mem_flatMap.mpr
  refine ⟨history, List.mem_attach _ _, List.mem_flatMap.mpr ⟨table, generated, ?_⟩⟩
  apply List.mem_append_right
  exact List.mem_flatMap.mpr ⟨program, List.mem_attach _ _, List.mem_flatMap.mpr
    ⟨index, List.mem_range.mpr inside, List.mem_map.mpr ⟨holder, code.parties_cover holder, rfl⟩⟩⟩

theorem comparison_iff (new old : Program code) : NonRegression code new old ↔
    ValuesNoWorse code new old ∧ ∀ history : OriginalHistory code, ∀ table ∈ tables code,
      profile code new history table = profile code old history table := by
  constructor
  · intro bounded
    refine ⟨fun axis inside => bounded (.value axis) (List.mem_append_left _ (List.mem_map.mpr ⟨axis, inside, rfl⟩)), ?_⟩
    intro history table generated
    have checked := bounded _ (native_axis_is_generated code old history table generated)
    simp only [cost] at checked
    split at checked
    next same => exact same
    next => norm_num at checked
  · rintro ⟨values, natives⟩ axis inside
    rcases List.mem_append.mp inside with valueAxis | nativeAxis
    · obtain ⟨axis, generated, rfl⟩ := List.mem_map.mp valueAxis
      exact values axis generated
    · obtain ⟨history, _, inner⟩ := List.mem_flatMap.mp nativeAxis
      obtain ⟨table, generated, inner⟩ := List.mem_flatMap.mp inner
      obtain ⟨program, _, rfl⟩ := List.mem_map.mp inner
      simp only [cost, natives history table generated, le_refl]

theorem strictness_comes_from_actual_values (old new : Program code) : Better code old new ↔
    Improves (valueAxes code) (value code) old new ∧ ∀ history : OriginalHistory code,
      ∀ table ∈ tables code, profile code new history table = profile code old history table := by
  constructor
  · rintro ⟨forward, strict⟩
    obtain ⟨values, same⟩ := (comparison_iff code new old).mp forward
    exact ⟨⟨values, fun backward => strict ((comparison_iff code old new).mpr
      ⟨backward, fun history table generated => (same history table generated).symm⟩)⟩, same⟩
  · rintro ⟨⟨values, strict⟩, same⟩
    exact ⟨(comparison_iff code new old).mpr ⟨values, same⟩,
      fun backward => strict ((comparison_iff code old new).mp backward).1⟩

theorem lawful_comparison_protects_each_original_holder (new old : Program code)
    (bounded : NonRegression code new old) (history : OriginalHistory code) (table : Table code)
    (generated : table ∈ tables code) (index : Nat)
    (inside : index < (before code old history table).current.slots.length) (holder : Party) :
    received code old history table index holder ≤ received code new history table index holder := by
  obtain ⟨values, profiles⟩ := (comparison_iff code new old).mp bounded
  have debt := values (.unpaid history table index holder)
    (unpaid_axis_is_generated code old history table generated index inside holder)
  change remaining code new history table index holder ≤ remaining code old history table index holder at debt
  exact equal_profiles_and_less_unpaid_give_more_actual_receipts code new old history table
    (profiles history table generated) index holder debt

end SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Settlement
