import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Identity.Family

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Identity

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Technology] [DecidableEq Instrument]
  (code : Code Party Good Port Technology Instrument)

inductive Axis where
  | original (axis : Open.Axis code)
  | native (history : OriginalHistory code) (table : Table code) (anchor : Profile Party Good Port Technology Instrument)

def axes : List (Axis code) := (Open.axes code).map .original ++
  code.histories.attach.flatMap fun history => (tables code).flatMap fun table =>
    code.policies.attach.map fun program => .native history table (profile code program history table)

def cost (program : Program code) : Axis code → ℚ
  | .original axis => Open.cost code program.val axis
  | .native history table anchor => if profile code program history table = anchor then 0 else 1

abbrev NonRegression (new old : Program code) := NoWorse (axes code) (cost code) new old
abbrev Better (old new : Program code) := Improves (axes code) (cost code) old new

theorem native_axis_is_generated (program : Program code) (history : OriginalHistory code)
    (table : Table code) (generated : table ∈ tables code) :
    Axis.native history table (profile code program history table) ∈ axes code := by
  exact List.mem_append_right _ (List.mem_flatMap.mpr ⟨history, List.mem_attach _ _,
    List.mem_flatMap.mpr ⟨table, generated, List.mem_map.mpr ⟨program, List.mem_attach _ _, rfl⟩⟩⟩)

theorem comparison_iff (new old : Program code) : NonRegression code new old ↔
    Open.NonRegression code new.val old.val ∧
      ∀ history : OriginalHistory code, ∀ table ∈ tables code, profile code new history table = profile code old history table := by
  constructor
  · intro bounded
    refine ⟨fun axis inside => bounded (.original axis) (List.mem_append_left _ (List.mem_map.mpr ⟨axis, inside, rfl⟩)), ?_⟩
    intro history table generated
    have checked := bounded _ (native_axis_is_generated code old history table generated)
    simp only [cost] at checked
    split at checked
    next same => exact same
    next => norm_num at checked
  · rintro ⟨original, natives⟩ axis inside
    rcases List.mem_append.mp inside with oldAxis | nativeAxis
    · obtain ⟨axis, generated, rfl⟩ := List.mem_map.mp oldAxis
      exact original axis generated
    · obtain ⟨history, _, inner⟩ := List.mem_flatMap.mp nativeAxis
      obtain ⟨table, generated, inner⟩ := List.mem_flatMap.mp inner
      obtain ⟨program, _, rfl⟩ := List.mem_map.mp inner
      simp only [cost, natives history table generated, le_refl]

theorem strictness_comes_from_the_original_vector (old new : Program code) : Better code old new ↔
    Open.Better code old.val new.val ∧
      ∀ history : OriginalHistory code, ∀ table ∈ tables code, profile code new history table = profile code old history table := by
  constructor
  · rintro ⟨forward, strict⟩
    obtain ⟨original, same⟩ := (comparison_iff code new old).mp forward
    refine ⟨⟨original, ?_⟩, same⟩
    intro backward
    exact strict ((comparison_iff code old new).mpr ⟨backward, fun history table generated => (same history table generated).symm⟩)
  · rintro ⟨⟨original, strict⟩, same⟩
    exact ⟨(comparison_iff code new old).mpr ⟨original, same⟩,
      fun backward => strict ((comparison_iff code old new).mp backward).1⟩

end SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Identity
