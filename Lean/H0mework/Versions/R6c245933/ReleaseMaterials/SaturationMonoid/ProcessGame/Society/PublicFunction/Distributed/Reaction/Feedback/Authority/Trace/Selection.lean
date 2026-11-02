import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Feedback.Authority.Trace.Lawful
import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Feedback.Authority.Trace.LocalJoint
import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Feedback.Cut.Compiler

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Feedback.Authority.Trace.Selection

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Technology] [DecidableEq Instrument]
  (bound : Native.Authority.Bound (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument))
  (input : Input bound.source.code) (cut : Nat) (active : bound.source.feedback? = some input)

abbrev Term := Cut.Term bound.source input cut
abbrev Table := Cut.Table bound.source input cut

def native (table : Table bound input cut) (new old : Term bound input cut) : Prop :=
  Lawful.NoWorse (generate bound input cut (Cut.opponent bound.source input cut table) new active)
    (generate bound input cut (Cut.opponent bound.source input cut table) old active)

instance (table : Table bound input cut) (new old : Term bound input cut) : Decidable (native bound input cut active table new old) := by
  unfold native
  infer_instance

/-- Archive retention is an admissibility constraint, never a source of strict profit. -/
def burden (table : Table bound input cut) (new old : Term bound input cut) : Prop :=
  (Lawful.inventory (generate bound input cut (Cut.opponent bound.source input cut table) new active)).due.Subperm
    (Lawful.inventory (generate bound input cut (Cut.opponent bound.source input cut table) old active)).due

instance (table : Table bound input cut) (new old : Term bound input cut) : Decidable (burden bound input cut active table new old) := by
  unfold burden
  infer_instance

inductive Axis where
  | economic (axis : Cut.Axis bound.source input cut)
  | native (table : Table bound input cut) (anchor : Term bound input cut)

def axes : List (Axis bound input cut) := (Cut.axes bound.source input cut).map .economic ++
  (Cut.tables bound.source input cut).flatMap fun table => (Cut.terms bound.source input cut).map (.native table)

/-- Lower-set tests embed this exact preorder; no weights or exchange rates are chosen. -/
def cost (term : Term bound input cut) : Axis bound input cut → ℚ
  | .economic axis => Cut.cost bound.source input cut term axis
  | .native table anchor => if native bound input cut active table term anchor then 0 else 1

def benefitCost (term : Term bound input cut) : Axis bound input cut → ℚ
  | .economic axis => Cut.cost bound.source input cut term axis
  | .native table anchor => if burden bound input cut active table term anchor then 0 else 1

abbrev NoWorse (new old : Term bound input cut) := Distributed.NoWorse (axes bound input cut) (cost bound input cut active) new old
abbrev BenefitNoWorse (new old : Term bound input cut) := Distributed.NoWorse (axes bound input cut) (benefitCost bound input cut active) new old
abbrev Better (old new : Term bound input cut) := NoWorse bound input cut active new old ∧ ¬ BenefitNoWorse bound input cut active old new

theorem native_axis_is_generated (table : Table bound input cut) (inside : table ∈ Cut.tables bound.source input cut)
    (anchor : Term bound input cut) : Axis.native table anchor ∈ axes bound input cut :=
  List.mem_append_right _ (List.mem_flatMap.mpr ⟨table, inside,
    List.mem_map.mpr ⟨anchor, List.mem_attach _ _, rfl⟩⟩)

theorem comparison_iff (new old : Term bound input cut) : NoWorse bound input cut active new old ↔
    Cut.NonRegression bound.source input cut new old ∧
      ∀ table ∈ Cut.tables bound.source input cut, native bound input cut active table new old := by
  constructor
  · intro bounded
    refine ⟨fun axis inside => bounded (.economic axis) (by simp [axes, inside]), ?_⟩
    intro table inside
    have checked := bounded _ (native_axis_is_generated bound input cut table inside old)
    have self : native bound input cut active table old old := Lawful.refl _
    simp only [cost, if_pos self] at checked
    split at checked
    next valid => exact valid
    next => norm_num at checked
  · rintro ⟨economic, natives⟩ axis inside
    rcases List.mem_append.mp inside with first | second
    · obtain ⟨axis, member, rfl⟩ := List.mem_map.mp first
      exact economic axis member
    · obtain ⟨table, member, inner⟩ := List.mem_flatMap.mp second
      obtain ⟨anchor, _, rfl⟩ := List.mem_map.mp inner
      change (if native bound input cut active table new anchor then (0 : ℚ) else 1) ≤
        (if native bound input cut active table old anchor then 0 else 1)
      by_cases holding : native bound input cut active table old anchor
      · have forwarded : native bound input cut active table new anchor := Lawful.trans (natives table member) holding
        simp only [if_pos holding, if_pos forwarded, le_refl]
      · split <;> simp_all

theorem benefit_comparison_iff (new old : Term bound input cut) : BenefitNoWorse bound input cut active new old ↔
    Cut.NonRegression bound.source input cut new old ∧
      ∀ table ∈ Cut.tables bound.source input cut, burden bound input cut active table new old := by
  constructor
  · intro bounded
    refine ⟨fun axis inside => bounded (.economic axis) (by simp [axes, inside]), ?_⟩
    intro table inside
    have checked := bounded _ (native_axis_is_generated bound input cut table inside old)
    have self : burden bound input cut active table old old := List.Subperm.refl _
    simp only [benefitCost, if_pos self] at checked
    split at checked
    next valid => exact valid
    next => norm_num at checked
  · rintro ⟨economic, natives⟩ axis inside
    rcases List.mem_append.mp inside with first | second
    · obtain ⟨axis, member, rfl⟩ := List.mem_map.mp first
      exact economic axis member
    · obtain ⟨table, member, inner⟩ := List.mem_flatMap.mp second
      obtain ⟨anchor, _, rfl⟩ := List.mem_map.mp inner
      change (if burden bound input cut active table new anchor then (0 : ℚ) else 1) ≤
        (if burden bound input cut active table old anchor then 0 else 1)
      by_cases holding : burden bound input cut active table old anchor
      · have forwarded : burden bound input cut active table new anchor := (natives table member).trans holding
        simp only [if_pos holding, if_pos forwarded, le_refl]
      · split <;> simp_all

/-- The equivalent direct native tests avoid replaying every lower-set anchor during acceptance. -/
instance decidableNoWorse (new old : Term bound input cut) : Decidable (NoWorse bound input cut active new old) :=
  decidable_of_iff (Cut.NonRegression bound.source input cut new old ∧
    ∀ table ∈ Cut.tables bound.source input cut, native bound input cut active table new old)
    (comparison_iff bound input cut active new old).symm

instance decidableBenefitNoWorse (new old : Term bound input cut) : Decidable (BenefitNoWorse bound input cut active new old) :=
  decidable_of_iff (Cut.NonRegression bound.source input cut new old ∧
    ∀ table ∈ Cut.tables bound.source input cut, burden bound input cut active table new old)
    (benefit_comparison_iff bound input cut active new old).symm

instance decidableBetter (old new : Term bound input cut) : Decidable (Better bound input cut active old new) := by
  letI := decidableNoWorse bound input cut active new old
  letI := decidableBenefitNoWorse bound input cut active old new
  unfold Better
  infer_instance

theorem no_worse_bounds_the_benefit_vector (new old : Term bound input cut)
    (bounded : NoWorse bound input cut active new old) : BenefitNoWorse bound input cut active new old := by
  obtain ⟨economic, native⟩ := (comparison_iff bound input cut active new old).mp bounded
  exact (benefit_comparison_iff bound input cut active new old).mpr
    ⟨economic, fun table member => (native table member).2⟩

theorem strictness_requires_a_real_benefit_improvement (old new : Term bound input cut) :
    Better bound input cut active old new ↔ NoWorse bound input cut active new old ∧
      Improves (axes bound input cut) (benefitCost bound input cut active) old new := by
  constructor
  · rintro ⟨bounded, strict⟩
    exact ⟨bounded, no_worse_bounds_the_benefit_vector bound input cut active new old bounded, strict⟩
  · rintro ⟨bounded, _, strict⟩
    exact ⟨bounded, strict⟩

theorem archives_alone_cannot_create_a_strict_dividend (old new : Term bound input cut)
    (equalBenefit : ∀ axis ∈ axes bound input cut,
      benefitCost bound input cut active old axis = benefitCost bound input cut active new axis) :
    ¬ Better bound input cut active old new :=
  fun strict => strict.2 (fun axis inside => le_of_eq (equalBenefit axis inside))

variable (empty : bound.source.continuation = [])

def AgainstEveryOpponent (new old : Term bound input cut) : Prop :=
  Cut.AgainstEveryOpponent bound.source input cut new old ∧
    ∀ rival : Opponent bound.source.code,
      Lawful.NoWorse (generate bound input cut rival new active) (generate bound input cut rival old active)

def BenefitAgainstEveryOpponent (new old : Term bound input cut) : Prop :=
  Cut.AgainstEveryOpponent bound.source input cut new old ∧
    ∀ rival : Opponent bound.source.code,
      (Lawful.inventory (generate bound input cut rival new active)).due.Subperm
        (Lawful.inventory (generate bound input cut rival old active)).due

include empty in
theorem benefit_iff_every_future_opponent (new old : Term bound input cut) :
    BenefitNoWorse bound input cut active new old ↔ BenefitAgainstEveryOpponent bound input cut active new old := by
  rw [benefit_comparison_iff, BenefitAgainstEveryOpponent]
  exact and_congr (Cut.finite_comparison_iff_every_future_opponent bound.source input cut active empty new old)
    (finite_manifest_relation_iff_every_future_opponent bound input cut active empty
      (fun new old => (Lawful.inventory new).due.Subperm (Lawful.inventory old).due) new old)

include empty in
theorem comparison_iff_every_future_opponent (new old : Term bound input cut) :
    NoWorse bound input cut active new old ↔ AgainstEveryOpponent bound input cut active new old := by
  rw [comparison_iff, AgainstEveryOpponent]
  exact and_congr (Cut.finite_comparison_iff_every_future_opponent bound.source input cut active empty new old)
    (finite_manifest_relation_iff_every_future_opponent bound input cut active empty Lawful.NoWorse new old)


end SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Feedback.Authority.Trace.Selection
