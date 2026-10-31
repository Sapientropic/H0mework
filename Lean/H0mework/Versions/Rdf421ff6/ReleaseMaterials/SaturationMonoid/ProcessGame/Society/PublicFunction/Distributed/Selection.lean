import Mathlib.Data.List.Pi
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Planning

/-! Finite Pareto selection. The scan is the carrier-independent version of
Migration.Preferred's source-plan scan. Coordinates retain their own units;
there is no welfare scalar or priority attached to the enumerator. -/

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed

universe u v
variable {Policy : Type u} {Coordinate : Type v}

inductive Inspection {Row : Type u} (holds : Row → Prop) (rows : List Row) where
  | accepted (checked : ∀ row ∈ rows, holds row)
  | rejected (row : Row) (original : row ∈ rows) (broken : ¬ holds row)

def inspect {Row : Type u} (holds : Row → Prop) [DecidablePred holds] :
    (rows : List Row) → Inspection holds rows
  | [] => .accepted (by simp)
  | row :: rest =>
    if checked : holds row then match inspect holds rest with
      | .accepted all => .accepted (by
          intro other inside
          rcases List.mem_cons.mp inside with same | later
          · exact same ▸ checked
          · exact all other later)
      | .rejected other inside broken => .rejected other (List.mem_cons_of_mem _ inside) broken
    else .rejected row List.mem_cons_self checked

def NoWorse (coordinates : List Coordinate) (cost : Policy → Coordinate → ℚ)
    (new old : Policy) : Prop := ∀ coordinate ∈ coordinates, cost new coordinate ≤ cost old coordinate

def Improves (coordinates : List Coordinate) (cost : Policy → Coordinate → ℚ)
    (old new : Policy) : Prop := NoWorse coordinates cost new old ∧ ¬ NoWorse coordinates cost old new

instance (coordinates : List Coordinate) (cost : Policy → Coordinate → ℚ) (new old : Policy) :
    Decidable (NoWorse coordinates cost new old) := by unfold NoWorse; infer_instance

instance (coordinates : List Coordinate) (cost : Policy → Coordinate → ℚ) (old new : Policy) :
    Decidable (Improves coordinates cost old new) := by unfold Improves; infer_instance

theorem noWorse_trans {coordinates : List Coordinate} {cost : Policy → Coordinate → ℚ}
    {first middle last : Policy} (a : NoWorse coordinates cost first middle)
    (b : NoWorse coordinates cost middle last) : NoWorse coordinates cost first last :=
  fun coordinate inside => (a coordinate inside).trans (b coordinate inside)

theorem improves_irrefl (coordinates : List Coordinate) (cost : Policy → Coordinate → ℚ)
    (policy : Policy) : ¬ Improves coordinates cost policy policy := fun h => h.2 h.1

theorem improves_trans {coordinates : List Coordinate} {cost : Policy → Coordinate → ℚ}
    {first middle last : Policy} (a : Improves coordinates cost first middle)
    (b : Improves coordinates cost middle last) : Improves coordinates cost first last := by
  refine ⟨noWorse_trans b.1 a.1, ?_⟩
  intro backward
  exact a.2 (noWorse_trans backward b.1)

variable (coordinates : List Coordinate) (cost : Policy → Coordinate → ℚ)

private structure Scanned (seed : Policy) (remaining : List Policy) where
  policy : Policy
  original : policy = seed ∨ policy ∈ remaining
  advances : policy = seed ∨ Improves coordinates cost seed policy
  maximal : ∀ other ∈ remaining, ¬ Improves coordinates cost policy other

private theorem cannot_improve_seed {seed : Policy} {remaining : List Policy}
    (result : Scanned coordinates cost seed remaining) : ¬ Improves coordinates cost result.policy seed := by
  intro backward
  rcases result.advances with same | forward
  · apply improves_irrefl coordinates cost seed
    simpa only [same] using backward
  · exact improves_irrefl coordinates cost seed (improves_trans forward backward)

private def scan (seed : Policy) : (remaining : List Policy) → Scanned coordinates cost seed remaining
  | [] => ⟨seed, .inl rfl, .inl rfl, by simp⟩
  | head :: tail =>
    if improves : Improves coordinates cost seed head then
      let result := scan head tail
      { policy := result.policy
        original := .inr (by
          rcases result.original with same | inside
          · simpa only [same] using (List.mem_cons_self : head ∈ head :: tail)
          · exact List.mem_cons_of_mem _ inside)
        advances := .inr (by
          rcases result.advances with same | further
          · exact same.symm ▸ improves
          · exact improves_trans improves further)
        maximal := by
          intro other inside
          rcases List.mem_cons.mp inside with same | later
          · subst other; exact cannot_improve_seed coordinates cost result
          · exact result.maximal other later }
    else
      let result := scan seed tail
      { policy := result.policy
        original := result.original.imp_right (List.mem_cons_of_mem _)
        advances := result.advances
        maximal := by
          intro other inside
          rcases List.mem_cons.mp inside with same | later
          · subst other
            intro backward
            rcases result.advances with same | forward
            · exact improves (same ▸ backward)
            · exact improves (improves_trans forward backward)
          · exact result.maximal other later }

structure Selected (candidates : List Policy) where
  policy : Policy
  original : policy ∈ candidates
  maximal : ∀ other ∈ candidates, ¬ Improves coordinates cost policy other

def choose (candidates : List Policy) : Option (Selected coordinates cost candidates) :=
  match same : candidates with
  | [] => none
  | head :: tail =>
    let result := scan coordinates cost head tail
    some ⟨result.policy, by
      rcases result.original with h | h
      · simpa only [h] using (List.mem_cons_self : head ∈ head :: tail)
      · exact List.mem_cons_of_mem _ h, by
      intro other inside
      rcases List.mem_cons.mp inside with h | h
      · subst other; exact cannot_improve_seed coordinates cost result
      · exact result.maximal other h⟩

theorem choose_none_iff_empty (candidates : List Policy) :
    choose coordinates cost candidates = none ↔ candidates = [] := by
  unfold choose
  split <;> simp_all

/-- The improvement exists in a named physical coordinate, not in a sum of
incommensurable costs. -/
theorem improves_iff (old new : Policy) : Improves coordinates cost old new ↔
    NoWorse coordinates cost new old ∧ ∃ coordinate ∈ coordinates, cost new coordinate < cost old coordinate := by
  simp only [Improves, NoWorse, not_forall, not_le]
  tauto

end SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed
