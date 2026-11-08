import Mathlib.Algebra.Order.Field.Rat
import Mathlib.Data.List.MinMax

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Threshold

variable {α β : Type*}

def best (score : α → ℚ) (rows : List α) : Option α :=
  rows.argmax score

theorem best_spec {score : α → ℚ} {rows : List α} {entry : α}
    (selected : best score rows = some entry) :
    entry ∈ rows ∧ ∀ other ∈ rows, score other ≤ score entry := by
  have selected' : entry ∈ rows.argmax score := by simp [best] at selected; simp [selected]
  exact ⟨List.argmax_mem selected', fun _ member => List.le_of_mem_argmax member selected'⟩

@[simp] theorem best_eq_none {score : α → ℚ} {rows : List α} :
    best score rows = none ↔ rows = [] :=
  List.argmax_eq_none

/-- Both alternatives must be executable before their best values can be compared. -/
def gap (conflictScore : α → ℚ) (peaceScore : β → ℚ)
    (conflicts : List α) (peaceful : List β) : Option ℚ :=
  match best conflictScore conflicts, best peaceScore peaceful with
  | some conflict, some peace => some (conflictScore conflict - peaceScore peace)
  | _, _ => none

theorem gap_exact {conflictScore : α → ℚ} {peaceScore : β → ℚ}
    {conflicts : List α} {peaceful : List β} {margin : ℚ}
    (computed : gap conflictScore peaceScore conflicts peaceful = some margin) :
    ∃ conflict ∈ conflicts, ∃ peace ∈ peaceful,
      margin = conflictScore conflict - peaceScore peace ∧
      (∀ other ∈ conflicts, conflictScore other ≤ conflictScore conflict) ∧
      (∀ other ∈ peaceful, peaceScore other ≤ peaceScore peace) := by
  unfold gap at computed
  cases war : best conflictScore conflicts with
  | none => simp [war] at computed
  | some conflict =>
    cases calm : best peaceScore peaceful with
    | none => simp [war, calm] at computed
    | some peace =>
      have ⟨conflictMem, conflictBest⟩ := best_spec war
      have ⟨peaceMem, peaceBest⟩ := best_spec calm
      simp [war, calm] at computed
      exact ⟨conflict, conflictMem, peace, peaceMem, computed.symm, conflictBest, peaceBest⟩

@[simp] theorem gap_eq_none {conflictScore : α → ℚ} {peaceScore : β → ℚ}
    {conflicts : List α} {peaceful : List β} :
    gap conflictScore peaceScore conflicts peaceful = none ↔ conflicts = [] ∨ peaceful = [] := by
  rw [← @best_eq_none _ conflictScore conflicts, ← @best_eq_none _ peaceScore peaceful]
  cases war : best conflictScore conflicts <;> cases calm : best peaceScore peaceful <;>
    simp [gap, war, calm]

/-- The first actual cut with strictly positive pressure. A tied cut is not a crossing. -/
def firstPositive (score : α → Option ℚ) (cuts : List α) : Option α :=
  cuts.find? fun cut => (score cut).any fun value => decide (0 < value)

theorem firstPositive_exact {score : α → Option ℚ} {cuts : List α} {cut : α} :
    firstPositive score cuts = some cut ↔
      (∃ value, score cut = some value ∧ 0 < value) ∧
      ∃ before after, cuts = before ++ cut :: after ∧
        ∀ earlier ∈ before, ∀ value, score earlier = some value → value ≤ 0 := by
  unfold firstPositive
  rw [List.find?_eq_some_iff_append]
  have positive (entry : α) :
      ((score entry).any fun value => decide (0 < value)) = true ↔
        ∃ value, score entry = some value ∧ 0 < value := by
    cases score entry <;> simp
  simp only [positive]
  constructor
  · rintro ⟨first, before, after, history, earlier⟩
    refine ⟨first, before, after, history, ?_⟩
    intro entry member value computed
    simpa [computed] using earlier entry member
  · rintro ⟨first, before, after, history, earlier⟩
    refine ⟨first, before, after, history, ?_⟩
    intro entry member
    cases computed : score entry with
    | none => simp
    | some value => simpa [computed] using earlier entry member value computed

theorem firstPositive_eq_none {score : α → Option ℚ} {cuts : List α} :
    firstPositive score cuts = none ↔
      ∀ cut ∈ cuts, ∀ value, score cut = some value → value ≤ 0 := by
  unfold firstPositive
  rw [List.find?_eq_none]
  refine forall_congr' fun cut => forall_congr' fun _ => ?_
  cases score cut <;> simp

/-- Failed comparisons have no score. All comparable cuts keep their original identities. -/
def peak (score : α → Option ℚ) (cuts : List α) : Option (α × ℚ) :=
  best Prod.snd (cuts.filterMap fun cut => (score cut).map (cut, ·))

private theorem mem_scored {score : α → Option ℚ} {cuts : List α} {cut : α} {value : ℚ} :
    (cut, value) ∈ cuts.filterMap (fun entry => (score entry).map (entry, ·)) ↔
      cut ∈ cuts ∧ score cut = some value := by
  rw [List.mem_filterMap]
  constructor
  · rintro ⟨entry, member, mapped⟩
    cases h : score entry with
    | none => simp [h] at mapped
    | some found =>
      simp [h] at mapped
      obtain ⟨rfl, rfl⟩ := mapped
      exact ⟨member, h⟩
  · rintro ⟨member, computed⟩
    exact ⟨cut, member, by simp [computed]⟩

theorem peak_exact {score : α → Option ℚ} {cuts : List α} {cut : α} {value : ℚ}
    (selected : peak score cuts = some (cut, value)) :
    cut ∈ cuts ∧ score cut = some value ∧
      ∀ other ∈ cuts, ∀ reading, score other = some reading → reading ≤ value := by
  have ⟨member, maximal⟩ := best_spec selected
  have ⟨inHistory, computed⟩ := mem_scored.mp member
  exact ⟨inHistory, computed, fun _ inCuts _ reads =>
    maximal _ (mem_scored.mpr ⟨inCuts, reads⟩)⟩

theorem peak_eq_none {score : α → Option ℚ} {cuts : List α} :
    peak score cuts = none ↔ ∀ cut ∈ cuts, score cut = none := by
  rw [peak, best_eq_none]
  constructor
  · intro empty cut member
    cases computed : score cut with
    | none => rfl
    | some value =>
      have inList := mem_scored.mpr ⟨member, computed⟩
      simp [empty] at inList
  · intro empty
    apply List.eq_nil_iff_forall_not_mem.mpr
    rintro ⟨cut, value⟩ member
    have ⟨inHistory, computed⟩ := mem_scored.mp member
    simp [empty cut inHistory] at computed

end SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Threshold
