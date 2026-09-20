/-
  Proposition 21: finite field-interference budget, V0.

  The full generative/on-the-fly interference problem needs a richer cost
  model.  This module proves the finite-cover core: if the runtime has already
  materialized two finite local candidate lists, then pairwise gluing /
  compatibility checks can be scheduled by a complete cross-product scan whose
  exact size is `|left| * |right|`.

  This gives the mathematical budget for explicit local covers.  It does not
  claim a bound for candidate generation, semantic search, or model calls that
  create the cover.
-/

import H0mework.Realization.Observation.QueryAlgebra

/-! ## Cross-product interference pairs -/

/-- Enumerate every ordered pair between two finite local candidate lists. -/
def crossInterferencePairs {α β : Type*} : List α → List β → List (α × β)
  | [], _right => []
  | left :: rest, right =>
      right.map (fun item => (left, item)) ++ crossInterferencePairs rest right

/-- THEOREM 1: the cross-product scan has exact `|left| * |right|` cost. -/
theorem crossInterferencePairs_length {α β : Type*}
    (left : List α) (right : List β) :
    (crossInterferencePairs left right).length = left.length * right.length := by
  induction left with
  | nil =>
      simp [crossInterferencePairs]
  | cons head tail ih =>
      simp [crossInterferencePairs, ih, Nat.succ_mul]
      omega

/-- THEOREM 2: every generated pair contains one item from each side. -/
theorem crossInterferencePairs_sound {α β : Type*}
    {left : List α} {right : List β} {pair : α × β}
    (h : pair ∈ crossInterferencePairs left right) :
    pair.1 ∈ left ∧ pair.2 ∈ right := by
  induction left with
  | nil =>
      simp [crossInterferencePairs] at h
  | cons head tail ih =>
      rw [crossInterferencePairs] at h
      rcases List.mem_append.mp h with hhead | htail
      · rcases List.mem_map.mp hhead with ⟨item, hitem, hpair⟩
        cases hpair
        exact ⟨by simp, hitem⟩
      · have htail' := ih htail
        exact ⟨List.mem_cons_of_mem head htail'.1, htail'.2⟩

/-- THEOREM 3: every pair of members appears in the scan. -/
theorem crossInterferencePairs_complete {α β : Type*}
    {left : List α} {right : List β} {a : α} {b : β}
    (ha : a ∈ left) (hb : b ∈ right) :
    (a, b) ∈ crossInterferencePairs left right := by
  induction left with
  | nil =>
      simp at ha
  | cons head tail ih =>
      rw [List.mem_cons] at ha
      rw [crossInterferencePairs]
      apply List.mem_append.mpr
      rcases ha with ha | htail
      · subst head
        left
        exact List.mem_map.mpr ⟨b, hb, rfl⟩
      · right
        exact ih htail

/-- THEOREM 4: membership in the scan is exactly cross-membership. -/
theorem crossInterferencePairs_mem_iff {α β : Type*}
    {left : List α} {right : List β} {a : α} {b : β} :
    (a, b) ∈ crossInterferencePairs left right ↔ a ∈ left ∧ b ∈ right := by
  constructor
  · intro h
    exact crossInterferencePairs_sound h
  · intro h
    exact crossInterferencePairs_complete h.1 h.2

/-! ## Self-interference budget -/

/-- Ordered self-interference pairs for one finite candidate list. -/
def selfInterferencePairs {α : Type*} (items : List α) : List (α × α) :=
  crossInterferencePairs items items

/-- THEOREM 5: ordered self-interference has exact quadratic budget. -/
theorem selfInterferencePairs_length {α : Type*} (items : List α) :
    (selfInterferencePairs items).length = items.length * items.length := by
  exact crossInterferencePairs_length items items

/-!
  Summary:
  - Explicit finite covers have a complete pairwise interference schedule.
  - The exact number of pair checks is `|left| * |right|`; self-interference is
    quadratic in the number of materialized candidates.

  Boundary:
  - This proves the finite materialized-cover budget only.  It does not bound
    how expensive it is to generate candidates, reopen sources, or run a model
    to propose new field edges.
-/
