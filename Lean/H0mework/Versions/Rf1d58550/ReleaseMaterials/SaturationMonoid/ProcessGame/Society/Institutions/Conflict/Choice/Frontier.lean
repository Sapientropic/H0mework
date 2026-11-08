import Mathlib.Algebra.Order.Archimedean.Real.Basic

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Choice

universe u v

/-- A score is admissible only on a candidate that passes its own execution gate. -/
structure Menu (Candidate : Type u) where
  executable : Set Candidate
  score : Candidate → ℝ

namespace Menu

variable {A : Type u} {B : Type v} (menu : Menu A)

def values : Set ℝ := menu.score '' menu.executable

def Bounded : Prop := menu.values.Nonempty ∧ BddAbove menu.values

noncomputable def frontier : ℝ := sSup menu.values

theorem score_le_frontier (bounds : menu.Bounded) {candidate : A}
    (actual : candidate ∈ menu.executable) : menu.score candidate ≤ menu.frontier :=
  le_csSup bounds.2 ⟨candidate, actual, rfl⟩

theorem exists_above (bounds : menu.Bounded) {floor : ℝ} (lower : floor < menu.frontier) :
    ∃ candidate ∈ menu.executable, floor < menu.score candidate := by
  obtain ⟨_, ⟨candidate, actual, rfl⟩, higher⟩ := exists_lt_of_lt_csSup bounds.1 lower
  exact ⟨candidate, actual, higher⟩

def Attained : Prop := ∃ candidate ∈ menu.executable, menu.score candidate = menu.frontier

/-- All four dispositions refer to the original candidates. The unbounded case supplies an
executable counterexample to each proposed finite cap. -/
inductive Resolution : Prop
  | blocked (noCandidate : ∀ candidate, candidate ∉ menu.executable)
  | unbounded (aboveEveryCap : ∀ cap, ∃ candidate ∈ menu.executable, cap < menu.score candidate)
  | attained (bounds : menu.Bounded) (witness : menu.Attained)
  | approached (bounds : menu.Bounded) (noMaximum : ¬ menu.Attained)
      (near : ∀ ε > 0, ∃ candidate ∈ menu.executable, menu.frontier - ε < menu.score candidate)

theorem resolve : menu.Resolution := by
  classical
  by_cases actual : menu.values.Nonempty
  · by_cases bounded : BddAbove menu.values
    · have bounds : menu.Bounded := ⟨actual, bounded⟩
      by_cases attained : menu.Attained
      · exact .attained bounds attained
      · exact .approached bounds attained fun ε positive =>
          menu.exists_above bounds (sub_lt_self _ positive)
    · refine .unbounded fun cap => ?_
      by_contra noCandidate
      apply bounded
      refine ⟨cap, ?_⟩
      rintro value ⟨candidate, actualCandidate, exactValue⟩
      rw [← exactValue]
      exact le_of_not_gt fun h => noCandidate ⟨candidate, actualCandidate, h⟩
  · exact .blocked fun candidate accepted => actual ⟨menu.score candidate, candidate, accepted, rfl⟩

/-- A strict comparison requires a uniform positive gap over the whole opposing menu. -/
def StrictlyDominates (opponent : Menu B) : Prop :=
  ∃ candidate ∈ menu.executable, ∃ gap > 0,
    ∀ other ∈ opponent.executable, opponent.score other + gap ≤ menu.score candidate

theorem strictlyDominates_iff_frontier_lt (opponent : Menu B)
    (bounds : menu.Bounded) (opponentBounds : opponent.Bounded) :
    menu.StrictlyDominates opponent ↔ opponent.frontier < menu.frontier := by
  constructor
  · rintro ⟨candidate, actual, gap, positive, above⟩
    have upper : opponent.frontier ≤ menu.score candidate - gap := by
      apply csSup_le opponentBounds.1
      rintro _ ⟨other, actualOther, rfl⟩
      exact le_sub_iff_add_le.mpr (above other actualOther)
    exact (upper.trans_lt (sub_lt_self _ positive)).trans_le (menu.score_le_frontier bounds actual)
  · intro larger
    obtain ⟨candidate, actual, above⟩ := menu.exists_above bounds larger
    refine ⟨candidate, actual, menu.score candidate - opponent.frontier, sub_pos.mpr above, ?_⟩
    intro other actualOther
    exact add_le_of_le_sub_right <| by
      rw [sub_sub_cancel]
      exact opponent.score_le_frontier opponentBounds actualOther

theorem tied_iff_neither_dominates (opponent : Menu B)
    (bounds : menu.Bounded) (opponentBounds : opponent.Bounded) :
    menu.frontier = opponent.frontier ↔
      ¬ menu.StrictlyDominates opponent ∧ ¬ opponent.StrictlyDominates menu := by
  rw [menu.strictlyDominates_iff_frontier_lt opponent bounds opponentBounds,
    opponent.strictlyDominates_iff_frontier_lt menu opponentBounds bounds, not_lt, not_lt]
  exact ⟨fun equality => ⟨equality.le, equality.ge⟩, fun bounds => le_antisymm bounds.1 bounds.2⟩

end Menu

theorem strict_flip_iff
    {W₀ P₀ W₁ P₁ : Type*} (oldWar : Menu W₀) (oldPeace : Menu P₀)
    (returnedWar : Menu W₁) (returnedPeace : Menu P₁)
    (oldWarBounds : oldWar.Bounded) (oldPeaceBounds : oldPeace.Bounded)
    (returnedWarBounds : returnedWar.Bounded) (returnedPeaceBounds : returnedPeace.Bounded) :
    (0 < oldWar.frontier - oldPeace.frontier ∧ returnedWar.frontier - returnedPeace.frontier < 0) ↔
      oldWar.StrictlyDominates oldPeace ∧ returnedPeace.StrictlyDominates returnedWar := by
  rw [oldWar.strictlyDominates_iff_frontier_lt oldPeace oldWarBounds oldPeaceBounds,
    returnedPeace.strictlyDominates_iff_frontier_lt returnedWar returnedPeaceBounds returnedWarBounds,
    sub_pos, sub_neg]

end SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Choice
