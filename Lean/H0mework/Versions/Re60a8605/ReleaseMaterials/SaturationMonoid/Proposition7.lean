/-
  Proposition 7 (algebraic core): Ω axioms as sections preserve C1/C2 under
  restriction and gluing.
-/

import Mathlib

/-! ## Section model -/

/-- A section carries scope, authority level (ℕ), and source-backed flag. -/
structure Section (ι : Type*) where
  scope : Set ι
  authority : ℕ
  hasSource : Bool

/-- C1: has source handles. -/
def satisfiesC1 {ι : Type*} (s : Section ι) : Prop := s.hasSource = true

/-- C2: authority ≤ ceiling. -/
def satisfiesC2 {ι : Type*} (s : Section ι) (ceiling : ℕ) : Prop :=
  s.authority ≤ ceiling

/-- Combined discipline. -/
def satisfiesDiscipline {ι : Type*} (s : Section ι) (ceiling : ℕ) : Prop :=
  satisfiesC1 s ∧ satisfiesC2 s ceiling

/-! ## Restriction (S1) -/

/-- Restrict to a sub-scope. Authority and hasSource unchanged. -/
def restrictSection {ι : Type*} (s : Section ι) (sub : Set ι)
    (_hsub : sub ⊆ s.scope) : Section ι :=
  { scope := sub, authority := s.authority, hasSource := s.hasSource }

/-- THEOREM 1: C1 preserved by restriction. -/
theorem C1_preserved_by_restriction {ι : Type*} (s : Section ι)
    (sub : Set ι) (hsub : sub ⊆ s.scope)
    (h : satisfiesC1 s) : satisfiesC1 (restrictSection s sub hsub) := h

/-- THEOREM 2: C2 preserved by restriction. -/
theorem C2_preserved_by_restriction {ι : Type*} (s : Section ι)
    (sub : Set ι) (hsub : sub ⊆ s.scope)
    (ceiling : ℕ) (h : satisfiesC2 s ceiling) :
    satisfiesC2 (restrictSection s sub hsub) ceiling := h

/-- THEOREM 3: discipline preserved by restriction. -/
theorem discipline_preserved_by_restriction {ι : Type*} (s : Section ι)
    (sub : Set ι) (hsub : sub ⊆ s.scope)
    (ceiling : ℕ) (h : satisfiesDiscipline s ceiling) :
    satisfiesDiscipline (restrictSection s sub hsub) ceiling :=
  ⟨h.1, h.2⟩

/-! ## Gluing (S2/S3) -/

/-- Glue two sections: union scopes, min authority, OR source. -/
def glueSections {ι : Type*} (s₁ s₂ : Section ι) : Section ι :=
  { scope := s₁.scope ∪ s₂.scope
    authority := min s₁.authority s₂.authority
    hasSource := s₁.hasSource || s₂.hasSource }

/-- THEOREM 4: C1 preserved by gluing. -/
theorem C1_preserved_by_gluing {ι : Type*} (s₁ s₂ : Section ι)
    (h₁ : satisfiesC1 s₁) (_h₂ : satisfiesC1 s₂) :
    satisfiesC1 (glueSections s₁ s₂) := by
  show (s₁.hasSource || s₂.hasSource) = true
  rw [h₁]; simp

/-- THEOREM 5: C2 preserved by gluing.
    min(a₁, a₂) ≤ ceiling when both ≤ ceiling. -/
theorem C2_preserved_by_gluing {ι : Type*} (s₁ s₂ : Section ι)
    (ceiling : ℕ) (h₁ : satisfiesC2 s₁ ceiling) (_h₂ : satisfiesC2 s₂ ceiling) :
    satisfiesC2 (glueSections s₁ s₂) ceiling := by
  show min s₁.authority s₂.authority ≤ ceiling
  exact (min_le_left s₁.authority s₂.authority).trans h₁

/-- THEOREM 6: discipline preserved by gluing. -/
theorem discipline_preserved_by_gluing {ι : Type*} (s₁ s₂ : Section ι)
    (ceiling : ℕ)
    (h₁ : satisfiesDiscipline s₁ ceiling) (h₂ : satisfiesDiscipline s₂ ceiling) :
    satisfiesDiscipline (glueSections s₁ s₂) ceiling :=
  ⟨C1_preserved_by_gluing s₁ s₂ h₁.1 h₂.1,
   C2_preserved_by_gluing s₁ s₂ ceiling h₁.2 h₂.2⟩
