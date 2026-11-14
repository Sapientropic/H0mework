import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Go.CriticalKomi.CoreHistory

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Go.CriticalKomi.CoreHistory

def footprint {n : Nat} (signature : BoardSignature n) (colour : Polarity) : Finset (Point n) :=
  Finset.univ.filter (fun point => TwoEye.History.signatureCell signature point = some colour)

theorem subset_footprint {n : Nat} (signature : BoardSignature n) (colour : Polarity)
    (core : Finset (Point n)) : core ⊆ footprint signature colour ↔
      ∀ point ∈ core, TwoEye.History.signatureCell signature point = some colour := by
  simp only [Finset.subset_iff, footprint, Finset.mem_filter, Finset.mem_univ, true_and]

def covered {n : Nat} (history : List (Finset (Point n))) (core : Finset (Point n)) : Bool :=
  history.any (fun old => decide (core ⊆ old))

theorem covered_iff {n : Nat} (history : List (Finset (Point n))) (core : Finset (Point n)) :
    covered history core = true ↔ ∃ old ∈ history, core ⊆ old := by
  simp only [covered, List.any_eq_true, decide_eq_true_eq]

def insertFootprint {n : Nat} (current : Finset (Point n)) (history : List (Finset (Point n))) :
    List (Finset (Point n)) :=
  if covered history current then history
  else current :: history.filter (fun old => !decide (old ⊆ current))

theorem covered_insert_iff {n : Nat} (current core : Finset (Point n))
    (history : List (Finset (Point n))) :
    covered (insertFootprint current history) core = true ↔ core ⊆ current ∨ covered history core = true := by
  unfold insertFootprint
  split
  · rename_i present
    obtain ⟨old, member, includes⟩ := (covered_iff history current).mp present
    constructor
    · exact Or.inr
    · rintro (inside | found)
      · exact (covered_iff history core).mpr ⟨old, member, inside.trans includes⟩
      · exact found
  · rw [covered_iff]
    constructor
    · rintro ⟨old, member, inside⟩
      rcases List.mem_cons.mp member with same | kept
      · subst old; exact Or.inl inside
      · exact Or.inr ((covered_iff history core).mpr ⟨old, (List.mem_filter.mp kept).1, inside⟩)
    · rintro (inside | found)
      · exact ⟨current, List.mem_cons_self, inside⟩
      · obtain ⟨old, member, inside⟩ := (covered_iff history core).mp found
        by_cases absorbed : old ⊆ current
        · exact ⟨current, List.mem_cons_self, inside.trans absorbed⟩
        · exact ⟨old, List.mem_cons_of_mem _ (List.mem_filter.mpr ⟨member, by simp [absorbed]⟩), inside⟩

def retain {n : Nat} (colour : Polarity) : List (Situation n) → List (Finset (Point n))
  | [] => []
  | previous :: rest => insertFootprint (footprint previous.board colour) (retain colour rest)

theorem covered_retain_iff {n : Nat} (colour : Polarity) (history : List (Situation n))
    (core : Finset (Point n)) :
    covered (retain colour history) core = true ↔
      ∃ previous ∈ history, ∀ point ∈ core, TwoEye.History.signatureCell previous.board point = some colour := by
  induction history with
  | nil => simp [retain, covered]
  | cons previous rest ih =>
      rw [retain, covered_insert_iff, subset_footprint, ih]
      constructor
      · rintro (first | ⟨old, member, occupied⟩)
        · exact ⟨previous, List.mem_cons_self, first⟩
        · exact ⟨old, List.mem_cons_of_mem _ member, occupied⟩
      · rintro ⟨old, member, occupied⟩
        rcases List.mem_cons.mp member with same | later
        · subst old; exact Or.inl occupied
        · exact Or.inr ⟨old, later, occupied⟩

/-- Removing a historically dominated footprint preserves every prospective
core-freshness query, without erasing the original frame history. -/
theorem fresh_iff_retained {n : Nat} (frame : Frame n) (colour : Polarity) (core : Finset (Point n)) :
    Fresh frame colour core ↔ covered (retain colour frame.positionHistory) core = false := by
  constructor
  · intro fresh
    cases result : covered (retain colour frame.positionHistory) core with
    | false => rfl
    | true =>
        obtain ⟨previous, member, occupied⟩ := (covered_retain_iff colour frame.positionHistory core).mp result
        exact False.elim (fresh previous member occupied)
  · intro absent previous member occupied
    have present := (covered_retain_iff colour frame.positionHistory core).mpr ⟨previous, member, occupied⟩
    rw [absent] at present
    cases present

end SaturationMonoid.ProcessGame.Go.CriticalKomi.CoreHistory
