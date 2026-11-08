import H0mework.Versions.R5e4033a6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Clock.Mandate.SafeTerm.Guard

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Clock.Mandate.SafeTerm

structure Interval where
  lower : Option ℚ
  upper : Option ℚ
  deriving DecidableEq

namespace Interval

def Holds (window : Interval) (cutoff : ℚ) : Prop :=
  (∀ lower, window.lower = some lower → lower ≤ cutoff) ∧
    (∀ upper, window.upper = some upper → cutoff < upper)

instance (window : Interval) (cutoff : ℚ) : Decidable (window.Holds cutoff) := by
  rcases window with ⟨lower, upper⟩
  cases lower <;> cases upper <;> unfold Holds <;> simp <;> infer_instance

def insert (window : Interval) : Guard → Interval
  | .any => window
  | .atLeast clock => {window with lower := some (window.lower.elim clock (max clock))}
  | .below clock => {window with upper := some (window.upper.elim clock (min clock))}

theorem insert_holds_iff (window : Interval) (guard : Guard) (cutoff : ℚ) :
    (window.insert guard).Holds cutoff ↔ window.Holds cutoff ∧ guard.Holds cutoff := by
  rcases window with ⟨lower, upper⟩
  cases guard with
  | any => simp [insert, Guard.Holds]
  | atLeast clock =>
    cases lower <;> simp [insert, Holds, Guard.Holds, and_assoc, and_comm]
  | below clock =>
    cases upper <;> simp [insert, Holds, Guard.Holds, and_assoc, and_comm]

def ofGuards (guards : List Guard) : Interval :=
  guards.foldr (fun guard window => window.insert guard) ⟨none, none⟩

theorem of_guards_holds_iff (guards : List Guard) (cutoff : ℚ) :
    (ofGuards guards).Holds cutoff ↔ ∀ guard ∈ guards, guard.Holds cutoff := by
  induction guards with
  | nil => simp [ofGuards, Holds]
  | cons guard tail ih =>
    change ((ofGuards tail).insert guard).Holds cutoff ↔ _
    rw [insert_holds_iff, ih]
    simp [and_comm]

theorem lower_is_an_original_guard (guards : List Guard) (clock : ℚ)
    (found : (ofGuards guards).lower = some clock) : Guard.atLeast clock ∈ guards := by
  induction guards with
  | nil => cases found
  | cons guard tail ih =>
    change ((ofGuards tail).insert guard).lower = some clock at found
    cases guard with
    | any => exact List.mem_cons_of_mem _ (ih found)
    | below time => exact List.mem_cons_of_mem _ (ih found)
    | atLeast time =>
      cases prior : (ofGuards tail).lower with
      | none =>
        have same : time = clock := by simpa [insert, prior] using found
        exact List.mem_cons.mpr (Or.inl (congrArg Guard.atLeast same.symm))
      | some old =>
        have same : max time old = clock := by simpa [insert, prior] using found
        rcases le_total time old with upper | lower
        · rw [max_eq_right upper] at same
          exact List.mem_cons_of_mem _ (ih (prior.trans (congrArg some same)))
        · rw [max_eq_left lower] at same
          exact List.mem_cons.mpr (Or.inl (congrArg Guard.atLeast same.symm))

theorem upper_is_an_original_guard (guards : List Guard) (clock : ℚ)
    (found : (ofGuards guards).upper = some clock) : Guard.below clock ∈ guards := by
  induction guards with
  | nil => cases found
  | cons guard tail ih =>
    change ((ofGuards tail).insert guard).upper = some clock at found
    cases guard with
    | any => exact List.mem_cons_of_mem _ (ih found)
    | atLeast time => exact List.mem_cons_of_mem _ (ih found)
    | below time =>
      cases prior : (ofGuards tail).upper with
      | none =>
        have same : time = clock := by simpa [insert, prior] using found
        exact List.mem_cons.mpr (Or.inl (congrArg Guard.below same.symm))
      | some old =>
        have same : min time old = clock := by simpa [insert, prior] using found
        rcases le_total time old with lower | upper
        · rw [min_eq_left lower] at same
          exact List.mem_cons.mpr (Or.inl (congrArg Guard.below same.symm))
        · rw [min_eq_right upper] at same
          exact List.mem_cons_of_mem _ (ih (prior.trans (congrArg some same)))

theorem exists_iff (window : Interval) :
    (∃ cutoff, window.Holds cutoff) ↔ ∀ lower upper, window.lower = some lower →
      window.upper = some upper → lower < upper := by
  refine ⟨?_, ?_⟩
  · rintro ⟨cutoff, minimum, maximum⟩ lower upper lowerAt upperAt
    exact (minimum lower lowerAt).trans_lt (maximum upper upperAt)
  · intro consistent
    rcases window with ⟨lower, upper⟩
    cases lower with
    | none =>
      cases upper with
      | none => exact ⟨0, by simp [Holds]⟩
      | some stop => exact ⟨stop - 1, by simp [Holds]⟩
    | some start =>
      refine ⟨start, ?_, ?_⟩
      · intro value same
        exact (Option.some.inj same).ge
      · intro value same
        exact consistent start value rfl same

theorem closed_lower (window : Interval) (lower : ℚ) (found : window.lower = some lower)
    (feasible : ∃ cutoff, window.Holds cutoff) : IsLeast {cutoff | window.Holds cutoff} lower := by
  obtain ⟨cutoff, minimum, maximum⟩ := feasible
  exact ⟨⟨fun _ same => (Option.some.inj (same.symm.trans found)).le,
      fun upper same => (minimum lower found).trans_lt (maximum upper same)⟩,
    fun _ safe => safe.1 lower found⟩

theorem open_upper (window : Interval) (upper : ℚ) (found : window.upper = some upper)
    (feasible : ∃ cutoff, window.Holds cutoff) :
    IsLUB {cutoff | window.Holds cutoff} upper ∧ ¬ window.Holds upper ∧
      ∀ before < upper, ∃ cutoff, before < cutoff ∧ window.Holds cutoff := by
  obtain ⟨first, firstLower, firstUpper⟩ := feasible
  have approach : ∀ before < upper, ∃ cutoff, before < cutoff ∧ window.Holds cutoff := by
    intro before early
    let cutoff := (max first before + upper) / 2
    have room := max_lt_iff.mpr ⟨firstUpper upper found, early⟩
    have earlier : max first before < cutoff := by dsimp [cutoff]; linarith
    have later : cutoff < upper := by dsimp [cutoff]; linarith
    exact ⟨cutoff, (le_max_right first before).trans_lt earlier,
      ⟨fun lower same => (firstLower lower same).trans ((le_max_left first before).trans earlier.le),
        fun stop same => (Option.some.inj (found.symm.trans same)) ▸ later⟩⟩
  refine ⟨⟨fun _ safe => (safe.2 upper found).le, ?_⟩, fun safe => (lt_irrefl upper) (safe.2 upper found), approach⟩
  intro ceiling bounds
  apply le_of_not_gt
  intro early
  obtain ⟨cutoff, later, safe⟩ := approach ceiling early
  exact (not_lt_of_ge (bounds safe)) later

theorem unbounded_without_upper (window : Interval) (absent : window.upper = none)
    (feasible : ∃ cutoff, window.Holds cutoff) :
    ∀ before, ∃ cutoff, before < cutoff ∧ window.Holds cutoff := by
  obtain ⟨first, firstLower, _⟩ := feasible
  intro before
  let cutoff := max first before + 1
  have later : max first before < cutoff := by dsimp [cutoff]; linarith
  refine ⟨cutoff, (le_max_right first before).trans_lt later, ?_, ?_⟩
  · intro lower found
    exact (firstLower lower found).trans ((le_max_left first before).trans later.le)
  · intro upper found
    rw [absent] at found
    cases found

end Interval

end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Clock.Mandate.SafeTerm
