import Mathlib.Analysis.ODE.Transform
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Tactic.Linarith

set_option autoImplicit false

namespace LAlanineTrueTube.Signed

open Set
noncomputable section

variable {E : Type*}

/-- The negative-time restriction uses the same generated negative branch, with reversed clock. -/
def full (negative positive : ℝ → E) (s : ℝ) : E :=
  if s ≤ 0 then negative (-s) else positive s

theorem full_left (negative positive : ℝ → E) (s : ℝ) (hs : s ≤ 0) :
    full negative positive s = negative (-s) := if_pos hs

theorem full_right {negative positive : ℝ → E} (same : negative 0 = positive 0)
    (s : ℝ) (hs : 0 ≤ s) : full negative positive s = positive s := by
  by_cases zero : s = 0
  · subst s
    simpa [full] using same
  · exact if_neg (not_le.mpr (lt_of_le_of_ne hs (Ne.symm zero)))

@[simp] theorem full_zero (negative positive : ℝ → E) :
    full negative positive 0 = negative 0 := by simp [full]

theorem full_mem {negative positive : ℝ → E} {h s : ℝ} {domain : Set E}
    (left : ∀ t ∈ Icc 0 h, negative t ∈ domain)
    (right : ∀ t ∈ Icc 0 h, positive t ∈ domain)
    (time : s ∈ Icc (-h) h) : full negative positive s ∈ domain := by
  by_cases hs : s ≤ 0
  · rw [full_left _ _ _ hs]
    exact left (-s) ⟨neg_nonneg.mpr hs, by linarith [time.1]⟩
  · rw [full, if_neg hs]
    exact right s ⟨(not_le.mp hs).le, time.2⟩

theorem full_eqOn {negative positive negative' positive' : ℝ → E} {h : ℝ}
    (left : EqOn negative negative' (Icc 0 h))
    (right : EqOn positive positive' (Icc 0 h)) :
    EqOn (full negative positive) (full negative' positive') (Icc (-h) h) := by
  intro s time
  by_cases hs : s ≤ 0
  · rw [full_left _ _ _ hs, full_left _ _ _ hs]
    exact left ⟨neg_nonneg.mpr hs, by linarith [time.1]⟩
  · simp only [full, if_neg hs]
    exact right ⟨(not_le.mp hs).le, time.2⟩

variable [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem reversed_integralCurve {negative : ℝ → E} {field : E → E} {h : ℝ}
    (law : IsIntegralCurveOn negative (fun _ x => -field x) (Icc 0 h)) :
    IsIntegralCurveOn (fun s => negative (-s)) (fun _ => field) (Icc (-h) 0) := by
  intro s time
  have sourceTime : -s ∈ Icc 0 h := ⟨neg_nonneg.mpr time.2, by linarith [time.1]⟩
  have derivative := (law (-s) sourceTime).scomp s
    (hasDerivAt_id s).neg.hasDerivWithinAt
    (show MapsTo (fun t : ℝ => -t) (Icc (-h) 0) (Icc 0 h) from
      fun t ht => ⟨neg_nonneg.mpr ht.2, by linarith [ht.1]⟩)
  simpa only [Function.comp_def, neg_smul, one_smul, neg_neg] using derivative

end
end LAlanineTrueTube.Signed
