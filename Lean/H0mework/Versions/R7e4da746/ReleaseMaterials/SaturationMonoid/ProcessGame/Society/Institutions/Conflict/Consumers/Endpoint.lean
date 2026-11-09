import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Consumers.Readback
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Root.RateDomain

set_option autoImplicit false
set_option maxRecDepth 8192

namespace SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Consumers.Evolving

open Conflict.Root

noncomputable section

abbrev OriginalShift := Shift source front levy settle 1

def actualSafeRates (shift : OriginalShift) : Set ℝ :=
  let caseAt : ShiftCase source := ⟨front, levy, settle, 1, shift⟩
  Choice.safeRates (admittedRates source decisionStock caseAt [] (fun _ => []) (fun _ => [peace]))
    (rateGap source decisionStock caseAt [] (fun _ => []) (fun _ => [peace]))

/-- The least rate in the original root's recomputed domain is actually
executed. Every smaller admitted rate retains a strict conflict advantage. -/
theorem the_original_root_rate_domain_attains_two_thirds :
    ∃ shift : OriginalShift, readShift source front levy settle 1 = .shifted shift ∧
      IsLeast (actualSafeRates shift) (2 / 3) := by
  obtain ⟨shift, discovered, named, bearer, quantity⟩ := the_original_incidence_reader_selects_the_old_row
  let caseAt : ShiftCase source := ⟨front, levy, settle, 1, shift⟩
  let war : ℚ → List W := fun _ => []
  let calm : ℚ → List W := fun _ => [peace]
  have interpretation := safe_rates_are_exactly_paid_comparable_rates source decisionStock caseAt [] war calm
  have same := exact_binding_word shift named bearer quantity
  have binding : Paid source (shift.returnedWord (2 / 3)) := by
    rw [same]
    exact bindingReturnPaid
  refine ⟨shift, discovered, ?_, ?_⟩
  · apply (interpretation (2 / 3)).mpr
    refine ⟨by norm_num, by norm_num, 2 / 3, by norm_num, ?_, 0, ?_, le_rfl⟩
    · intro word present
      change word ∈ [shift.returnedWord (2 / 3)] at present
      rw [List.mem_singleton.mp present]
      exact binding
    · change pressure source decisionStock [shift.returnedWord (2 / 3)] [peace] = some 0
      rw [pressure_of_two_paid_words decisionStock binding peacePaid, same, binding_return_is_a_paid_tie]
  · intro rate safe
    obtain ⟨_, _, rational, rfl, paid, margin, readMargin, nonpositive⟩ := (interpretation rate).mp safe
    have returned : Paid source (shift.returnedWord rational) := paid _ List.mem_cons_self
    change pressure source decisionStock [shift.returnedWord rational] [peace] = some margin at readMargin
    rw [pressure_of_two_paid_words decisionStock returned peacePaid] at readMargin
    apply le_of_not_gt
    intro smaller
    have castRate : ((2 / 3 : ℚ) : ℝ) = (2 / 3 : ℝ) := by norm_num
    have small : rational < (2 / 3 : ℚ) := (Rat.cast_lt (K := ℝ)).mp (by rw [castRate]; exact smaller)
    have profitable := every_smaller_executable_return_leaves_positive_pressure shift named quantity
      rational small returned
    have exactGap := Option.some.inj readMargin
    linarith

end

end SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Consumers.Evolving
