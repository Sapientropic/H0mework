import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Material.Continuation.Balance.Support
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Settlement.NonFinancial

/-! Finite source instruction periods, including migration and maintenance.
Their exact material difference already includes every actual input/output;
adding a separate saved-input dividend would count that resource twice. -/

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Material.Dividend

open Source.Program

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Instrument]
  (law : RawLaw Party Good Port Technology Instrument)

def final (current : RawCurrent Party Good Technology Instrument) :
    List (RawEvent Party Good Port Technology Instrument) → RawCurrent Party Good Technology Instrument
  | [] => current
  | word :: later => final (law.next current word) later

def cells (current : RawCurrent Party Good Technology Instrument) :
    List (RawEvent Party Good Port Technology Instrument) → List (Party × Good)
  | [] => []
  | word :: later => Continuation.Balance.cells law current word ++ cells (law.next current word) later

def net (current : RawCurrent Party Good Technology Instrument) :
    List (RawEvent Party Good Port Technology Instrument) → Party → Good → ℚ
  | [], _, _ => 0
  | word :: later, person, good =>
      Continuation.Balance.gain law current word person good + net (law.next current word) later person good

theorem final_stock_is_exact_net (current : RawCurrent Party Good Technology Instrument)
    (periods : List (RawEvent Party Good Port Technology Instrument)) (person : Party) (good : Good) :
    (final law current periods).stock person good = current.stock person good + net law current periods person good := by
  induction periods generalizing current with
  | nil => simp only [final, net, add_zero]
  | cons word later induction =>
      change (final law (law.next current word) later).stock person good = _
      rw [induction]
      have first := Continuation.Balance.exact_stock_after_original_effects law current word person good
      change (law.next current word).stock person good = _ at first
      rw [first]
      exact add_assoc _ _ _

theorem no_effect_outside_actual_cells (current : RawCurrent Party Good Technology Instrument)
    (periods : List (RawEvent Party Good Port Technology Instrument)) (person : Party) (good : Good)
    (absent : (person, good) ∉ cells law current periods) : net law current periods person good = 0 := by
  induction periods generalizing current with
  | nil => rfl
  | cons word later induction =>
      have head : (person, good) ∉ Continuation.Balance.cells law current word :=
        fun inside => absent (List.mem_append_left _ inside)
      have tail : (person, good) ∉ cells law (law.next current word) later :=
        fun inside => absent (List.mem_append_right _ inside)
      obtain ⟨debit, credit⟩ := Continuation.Balance.no_effect_outside_original_support law current word person good head
      simp only [net, Continuation.Balance.gain, debit, credit, sub_self, induction _ tail, add_zero]

def NonFinancial (periods : List (RawEvent Party Good Port Technology Instrument)) : Prop :=
  ∀ word ∈ periods, Root.Settlement.NonFinancial word

instance (periods : List (RawEvent Party Good Port Technology Instrument)) : Decidable (NonFinancial periods) := by
  unfold NonFinancial
  infer_instance

theorem original_claims_are_retained (current : RawCurrent Party Good Technology Instrument)
    (periods : List (RawEvent Party Good Port Technology Instrument)) (checked : NonFinancial periods) :
    (final law current periods).claims = current.claims := by
  induction periods generalizing current with
  | nil => rfl
  | cons word later induction =>
      have head := checked word List.mem_cons_self
      have tail : NonFinancial later := fun item inside => checked item (List.mem_cons_of_mem _ inside)
      exact (induction (law.next current word) tail).trans (head.next_claims law current word)

#print axioms final_stock_is_exact_net
#print axioms no_effect_outside_actual_cells
#print axioms original_claims_are_retained

end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Material.Dividend
