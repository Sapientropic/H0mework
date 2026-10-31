import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Review.MicroBudget

/-! Actual fee traces use only paid microsteps. Instruction indices locate
the original requests; they do not advance the source period clock. -/

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Review

open Source.Program

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Instrument]
  (law : RawLaw Party Good Port Technology Instrument)

theorem execution_final_independent_of_index
    (current : RawCurrent Party Good Technology Instrument)
    (word : RawEvent Party Good Port Technology Instrument) (left right : Nat) :
    (law.execute current left word).final = (law.execute current right word).final := by
  induction word generalizing current left right with
  | nil => rfl
  | cons request tail induction => exact induction (law.step current request) (left + 1) (right + 1)

theorem execution_preserves_period
    (current : RawCurrent Party Good Technology Instrument)
    (word : RawEvent Party Good Port Technology Instrument) (index : Nat) :
    (law.execute current index word).final.clock = current.clock ∧
      (law.execute current index word).final.round = current.round := by
  induction word generalizing current index with
  | nil => exact ⟨rfl, rfl⟩
  | cons request tail induction =>
      have remaining := induction (law.step current request) (index + 1)
      have step : (law.step current request).clock = current.clock ∧
          (law.step current request).round = current.round := by
        unfold RawLaw.step
        split <;> exact ⟨rfl, rfl⟩
      exact ⟨remaining.1.trans step.1, remaining.2.trans step.2⟩

namespace PaidMicroRun

variable {law} {request : Request Party Good Port Technology Instrument}
  {start target : RawCurrent Party Good Technology Instrument} {count : Nat}
  (run : PaidMicroRun law request start target count)

include run in
theorem execution_is_the_original_fee_word (index : Nat) :
    (law.execute start index (List.replicate count request)).final = target := by
  induction run generalizing index with
  | nil => rfl
  | snoc prior payment induction =>
      rw [List.replicate_add, List.replicate_one, law.execute_append]
      dsimp only
      rw [induction index]
      rfl

def execution (_run : PaidMicroRun law request start target count) :=
  law.execute start 0 (List.replicate count request)

theorem execution_has_exactly_the_paid_requests :
    run.execution.items.map ExecutionItem.request = List.replicate count request :=
  law.inventory_requests_exact start 0 _

theorem execution_reaches_original_current : run.execution.final = target :=
  run.execution_is_the_original_fee_word 0

end PaidMicroRun

end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Review

#print axioms SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Review.PaidMicroRun.execution_reaches_original_current
