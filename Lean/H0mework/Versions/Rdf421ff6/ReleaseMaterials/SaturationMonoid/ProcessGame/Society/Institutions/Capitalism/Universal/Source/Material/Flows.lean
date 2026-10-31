import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Source.Decoder.ActualInventory
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Source.Program.Conservation
import Mathlib.Algebra.Order.BigOperators.Group.List

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Source.Material

open Program Decoder

universe u
variable {Party Good Port Technology Instrument : Type u}
  [DecidableEq Party] [DecidableEq Good]
  (law : RawLaw Party Good Port Technology Instrument)

def otherPaid (item : ExecutionItem Party Good Port Technology Instrument)
    (party : Party) (good : Good) : ℚ :=
  match item.request.operation with
  | .use _ _ .necessity | .use _ _ .maintenance => 0
  | _ => paid law item party good

theorem paid_nonnegative (item : ExecutionItem Party Good Port Technology Instrument)
    (party : Party) (good : Good) : 0 ≤ paid law item party good := by
  by_cases accepted : law.Valid item.before item.request
  · simpa only [paid, RawLaw.actualDebit, if_pos accepted, flowAt] using
      amount_nonnegative (law.debit item.before item.request) accepted.2.2.2.1 (party, good)
  · simp [paid, RawLaw.actualDebit, accepted, flowAt, amount]

theorem acquired_nonnegative (item : ExecutionItem Party Good Port Technology Instrument)
    (party : Party) (good : Good) : 0 ≤ acquired law item party good := by
  by_cases accepted : law.Valid item.before item.request
  · simpa only [acquired, RawLaw.actualCredit, if_pos accepted, flowAt] using
      amount_nonnegative (law.credit item.before item.request) accepted.2.2.2.2.1 (party, good)
  · simp [acquired, RawLaw.actualCredit, accepted, flowAt, amount]

theorem consumed_nonnegative (purpose : Use) (item : ExecutionItem Party Good Port Technology Instrument)
    (party : Party) (good : Good) : 0 ≤ consumedFor law purpose item party good := by
  unfold consumedFor
  split
  · split <;> first | exact paid_nonnegative law item party good | exact le_refl _
  · exact le_refl _

theorem other_nonnegative (item : ExecutionItem Party Good Port Technology Instrument)
    (party : Party) (good : Good) : 0 ≤ otherPaid law item party good := by
  unfold otherPaid
  split <;> first | exact le_refl _ | exact paid_nonnegative law item party good

theorem outflow_partition (item : ExecutionItem Party Good Port Technology Instrument)
    (party : Party) (good : Good) :
    consumedFor law .necessity item party good + consumedFor law .maintenance item party good +
      otherPaid law item party good = paid law item party good := by
  cases operation : item.request.operation with
  | use bearer goods purpose => cases purpose <;> simp [consumedFor, otherPaid, operation]
  | _ => simp [consumedFor, otherPaid, operation]

def total (items : List (ExecutionItem Party Good Port Technology Instrument))
    (read : ExecutionItem Party Good Port Technology Instrument → ℚ) : ℚ := (items.map read).sum

omit [DecidableEq Party] [DecidableEq Good] in
theorem total_nonnegative (items : List (ExecutionItem Party Good Port Technology Instrument))
    (read : ExecutionItem Party Good Port Technology Instrument → ℚ)
    (positive : ∀ item ∈ items, 0 ≤ read item) : 0 ≤ total items read := by
  exact List.sum_nonneg (fun quantity present => by
    obtain ⟨item, inside, rfl⟩ := List.mem_map.mp present
    exact positive item inside)

theorem total_outflow_partition (items : List (ExecutionItem Party Good Port Technology Instrument))
    (party : Party) (good : Good) :
    total items (fun item => consumedFor law .necessity item party good) +
      total items (fun item => consumedFor law .maintenance item party good) +
      total items (fun item => otherPaid law item party good) = law.totalDebit items party good := by
  induction items with
  | nil => simp [total, RawLaw.totalDebit]
  | cons item tail ih =>
      have itemEq := outflow_partition law item party good
      simp only [total, RawLaw.totalDebit, List.map_cons, List.sum_cons] at ih ⊢
      change consumedFor law .necessity item party good + _ +
        (consumedFor law .maintenance item party good + _) +
        (otherPaid law item party good + _) = paid law item party good + _
      linarith

end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Source.Material
