import H0mework.Versions.R5e4033a6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Recovery.PersonTime.MaterialLimit
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Recovery.PersonTime.Cohort.Conservation

open Source.Program
open scoped BigOperators

variable {Party Good Port Technology Instrument : Type}
  [Fintype Party] [DecidableEq Party] [DecidableEq Good] [DecidableEq Instrument]

local notation "Law" => RawLaw Party Good Port Technology Instrument
local notation "Raw" => RawCurrent Party Good Technology Instrument
local notation "RequestAt" => Request Party Good Port Technology Instrument

def stock (current : RawCurrent Party Good Technology Instrument) (good : Good) : ℚ :=
  ∑ person : Party, current.stock person good

omit [Fintype Party] [DecidableEq Instrument] in
private theorem located (owner person : Party) (goods : Bundle Good) (good : Good) :
    flowAt (locate owner goods) person good = if owner = person then amount Good goods good else 0 := by
  by_cases same : owner = person
  · subst owner
    simp only [flowAt, amount, locate, List.map_map, Function.comp_def, Prod.mk.injEq, true_and, if_true]
  · simp [flowAt, amount, locate, List.map_map, Function.comp_def, Prod.mk.injEq, same]

omit [DecidableEq Instrument] in
private theorem sum_located (owner : Party) (goods : Bundle Good) (good : Good) :
    (∑ person : Party, flowAt (locate owner goods) person good) = amount Good goods good := by
  simp only [located]
  rw [Finset.sum_eq_single owner]
  · simp
  · intro person _ different
    simp [Ne.symm different]
  · simp

omit [DecidableEq Instrument] in
private theorem credits_le_debits (law : Law) (current : Raw) (request : RequestAt)
    (good : Good) (noOutput : ∀ tech person, amount Good (law.technique tech person).outputs good = 0)
    (valid : law.Valid current request) :
    (∑ person : Party, flowAt (law.credit current request) person good) ≤
      ∑ person : Party, flowAt (law.debit current request) person good := by
  have debits : 0 ≤ ∑ person : Party, flowAt (law.debit current request) person good :=
    Finset.sum_nonneg fun person _ => amount_nonnegative _ valid.2.2.2.1 (person, good)
  cases kind : request.operation with
  | produce operator => simpa only [RawLaw.credit, kind, sum_located, noOutput] using debits
  | transfer | settle => simp only [RawLaw.credit, RawLaw.debit, kind, sum_located, le_refl]
  | use | issue | assign | revise | present => simpa [RawLaw.credit, kind, flowAt, amount] using debits

theorem stock_cannot_increase_in_one_instruction_without_output (law : Law) (current : Raw)
    (request : RequestAt) (good : Good)
    (noOutput : ∀ tech person, amount Good (law.technique tech person).outputs good = 0) :
    stock (law.step current request) good ≤ stock current good := by
  by_cases accepted : law.Valid current request
  · have consumption := credits_le_debits law current request good noOutput accepted
    have accounting : (∑ person : Party,
        ((law.step current request).stock person good + flowAt (law.actualDebit current request) person good)) =
        ∑ person : Party, (current.stock person good + flowAt (law.actualCredit current request) person good) :=
      Finset.sum_congr rfl (fun person _ => law.material_step_balance current request person good)
    simp only [Finset.sum_add_distrib, RawLaw.actualDebit, RawLaw.actualCredit, if_pos accepted] at accounting
    unfold stock
    linarith only [accounting, consumption]
  · rw [law.rejected_preserves_current current request accepted]

theorem stock_cannot_increase_in_an_original_word_without_output (law : Law) (current : Raw)
    (word : RawEvent Party Good Port Technology Instrument) (index : Nat) (good : Good)
    (noOutput : ∀ tech person, amount Good (law.technique tech person).outputs good = 0) :
    stock (law.execute current index word).final good ≤ stock current good := by
  induction word generalizing current index with
  | nil => exact le_rfl
  | cons request tail ih =>
    exact (ih (law.step current request) (index + 1)).trans
      (stock_cannot_increase_in_one_instruction_without_output law current request good noOutput)

end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Recovery.PersonTime.Cohort.Conservation
