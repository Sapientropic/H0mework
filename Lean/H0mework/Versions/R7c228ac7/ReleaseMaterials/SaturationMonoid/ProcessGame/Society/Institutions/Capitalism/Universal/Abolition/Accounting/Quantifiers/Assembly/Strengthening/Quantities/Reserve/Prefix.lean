import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Reserve.Stock

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Reserve

open Source.Program

universe u

variable {Party Good Port Technology Instrument : Type u}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Instrument]
  (law : RawLaw Party Good Port Technology Instrument)

local notation "Current" => RawCurrent Party Good Technology Instrument
local notation "Word" => RawEvent Party Good Port Technology Instrument

/-- A single original debit address constrains the whole aggregate debit
at that address, including repeated goods in a bundle. -/
def firstNeed (current : Current) (request : Request Party Good Port Technology Instrument)
    (bearer : Party) (good : Good) : ℚ :=
  if (bearer, good) ∈ (law.debit current request).map Prod.fst then
    max 0 (flowAt (law.debit current request) bearer good - current.stock bearer good)
  else 0

omit [DecidableEq Instrument] in
theorem first_need_iff_stock (current : Current) (request : Request Party Good Port Technology Instrument)
    (reserve : Party → Good → ℚ) (nonnegative : ∀ bearer good, 0 ≤ reserve bearer good) :
    (∀ bearer good, firstNeed law current request bearer good ≤ reserve bearer good) ↔
      StockFits law current request reserve := by
  constructor
  · intro enough cell present
    have listed : cell.1 ∈ (law.debit current request).map Prod.fst :=
      List.mem_map.mpr ⟨cell, present, rfl⟩
    have bound := enough cell.1.1 cell.1.2
    rw [firstNeed, if_pos listed] at bound
    exact (le_max_right _ _).trans bound
  · intro enough bearer good
    unfold firstNeed
    split
    · rename_i present
      obtain ⟨cell, listed, address⟩ := List.mem_map.mp present
      have bound := enough cell listed
      rw [address] at bound
      exact max_le (nonnegative bearer good) bound
    · exact nonnegative bearer good

/-- Reserve is the greatest uncovered prefix debit at each address.
The fold computes the debits of the submitted word under paidStep.
The actual fold is related to it by the admission theorem. -/
def minimumReserve : Current → Word → Party → Good → ℚ
  | _, [], _, _ => 0
  | current, request :: tail, bearer, good =>
      max (firstNeed law current request bearer good)
        (minimumReserve (law.paidStep current request) tail bearer good)

def Guards (reserve : Party → Good → ℚ) : Current → Word → Prop
  | _, [] => True
  | current, request :: tail =>
      NonmaterialGuards law (current.addReserve reserve) request ∧ Guards reserve (law.paidStep current request) tail

def FitsThrough (reserve : Party → Good → ℚ) : Current → Word → Prop
  | _, [] => True
  | current, request :: tail =>
      StockFits law current request reserve ∧ FitsThrough reserve (law.paidStep current request) tail

def support : Current → Word → List (Party × Good)
  | _, [] => []
  | current, request :: tail =>
      (law.debit current request).map Prod.fst ++ support (law.paidStep current request) tail

theorem minimumReserve_nonnegative (current : Current) (word : Word) (bearer : Party) (good : Good) :
    0 ≤ minimumReserve law current word bearer good := by
  cases word with
  | nil => exact le_rfl
  | cons request tail =>
      have first : 0 ≤ firstNeed law current request bearer good := by
        unfold firstNeed
        split
        · exact le_max_left _ _
        · exact le_rfl
      exact first.trans (le_max_left _ _)

theorem no_reserve_is_needed_outside_original_debit_support
    (current : Current) (word : Word) (bearer : Party) (good : Good)
    (outside : (bearer, good) ∉ support law current word) :
    minimumReserve law current word bearer good = 0 := by
  induction word generalizing current with
  | nil => rfl
  | cons request tail ih =>
      rw [support, List.mem_append, not_or] at outside
      rw [minimumReserve, firstNeed, if_neg outside.1, ih _ outside.2, max_self]

theorem joint_reserve_bound_is_exact (current : Current) (word : Word)
    (reserve : Party → Good → ℚ) (nonnegative : ∀ bearer good, 0 ≤ reserve bearer good) :
    FitsThrough law reserve current word ↔
      ∀ bearer good, minimumReserve law current word bearer good ≤ reserve bearer good := by
  induction word generalizing current with
  | nil => simp [FitsThrough, minimumReserve, nonnegative]
  | cons request tail ih =>
      rw [FitsThrough, ← first_need_iff_stock law current request reserve nonnegative, ih]
      simp only [minimumReserve, max_le_iff]
      exact ⟨fun ⟨first, rest⟩ bearer good => ⟨first bearer good, rest bearer good⟩,
        fun bounds => ⟨fun bearer good => (bounds bearer good).1, fun bearer good => (bounds bearer good).2⟩⟩

end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Reserve
