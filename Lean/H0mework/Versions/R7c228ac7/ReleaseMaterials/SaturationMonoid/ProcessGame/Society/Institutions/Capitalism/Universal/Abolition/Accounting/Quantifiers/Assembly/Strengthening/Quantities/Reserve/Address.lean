import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Reserve.Prefix

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Reserve

open Source.Program

universe u

variable {Party Good Port Technology Instrument : Type u}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Instrument]
  (law : RawLaw Party Good Port Technology Instrument)

local notation "Current" => RawCurrent Party Good Technology Instrument
local notation "Word" => RawEvent Party Good Port Technology Instrument

def FitsAt (bearer : Party) (good : Good) (amount : ℚ) : Current → Word → Prop
  | _, [] => True
  | current, request :: tail =>
      ((bearer, good) ∈ (law.debit current request).map Prod.fst →
        flowAt (law.debit current request) bearer good - current.stock bearer good ≤ amount) ∧
      FitsAt bearer good amount (law.paidStep current request) tail

theorem fits_through_iff_all_addresses (reserve : Party → Good → ℚ)
    (current : Current) (word : Word) :
    FitsThrough law reserve current word ↔
      ∀ bearer good, FitsAt law bearer good (reserve bearer good) current word := by
  induction word generalizing current with
  | nil => simp [FitsThrough, FitsAt]
  | cons request tail ih =>
      rw [FitsThrough, ih]
      constructor
      · rintro ⟨first, rest⟩ bearer good
        refine ⟨?_, rest bearer good⟩
        rintro inside
        obtain ⟨cell, listed, address⟩ := List.mem_map.mp inside
        have bound := first cell listed
        rw [address] at bound
        exact bound
      · intro every
        refine ⟨?_, fun bearer good => (every bearer good).2⟩
        intro cell listed
        exact (every cell.1.1 cell.1.2).1 (List.mem_map.mpr ⟨cell, listed, rfl⟩)

theorem a_nonnegative_reserve_fits_at_its_original_address_iff_tight
    (bearer : Party) (good : Good) (amount : ℚ) (nonnegative : 0 ≤ amount)
    (current : Current) (word : Word) :
    FitsAt law bearer good amount current word ↔ minimumReserve law current word bearer good ≤ amount := by
  induction word generalizing current with
  | nil => simp [FitsAt, minimumReserve, nonnegative]
  | cons request tail ih =>
      simp only [FitsAt, minimumReserve, max_le_iff, ih]
      by_cases inside : (bearer, good) ∈ (law.debit current request).map Prod.fst
      · simp [firstNeed, inside, nonnegative]
      · simp [firstNeed, inside, nonnegative]

end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Reserve
