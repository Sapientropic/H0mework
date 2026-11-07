import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Reserve.Address
import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Reserve.Funding
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Financing

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Reserve.Installation

open Source.Program PublicFunction.Financing

universe u

variable {Party Good Port Technology Instrument : Type u}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Instrument]
  {law : RawLaw Party Good Port Technology Instrument}
  {origin : RawCurrent Party Good Technology Instrument}
  {funding : RawEvent Party Good Port Technology Instrument}
  {terms : Terms Party Instrument}

local notation "Receipt" => Disbursement law origin funding terms
local notation "Word" => RawEvent Party Good Port Technology Instrument

def funds (_paid : Receipt) : ℚ := terms.principal * law.settlementRate terms.instrument

def address (_paid : Receipt) : Party × Good := (terms.borrower, law.settlementUnit terms.instrument)

def atBorrower (paid : Receipt) (amount : ℚ) (bearer : Party) (good : Good) : ℚ :=
  if (bearer, good) = (address paid) then amount else 0

def payoutAfter (paid : Receipt) := law.step paid.payout.before paid.payout.request

/-- Remove the material allocation at the funded address while leaving the
actual lender debit, rights, original claims and clock at their payout cut. -/
def reserveBaseline (paid : Receipt) := (payoutAfter paid).addReserve (atBorrower paid (-(funds paid)))

def retaining (paid : Receipt) (share : ℚ) := (reserveBaseline paid).addReserve (atBorrower paid (share * (funds paid)))

def floorShare (paid : Receipt) (word : Word) : ℚ :=
  minimumReserve law (reserveBaseline paid) word (address paid).1 (address paid).2 / (funds paid)

theorem funds_positive (paid : Receipt) : 0 < funds paid :=
  mul_pos paid.principal_positive paid.rate_positive

theorem floorShare_nonnegative (paid : Receipt) (word : Word) : 0 ≤ (floorShare paid word) :=
  div_nonneg (minimumReserve_nonnegative law (reserveBaseline paid) word _ _) (funds_positive paid).le

theorem the_full_share_is_the_literal_original_payout (paid : Receipt) :
    retaining paid 1 = payoutAfter paid := by
  apply RawCurrent.ext
  · funext bearer good
    change (payoutAfter paid).stock bearer good + atBorrower paid (-(funds paid)) bearer good +
        atBorrower paid (1 * (funds paid)) bearer good = _
    by_cases same : (bearer, good) = (address paid) <;> simp [atBorrower, same]
  · rfl
  · rfl
  · rfl
  · rfl

theorem every_share_keeps_the_original_lender_debit_and_principal (paid : Receipt) (share : ℚ) :
    (retaining paid share).stock terms.lender (law.settlementUnit terms.instrument) =
      paid.payout.before.stock terms.lender (law.settlementUnit terms.instrument) - (funds paid) ∧
    (retaining paid share).claims = (payoutAfter paid).claims := by
  have separate : (terms.lender, law.settlementUnit terms.instrument) ≠ (address paid) :=
    fun same => paid.distinct (congrArg Prod.fst same)
  refine ⟨?_, rfl⟩
  change (payoutAfter paid).stock terms.lender (law.settlementUnit terms.instrument) +
    atBorrower paid (-(funds paid)) terms.lender (law.settlementUnit terms.instrument) +
    atBorrower paid (share * (funds paid)) terms.lender (law.settlementUnit terms.instrument) = _
  simp only [atBorrower, if_neg separate, add_zero]
  exact paid.lender_paid_material

/-- Every material prefix of the original authored installation contributes
to one tight share. Rights are checked at the actual allocation and all
other bearers retain their original capacity checks. -/
theorem exact_share_iff_original_gates_and_material_floor
    (paid : Receipt) (word : Word) (share : ℚ) (nonnegative : 0 ≤ share) :
    Accepted law (retaining paid share) word ↔
      Guards law (atBorrower paid (share * (funds paid))) (reserveBaseline paid) word ∧
      (∀ bearer good, (bearer, good) ≠ (address paid) →
        FitsAt law bearer good 0 (reserveBaseline paid) word) ∧ (floorShare paid word) ≤ share := by
  unfold retaining
  rw [the_original_word_is_executable_iff_its_gates_and_joint_stock_fit, fits_through_iff_all_addresses]
  have localFloor := a_nonnegative_reserve_fits_at_its_original_address_iff_tight law
    (address paid).1 (address paid).2 (share * (funds paid)) (mul_nonneg nonnegative (funds_positive paid).le)
    (reserveBaseline paid) word
  have scale : (floorShare paid word) ≤ share ↔
      minimumReserve law (reserveBaseline paid) word (address paid).1 (address paid).2 ≤ share * (funds paid) :=
    div_le_iff₀ (funds_positive paid)
  constructor
  · rintro ⟨gates, every⟩
    refine ⟨gates, fun bearer good other => ?_, scale.mpr (localFloor.mp ?_)⟩
    · simpa only [atBorrower, if_neg other] using every bearer good
    · simpa [atBorrower, address] using every (address paid).1 (address paid).2
  · rintro ⟨gates, other, floor⟩
    refine ⟨gates, fun bearer good => ?_⟩
    by_cases same : (bearer, good) = (address paid)
    · obtain ⟨rfl, rfl⟩ := Prod.mk.inj same
      simpa [atBorrower, address] using localFloor.mpr (scale.mp floor)
    · simpa only [atBorrower, if_neg same] using other bearer good same

theorem the_checked_floor_is_the_least_share_and_exhaustion_names_the_borrower
    (paid : Receipt) (word : Word) :
    (∀ share, 0 ≤ share → Accepted law (retaining paid share) word → (floorShare paid word) ≤ share) ∧
      (Guards law (atBorrower paid (floorShare paid word * (funds paid))) (reserveBaseline paid) word →
        (∀ bearer good, (bearer, good) ≠ (address paid) → FitsAt law bearer good 0 (reserveBaseline paid) word) →
        Accepted law (retaining paid ((floorShare paid word))) word) ∧
      (1 < (floorShare paid word) → ∀ share, 0 ≤ share → share ≤ 1 →
        ¬ FitsAt law (address paid).1 (address paid).2 (share * (funds paid)) (reserveBaseline paid) word) := by
  refine ⟨fun share nonnegative accepted =>
    ((exact_share_iff_original_gates_and_material_floor paid word share nonnegative).mp accepted).2.2,
    fun guards other => (exact_share_iff_original_gates_and_material_floor paid word _
      (floorShare_nonnegative paid word)).mpr ⟨guards, other, le_rfl⟩, ?_⟩
  intro exceeds share nonnegative capped fit
  have enough := (a_nonnegative_reserve_fits_at_its_original_address_iff_tight law
    (address paid).1 (address paid).2 (share * (funds paid)) (mul_nonneg nonnegative (funds_positive paid).le)
    (reserveBaseline paid) word).mp fit
  exact (not_le_of_gt (capped.trans_lt exceeds)) ((div_le_iff₀ (funds_positive paid)).mpr enough)

end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Reserve.Installation
