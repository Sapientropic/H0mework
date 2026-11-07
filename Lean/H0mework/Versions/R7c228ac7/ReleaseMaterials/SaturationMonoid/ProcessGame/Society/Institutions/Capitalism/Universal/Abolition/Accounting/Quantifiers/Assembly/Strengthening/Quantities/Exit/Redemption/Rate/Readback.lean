import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Exit.Redemption.Rate.Material

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Exit.Redemption.Rate

open Source.Program PublicFunction.Repayment Abolition.Root Abolition.Root.Registered

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Instrument]

local notation "C" => Evolving.Epoch.Current (Party := Party) (Good := Good) (Port := Port)
  (Technology := Technology) (Instrument := Instrument)
local notation "Law" => RawLaw Party Good Port Technology Instrument
local notation "Raw" => RawCurrent Party Good Technology Instrument

structure Movement where
  principal : ℚ
  received : ℚ
  spent : ℚ

def movement (law : Law) (position : Position Party Instrument) (before after : Raw) : Movement :=
  ⟨balance position before - balance position after,
    creditorStock law after position - creditorStock law before position,
    debtorStock law before position - debtorStock law after position⟩

def Movement.reconciles (actual : Movement) (conversion : ℚ) : Prop :=
  actual.received = actual.principal * conversion ∧ actual.spent = actual.principal * conversion

def Movement.rate? (actual : Movement) : Option ℚ :=
  if 0 < actual.principal then some (actual.received / actual.principal) else none

theorem a_paid_leg_reconciles_both_material_addresses_with_its_own_principal
    (law : Law) (position : Position Party Instrument) (before : Raw) (quantity : ℚ)
    (distinct : position.debtor ≠ position.creditor) (paid : law.Valid before (request law position quantity)) :
    movement law position before (law.step before (request law position quantity)) =
      ⟨quantity, quantity * rate law position, quantity * rate law position⟩ := by
  obtain ⟨creditor, debtor, principal⟩ := paid_leg_moves_original_stock_and_claim law before position quantity distinct paid
  change balance position (law.step before (request law position quantity)) = _ at principal
  change creditorStock law (law.step before (request law position quantity)) position = _ at creditor
  change debtorStock law (law.step before (request law position quantity)) position = _ at debtor
  unfold movement
  rw [principal, creditor, debtor]
  congr 1 <;> ring

theorem positive_paid_principal_identifies_one_rate_for_both_original_bearers
    (law : Law) (position : Position Party Instrument) (before : Raw) (quantity : ℚ)
    (distinct : position.debtor ≠ position.creditor) (paid : law.Valid before (request law position quantity))
    (positive : 0 < quantity) :
    let actual := movement law position before (law.step before (request law position quantity))
    actual.rate? = some (rate law position) ∧
      ∀ conversion, actual.reconciles conversion ↔ conversion = rate law position := by
  dsimp only
  rw [a_paid_leg_reconciles_both_material_addresses_with_its_own_principal law position before quantity distinct paid]
  refine ⟨?_, fun conversion => ⟨?_, ?_⟩⟩
  · unfold Movement.rate?
    rw [if_pos positive, mul_comm quantity, mul_div_cancel_right₀ _ positive.ne']
  · intro agreed
    exact (mul_left_cancel₀ positive.ne' agreed.1).symm
  · rintro rfl
    exact ⟨rfl, rfl⟩

theorem zero_payment_leaves_all_conversions_unidentified
    (law : Law) (position : Position Party Instrument) (before : Raw)
    (distinct : position.debtor ≠ position.creditor) (paid : law.Valid before (request law position 0)) :
    let actual := movement law position before (law.step before (request law position 0))
    actual.rate? = none ∧ ∀ conversion, actual.reconciles conversion := by
  dsimp only
  rw [a_paid_leg_reconciles_both_material_addresses_with_its_own_principal law position before 0 distinct paid]
  simp [Movement.rate?, Movement.reconciles]

variable [DecidableEq Port]

theorem the_rate_is_recovered_from_the_literal_original_paid_successor
    (source : C) (position : Position Party Instrument) (quantity : ℚ)
    (paid : PaidAt source position quantity) (positive : 0 < quantity) :
    let target := Execution.endAt source (script source position quantity)
    let actual := movement (sourceLaw source) position source.raw target.raw
    actual.rate? = some (rate (sourceLaw source) position) ∧
      (∀ conversion, actual.reconciles conversion ↔ conversion = rate (sourceLaw source) position) ∧
      Recorded source (script source position quantity) := by
  dsimp only
  rw [paid.readback]
  obtain ⟨identified, unique⟩ := positive_paid_principal_identifies_one_rate_for_both_original_bearers
    (sourceLaw source) position source.raw quantity paid.safe.1 paid.safe.2.1 positive
  exact ⟨identified, unique, paid.complete⟩

end

end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Exit.Redemption.Rate
