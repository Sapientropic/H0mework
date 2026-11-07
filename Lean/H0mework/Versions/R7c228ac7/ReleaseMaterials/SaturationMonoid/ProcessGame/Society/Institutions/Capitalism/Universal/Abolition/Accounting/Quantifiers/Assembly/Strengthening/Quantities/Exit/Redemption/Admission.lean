import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Exit.Redemption.Source

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Exit.Redemption

open Source.Program PublicFunction.Repayment

section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Instrument]

variable (law : RawLaw Party Good Port Technology Instrument)
  (origin current : RawCurrent Party Good Technology Instrument)
  (position : Position Party Instrument)

def request (quantity : ℚ) : Request Party Good Port Technology Instrument :=
  ⟨position.creditor, [], law.issuerPort position.instrument, [],
    .settle position.instrument position.debtor position.creditor quantity⟩

def Authorized (quantity : ℚ) : Prop :=
  law.operationAllowed current (request law position quantity) = true ∧
    ∀ port ∈ law.requiredPorts current (request law position quantity),
      law.allowed current.technology port position.creditor = true

omit [DecidableEq Instrument] in
private theorem debit_capacity (quantity : ℚ) :
    (∀ item ∈ law.debit current (request law position quantity),
      flowAt (law.debit current (request law position quantity)) item.1.1 item.1.2 ≤
        current.stock item.1.1 item.1.2) ↔
    quantity * rate law position ≤ debtorStock law current position := by
  simp [request, RawLaw.debit, locate, flowAt, amount, debtorStock]

omit [DecidableEq Instrument] in
theorem valid_iff_original_gates_and_capacity (quantity : ℚ) :
    law.Valid current (request law position quantity) ↔
    Authorized law current position quantity ∧ 0 ≤ quantity ∧
      quantity ≤ balance position current ∧ 0 < rate law position ∧
      quantity * rate law position ≤ debtorStock law current position := by
  constructor
  · intro checked
    have gates : Authorized law current position quantity :=
      ⟨checked.1.2, fun port present => (checked.2.1 port present).resolve_right (by simp [request])⟩
    have claim : 0 ≤ quantity ∧ quantity ≤ balance position current ∧ 0 < rate law position :=
      checked.2.2.1
    exact ⟨gates, claim.1, claim.2.1, claim.2.2, (debit_capacity law current position quantity).mp checked.2.2.2.2.2⟩
  · rintro ⟨gates, nonnegative, claim, positive, stocked⟩
    have material := mul_nonneg nonnegative positive.le
    refine ⟨⟨trivial, gates.1⟩, fun port present => Or.inl (gates.2 port present),
      ⟨nonnegative, claim, positive⟩, ?_, ?_, (debit_capacity law current position quantity).mpr stocked⟩
    · simpa [request, RawLaw.debit, locate, NonnegativeBundle] using material
    · simpa [request, RawLaw.credit, locate, NonnegativeBundle] using material

theorem paid_leg_moves_original_stock_and_claim (quantity : ℚ)
    (different : position.debtor ≠ position.creditor)
    (paid : law.Valid current (request law position quantity)) :
    (law.step current (request law position quantity)).stock position.creditor (unit law position) =
        creditorStock law current position + quantity * rate law position ∧
    (law.step current (request law position quantity)).stock position.debtor (unit law position) =
        debtorStock law current position - quantity * rate law position ∧
    (law.step current (request law position quantity)).claims position.instrument position.debtor position.creditor =
        balance position current - quantity := by
  rw [RawLaw.step, if_pos paid]
  simp [RawLaw.paidStep, RawLaw.debit, RawLaw.credit, RawLaw.nextClaims, request, locate, flowAt, amount,
    creditorStock, debtorStock, balance, different, Ne.symm different]

def Safe (quantity : ℚ) : Prop :=
  position.debtor ≠ position.creditor ∧ law.Valid current (request law position quantity) ∧
    essentials law origin position.creditor (unit law position) ≤
      (law.step current (request law position quantity)).stock position.creditor (unit law position) ∧
    essentials law origin position.debtor (unit law position) ≤
      (law.step current (request law position quantity)).stock position.debtor (unit law position)

theorem safe_iff_original_authority_and_tight_material_interval (quantity : ℚ) :
    Safe law origin current position quantity ↔
      position.debtor ≠ position.creditor ∧ 0 < rate law position ∧
      Within law origin current position quantity ∧ Authorized law current position quantity := by
  constructor
  · rintro ⟨distinct, valid, recipient, payer⟩
    obtain ⟨gates, nonneg, principal, positive, _⟩ :=
      (valid_iff_original_gates_and_capacity law current position quantity).mp valid
    have paid := paid_leg_moves_original_stock_and_claim law current position quantity distinct valid
    rw [paid.1] at recipient
    rw [paid.2.1] at payer
    exact ⟨distinct, positive, (safe_iff_within law origin current position quantity positive).mp
      ⟨nonneg, principal, recipient, payer⟩, gates⟩
  · rintro ⟨distinct, positive, within, gates⟩
    obtain ⟨nonneg, principal, recipient, payer⟩ :=
      (safe_iff_within law origin current position quantity positive).mpr within
    have reserve_nonnegative : 0 ≤ essentials law origin position.debtor (unit law position) := le_max_left _ _
    have valid := (valid_iff_original_gates_and_capacity law current position quantity).mpr
      ⟨gates, nonneg, principal, positive, by linarith⟩
    have paid := paid_leg_moves_original_stock_and_claim law current position quantity distinct valid
    exact ⟨distinct, valid, paid.1.symm ▸ recipient, paid.2.1.symm ▸ payer⟩

end

end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Exit.Redemption
