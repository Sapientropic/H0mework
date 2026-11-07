import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Exit.Redemption.Native

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Exit.Redemption.Rate

open Source.Program PublicFunction.Repayment Abolition.Root Abolition.Root.Registered
open Innovation.Contribution.Pricing.Root.Runtime (Ready ReviewAvailable)

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]

local notation "C" => Evolving.Epoch.Current (Party := Party) (Good := Good) (Port := Port)
  (Technology := Technology) (Instrument := Instrument)

def required (source : C) (position : Position Party Instrument) : ℚ :=
  max 0 (essentials (sourceLaw source) (sourceOrigin source) position.creditor (unit (sourceLaw source) position) -
    creditorStock (sourceLaw source) source.raw position)

def available (source : C) (position : Position Party Instrument) : ℚ :=
  debtorStock (sourceLaw source) source.raw position -
    essentials (sourceLaw source) (sourceOrigin source) position.debtor (unit (sourceLaw source) position)

def minimum (source : C) (position : Position Party Instrument) (principal : ℚ) : ℚ :=
  required source position / principal

def maximum (source : C) (position : Position Party Instrument) (principal : ℚ) : ℚ :=
  available source position / principal

/-- Physical admissibility of an amount per principal unit at this cut.
The original instrument is paid at its installed denomination. -/
def Fits (source : C) (position : Position Party Instrument) (principal conversion : ℚ) : Prop :=
  0 < conversion ∧ required source position ≤ principal * conversion ∧
    principal * conversion ≤ available source position

theorem exact_conversion_corridor (source : C) (position : Position Party Instrument)
    (principal conversion : ℚ) (positive : 0 < principal) :
    Fits source position principal conversion ↔
      0 < conversion ∧ minimum source position principal ≤ conversion ∧
        conversion ≤ maximum source position principal := by
  unfold Fits minimum maximum
  rw [div_le_iff₀ positive, le_div_iff₀ positive, mul_comm conversion principal]

theorem the_original_instrument_pays_iff_its_rate_fits_both_original_bearers
    (source : C) (position : Position Party Instrument) (principal : ℚ) (positive : 0 < principal)
    (ready : Ready source) (review : ReviewAvailable source) :
    PaidAt source position principal ↔ position.debtor ≠ position.creditor ∧
      principal ≤ balance position source.raw ∧ Fits source position principal (rate (sourceLaw source) position) := by
  rw [actual_personal_redemption_domain_is_exact _ _ _ ready review]
  constructor
  · rintro ⟨distinct, positiveRate, inside⟩
    obtain ⟨_, claim, receiver, payer⟩ := (safe_iff_within _ _ _ _ _ positiveRate).mpr inside
    refine ⟨distinct, claim, positiveRate, ?_, ?_⟩
    · unfold required
      exact max_le (mul_nonneg positive.le positiveRate.le) (by linarith)
    · unfold available
      linarith
  · rintro ⟨distinct, claim, positiveRate, receiver, payer⟩
    refine ⟨distinct, positiveRate, (safe_iff_within _ _ _ _ _ positiveRate).mp
      ⟨positive.le, claim, ?_, ?_⟩⟩
    · unfold required at receiver
      have lower := (le_max_right (0 : ℚ) _).trans receiver
      linarith
    · unfold available at payer
      linarith

theorem the_conversion_endpoints_are_tight_in_original_material
    (source : C) (position : Position Party Instrument) (principal : ℚ) (positive : 0 < principal) :
    (∀ conversion, Fits source position principal conversion →
      minimum source position principal ≤ conversion ∧ conversion ≤ maximum source position principal) ∧
    (Fits source position principal (maximum source position principal) ↔
      0 < maximum source position principal ∧ minimum source position principal ≤ maximum source position principal) ∧
    (Fits source position principal (minimum source position principal) ↔
      0 < minimum source position principal ∧ minimum source position principal ≤ maximum source position principal) := by
  refine ⟨fun conversion fitted => ((exact_conversion_corridor _ _ _ _ positive).mp fitted).2, ?_, ?_⟩
  · rw [exact_conversion_corridor _ _ _ _ positive]
    simp
  · rw [exact_conversion_corridor _ _ _ _ positive]
    simp

theorem a_zero_material_lower_bound_is_approached_by_positive_conversions
    (source : C) (position : Position Party Instrument) (principal : ℚ) (positive : 0 < principal)
    (free : minimum source position principal = 0) (room : 0 < maximum source position principal) :
    ¬ Fits source position principal 0 ∧
      ∀ tolerance : ℚ, 0 < tolerance →
        ∃ conversion, Fits source position principal conversion ∧ conversion < tolerance := by
  refine ⟨fun absent => (lt_irrefl 0) absent.1, ?_⟩
  intro tolerance posTolerance
  let conversion := min (maximum source position principal) (tolerance / 2)
  have nonzero : 0 < conversion := lt_min room (by linarith)
  refine ⟨conversion, (exact_conversion_corridor _ _ _ _ positive).mpr
    ⟨nonzero, free.symm ▸ nonzero.le, min_le_left _ _⟩, ?_⟩
  exact (min_le_right _ _).trans_lt (by linarith)

end

end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Exit.Redemption.Rate
