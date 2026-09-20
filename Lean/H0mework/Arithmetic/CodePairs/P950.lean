import H0mework.Arithmetic.CodePairs.P949

/-!
# Proposition 950: filtered code-pair gaps are permanent holonomy

P949 built the gauge-filtered generated spectrum.  This file gives the exact
residual-transport reading of the remaining producer:

```text
failure of filtered unit descent
  =
existence of a bounded allowed Boolean-atomic endpoint pair with nonzero
residual energy and no allowed one-unit successor.
```

So the next SU(7) physics statement can be written without ambiguity:
confinement must forbid these filtered raw code-pair permanent-holonomy cells.
-/

namespace SaturationMonoid
namespace StandardModelConstraint

noncomputable section

open SaturationMonoid.AffineRelaxation
open RunningSigmaBeta

set_option linter.defProp false

/-! ## Filtered raw code-pair permanent holonomy -/

/-- A filtered raw code-pair unit-permanent-holonomy cell.

It is an allowed bounded Boolean-atomic endpoint pair with nonzero residual
energy and no allowed bounded Boolean-atomic endpoint pair whose residual
energy is lower by exactly one. -/
def BoolGaugeFilteredRawCodePairUnitPermanentHolonomyCell
    (n bound : ℕ) (allowed : ℕ -> ℕ -> Bool)
    (left right : ℕ) : Prop :=
  allowed left right = true ∧
    left ∈ rawCodeBoundedList bound ∧
      right ∈ rawCodeBoundedList bound ∧
        natMultiplicativelyAtomicCheck left = true ∧
          natMultiplicativelyAtomicCheck right = true ∧
            rawCodePairResidualEnergy n left right ≠ 0 ∧
              ∀ left' right' : ℕ,
                allowed left' right' = true ->
                  left' ∈ rawCodeBoundedList bound ->
                    right' ∈ rawCodeBoundedList bound ->
                      natMultiplicativelyAtomicCheck left' = true ->
                        natMultiplicativelyAtomicCheck right' = true ->
                          rawCodePairResidualEnergy n left' right' + 1 ≠
                            rawCodePairResidualEnergy n left right

/-- The filtered raw code-pair sector forbids unit permanent holonomy. -/
def BoolGaugeFilteredRawCodePairForbidsUnitPermanentHolonomy
    (n bound : ℕ) (allowed : ℕ -> ℕ -> Bool) : Prop :=
  ∀ left right : ℕ,
    ¬ BoolGaugeFilteredRawCodePairUnitPermanentHolonomyCell
      n bound allowed left right

/-- Absence of filtered raw code-pair permanent holonomy is exactly the
filtered raw code-pair unit successor law of P949. -/
theorem noFilteredRawCodePairPermanentHolonomy_iff_unitSuccessorLaw
    (n bound : ℕ) (allowed : ℕ -> ℕ -> Bool) :
    BoolGaugeFilteredRawCodePairForbidsUnitPermanentHolonomy
      n bound allowed ↔
      BoolGaugeFilteredRawCodePairEnergyUnitSuccessorLaw
        n bound allowed := by
  constructor
  · intro H left right hallowed hleft_mem hright_mem
      hleft_check hright_check hnonzero
    by_contra hnone
    have hterminal :
        ∀ left' right' : ℕ,
          allowed left' right' = true ->
            left' ∈ rawCodeBoundedList bound ->
              right' ∈ rawCodeBoundedList bound ->
                natMultiplicativelyAtomicCheck left' = true ->
                  natMultiplicativelyAtomicCheck right' = true ->
                    rawCodePairResidualEnergy n left' right' + 1 ≠
                      rawCodePairResidualEnergy n left right := by
      intro left' right' hallowed' hleft'_mem hright'_mem
        hleft'_check hright'_check hsucc
      exact hnone
        ⟨left', right', hallowed', hleft'_mem, hright'_mem,
          hleft'_check, hright'_check, hsucc⟩
    exact H left right
      ⟨hallowed, hleft_mem, hright_mem, hleft_check, hright_check,
        hnonzero, hterminal⟩
  · intro H left right hperm
    rcases hperm with
      ⟨hallowed, hleft_mem, hright_mem, hleft_check, hright_check,
        hnonzero, hterminal⟩
    rcases
        H left right hallowed hleft_mem hright_mem
          hleft_check hright_check hnonzero with
      ⟨left', right', hallowed', hleft'_mem, hright'_mem,
        hleft'_check, hright'_check, hsucc⟩
    exact hterminal left' right' hallowed' hleft'_mem hright'_mem
      hleft'_check hright'_check hsucc

/-- A missing one-unit successor is exactly a filtered raw code-pair
permanent-holonomy cell. -/
theorem filteredRawCodePairPermanentHolonomyCell_of_no_unit_successor
    {n bound : ℕ} {allowed : ℕ -> ℕ -> Bool}
    {left right : ℕ}
    (hallowed : allowed left right = true)
    (hleft_mem : left ∈ rawCodeBoundedList bound)
    (hright_mem : right ∈ rawCodeBoundedList bound)
    (hleft_check : natMultiplicativelyAtomicCheck left = true)
    (hright_check : natMultiplicativelyAtomicCheck right = true)
    (hnonzero : rawCodePairResidualEnergy n left right ≠ 0)
    (hterminal :
      ∀ left' right' : ℕ,
        allowed left' right' = true ->
          left' ∈ rawCodeBoundedList bound ->
            right' ∈ rawCodeBoundedList bound ->
              natMultiplicativelyAtomicCheck left' = true ->
                natMultiplicativelyAtomicCheck right' = true ->
                  rawCodePairResidualEnergy n left' right' + 1 ≠
                    rawCodePairResidualEnergy n left right) :
    BoolGaugeFilteredRawCodePairUnitPermanentHolonomyCell
      n bound allowed left right :=
  ⟨hallowed, hleft_mem, hright_mem, hleft_check, hright_check,
    hnonzero, hterminal⟩

/-- Forbidding filtered raw code-pair permanent holonomy forbids unit
permanent holonomy in the filtered generated SU(7) spectrum. -/
theorem gaugeFilteredForbidsUnitPermanentHolonomy_of_noRawCodePairHolonomy
    {n bound : ℕ} {allowed : ℕ -> ℕ -> Bool}
    (H :
      BoolGaugeFilteredRawCodePairForbidsUnitPermanentHolonomy
        n bound allowed) :
    SU7RawBranchingSpectrumForbidsUnitPermanentHolonomy
      (gaugeFilteredRawBranchingSpectrum n bound allowed) :=
  gaugeFilteredForbidsUnitPermanentHolonomy_of_rawCodePairLaw
    ((noFilteredRawCodePairPermanentHolonomy_iff_unitSuccessorLaw
      n bound allowed).mp H)

/-! ## Certificate -/

/-- P950 certificate: filtered code-pair gaps are exactly permanent holonomy,
and forbidding them is sufficient to forbid unit permanent holonomy in the
filtered generated SU(7) spectrum. -/
structure SU7FilteredRawCodePairPermanentHolonomyCertificate where
  no_holonomy_iff_unit_successor :
    ∀ n bound : ℕ, ∀ allowed : ℕ -> ℕ -> Bool,
      BoolGaugeFilteredRawCodePairForbidsUnitPermanentHolonomy
        n bound allowed ↔
        BoolGaugeFilteredRawCodePairEnergyUnitSuccessorLaw
          n bound allowed
  no_successor_to_holonomy_cell :
    ∀ {n bound : ℕ} {allowed : ℕ -> ℕ -> Bool}
      {left right : ℕ},
      allowed left right = true ->
        left ∈ rawCodeBoundedList bound ->
          right ∈ rawCodeBoundedList bound ->
            natMultiplicativelyAtomicCheck left = true ->
              natMultiplicativelyAtomicCheck right = true ->
                rawCodePairResidualEnergy n left right ≠ 0 ->
                  (∀ left' right' : ℕ,
                    allowed left' right' = true ->
                      left' ∈ rawCodeBoundedList bound ->
                        right' ∈ rawCodeBoundedList bound ->
                          natMultiplicativelyAtomicCheck left' = true ->
                            natMultiplicativelyAtomicCheck right' = true ->
                              rawCodePairResidualEnergy n left' right' + 1 ≠
                                rawCodePairResidualEnergy n left right) ->
                    BoolGaugeFilteredRawCodePairUnitPermanentHolonomyCell
                      n bound allowed left right
  no_code_pair_holonomy_to_no_spectrum_holonomy :
    ∀ {n bound : ℕ} {allowed : ℕ -> ℕ -> Bool},
      BoolGaugeFilteredRawCodePairForbidsUnitPermanentHolonomy
        n bound allowed ->
        SU7RawBranchingSpectrumForbidsUnitPermanentHolonomy
          (gaugeFilteredRawBranchingSpectrum n bound allowed)

/-- Canonical P950 filtered raw code-pair permanent-holonomy certificate. -/
def su7FilteredRawCodePairPermanentHolonomyCertificate :
    SU7FilteredRawCodePairPermanentHolonomyCertificate where
  no_holonomy_iff_unit_successor :=
    noFilteredRawCodePairPermanentHolonomy_iff_unitSuccessorLaw
  no_successor_to_holonomy_cell := by
    intro n bound allowed left right hallowed hleft_mem hright_mem
      hleft_check hright_check hnonzero hterminal
    exact filteredRawCodePairPermanentHolonomyCell_of_no_unit_successor
      hallowed hleft_mem hright_mem hleft_check hright_check
      hnonzero hterminal
  no_code_pair_holonomy_to_no_spectrum_holonomy :=
    gaugeFilteredForbidsUnitPermanentHolonomy_of_noRawCodePairHolonomy


end
end StandardModelConstraint
end SaturationMonoid
