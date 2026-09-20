import H0mework.Arithmetic.CodePairs.P947

/-!
# Proposition 948: raw all-pair unit descent is too strong

P947 lowered generated unit confinement to raw code-pair unit descent.  This
file pins down the boundary of that move: if the law is read over *all*
bounded Boolean-atomic endpoint pairs, it is already false in a small fiber.

So the next producer cannot be "all raw code pairs descend by one unit."  It
must be a genuine SU(7) allowed-sector theorem: confinement has to select the
physical branch sector on which unit holonomy is forbidden.
-/

namespace SaturationMonoid
namespace StandardModelConstraint

noncomputable section

open SaturationMonoid.AffineRelaxation
open RunningSigmaBeta

set_option linter.defProp false

/-! ## A concrete obstruction to raw all-pair unit descent -/

/-- The endpoint code `3` passes the finite multiplicative-atomicity checker.
-/
theorem natMultiplicativelyAtomicCheck_three :
    natMultiplicativelyAtomicCheck 3 = true := by
  unfold natMultiplicativelyAtomicCheck natHasNontrivialDivisorCheck
  norm_num
  intro x hx htwo hlt hdiv
  interval_cases x
  norm_num at hdiv

/-- The endpoint code `3` is present in the bound-`3` raw-code list. -/
theorem three_mem_rawCodeBoundedList_three :
    3 ∈ rawCodeBoundedList 3 := by
  simp [rawCodeBoundedList]

/-- In the even fiber `12`, the raw pair `(3, 3)` has residual energy `6`. -/
theorem rawCodePairResidualEnergy_six_three_three :
    rawCodePairResidualEnergy 6 3 3 = 6 := by
  norm_num [rawCodePairResidualEnergy, rawCodePairResidual]

/-- Bound `3` contains no Boolean-atomic raw code pair with residual energy
`5` in the even fiber `12`. -/
theorem no_rawCodePairResidualEnergy_five_six_bound_three :
    ¬ ∃ left right : ℕ,
      left ∈ rawCodeBoundedList 3 ∧
        right ∈ rawCodeBoundedList 3 ∧
          natMultiplicativelyAtomicCheck left = true ∧
            natMultiplicativelyAtomicCheck right = true ∧
              rawCodePairResidualEnergy 6 left right = 5 := by
  rintro ⟨left, right, hleft_mem, hright_mem,
    hleft_check, hright_check, henergy⟩
  simp [rawCodeBoundedList] at hleft_mem hright_mem
  interval_cases left <;> interval_cases right <;>
    norm_num [natMultiplicativelyAtomicCheck, natHasNontrivialDivisorCheck,
      rawCodePairResidualEnergy, rawCodePairResidual] at *

/-- Consequently, the raw all-pair unit successor law from P947 fails for
fiber `n = 6` and bound `3`.

The obstruction is the generated Boolean-atomic pair `(3, 3)`: its residual
energy is `6`, but there is no bounded Boolean-atomic pair at energy `5`.
-/
theorem not_RawCodePairEnergyUnitSuccessorLaw_six_three :
    ¬ RawCodePairEnergyUnitSuccessorLaw 6 3 := by
  intro H
  have hnonzero :
      rawCodePairResidualEnergy 6 3 3 ≠ 0 := by
    norm_num [rawCodePairResidualEnergy, rawCodePairResidual]
  rcases
      H 3 3
        three_mem_rawCodeBoundedList_three
        three_mem_rawCodeBoundedList_three
        natMultiplicativelyAtomicCheck_three
        natMultiplicativelyAtomicCheck_three
        hnonzero with
    ⟨left', right', hleft'_mem, hright'_mem,
      hleft'_check, hright'_check, hsucc⟩
  have henergy5 :
      rawCodePairResidualEnergy 6 left' right' = 5 := by
    have hpair : rawCodePairResidualEnergy 6 3 3 = 6 :=
      rawCodePairResidualEnergy_six_three_three
    omega
  exact no_rawCodePairResidualEnergy_five_six_bound_three
    ⟨left', right', hleft'_mem, hright'_mem,
      hleft'_check, hright'_check, henergy5⟩

/-! ## The corrected producer shape -/

/-- A gauge-filtered raw code-pair unit successor law.

The filter is the missing SU(7) allowed-sector object.  Unlike
`RawCodePairEnergyUnitSuccessorLaw`, this law is not over every Boolean-atomic
endpoint pair in the bound; it is over the physical branch sector selected by
confinement/representation dynamics. -/
def GaugeFilteredRawCodePairEnergyUnitSuccessorLaw
    (n bound : ℕ) (allowed : ℕ -> ℕ -> Prop) : Prop :=
  ∀ left right : ℕ,
    allowed left right ->
      left ∈ rawCodeBoundedList bound ->
        right ∈ rawCodeBoundedList bound ->
          natMultiplicativelyAtomicCheck left = true ->
            natMultiplicativelyAtomicCheck right = true ->
              rawCodePairResidualEnergy n left right ≠ 0 ->
                ∃ left' right' : ℕ,
                  allowed left' right' ∧
                    left' ∈ rawCodeBoundedList bound ∧
                      right' ∈ rawCodeBoundedList bound ∧
                        natMultiplicativelyAtomicCheck left' = true ∧
                          natMultiplicativelyAtomicCheck right' = true ∧
                            rawCodePairResidualEnergy n left' right' + 1 =
                              rawCodePairResidualEnergy n left right

/-- If the gauge filter is the full raw pair space, the filtered law collapses
back to P947's over-strong raw all-pair law. -/
theorem rawCodePairUnitSuccessorLaw_of_gaugeFiltered_true
    {n bound : ℕ}
    (H : GaugeFilteredRawCodePairEnergyUnitSuccessorLaw
      n bound (fun _ _ => True)) :
    RawCodePairEnergyUnitSuccessorLaw n bound := by
  intro left right hleft_mem hright_mem hleft_check hright_check hnonzero
  rcases
      H left right True.intro hleft_mem hright_mem hleft_check hright_check
        hnonzero with
    ⟨left', right', _hallowed, hleft'_mem, hright'_mem,
      hleft'_check, hright'_check, hsucc⟩
  exact
    ⟨left', right', hleft'_mem, hright'_mem,
      hleft'_check, hright'_check, hsucc⟩

/-- Therefore the full-space gauge filter cannot be the missing SU(7)
producer in the concrete obstructed fiber. -/
theorem not_GaugeFilteredRawCodePairEnergyUnitSuccessorLaw_true_six_three :
    ¬ GaugeFilteredRawCodePairEnergyUnitSuccessorLaw
      6 3 (fun _ _ => True) := by
  intro H
  exact not_RawCodePairEnergyUnitSuccessorLaw_six_three
    (rawCodePairUnitSuccessorLaw_of_gaugeFiltered_true H)

/-! ## Certificate -/

/-- P948 certificate: the raw all-pair unit descent throat is too strong, and
the next real producer must be a gauge-filtered SU(7) allowed-sector descent
law. -/
structure SU7RawAllPairUnitDescentBoundaryCertificate where
  three_atomic_check :
    natMultiplicativelyAtomicCheck 3 = true
  three_three_energy :
    rawCodePairResidualEnergy 6 3 3 = 6
  no_energy_five_bound_three :
    ¬ ∃ left right : ℕ,
      left ∈ rawCodeBoundedList 3 ∧
        right ∈ rawCodeBoundedList 3 ∧
          natMultiplicativelyAtomicCheck left = true ∧
            natMultiplicativelyAtomicCheck right = true ∧
              rawCodePairResidualEnergy 6 left right = 5
  raw_all_pair_law_false :
    ¬ RawCodePairEnergyUnitSuccessorLaw 6 3
  full_filter_law_false :
    ¬ GaugeFilteredRawCodePairEnergyUnitSuccessorLaw
      6 3 (fun _ _ => True)

/-- Canonical P948 boundary certificate. -/
def su7RawAllPairUnitDescentBoundaryCertificate :
    SU7RawAllPairUnitDescentBoundaryCertificate where
  three_atomic_check :=
    natMultiplicativelyAtomicCheck_three
  three_three_energy :=
    rawCodePairResidualEnergy_six_three_three
  no_energy_five_bound_three :=
    no_rawCodePairResidualEnergy_five_six_bound_three
  raw_all_pair_law_false :=
    not_RawCodePairEnergyUnitSuccessorLaw_six_three
  full_filter_law_false :=
    not_GaugeFilteredRawCodePairEnergyUnitSuccessorLaw_true_six_three


end
end StandardModelConstraint
end SaturationMonoid
