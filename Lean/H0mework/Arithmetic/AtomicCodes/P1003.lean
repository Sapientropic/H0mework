import H0mework.Arithmetic.AtomicCodes.P1002

/-!
# Proposition 1003: real endpoint atomicity blocks the naive full-zero closure

P1002 put the atom-irreducibility residual on the same carrier, but left it as
a readout parameter.  This file installs a concrete endpoint atomicity readout
that does not mention any downstream arithmetic theorem.  It then proves the
important no-go fact: the P1001 endpoint candidate `(n,n)` cannot close the
atom component under this real readout.

The result is not a replacement producer.  It is the guardrail that prevents
the same-carrier full-zero theorem from being closed by an arbitrary zero
readout.
-/

noncomputable section

namespace SaturationMonoid
namespace StandardModelConstraint

set_option linter.defProp false

/-! ## Endpoint atomicity without downstream projection -/

/-- Multiplicative endpoint atomicity, stated without using any downstream
projection predicate. -/
def SameCarrierEndpointAtomic (n : ℕ) : Prop :=
  2 ≤ n ∧ ∀ a b : ℕ, n = a * b -> a = 1 ∨ b = 1

/-- Atomicity of a same-carrier atom's endpoint code. -/
def SameCarrierAtomAtomic (a : SameCarrierSU7Atom) : Prop :=
  SameCarrierEndpointAtomic (sameCarrierAtomCode a)

/-- Concrete atom-irreducibility residual: zero for atomic endpoint codes and
one otherwise. -/
noncomputable def sameCarrierEndpointAtomicReadout
    (a : SameCarrierSU7Atom) : ℤ :=
  by
    classical
    exact if SameCarrierAtomAtomic a then 0 else 1

/-- Same-carrier object with the concrete endpoint-atomicity readout. -/
def sameCarrierObjectWithEndpointAtomicReadout
    (n : ℕ) : SameCarrierObject n :=
  sameCarrierObjectOfIrreducibilityReadout n
    sameCarrierEndpointAtomicReadout

/-! ## The naive `(n,n)` endpoint candidate fails at composite fibers -/

theorem not_sameCarrierEndpointAtomic_four :
    ¬ SameCarrierEndpointAtomic 4 := by
  intro h
  rcases h with ⟨_h2, hfac⟩
  rcases hfac 2 2 (by norm_num) with hleft | hright <;> norm_num at *

@[simp] theorem sameCarrierAtomicZeroCandidate_left_code
    (n : ℕ) :
    sameCarrierAtomCode (sameCarrierAtomicZeroCandidate n).leftAtom = n := by
  simp [sameCarrierAtomicZeroCandidate, sameCarrierAtomCode,
    sameCarrierAtomOfWeightAndCode]

@[simp] theorem sameCarrierAtomicZeroCandidate_right_code
    (n : ℕ) :
    sameCarrierAtomCode (sameCarrierAtomicZeroCandidate n).rightAtom = n := by
  simp [sameCarrierAtomicZeroCandidate, sameCarrierAtomCode,
    sameCarrierAtomOfWeightAndCode]

theorem not_sameCarrierAtomAtomic_candidate_left_four :
    ¬ SameCarrierAtomAtomic
        (sameCarrierAtomicZeroCandidate 4).leftAtom := by
  simpa [SameCarrierAtomAtomic] using not_sameCarrierEndpointAtomic_four

theorem not_sameCarrierAtomAtomic_candidate_right_four :
    ¬ SameCarrierAtomAtomic
        (sameCarrierAtomicZeroCandidate 4).rightAtom := by
  simpa [SameCarrierAtomAtomic] using not_sameCarrierEndpointAtomic_four

theorem sameCarrierEndpointAtomicReadout_candidate_left_four_eq_one :
    sameCarrierEndpointAtomicReadout
        (sameCarrierAtomicZeroCandidate 4).leftAtom = 1 := by
  unfold sameCarrierEndpointAtomicReadout
  simp [not_sameCarrierAtomAtomic_candidate_left_four]

theorem sameCarrierEndpointAtomicReadout_candidate_right_four_eq_one :
    sameCarrierEndpointAtomicReadout
        (sameCarrierAtomicZeroCandidate 4).rightAtom = 1 := by
  unfold sameCarrierEndpointAtomicReadout
  simp [not_sameCarrierAtomAtomic_candidate_right_four]

/-- At fiber `4`, the concrete atom-irreducibility residual of the P1001
candidate is nonzero. -/
theorem sameCarrierEndpointAtomicResidual_candidate_four_ne_zero :
    sameCarrierAtomIrreducibilityResidual
        (sameCarrierObjectWithEndpointAtomicReadout 4) ≠ 0 := by
  unfold sameCarrierAtomIrreducibilityResidual
    sameCarrierObjectWithEndpointAtomicReadout
    sameCarrierObjectOfIrreducibilityReadout
  change
    sameCarrierEndpointAtomicReadout
          (sameCarrierAtomicZeroCandidate 4).leftAtom +
        sameCarrierEndpointAtomicReadout
          (sameCarrierAtomicZeroCandidate 4).rightAtom ≠ 0
  rw [sameCarrierEndpointAtomicReadout_candidate_left_four_eq_one,
    sameCarrierEndpointAtomicReadout_candidate_right_four_eq_one]
  norm_num

/-- Therefore the concrete endpoint-atomicity readout blocks the full-zero
claim for the naive P1001 `(n,n)` endpoint candidate at `n = 4`. -/
theorem not_sameCarrierFullZero_endpointAtomicReadout_candidate_four :
    ¬ SameCarrierFullZero
        (sameCarrierObjectWithEndpointAtomicReadout 4) := by
  intro hzero
  have hatom :
      sameCarrierAtomIrreducibilityResidual
          (sameCarrierObjectWithEndpointAtomicReadout 4) = 0 := by
    unfold SameCarrierFullZero sameCarrierResidualVector at hzero
    exact congrArg Prod.fst (congrArg Prod.snd hzero)
  exact sameCarrierEndpointAtomicResidual_candidate_four_ne_zero hatom


end StandardModelConstraint
end SaturationMonoid
