import H0mework.Arithmetic.CodePairs.P974

/-!
# Proposition 976: flow/quantization directly enters the zero-shell throat

P962 defines the real generated no-prime producer object:

```text
confining residual flow + quantized unit bridge
```

P974 shows that once generated no-prime endpoint coverage reaches shell `0`,
the result is exactly a bounded Goldbach pair.  This file removes one remaining
numerical side condition from that handoff.  The explicit Boolean raw generator
has positive computed max-energy as soon as the endpoint-code bound includes
`2` and `3`; the witness is the generated Boolean-atomic cell `(2,3)`, whose
residual against `2n` is never zero.

So a generated flow/quantization certificate with `codeBound >= 3` feeds the
zero-shell throat directly.
-/

namespace SaturationMonoid
namespace StandardModelConstraint

noncomputable section

open SaturationMonoid.AffineRelaxation
open RunningSigmaBeta

set_option linter.defProp false

/-! ## The explicit generated raw max is positive once 2 and 3 are present -/

/-- The Boolean multiplicative-atomic checker accepts endpoint code `2`. -/
theorem natMultiplicativelyAtomicCheck_two_eq_true :
    natMultiplicativelyAtomicCheck 2 = true := by
  exact
    (natMultiplicativelyAtomicCheck_eq_true_iff_prime).mpr
      (by norm_num)

/-- The Boolean multiplicative-atomic checker accepts endpoint code `3`. -/
theorem natMultiplicativelyAtomicCheck_three_eq_true :
    natMultiplicativelyAtomicCheck 3 = true := by
  exact
    (natMultiplicativelyAtomicCheck_eq_true_iff_prime).mpr
      (by norm_num)

/-- For every fiber `n`, the raw code-pair residual of `(2,3)` against `2n`
has positive energy, because an odd number cannot equal `2n`. -/
theorem rawCodePairResidualEnergy_two_three_pos (n : ℕ) :
    0 < rawCodePairResidualEnergy n 2 3 := by
  unfold rawCodePairResidualEnergy
  apply Int.natAbs_pos.mpr
  unfold rawCodePairResidual
  omega

/-- The generated Boolean raw branch spectrum has positive computed max-energy
whenever the endpoint bound contains `2` and `3`.  The proof uses the generated
cell `(2,3)` and does not store any prime proof in the generator. -/
theorem generatedRawBranchingMaxEnergy_pos_of_bound_ge_three
    (n bound : ℕ) (hbound : 3 ≤ bound) :
    0 < generatedRawBranchingMaxEnergy n bound := by
  let x :=
    booleanAtomicCellOfRawCodePair n 2 3
      natMultiplicativelyAtomicCheck_two_eq_true
      natMultiplicativelyAtomicCheck_three_eq_true
  have h2mem : 2 ∈ rawCodeBoundedList bound := by
    simp [rawCodeBoundedList]
    omega
  have h3mem : 3 ∈ rawCodeBoundedList bound := by
    simp [rawCodeBoundedList]
    omega
  have hxmem :
      x ∈ booleanAtomicRawBranchingCandidateList n bound := by
    exact
      booleanAtomicCellOfRawCodePair_mem_generated
        h2mem h3mem
        natMultiplicativelyAtomicCheck_two_eq_true
        natMultiplicativelyAtomicCheck_three_eq_true
  have hxspec :
      x.cell ∈ (booleanGeneratedRawBranchingSpectrum n bound).cells :=
    booleanAtomicCell_mem_booleanGeneratedSpectrum hxmem
  have hle :
      rawAtomCodeBranchingDecompositionResidualEnergy x.cell ≤
        generatedRawBranchingMaxEnergy n bound :=
    generatedRawBranching_energy_bound x.cell hxspec
  have henergy :
      rawAtomCodeBranchingDecompositionResidualEnergy x.cell =
        rawCodePairResidualEnergy n 2 3 := by
    simpa [x] using
      booleanAtomicCellOfRawCodePair_energy_eq
        n 2 3
        natMultiplicativelyAtomicCheck_two_eq_true
        natMultiplicativelyAtomicCheck_three_eq_true
  exact
    Nat.lt_of_lt_of_le
      (by simpa [henergy] using rawCodePairResidualEnergy_two_three_pos n)
      hle

/-! ## Flow/quantization directly produces the bounded zero-shell pair -/

/-- A generated no-prime flow/quantization certificate with a bound containing
`2` and `3` directly produces the bounded Goldbach pair for its fiber. -/
theorem boundedGoldbachPair_of_generatedNoPrimeFlowQuantizationCertificate
    {n : ℕ}
    (G : SU7GeneratedNoPrimeFlowQuantizationCertificate n)
    (hbound : 3 ≤ G.codeBound) :
    BoundedGoldbachPair n G.codeBound := by
  exact
    boundedGoldbachPair_of_generatedNoPrimeLyapunovCertificate
      (generatedNoPrimeLyapunovCertificate_of_flowQuantization G)
      (generatedRawBranchingMaxEnergy_pos_of_bound_ge_three
        n G.codeBound hbound)

/-- Every-fiber generated flow/quantization plus the concrete `codeBound >= 3`
condition gives a bounded Goldbach pair on every even fiber. -/
theorem boundedGoldbachPairEveryEven_of_generatedFlowQuantization
    (H : SU7GeneratedNoPrimeFlowQuantizationEveryEvenFiber)
    (Hbound :
      ∀ n : ℕ, ∀ hn : 2 ≤ n,
        3 ≤ (Classical.choice (H n hn)).codeBound) :
    ∀ n : ℕ, 2 ≤ n ->
      ∃ bound : ℕ, BoundedGoldbachPair n bound := by
  intro n hn
  let G := Classical.choice (H n hn)
  exact
    ⟨G.codeBound,
      boundedGoldbachPair_of_generatedNoPrimeFlowQuantizationCertificate
        G (Hbound n hn)⟩

/-! ## Certificate -/

/-- P976 certificate: explicit max positivity and direct flow-to-zero-shell
extraction. -/
structure SU7GeneratedFlowQuantizationZeroShellProducerCertificate where
  check_two :
    natMultiplicativelyAtomicCheck 2 = true
  check_three :
    natMultiplicativelyAtomicCheck 3 = true
  two_three_positive :
    ∀ n : ℕ, 0 < rawCodePairResidualEnergy n 2 3
  generated_max_positive :
    ∀ n bound : ℕ, 3 ≤ bound ->
      0 < generatedRawBranchingMaxEnergy n bound
  flow_quantization_to_bounded_pair :
    ∀ {n : ℕ}
      (G : SU7GeneratedNoPrimeFlowQuantizationCertificate n),
      3 ≤ G.codeBound -> BoundedGoldbachPair n G.codeBound
  every_even_flow_to_bounded_pair :
    ∀ (H : SU7GeneratedNoPrimeFlowQuantizationEveryEvenFiber),
      (∀ n : ℕ, ∀ hn : 2 ≤ n,
        3 ≤ (Classical.choice (H n hn)).codeBound) ->
        ∀ n : ℕ, 2 ≤ n ->
          ∃ bound : ℕ, BoundedGoldbachPair n bound

/-- A usable every-fiber field kept outside the certificate above, because its
dependent `Classical.choice` binder is the stable API. -/
theorem generatedFlowQuantizationEveryEven_to_boundedPairs
    (H : SU7GeneratedNoPrimeFlowQuantizationEveryEvenFiber)
    (Hbound :
      ∀ n : ℕ, ∀ hn : 2 ≤ n,
        3 ≤ (Classical.choice (H n hn)).codeBound) :
    ∀ n : ℕ, 2 ≤ n ->
      ∃ bound : ℕ, BoundedGoldbachPair n bound :=
  boundedGoldbachPairEveryEven_of_generatedFlowQuantization H Hbound

/-- Canonical P976 zero-shell producer certificate. -/
def su7GeneratedFlowQuantizationZeroShellProducerCertificate :
    SU7GeneratedFlowQuantizationZeroShellProducerCertificate where
  check_two := natMultiplicativelyAtomicCheck_two_eq_true
  check_three := natMultiplicativelyAtomicCheck_three_eq_true
  two_three_positive := rawCodePairResidualEnergy_two_three_pos
  generated_max_positive :=
    generatedRawBranchingMaxEnergy_pos_of_bound_ge_three
  flow_quantization_to_bounded_pair := by
    intro n G hbound
    exact
      boundedGoldbachPair_of_generatedNoPrimeFlowQuantizationCertificate
        G hbound
  every_even_flow_to_bounded_pair := by
    intro H Hbound
    exact generatedFlowQuantizationEveryEven_to_boundedPairs H Hbound


end
end StandardModelConstraint
end SaturationMonoid
