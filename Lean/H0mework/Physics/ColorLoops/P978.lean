import H0mework.Physics.ColorLoops.P824
import H0mework.Arithmetic.ShellSources.P976

/-!
# Proposition 978: generated flow/quantization gives the global color loop

P976 extracts a bounded prime pair from each generated no-prime
flow/quantization certificate.  This file pushes that result back to the
global arithmetic/color-loop statements:

```text
fiberwise generated flow + unit bridge + bound >= 3
-> EvenGoldbachStatement
-> SU7FilteredPrimeEdgeLoopProducer
```

No new search object is introduced here; it is the global projection of the
P976 zero-shell extraction.
-/

namespace SaturationMonoid
namespace StandardModelConstraint

noncomputable section

open SaturationMonoid.AffineRelaxation

set_option linter.defProp false

/-! ## Bounded pairs project to ordinary additive decompositions -/

/-- A bounded Goldbach pair for the fiber `2n` projects to an ordinary
prime-exponent additive decomposition of `2n`. -/
theorem hasPrimeAdditiveDecomposition_of_boundedGoldbachPair
    {n bound : ℕ}
    (h : BoundedGoldbachPair n bound) :
    HasPrimeAdditiveDecomposition (2 * n) := by
  rcases h with ⟨p, q, _hp_mem, _hq_mem, hp, hq, hsum⟩
  exact ⟨⟨p, hp⟩, ⟨q, hq⟩, hsum.symm⟩

/-- Fiberwise generated no-prime flow/quantization, with endpoint bounds
covering `2` and `3`, gives the ordinary even Goldbach statement. -/
theorem evenGoldbach_of_generatedFlowQuantizationEveryEven
    (H : SU7GeneratedNoPrimeFlowQuantizationEveryEvenFiber)
    (Hbound :
      ∀ n : ℕ, ∀ hn : 2 ≤ n,
        3 ≤ (Classical.choice (H n hn)).codeBound) :
    EvenGoldbachStatement := by
  intro n hn
  rcases generatedFlowQuantizationEveryEven_to_boundedPairs
      H Hbound n hn with
    ⟨bound, hpair⟩
  exact hasPrimeAdditiveDecomposition_of_boundedGoldbachPair hpair

/-- The same generated flow/quantization data produces the SU(7)-filtered
prime-edge loop producer. -/
theorem su7FilteredPrimeEdgeLoopProducer_of_generatedFlowQuantizationEveryEven
    (H : SU7GeneratedNoPrimeFlowQuantizationEveryEvenFiber)
    (Hbound :
      ∀ n : ℕ, ∀ hn : 2 ≤ n,
        3 ≤ (Classical.choice (H n hn)).codeBound) :
    SU7FilteredPrimeEdgeLoopProducer := by
  exact
    (su7FilteredPrimeEdgeLoopProducer_iff_evenGoldbach).mpr
      (evenGoldbach_of_generatedFlowQuantizationEveryEven H Hbound)

/-! ## Certificate -/

/-- P978 certificate: the generated flow/quantization zero-shell producer
projects to global Goldbach and the SU(7)-filtered color-loop producer. -/
structure SU7GeneratedFlowQuantizationGlobalColorLoopCertificate where
  bounded_pair_to_additive :
    ∀ {n bound : ℕ},
      BoundedGoldbachPair n bound ->
        HasPrimeAdditiveDecomposition (2 * n)
  flow_quantization_to_even_goldbach :
    ∀ (H : SU7GeneratedNoPrimeFlowQuantizationEveryEvenFiber),
      (∀ n : ℕ, ∀ hn : 2 ≤ n,
        3 ≤ (Classical.choice (H n hn)).codeBound) ->
        EvenGoldbachStatement
  flow_quantization_to_su7_filtered_loop :
    ∀ (H : SU7GeneratedNoPrimeFlowQuantizationEveryEvenFiber),
      (∀ n : ℕ, ∀ hn : 2 ≤ n,
        3 ≤ (Classical.choice (H n hn)).codeBound) ->
        SU7FilteredPrimeEdgeLoopProducer

/-- Canonical P978 global color-loop certificate. -/
def su7GeneratedFlowQuantizationGlobalColorLoopCertificate :
    SU7GeneratedFlowQuantizationGlobalColorLoopCertificate where
  bounded_pair_to_additive :=
    hasPrimeAdditiveDecomposition_of_boundedGoldbachPair
  flow_quantization_to_even_goldbach :=
    evenGoldbach_of_generatedFlowQuantizationEveryEven
  flow_quantization_to_su7_filtered_loop :=
    su7FilteredPrimeEdgeLoopProducer_of_generatedFlowQuantizationEveryEven


end
end StandardModelConstraint
end SaturationMonoid
