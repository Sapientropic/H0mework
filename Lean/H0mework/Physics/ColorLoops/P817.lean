import H0mework.Physics.JointSources.P710
import H0mework.Physics.JointSources.P816

/-!
# Proposition 817: P710 three-nail lock and color-loop confinement

P710 locks the finite physical-output package to one canonical three-nail
surface: the trace-weighted QCD/Poincare axis, the `alpha_s` inverse residual,
the nine Yukawa depths, and the CKM/Jarlskog depth sum.

P348 says a prime-edge color loop escapes confinement exactly when its
gauge-invariant trace is nonzero.

P816 lowers the remaining producer debt to a discrete unit-bracket trace
producer.  This file welds those three surfaces together:

* in a P710-compatible selected color-loop sector, trace-exact loops and
  nonzero-trace escapes are disjoint;
* a P816 unit-bracket producer selects, for every even fiber, a prime-edge
  representative that is trace-exact on every P710 three-nail package;
* the selected representative carries the three nail values and the
  trace-zero confinement equation in one theorem.

Boundary: this is the machine-checked bridge from P710 + the P816 discrete
trace producer to confinement.  The next producer debt is still to derive the
unit-bracket producer from the internal SU(7)/sigma-carrier gauge dynamics.
-/

noncomputable section

namespace SaturationMonoid
namespace GrandUnification

open StandardModelConstraint
open AffineRelaxation

set_option linter.checkUnivs false
set_option linter.defProp false

universe u v w z

/-! ## P710-compatible confined and escaping prime-edge loops -/

/-- A P710-selected prime-edge color loop is confined when it sits in the
zero fiber of the gauge-invariant color-loop trace. -/
def ThreeNailConfinedPrimeEdgeLoop
    {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [CompleteSpace E]
    {Clause : Type v} {Var : Type w} [Fintype Clause]
    (R : HamiltonianSATEnergySameCarrierUnifiedRootCertificate.{w, z, u, v}
      E)
    (X : HamiltonianSATPhysicalProducerPair Clause Var)
    (n : ℕ) (p q : AffineRelaxation.PrimeExponent) : Prop :=
  HamiltonianSATCoordinateSpineProducerNailSurface R X ∧
    ColorLoopTraceExact (primeEdgeColorLoopMatrix n p q)

/-- A P710-selected prime-edge color loop escapes when the same
gauge-invariant trace is nonzero. -/
def ThreeNailEscapingPrimeEdgeLoop
    {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [CompleteSpace E]
    {Clause : Type v} {Var : Type w} [Fintype Clause]
    (R : HamiltonianSATEnergySameCarrierUnifiedRootCertificate.{w, z, u, v}
      E)
    (X : HamiltonianSATPhysicalProducerPair Clause Var)
    (n : ℕ) (p q : AffineRelaxation.PrimeExponent) : Prop :=
  HamiltonianSATCoordinateSpineProducerNailSurface R X ∧
    PrimeEdgeColorLoopObstructed n p q

/-- THEOREM 1: the confined and escaping selected sectors are disjoint. -/
theorem threeNailConfinedPrimeEdgeLoop_not_escaping
    {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [CompleteSpace E]
    {Clause : Type v} {Var : Type w} [Fintype Clause]
    {R : HamiltonianSATEnergySameCarrierUnifiedRootCertificate.{w, z, u, v}
      E}
    {X : HamiltonianSATPhysicalProducerPair Clause Var}
    {n : ℕ} {p q : AffineRelaxation.PrimeExponent}
    (hconf : ThreeNailConfinedPrimeEdgeLoop R X n p q) :
    ¬ ThreeNailEscapingPrimeEdgeLoop R X n p q := by
  intro hesc
  exact hesc.2 hconf.2

/-- THEOREM 2: escaping excludes confinement for the same selected loop. -/
theorem threeNailEscapingPrimeEdgeLoop_not_confined
    {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [CompleteSpace E]
    {Clause : Type v} {Var : Type w} [Fintype Clause]
    {R : HamiltonianSATEnergySameCarrierUnifiedRootCertificate.{w, z, u, v}
      E}
    {X : HamiltonianSATPhysicalProducerPair Clause Var}
    {n : ℕ} {p q : AffineRelaxation.PrimeExponent}
    (hesc : ThreeNailEscapingPrimeEdgeLoop R X n p q) :
    ¬ ThreeNailConfinedPrimeEdgeLoop R X n p q := by
  intro hconf
  exact hesc.2 hconf.2

/-- THEOREM 3: on a P710 package, confinement is exactly non-escape. -/
theorem threeNailConfinedPrimeEdgeLoop_iff_nonescaping
    {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [CompleteSpace E]
    {Clause : Type v} {Var : Type w} [Fintype Clause]
    (R : HamiltonianSATEnergySameCarrierUnifiedRootCertificate.{w, z, u, v}
      E)
    (X : HamiltonianSATPhysicalProducerPair Clause Var)
    (n : ℕ) (p q : AffineRelaxation.PrimeExponent) :
    ThreeNailConfinedPrimeEdgeLoop R X n p q ↔
      HamiltonianSATCoordinateSpineProducerNailSurface R X ∧
        ¬ PrimeEdgeColorLoopObstructed n p q := by
  constructor
  · intro hconf
    exact ⟨hconf.1, fun hobs => hobs hconf.2⟩
  · intro h
    refine ⟨h.1, ?_⟩
    have hno :
        ¬ colorLoopTrace (primeEdgeColorLoopMatrix n p q) ≠ 0 := by
      exact h.2
    show colorLoopTrace (primeEdgeColorLoopMatrix n p q) = 0
    exact not_not.mp hno

/-! ## Unit brackets select confined representatives on the P710 surface -/

/-- THEOREM 4: a P816 unit-bracket producer gives a trace-zero prime-edge
representative for every even fiber, uniformly over every P710 three-nail
package. -/
theorem threeNailUnitBracket_forces_confinedRepresentative
    {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [CompleteSpace E]
    {Clause : Type v} {Var : Type w} [Fintype Clause]
    (R : HamiltonianSATEnergySameCarrierUnifiedRootCertificate.{w, z, u, v}
      E)
    (producer : ColorLoopTraceUnitBracketProducer) :
    ∀ n : ℕ, 2 <= n ->
      ∃ p q : AffineRelaxation.PrimeExponent,
        ∀ X : HamiltonianSATPhysicalProducerPair Clause Var,
          HamiltonianSATCoordinateSpineProducerNailSurface R X ->
            ThreeNailConfinedPrimeEdgeLoop R X n p q ∧
              ¬ ThreeNailEscapingPrimeEdgeLoop R X n p q := by
  intro n hn
  have goldbach : EvenGoldbachStatement :=
    evenGoldbach_of_colorLoopTraceUnitBracketProducer producer
  rcases goldbach n hn with ⟨p, q, hpair⟩
  have hexact :
      ColorLoopTraceExact (primeEdgeColorLoopMatrix n p q) := by
    exact (primeEdgeColorLoop_trace_zero_iff n p q).mpr hpair
  refine ⟨p, q, ?_⟩
  intro X hX
  have hconf : ThreeNailConfinedPrimeEdgeLoop R X n p q :=
    ⟨hX, hexact⟩
  exact ⟨hconf, threeNailConfinedPrimeEdgeLoop_not_escaping hconf⟩

/-- THEOREM 5: the same representative carries the three locked P710 nail
values and the trace-zero confinement equation in one readout. -/
theorem threeNailUnitBracket_forces_lockedNailsAndConfinement
    {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [CompleteSpace E]
    {Clause : Type v} {Var : Type w} [Fintype Clause]
    (R : HamiltonianSATEnergySameCarrierUnifiedRootCertificate.{w, z, u, v}
      E)
    (producer : ColorLoopTraceUnitBracketProducer) :
    ∀ n : ℕ, 2 <= n ->
      ∃ p q : AffineRelaxation.PrimeExponent,
        ∀ X : HamiltonianSATPhysicalProducerPair Clause Var,
          HamiltonianSATCoordinateSpineProducerNailSurface R X ->
            X.2.2.alphaInverseResidual = -((89000 : ℚ) / 128511) ∧
              X.2.2.yukawaMassOrder =
                [50, 346, 372, 489, 583, 682, 880, 908, 982] ∧
              X.2.2.ckmDepthSum = (386 : ℚ) ∧
              ColorLoopTraceExact (primeEdgeColorLoopMatrix n p q) ∧
              ¬ PrimeEdgeColorLoopObstructed n p q := by
  intro n hn
  have hconf :=
    threeNailUnitBracket_forces_confinedRepresentative
      (Clause := Clause) (Var := Var) (R := R) producer n hn
  rcases hconf with ⟨p, q, hloop⟩
  refine ⟨p, q, ?_⟩
  intro X hX
  have hselected := hloop X hX
  exact
    ⟨hX.2.2.1, hX.2.2.2.1, hX.2.2.2.2,
      hselected.1.2, fun hobs => hobs hselected.1.2⟩

/-! ## Packaged certificate -/

/-- P817 certificate: the P710 three-nail lock and the P816 discrete
unit-bracket producer force selected prime-edge color loops into the
trace-zero confined sector. -/
structure P710ThreeNailGaugeConfinementCertificate
    {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [CompleteSpace E]
    {Clause : Type v} {Var : Type w} [Fintype Clause]
    (R : HamiltonianSATEnergySameCarrierUnifiedRootCertificate.{w, z, u, v}
      E) : Prop where
  three_nail_surface_iff_canonical :
    ∀ X : HamiltonianSATPhysicalProducerPair Clause Var,
      HamiltonianSATCoordinateSpineProducerNailSurface R X ↔
        X = canonicalHamiltonianSATPhysicalProducerPair Clause Var
  confined_iff_nonescaping :
    ∀ (X : HamiltonianSATPhysicalProducerPair Clause Var)
      (n : ℕ) (p q : AffineRelaxation.PrimeExponent),
      ThreeNailConfinedPrimeEdgeLoop R X n p q ↔
        HamiltonianSATCoordinateSpineProducerNailSurface R X ∧
          ¬ PrimeEdgeColorLoopObstructed n p q
  confined_not_escaping :
    ∀ (X : HamiltonianSATPhysicalProducerPair Clause Var)
      (n : ℕ) (p q : AffineRelaxation.PrimeExponent),
      ThreeNailConfinedPrimeEdgeLoop R X n p q ->
        ¬ ThreeNailEscapingPrimeEdgeLoop R X n p q
  unit_bracket_forces_confined_representative :
    ColorLoopTraceUnitBracketProducer ->
      ∀ n : ℕ, 2 <= n ->
        ∃ p q : AffineRelaxation.PrimeExponent,
          ∀ X : HamiltonianSATPhysicalProducerPair Clause Var,
            HamiltonianSATCoordinateSpineProducerNailSurface R X ->
              ThreeNailConfinedPrimeEdgeLoop R X n p q ∧
                ¬ ThreeNailEscapingPrimeEdgeLoop R X n p q
  unit_bracket_forces_locked_nails_and_confinement :
    ColorLoopTraceUnitBracketProducer ->
      ∀ n : ℕ, 2 <= n ->
        ∃ p q : AffineRelaxation.PrimeExponent,
          ∀ X : HamiltonianSATPhysicalProducerPair Clause Var,
            HamiltonianSATCoordinateSpineProducerNailSurface R X ->
              X.2.2.alphaInverseResidual = -((89000 : ℚ) / 128511) ∧
                X.2.2.yukawaMassOrder =
                  [50, 346, 372, 489, 583, 682, 880, 908, 982] ∧
                X.2.2.ckmDepthSum = (386 : ℚ) ∧
                ColorLoopTraceExact (primeEdgeColorLoopMatrix n p q) ∧
                ¬ PrimeEdgeColorLoopObstructed n p q
  unit_bracket_iff_even_crossing_half :
    ColorLoopTraceUnitBracketProducer ↔
      ColorLoopTraceLyapunovEvenCrossingProducer (1 / 2 : ℝ)

/-- THEOREM 6: canonical P710 three-nail gauge-confinement bridge. -/
theorem p710ThreeNailGaugeConfinementCertificate
    {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [CompleteSpace E]
    {Clause : Type v} {Var : Type w} [Fintype Clause]
    (R : HamiltonianSATEnergySameCarrierUnifiedRootCertificate.{w, z, u, v}
      E) :
    P710ThreeNailGaugeConfinementCertificate
      (Clause := Clause) (Var := Var) R where
  three_nail_surface_iff_canonical := by
    intro X
    exact hamiltonianSATCoordinateSpineProducerNailSurface_iff_canonical R X
  confined_iff_nonescaping := by
    intro X n p q
    exact threeNailConfinedPrimeEdgeLoop_iff_nonescaping R X n p q
  confined_not_escaping := by
    intro X n p q hconf
    exact threeNailConfinedPrimeEdgeLoop_not_escaping hconf
  unit_bracket_forces_confined_representative := by
    intro producer n hn
    exact
      threeNailUnitBracket_forces_confinedRepresentative
        (Clause := Clause) (Var := Var) (R := R) producer n hn
  unit_bracket_forces_locked_nails_and_confinement := by
    intro producer n hn
    exact
      threeNailUnitBracket_forces_lockedNailsAndConfinement
        (Clause := Clause) (Var := Var) (R := R) producer n hn
  unit_bracket_iff_even_crossing_half :=
    colorLoopTraceUnitBracketProducer_iff_evenCrossing
      (by norm_num) (by norm_num)

end GrandUnification
end SaturationMonoid
