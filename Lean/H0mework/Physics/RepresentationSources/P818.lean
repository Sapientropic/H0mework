import H0mework.Physics.RepresentationSources.P778
import H0mework.Physics.ColorLoops.P817

/-!
# Proposition 818: P710 nails force the SU(7) color-representation filter

P817 proved that P710 plus the P816 unit-bracket producer selects trace-zero
prime-edge representatives.  This file names the representation-theoretic
filter behind that statement.

Inside the `3+2+1+1` SU(7) block picture, the color sector visible to the
`SU(3)` adjoint is the traceless color block.  For a closed color loop this is
exactly the zero fiber of the gauge-invariant trace observable from P348.
Thus a nonzero-trace prime-edge loop is not a color-adjoint representative; it
is a trace/singlet leakage and is filtered out.

The theorem below welds that filter to the P710 three nails and the P778
SU(7) representation/matter/Higgs normal form.  A selected loop that passes the
P710-forced SU(7) representation filter cannot be a nonzero-trace color-loop
escape.

Boundary: this proves exclusion by the SU(7) color-adjoint trace filter and
connects the filter to the P710/P778/P816 producer spine.  The remaining
producer debt is still to derive the P816 unit-bracket producer from the
internal sigma/gauge-rate dynamics.
-/

noncomputable section

namespace SaturationMonoid
namespace GrandUnification

open StandardModelConstraint
open AffineRelaxation
open RunningSigmaBeta

set_option linter.checkUnivs false
set_option linter.defProp false

universe u v w z

/-! ## The SU(7) color-adjoint representation filter -/

/-- The SU(7) color-adjoint filter on closed color loops.

In the `3+2+1+1` block representation, the color-adjoint block is traceless.
For the P348 closed-loop observable this is exactly `colorLoopTrace M = 0`. -/
def SU7ColorAdjointRepresentationFilter
    (M : ColorLoopField) : Prop :=
  ColorLoopTraceExact M

/-- THEOREM 1: the SU(7) color-adjoint filter is literally the trace-zero
fiber of the P348 color-loop observable. -/
theorem su7ColorAdjointRepresentationFilter_iff_traceExact
    (M : ColorLoopField) :
    SU7ColorAdjointRepresentationFilter M ↔
      ColorLoopTraceExact M := by
  rfl

/-- THEOREM 2: anything passing the SU(7) color-adjoint filter has no nonzero
trace. -/
theorem su7ColorAdjointRepresentationFilter_excludes_nonzeroTrace
    {M : ColorLoopField}
    (hfilter : SU7ColorAdjointRepresentationFilter M) :
    colorLoopTrace M ≠ 0 -> False := by
  intro hnonzero
  exact hnonzero hfilter

/-- THEOREM 3: for a prime-edge loop, the SU(7) color-adjoint filter excludes
the P348 obstruction predicate. -/
theorem su7ColorAdjointRepresentationFilter_excludes_primeEdgeObstruction
    {n : ℕ} {p q : AffineRelaxation.PrimeExponent}
    (hfilter :
      SU7ColorAdjointRepresentationFilter
        (primeEdgeColorLoopMatrix n p q)) :
    ¬ PrimeEdgeColorLoopObstructed n p q := by
  intro hobs
  exact hobs hfilter

/-! ## P710-forced filtered sector -/

/-- A P710-compatible prime-edge color loop that also passes the SU(7)
representation normal form and the color-adjoint filter. -/
def P710SU7RepresentationFilteredPrimeEdgeLoop
    {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [CompleteSpace E]
    {Clause : Type v} {Var : Type w} [Fintype Clause]
    (R : HamiltonianSATEnergySameCarrierUnifiedRootCertificate.{w, z, u, v}
      E)
    (X : HamiltonianSATPhysicalProducerPair Clause Var)
    (n : ℕ) (p q : AffineRelaxation.PrimeExponent) : Prop :=
  HamiltonianSATCoordinateSpineProducerNailSurface R X ∧
    SU7RepresentationMatterHiggsSourceNormalFormCertificate ∧
      SU7ColorAdjointRepresentationFilter (primeEdgeColorLoopMatrix n p q)

/-- THEOREM 4: the P710 + SU(7) representation-filtered selected sector
excludes nonzero-trace prime-edge color loops. -/
theorem p710SU7RepresentationFilteredPrimeEdgeLoop_excludes_nonzeroTrace
    {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [CompleteSpace E]
    {Clause : Type v} {Var : Type w} [Fintype Clause]
    {R : HamiltonianSATEnergySameCarrierUnifiedRootCertificate.{w, z, u, v}
      E}
    {X : HamiltonianSATPhysicalProducerPair Clause Var}
    {n : ℕ} {p q : AffineRelaxation.PrimeExponent}
    (hloop : P710SU7RepresentationFilteredPrimeEdgeLoop R X n p q) :
    ¬ PrimeEdgeColorLoopObstructed n p q := by
  exact
    su7ColorAdjointRepresentationFilter_excludes_primeEdgeObstruction
      hloop.2.2

/-- THEOREM 5: P710 nails and the P778 representation normal form expose the
same QCD/Yukawa/CKM spine while the selected loop passes the traceless
color-adjoint filter. -/
theorem p710Nails_su7RepresentationFilter_readout
    {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [CompleteSpace E]
    {Clause : Type v} {Var : Type w} [Fintype Clause]
    {R : HamiltonianSATEnergySameCarrierUnifiedRootCertificate.{w, z, u, v}
      E}
    {X : HamiltonianSATPhysicalProducerPair Clause Var}
    {n : ℕ} {p q : AffineRelaxation.PrimeExponent}
    (hloop : P710SU7RepresentationFilteredPrimeEdgeLoop R X n p q) :
    X.2.2.axis = traceWeightedQCDPoincareCoordinateAxis ∧
      X.2.2.alphaInverseResidual = -((89000 : ℚ) / 128511) ∧
      X.2.2.yukawaMassOrder =
        [50, 346, 372, 489, 583, 682, 880, 908, 982] ∧
      X.2.2.ckmDepthSum = (386 : ℚ) ∧
      betaCoeff qcdBlockIncidenceOneLoopInput = 7 ∧
      selectedYukawaDepthTableCandidate.massOrder =
        [50, 346, 372, 489, 583, 682, 880, 908, 982] ∧
      ckmJarlskogDepthFromMatrix = (ckmCPDepthSum : Int) ∧
      SU7ColorAdjointRepresentationFilter (primeEdgeColorLoopMatrix n p q) ∧
      ¬ PrimeEdgeColorLoopObstructed n p q := by
  exact
    ⟨hloop.1.2.1,
      hloop.1.2.2.1,
      hloop.1.2.2.2.1,
      hloop.1.2.2.2.2,
      hloop.2.1.numerical_spine.1,
      hloop.2.1.numerical_spine.2.1,
      hloop.2.1.numerical_spine.2.2,
      hloop.2.2,
      p710SU7RepresentationFilteredPrimeEdgeLoop_excludes_nonzeroTrace hloop⟩

/-! ## Unit brackets select loops that pass the SU(7) filter -/

/-- THEOREM 6: a P816 unit-bracket producer selects, for every even fiber, a
P710/P778-compatible prime-edge loop that passes the SU(7) color-adjoint
representation filter. -/
theorem threeNailUnitBracket_selects_su7RepresentationFilteredLoop
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
            P710SU7RepresentationFilteredPrimeEdgeLoop R X n p q ∧
              ¬ PrimeEdgeColorLoopObstructed n p q := by
  intro n hn
  rcases
    threeNailUnitBracket_forces_confinedRepresentative
      (Clause := Clause) (Var := Var) (R := R) producer n hn with
    ⟨p, q, hselected⟩
  refine ⟨p, q, ?_⟩
  intro X hX
  have hconf := hselected X hX
  have hloop : P710SU7RepresentationFilteredPrimeEdgeLoop R X n p q :=
    ⟨hX, su7RepresentationMatterHiggsSourceNormalFormCertificate, hconf.1.2⟩
  exact
    ⟨hloop,
      p710SU7RepresentationFilteredPrimeEdgeLoop_excludes_nonzeroTrace hloop⟩

/-- THEOREM 7: the selected SU(7)-filtered loop carries the P710 nails and
cannot be a nonzero-trace color-loop escape. -/
theorem threeNailUnitBracket_forces_su7FilteredNailsAndConfinement
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
              betaCoeff qcdBlockIncidenceOneLoopInput = 7 ∧
              SU7ColorAdjointRepresentationFilter
                (primeEdgeColorLoopMatrix n p q) ∧
              ¬ PrimeEdgeColorLoopObstructed n p q := by
  intro n hn
  rcases
    threeNailUnitBracket_selects_su7RepresentationFilteredLoop
      (Clause := Clause) (Var := Var) (R := R) producer n hn with
    ⟨p, q, hselected⟩
  refine ⟨p, q, ?_⟩
  intro X hX
  have hloop := hselected X hX
  exact
    ⟨hX.2.2.1,
      hX.2.2.2.1,
      hX.2.2.2.2,
      hloop.1.2.1.numerical_spine.1,
      hloop.1.2.2,
      hloop.2⟩

/-! ## Packaged certificate -/

/-- P818 certificate: P710's three nails, read through the P778 SU(7)
representation normal form, force the color-adjoint trace filter that excludes
nonzero-trace prime-edge loops. -/
structure P710SU7RepresentationFilterConfinementCertificate
    {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [CompleteSpace E]
    {Clause : Type v} {Var : Type w} [Fintype Clause]
    (R : HamiltonianSATEnergySameCarrierUnifiedRootCertificate.{w, z, u, v}
      E) : Prop where
  su7_color_adjoint_filter_iff_trace_exact :
    ∀ M : ColorLoopField,
      SU7ColorAdjointRepresentationFilter M ↔
        ColorLoopTraceExact M
  filter_excludes_prime_edge_obstruction :
    ∀ {n : ℕ} {p q : AffineRelaxation.PrimeExponent},
      SU7ColorAdjointRepresentationFilter
        (primeEdgeColorLoopMatrix n p q) ->
        ¬ PrimeEdgeColorLoopObstructed n p q
  p710_su7_filtered_loop_excludes_nonzero_trace :
    ∀ {X : HamiltonianSATPhysicalProducerPair Clause Var}
      {n : ℕ} {p q : AffineRelaxation.PrimeExponent},
      P710SU7RepresentationFilteredPrimeEdgeLoop R X n p q ->
        ¬ PrimeEdgeColorLoopObstructed n p q
  p710_su7_filtered_loop_readout :
    ∀ {X : HamiltonianSATPhysicalProducerPair Clause Var}
      {n : ℕ} {p q : AffineRelaxation.PrimeExponent},
      P710SU7RepresentationFilteredPrimeEdgeLoop R X n p q ->
        X.2.2.axis = traceWeightedQCDPoincareCoordinateAxis ∧
          X.2.2.alphaInverseResidual = -((89000 : ℚ) / 128511) ∧
          X.2.2.yukawaMassOrder =
            [50, 346, 372, 489, 583, 682, 880, 908, 982] ∧
          X.2.2.ckmDepthSum = (386 : ℚ) ∧
          betaCoeff qcdBlockIncidenceOneLoopInput = 7 ∧
          selectedYukawaDepthTableCandidate.massOrder =
            [50, 346, 372, 489, 583, 682, 880, 908, 982] ∧
          ckmJarlskogDepthFromMatrix = (ckmCPDepthSum : Int) ∧
          SU7ColorAdjointRepresentationFilter
            (primeEdgeColorLoopMatrix n p q) ∧
          ¬ PrimeEdgeColorLoopObstructed n p q
  unit_bracket_selects_su7_filtered_loop :
    ColorLoopTraceUnitBracketProducer ->
      ∀ n : ℕ, 2 <= n ->
        ∃ p q : AffineRelaxation.PrimeExponent,
          ∀ X : HamiltonianSATPhysicalProducerPair Clause Var,
            HamiltonianSATCoordinateSpineProducerNailSurface R X ->
              P710SU7RepresentationFilteredPrimeEdgeLoop R X n p q ∧
                ¬ PrimeEdgeColorLoopObstructed n p q
  unit_bracket_forces_su7_filtered_nails_and_confinement :
    ColorLoopTraceUnitBracketProducer ->
      ∀ n : ℕ, 2 <= n ->
        ∃ p q : AffineRelaxation.PrimeExponent,
          ∀ X : HamiltonianSATPhysicalProducerPair Clause Var,
            HamiltonianSATCoordinateSpineProducerNailSurface R X ->
              X.2.2.alphaInverseResidual = -((89000 : ℚ) / 128511) ∧
                X.2.2.yukawaMassOrder =
                  [50, 346, 372, 489, 583, 682, 880, 908, 982] ∧
                X.2.2.ckmDepthSum = (386 : ℚ) ∧
                betaCoeff qcdBlockIncidenceOneLoopInput = 7 ∧
                SU7ColorAdjointRepresentationFilter
                  (primeEdgeColorLoopMatrix n p q) ∧
                ¬ PrimeEdgeColorLoopObstructed n p q

/-- THEOREM 8: canonical P710/SU(7) representation-filter confinement
certificate. -/
theorem p710SU7RepresentationFilterConfinementCertificate
    {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [CompleteSpace E]
    {Clause : Type v} {Var : Type w} [Fintype Clause]
    (R : HamiltonianSATEnergySameCarrierUnifiedRootCertificate.{w, z, u, v}
      E) :
    P710SU7RepresentationFilterConfinementCertificate
      (Clause := Clause) (Var := Var) R where
  su7_color_adjoint_filter_iff_trace_exact :=
    su7ColorAdjointRepresentationFilter_iff_traceExact
  filter_excludes_prime_edge_obstruction := by
    intro n p q hfilter
    exact
      su7ColorAdjointRepresentationFilter_excludes_primeEdgeObstruction
        hfilter
  p710_su7_filtered_loop_excludes_nonzero_trace := by
    intro X n p q hloop
    exact p710SU7RepresentationFilteredPrimeEdgeLoop_excludes_nonzeroTrace hloop
  p710_su7_filtered_loop_readout := by
    intro X n p q hloop
    exact p710Nails_su7RepresentationFilter_readout hloop
  unit_bracket_selects_su7_filtered_loop := by
    intro producer n hn
    exact
      threeNailUnitBracket_selects_su7RepresentationFilteredLoop
        (Clause := Clause) (Var := Var) (R := R) producer n hn
  unit_bracket_forces_su7_filtered_nails_and_confinement := by
    intro producer n hn
    exact
      threeNailUnitBracket_forces_su7FilteredNailsAndConfinement
        (Clause := Clause) (Var := Var) (R := R) producer n hn

end GrandUnification
end SaturationMonoid
