import H0mework.Physics.ColorLoops.P861

/-!
# Proposition 862: positive branch dimension produces the representation law

The requested chain is:

`SU(7) representation -> color-loop fiber branch rule
 -> prime-edge allowed-sector dimension > 0
 -> SU7RepresentationAllowedSectorLaw
 -> confinement / spectrum alpha / no-gap / unit bracket`.

This file formalizes the middle of that chain without storing trace-zero loops.
A branch rule stores:

* an underlying branch family;
* a finite list of allowed branch cells;
* proofs that allowed cells are in the family and have zero branch residual.

The allowed-sector dimension is the length of that allowed-cell list.  If it is
positive, Lean extracts branch-weight coverage, and the P861/P860/P835/P834
chain supplies the representation law and all downstream producer readouts.
-/

namespace SaturationMonoid
namespace StandardModelConstraint

noncomputable section

open SaturationMonoid.AffineRelaxation

set_option linter.defProp false

/-! ## Fiber branch rule and allowed dimension -/

/-- A SU(7) color-loop branch rule over one even fiber.

The `allowedCells` are branch cells, not `TraceZeroPrimeEdgeLoop`s.  Their
soundness is expressed by membership in the branch family plus zero branch
residual. -/
structure SU7ColorLoopFiberBranchRule (n : ℕ) where
  branchFamily : SU7PrimeEdgeBranchFamily n
  allowedCells : List (SU7PrimeEdgeBranchCell n)
  allowed_in_family :
    ∀ B : SU7PrimeEdgeBranchCell n,
      B ∈ allowedCells -> B ∈ branchFamily.branchCells
  allowed_residual_zero :
    ∀ B : SU7PrimeEdgeBranchCell n,
      B ∈ allowedCells -> branchWeightResidual B = 0

/-- The prime-edge allowed-sector dimension of a fiber branch rule. -/
def primeEdgeAllowedSectorDimension
    {n : ℕ} (R : SU7ColorLoopFiberBranchRule n) : ℕ :=
  R.allowedCells.length

/-- THEOREM 1: positive allowed-sector dimension gives branch-weight coverage
on that fiber. -/
theorem branchWeightCoverage_of_positiveAllowedDimension
    {n : ℕ} (R : SU7ColorLoopFiberBranchRule n)
    (hpos : 0 < primeEdgeAllowedSectorDimension R) :
    SU7PrimeEdgeBranchWeightCoverage R.branchFamily := by
  cases hcells : R.allowedCells with
  | nil =>
      simp [primeEdgeAllowedSectorDimension, hcells] at hpos
  | cons B Bs =>
      refine ⟨B, ?_, ?_⟩
      · exact R.allowed_in_family B (by simp [hcells])
      · exact R.allowed_residual_zero B (by simp [hcells])

/-! ## Fiberwise positive dimension gives representation law -/

/-- Every even fiber carries a SU(7) branch rule whose allowed-sector
dimension is positive. -/
def SU7BranchRulePositiveDimensionEveryEvenFiber : Prop :=
  ∀ n : ℕ, 2 ≤ n ->
    ∃ R : SU7ColorLoopFiberBranchRule n,
      0 < primeEdgeAllowedSectorDimension R

/-- THEOREM 2: positive branch-rule dimension on every even fiber gives
branch-weight coverage on every even fiber. -/
theorem branchWeightCoverageEveryEvenFiber_of_positiveBranchDimension
    (H : SU7BranchRulePositiveDimensionEveryEvenFiber) :
    SU7PrimeEdgeBranchWeightCoverageEveryEvenFiber := by
  intro n hn
  rcases H n hn with ⟨R, hdim⟩
  exact ⟨R.branchFamily,
    branchWeightCoverage_of_positiveAllowedDimension R hdim⟩

/-- THEOREM 3: positive branch-rule dimension on every even fiber gives the
P860 branch certificate producer. -/
theorem branchingEveryEvenFiber_of_positiveBranchDimension
    (H : SU7BranchRulePositiveDimensionEveryEvenFiber) :
    SU7PrimeEdgeBranchingEveryEvenFiber :=
  branchingEveryEvenFiber_of_branchWeightCoverageEveryEvenFiber
    (branchWeightCoverageEveryEvenFiber_of_positiveBranchDimension H)

/-- THEOREM 4: positive branch-rule dimension gives the SU(7)-filtered
prime-edge producer. -/
theorem su7FilteredProducer_of_positiveBranchDimension
    (H : SU7BranchRulePositiveDimensionEveryEvenFiber) :
    SU7FilteredPrimeEdgeLoopProducer :=
  su7FilteredProducer_of_branchingEveryEvenFiber
    (branchingEveryEvenFiber_of_positiveBranchDimension H)

/-- THEOREM 5: positive branch-rule dimension gives the representation
allowed-sector law. -/
theorem su7RepresentationAllowedSectorLaw_of_positiveBranchDimension
    (H : SU7BranchRulePositiveDimensionEveryEvenFiber) :
    SU7RepresentationAllowedSectorLaw :=
  su7RepresentationAllowedSectorLaw_of_filteredProducer
    (su7FilteredProducer_of_positiveBranchDimension H)

/-- THEOREM 6: positive branch-rule dimension gives residual-split
confinement via P835/P834. -/
theorem confinementResidualSplitLaw_of_positiveBranchDimension
    (H : SU7BranchRulePositiveDimensionEveryEvenFiber) :
    SU7ConfinementResidualSplitLaw :=
  confinementResidualSplitLaw_of_su7RepresentationAllowedSectorLaw
    (su7RepresentationAllowedSectorLaw_of_positiveBranchDimension H)

/-- THEOREM 7: positive branch-rule dimension gives spectrum-resolved alpha
convergence via P837. -/
theorem spectrumResolvedAlphaConvergentCarrier_of_positiveBranchDimension
    (H : SU7BranchRulePositiveDimensionEveryEvenFiber) :
    SpectrumResolvedAlphaConvergentCarrier :=
  spectrumResolvedAlphaConvergentCarrier_of_su7RepresentationAllowedSectorLaw
    (su7RepresentationAllowedSectorLaw_of_positiveBranchDimension H)

/-- THEOREM 8: positive branch-rule dimension gives no-gap. -/
theorem traceSpectrumNoGap_of_positiveBranchDimension
    (H : SU7BranchRulePositiveDimensionEveryEvenFiber) :
    PrimeEdgeTraceSpectrumNoGap :=
  traceSpectrumNoGap_of_branchWeightCoverageEveryEvenFiber
    (branchWeightCoverageEveryEvenFiber_of_positiveBranchDimension H)

/-- THEOREM 9: positive branch-rule dimension gives the unit bracket. -/
theorem unitBracketProducer_of_positiveBranchDimension
    (H : SU7BranchRulePositiveDimensionEveryEvenFiber) :
    ColorLoopTraceUnitBracketProducer :=
  unitBracketProducer_of_branchWeightCoverageEveryEvenFiber
    (branchWeightCoverageEveryEvenFiber_of_positiveBranchDimension H)

/-- THEOREM 10: positive branch-rule dimension gives the fixed-point
producer. -/
theorem fixedPointProducer_of_positiveBranchDimension
    (H : SU7BranchRulePositiveDimensionEveryEvenFiber) :
    Nonempty EvenGoldbachDynamicalFixedPointProducer :=
  fixedPointProducer_of_branchWeightCoverageEveryEvenFiber
    (branchWeightCoverageEveryEvenFiber_of_positiveBranchDimension H)

/-- THEOREM 11: positive branch-rule dimension gives the ordinary even
Goldbach statement through the SU(7)-filtered producer equivalence. -/
theorem evenGoldbach_of_positiveBranchDimension
    (H : SU7BranchRulePositiveDimensionEveryEvenFiber) :
    EvenGoldbachStatement :=
  (su7FilteredPrimeEdgeLoopProducer_iff_evenGoldbach).mp
    (su7FilteredProducer_of_positiveBranchDimension H)

/-! ## Certificate -/

/-- P862 certificate: the branch-rule dimension route is now explicit. -/
structure SU7PositiveBranchDimensionRepresentationChainCertificate : Prop where
  positive_dimension_to_coverage :
    SU7BranchRulePositiveDimensionEveryEvenFiber ->
      SU7PrimeEdgeBranchWeightCoverageEveryEvenFiber
  positive_dimension_to_branching :
    SU7BranchRulePositiveDimensionEveryEvenFiber ->
      SU7PrimeEdgeBranchingEveryEvenFiber
  positive_dimension_to_filtered :
    SU7BranchRulePositiveDimensionEveryEvenFiber ->
      SU7FilteredPrimeEdgeLoopProducer
  positive_dimension_to_representation :
    SU7BranchRulePositiveDimensionEveryEvenFiber ->
      SU7RepresentationAllowedSectorLaw
  positive_dimension_to_confinement :
    SU7BranchRulePositiveDimensionEveryEvenFiber ->
      SU7ConfinementResidualSplitLaw
  positive_dimension_to_spectrum_alpha :
    SU7BranchRulePositiveDimensionEveryEvenFiber ->
      SpectrumResolvedAlphaConvergentCarrier
  positive_dimension_to_no_gap :
    SU7BranchRulePositiveDimensionEveryEvenFiber ->
      PrimeEdgeTraceSpectrumNoGap
  positive_dimension_to_unit_bracket :
    SU7BranchRulePositiveDimensionEveryEvenFiber ->
      ColorLoopTraceUnitBracketProducer
  positive_dimension_to_fixed_point :
    SU7BranchRulePositiveDimensionEveryEvenFiber ->
      Nonempty EvenGoldbachDynamicalFixedPointProducer
  positive_dimension_to_goldbach :
    SU7BranchRulePositiveDimensionEveryEvenFiber ->
      EvenGoldbachStatement

def su7PositiveBranchDimensionRepresentationChainCertificate :
    SU7PositiveBranchDimensionRepresentationChainCertificate where
  positive_dimension_to_coverage :=
    branchWeightCoverageEveryEvenFiber_of_positiveBranchDimension
  positive_dimension_to_branching :=
    branchingEveryEvenFiber_of_positiveBranchDimension
  positive_dimension_to_filtered :=
    su7FilteredProducer_of_positiveBranchDimension
  positive_dimension_to_representation :=
    su7RepresentationAllowedSectorLaw_of_positiveBranchDimension
  positive_dimension_to_confinement :=
    confinementResidualSplitLaw_of_positiveBranchDimension
  positive_dimension_to_spectrum_alpha :=
    spectrumResolvedAlphaConvergentCarrier_of_positiveBranchDimension
  positive_dimension_to_no_gap :=
    traceSpectrumNoGap_of_positiveBranchDimension
  positive_dimension_to_unit_bracket :=
    unitBracketProducer_of_positiveBranchDimension
  positive_dimension_to_fixed_point :=
    fixedPointProducer_of_positiveBranchDimension
  positive_dimension_to_goldbach :=
    evenGoldbach_of_positiveBranchDimension


end
end StandardModelConstraint
end SaturationMonoid
