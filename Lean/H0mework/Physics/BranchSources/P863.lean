import H0mework.Physics.BranchSources.P862

/-!
# Proposition 863: representation support generates positive branch dimension

P862 proved:

`positive branch-rule dimension -> SU7RepresentationAllowedSectorLaw -> ...`.

This file supplies the preceding producer shape:

`SU(7) representation weights -> color-loop branch rule -> positive dimension`.

A representation branch rule carries a branch rule plus a natural-valued
representation weight on branch cells.  If a cell in the representation support
has positive weight and zero branch residual, the branch-rule completeness law
puts it in `allowedCells`; therefore the allowed-sector dimension is positive.

Again, no `TraceZeroPrimeEdgeLoop` is stored.
-/

namespace SaturationMonoid
namespace StandardModelConstraint

noncomputable section

open SaturationMonoid.AffineRelaxation

set_option linter.defProp false

/-! ## Representation-weighted branch rules -/

/-- A representation-weighted color-loop branch rule over one even fiber.

The only new datum is a natural-valued representation multiplicity/weight on
branch cells.  The completeness law says: a family cell with positive
representation weight and zero residual is admitted into `allowedCells`. -/
structure SU7RepresentationWeightedBranchRule (n : ℕ) where
  rule : SU7ColorLoopFiberBranchRule n
  representationWeight : SU7PrimeEdgeBranchCell n -> ℕ
  support_complete :
    ∀ B : SU7PrimeEdgeBranchCell n,
      B ∈ rule.branchFamily.branchCells ->
        0 < representationWeight B ->
          branchWeightResidual B = 0 ->
            B ∈ rule.allowedCells

/-- A nonempty representation support witness with zero branch residual. -/
def SU7RepresentationZeroResidualSupport
    {n : ℕ} (R : SU7RepresentationWeightedBranchRule n) : Prop :=
  ∃ B : SU7PrimeEdgeBranchCell n,
    B ∈ R.rule.branchFamily.branchCells ∧
      0 < R.representationWeight B ∧
        branchWeightResidual B = 0

/-- THEOREM 1: a zero-residual representation support cell is admitted into
the branch rule's allowed cells. -/
theorem allowedCell_mem_of_representationZeroResidualSupport
    {n : ℕ} (R : SU7RepresentationWeightedBranchRule n)
    {B : SU7PrimeEdgeBranchCell n}
    (hB : B ∈ R.rule.branchFamily.branchCells)
    (hwt : 0 < R.representationWeight B)
    (hzero : branchWeightResidual B = 0) :
    B ∈ R.rule.allowedCells :=
  R.support_complete B hB hwt hzero

/-- THEOREM 2: representation support with zero residual forces positive
prime-edge allowed-sector dimension. -/
theorem positiveAllowedDimension_of_representationZeroResidualSupport
    {n : ℕ} (R : SU7RepresentationWeightedBranchRule n)
    (hR : SU7RepresentationZeroResidualSupport R) :
    0 < primeEdgeAllowedSectorDimension R.rule := by
  rcases hR with ⟨B, hfamily, hwt, hzero⟩
  have hmem : B ∈ R.rule.allowedCells :=
    allowedCell_mem_of_representationZeroResidualSupport
      R hfamily hwt hzero
  exact List.length_pos_of_mem hmem

/-! ## Fiberwise representation support gives the whole downstream chain -/

/-- Every even fiber has a representation-weighted branch rule with nonempty
zero-residual support. -/
def SU7RepresentationZeroResidualSupportEveryEvenFiber : Prop :=
  ∀ n : ℕ, 2 ≤ n ->
    ∃ R : SU7RepresentationWeightedBranchRule n,
      SU7RepresentationZeroResidualSupport R

/-- THEOREM 3: representation zero-residual support on every even fiber
produces positive branch-rule dimension on every even fiber. -/
theorem positiveBranchDimension_of_representationZeroResidualSupportEveryEvenFiber
    (H : SU7RepresentationZeroResidualSupportEveryEvenFiber) :
    SU7BranchRulePositiveDimensionEveryEvenFiber := by
  intro n hn
  rcases H n hn with ⟨R, hR⟩
  exact ⟨R.rule,
    positiveAllowedDimension_of_representationZeroResidualSupport R hR⟩

/-- THEOREM 4: representation zero-residual support produces the
representation allowed-sector law. -/
theorem su7RepresentationAllowedSectorLaw_of_representationZeroResidualSupport
    (H : SU7RepresentationZeroResidualSupportEveryEvenFiber) :
    SU7RepresentationAllowedSectorLaw :=
  su7RepresentationAllowedSectorLaw_of_positiveBranchDimension
    (positiveBranchDimension_of_representationZeroResidualSupportEveryEvenFiber H)

/-- THEOREM 5: representation zero-residual support produces residual-split
confinement. -/
theorem confinementResidualSplitLaw_of_representationZeroResidualSupport
    (H : SU7RepresentationZeroResidualSupportEveryEvenFiber) :
    SU7ConfinementResidualSplitLaw :=
  confinementResidualSplitLaw_of_positiveBranchDimension
    (positiveBranchDimension_of_representationZeroResidualSupportEveryEvenFiber H)

/-- THEOREM 6: representation zero-residual support produces
spectrum-resolved alpha convergence. -/
theorem spectrumResolvedAlphaConvergentCarrier_of_representationZeroResidualSupport
    (H : SU7RepresentationZeroResidualSupportEveryEvenFiber) :
    SpectrumResolvedAlphaConvergentCarrier :=
  spectrumResolvedAlphaConvergentCarrier_of_positiveBranchDimension
    (positiveBranchDimension_of_representationZeroResidualSupportEveryEvenFiber H)

/-- THEOREM 7: representation zero-residual support produces no-gap. -/
theorem traceSpectrumNoGap_of_representationZeroResidualSupport
    (H : SU7RepresentationZeroResidualSupportEveryEvenFiber) :
    PrimeEdgeTraceSpectrumNoGap :=
  traceSpectrumNoGap_of_positiveBranchDimension
    (positiveBranchDimension_of_representationZeroResidualSupportEveryEvenFiber H)

/-- THEOREM 8: representation zero-residual support produces the unit
bracket. -/
theorem unitBracketProducer_of_representationZeroResidualSupport
    (H : SU7RepresentationZeroResidualSupportEveryEvenFiber) :
    ColorLoopTraceUnitBracketProducer :=
  unitBracketProducer_of_positiveBranchDimension
    (positiveBranchDimension_of_representationZeroResidualSupportEveryEvenFiber H)

/-- THEOREM 9: representation zero-residual support produces the fixed-point
producer. -/
theorem fixedPointProducer_of_representationZeroResidualSupport
    (H : SU7RepresentationZeroResidualSupportEveryEvenFiber) :
    Nonempty EvenGoldbachDynamicalFixedPointProducer :=
  fixedPointProducer_of_positiveBranchDimension
    (positiveBranchDimension_of_representationZeroResidualSupportEveryEvenFiber H)

/-- THEOREM 10: representation zero-residual support produces ordinary even
Goldbach through the color-loop chain. -/
theorem evenGoldbach_of_representationZeroResidualSupport
    (H : SU7RepresentationZeroResidualSupportEveryEvenFiber) :
    EvenGoldbachStatement :=
  evenGoldbach_of_positiveBranchDimension
    (positiveBranchDimension_of_representationZeroResidualSupportEveryEvenFiber H)

/-! ## Certificate -/

/-- P863 certificate: representation support is now the named upstream throat
for the branch-rule dimension chain. -/
structure SU7RepresentationSupportBranchRuleProducerCertificate : Prop where
  support_to_positive_dimension :
    SU7RepresentationZeroResidualSupportEveryEvenFiber ->
      SU7BranchRulePositiveDimensionEveryEvenFiber
  support_to_representation :
    SU7RepresentationZeroResidualSupportEveryEvenFiber ->
      SU7RepresentationAllowedSectorLaw
  support_to_confinement :
    SU7RepresentationZeroResidualSupportEveryEvenFiber ->
      SU7ConfinementResidualSplitLaw
  support_to_spectrum_alpha :
    SU7RepresentationZeroResidualSupportEveryEvenFiber ->
      SpectrumResolvedAlphaConvergentCarrier
  support_to_no_gap :
    SU7RepresentationZeroResidualSupportEveryEvenFiber ->
      PrimeEdgeTraceSpectrumNoGap
  support_to_unit_bracket :
    SU7RepresentationZeroResidualSupportEveryEvenFiber ->
      ColorLoopTraceUnitBracketProducer
  support_to_fixed_point :
    SU7RepresentationZeroResidualSupportEveryEvenFiber ->
      Nonempty EvenGoldbachDynamicalFixedPointProducer
  support_to_goldbach :
    SU7RepresentationZeroResidualSupportEveryEvenFiber ->
      EvenGoldbachStatement

def su7RepresentationSupportBranchRuleProducerCertificate :
    SU7RepresentationSupportBranchRuleProducerCertificate where
  support_to_positive_dimension :=
    positiveBranchDimension_of_representationZeroResidualSupportEveryEvenFiber
  support_to_representation :=
    su7RepresentationAllowedSectorLaw_of_representationZeroResidualSupport
  support_to_confinement :=
    confinementResidualSplitLaw_of_representationZeroResidualSupport
  support_to_spectrum_alpha :=
    spectrumResolvedAlphaConvergentCarrier_of_representationZeroResidualSupport
  support_to_no_gap :=
    traceSpectrumNoGap_of_representationZeroResidualSupport
  support_to_unit_bracket :=
    unitBracketProducer_of_representationZeroResidualSupport
  support_to_fixed_point :=
    fixedPointProducer_of_representationZeroResidualSupport
  support_to_goldbach :=
    evenGoldbach_of_representationZeroResidualSupport


end
end StandardModelConstraint
end SaturationMonoid
