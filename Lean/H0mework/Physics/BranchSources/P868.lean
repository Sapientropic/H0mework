import H0mework.Physics.BranchSources.P863

/-!
# Proposition 868: computed representation support from branch weights

P863 named the remaining upstream throat as

`SU7RepresentationZeroResidualSupportEveryEvenFiber`.

Its `SU7RepresentationWeightedBranchRule` still carried an `allowedCells` list
and a `support_complete` field.  This file removes that hand-filled layer.
Given only:

* a finite branch family;
* a representation multiplicity/weight on its branch cells;
* one branch cell in the family with positive representation weight and zero
  branch residual,

Lean computes the allowed cells by filtering the branch family and then
constructs the P863 weighted branch rule and zero-residual support.  The
remaining producer debt is therefore exactly the real SU(7) branching theorem:
on every even fiber, the representation spectrum supplies such a positive
zero-residual branch cell.
-/

namespace SaturationMonoid
namespace StandardModelConstraint

noncomputable section

open SaturationMonoid.AffineRelaxation

set_option linter.defProp false

/-! ## Raw branch-weight generators -/

/-- Raw representation branch-weight generator over one even fiber.

This object does not store `allowedCells`, a `TraceZeroPrimeEdgeLoop`, or an
allowed-sector loop.  It stores only a finite branch family, a representation
weight on branch cells, and one support cell whose weight/residual data can be
checked directly. -/
structure SU7RepresentationBranchWeightGenerator (n : ℕ) where
  branchFamily : SU7PrimeEdgeBranchFamily n
  representationWeight : SU7PrimeEdgeBranchCell n -> ℕ
  supportCell : SU7PrimeEdgeBranchCell n
  support_mem : supportCell ∈ branchFamily.branchCells
  support_weight_positive : 0 < representationWeight supportCell
  support_residual_zero : branchWeightResidual supportCell = 0

/-- Boolean readout for computed allowed branch cells: positive representation
weight and zero branch residual. -/
def computedAllowedBranchCell
    {n : ℕ} (G : SU7RepresentationBranchWeightGenerator n)
    (B : SU7PrimeEdgeBranchCell n) : Bool :=
  decide (0 < G.representationWeight B ∧ branchWeightResidual B = 0)

/-- Computed allowed branch cells: a branch is allowed exactly when the
representation gives it positive weight and its prime-edge weight hits the
even-fiber target. -/
def computedAllowedBranchCells
    {n : ℕ} (G : SU7RepresentationBranchWeightGenerator n) :
    List (SU7PrimeEdgeBranchCell n) :=
  G.branchFamily.branchCells.filter (computedAllowedBranchCell G)

/-- THEOREM 1: every computed allowed cell comes from the original branch
family. -/
theorem computedAllowedBranchCells_mem_family
    {n : ℕ} (G : SU7RepresentationBranchWeightGenerator n)
    {B : SU7PrimeEdgeBranchCell n}
    (hB : B ∈ computedAllowedBranchCells G) :
    B ∈ G.branchFamily.branchCells := by
  exact List.mem_of_mem_filter hB

/-- THEOREM 2: every computed allowed cell has zero branch residual. -/
theorem computedAllowedBranchCells_residual_zero
    {n : ℕ} (G : SU7RepresentationBranchWeightGenerator n)
    {B : SU7PrimeEdgeBranchCell n}
    (hB : B ∈ computedAllowedBranchCells G) :
    branchWeightResidual B = 0 := by
  have hbool :
      computedAllowedBranchCell G B = true :=
    List.of_mem_filter hB
  have hprop :
      0 < G.representationWeight B ∧ branchWeightResidual B = 0 := by
    simpa [computedAllowedBranchCell, decide_eq_true_eq] using hbool
  exact hprop.2

/-- THEOREM 3: the generator's support cell is in the computed allowed-cell
list. -/
theorem supportCell_mem_computedAllowedBranchCells
    {n : ℕ} (G : SU7RepresentationBranchWeightGenerator n) :
    G.supportCell ∈ computedAllowedBranchCells G := by
  exact List.mem_filter_of_mem G.support_mem (by
    simp [computedAllowedBranchCell, G.support_weight_positive,
      G.support_residual_zero])

/-! ## From computed cells to P863 weighted branch rules -/

/-- THEOREM 4: a raw branch-weight generator computes the P862 fiber branch
rule.  The `allowedCells` field is no longer an input; it is the filter of the
finite branch family by positive representation weight and zero residual. -/
def colorLoopFiberBranchRule_of_branchWeightGenerator
    {n : ℕ} (G : SU7RepresentationBranchWeightGenerator n) :
    SU7ColorLoopFiberBranchRule n where
  branchFamily := G.branchFamily
  allowedCells := computedAllowedBranchCells G
  allowed_in_family := by
    intro B hB
    exact computedAllowedBranchCells_mem_family G hB
  allowed_residual_zero := by
    intro B hB
    exact computedAllowedBranchCells_residual_zero G hB

/-- THEOREM 5: the computed branch rule has positive allowed-sector dimension.
-/
theorem positiveAllowedDimension_of_branchWeightGenerator
    {n : ℕ} (G : SU7RepresentationBranchWeightGenerator n) :
    0 <
      primeEdgeAllowedSectorDimension
        (colorLoopFiberBranchRule_of_branchWeightGenerator G) := by
  exact List.length_pos_of_mem
    (supportCell_mem_computedAllowedBranchCells G)

/-- THEOREM 6: a raw branch-weight generator computes the P863
representation-weighted branch rule.  The support-completeness law is exactly
membership in the computed filter. -/
def representationWeightedBranchRule_of_branchWeightGenerator
    {n : ℕ} (G : SU7RepresentationBranchWeightGenerator n) :
    SU7RepresentationWeightedBranchRule n where
  rule := colorLoopFiberBranchRule_of_branchWeightGenerator G
  representationWeight := G.representationWeight
  support_complete := by
    intro B hfamily hwt hzero
    exact List.mem_filter_of_mem hfamily (by
      simp [computedAllowedBranchCell, hwt, hzero])

/-- THEOREM 7: a raw branch-weight generator produces the P863 nonempty
zero-residual representation support witness. -/
theorem representationZeroResidualSupport_of_branchWeightGenerator
    {n : ℕ} (G : SU7RepresentationBranchWeightGenerator n) :
    SU7RepresentationZeroResidualSupport
      (representationWeightedBranchRule_of_branchWeightGenerator G) := by
  refine ⟨G.supportCell, G.support_mem,
    G.support_weight_positive, G.support_residual_zero⟩

/-! ## Fiberwise generator gives the full downstream chain -/

/-- Every even fiber carries a raw SU(7) representation branch-weight
generator. -/
def SU7RepresentationBranchWeightGeneratorEveryEvenFiber : Prop :=
  ∀ n : ℕ, 2 ≤ n ->
    Nonempty (SU7RepresentationBranchWeightGenerator n)

/-- THEOREM 8: fiberwise raw branch-weight generators produce P863's
zero-residual support on every even fiber. -/
theorem representationZeroResidualSupportEveryEvenFiber_of_branchWeightGenerator
    (H : SU7RepresentationBranchWeightGeneratorEveryEvenFiber) :
    SU7RepresentationZeroResidualSupportEveryEvenFiber := by
  intro n hn
  rcases H n hn with ⟨G⟩
  exact ⟨representationWeightedBranchRule_of_branchWeightGenerator G,
    representationZeroResidualSupport_of_branchWeightGenerator G⟩

/-- THEOREM 9: fiberwise raw branch-weight generators produce positive branch
dimension on every even fiber. -/
theorem positiveBranchDimension_of_branchWeightGenerator
    (H : SU7RepresentationBranchWeightGeneratorEveryEvenFiber) :
    SU7BranchRulePositiveDimensionEveryEvenFiber :=
  positiveBranchDimension_of_representationZeroResidualSupportEveryEvenFiber
    (representationZeroResidualSupportEveryEvenFiber_of_branchWeightGenerator H)

/-- THEOREM 10: fiberwise raw branch-weight generators produce the SU(7)
representation allowed-sector law. -/
theorem su7RepresentationAllowedSectorLaw_of_branchWeightGenerator
    (H : SU7RepresentationBranchWeightGeneratorEveryEvenFiber) :
    SU7RepresentationAllowedSectorLaw :=
  su7RepresentationAllowedSectorLaw_of_representationZeroResidualSupport
    (representationZeroResidualSupportEveryEvenFiber_of_branchWeightGenerator H)

/-- THEOREM 11: fiberwise raw branch-weight generators produce residual-split
confinement. -/
theorem confinementResidualSplitLaw_of_branchWeightGenerator
    (H : SU7RepresentationBranchWeightGeneratorEveryEvenFiber) :
    SU7ConfinementResidualSplitLaw :=
  confinementResidualSplitLaw_of_representationZeroResidualSupport
    (representationZeroResidualSupportEveryEvenFiber_of_branchWeightGenerator H)

/-- THEOREM 12: fiberwise raw branch-weight generators produce spectrum
alpha convergence. -/
theorem spectrumResolvedAlphaConvergentCarrier_of_branchWeightGenerator
    (H : SU7RepresentationBranchWeightGeneratorEveryEvenFiber) :
    SpectrumResolvedAlphaConvergentCarrier :=
  spectrumResolvedAlphaConvergentCarrier_of_representationZeroResidualSupport
    (representationZeroResidualSupportEveryEvenFiber_of_branchWeightGenerator H)

/-- THEOREM 13: fiberwise raw branch-weight generators produce no-gap. -/
theorem traceSpectrumNoGap_of_branchWeightGenerator
    (H : SU7RepresentationBranchWeightGeneratorEveryEvenFiber) :
    PrimeEdgeTraceSpectrumNoGap :=
  traceSpectrumNoGap_of_representationZeroResidualSupport
    (representationZeroResidualSupportEveryEvenFiber_of_branchWeightGenerator H)

/-- THEOREM 14: fiberwise raw branch-weight generators produce the unit
bracket. -/
theorem unitBracketProducer_of_branchWeightGenerator
    (H : SU7RepresentationBranchWeightGeneratorEveryEvenFiber) :
    ColorLoopTraceUnitBracketProducer :=
  unitBracketProducer_of_representationZeroResidualSupport
    (representationZeroResidualSupportEveryEvenFiber_of_branchWeightGenerator H)

/-- THEOREM 15: fiberwise raw branch-weight generators produce ordinary even
Goldbach through the color-loop chain. -/
theorem evenGoldbach_of_branchWeightGenerator
    (H : SU7RepresentationBranchWeightGeneratorEveryEvenFiber) :
    EvenGoldbachStatement :=
  evenGoldbach_of_representationZeroResidualSupport
    (representationZeroResidualSupportEveryEvenFiber_of_branchWeightGenerator H)

/-! ## Certificate -/

/-- P868 certificate: the support throat is now computed from raw branch
weights.  The only remaining upstream theorem is the actual SU(7)
representation-branch generator on every even fiber. -/
structure SU7ComputedRepresentationSupportProducerCertificate where
  computed_allowed_mem_family :
    ∀ {n : ℕ} (G : SU7RepresentationBranchWeightGenerator n)
      {B : SU7PrimeEdgeBranchCell n},
      B ∈ computedAllowedBranchCells G ->
        B ∈ G.branchFamily.branchCells
  computed_allowed_residual_zero :
    ∀ {n : ℕ} (G : SU7RepresentationBranchWeightGenerator n)
      {B : SU7PrimeEdgeBranchCell n},
      B ∈ computedAllowedBranchCells G ->
        branchWeightResidual B = 0
  support_cell_computed :
    ∀ {n : ℕ} (G : SU7RepresentationBranchWeightGenerator n),
      G.supportCell ∈ computedAllowedBranchCells G
  generator_to_branch_rule :
    ∀ {n : ℕ}, SU7RepresentationBranchWeightGenerator n ->
      SU7ColorLoopFiberBranchRule n
  generator_to_weighted_rule :
    ∀ {n : ℕ}, SU7RepresentationBranchWeightGenerator n ->
      SU7RepresentationWeightedBranchRule n
  generator_to_support :
    ∀ {n : ℕ} (G : SU7RepresentationBranchWeightGenerator n),
      SU7RepresentationZeroResidualSupport
        (representationWeightedBranchRule_of_branchWeightGenerator G)
  every_fiber_to_support :
    SU7RepresentationBranchWeightGeneratorEveryEvenFiber ->
      SU7RepresentationZeroResidualSupportEveryEvenFiber
  every_fiber_to_representation :
    SU7RepresentationBranchWeightGeneratorEveryEvenFiber ->
      SU7RepresentationAllowedSectorLaw
  every_fiber_to_confinement :
    SU7RepresentationBranchWeightGeneratorEveryEvenFiber ->
      SU7ConfinementResidualSplitLaw
  every_fiber_to_no_gap :
    SU7RepresentationBranchWeightGeneratorEveryEvenFiber ->
      PrimeEdgeTraceSpectrumNoGap
  every_fiber_to_unit_bracket :
    SU7RepresentationBranchWeightGeneratorEveryEvenFiber ->
      ColorLoopTraceUnitBracketProducer
  every_fiber_to_goldbach :
    SU7RepresentationBranchWeightGeneratorEveryEvenFiber ->
      EvenGoldbachStatement

def su7ComputedRepresentationSupportProducerCertificate :
    SU7ComputedRepresentationSupportProducerCertificate where
  computed_allowed_mem_family :=
    computedAllowedBranchCells_mem_family
  computed_allowed_residual_zero :=
    computedAllowedBranchCells_residual_zero
  support_cell_computed :=
    supportCell_mem_computedAllowedBranchCells
  generator_to_branch_rule :=
    colorLoopFiberBranchRule_of_branchWeightGenerator
  generator_to_weighted_rule :=
    representationWeightedBranchRule_of_branchWeightGenerator
  generator_to_support :=
    representationZeroResidualSupport_of_branchWeightGenerator
  every_fiber_to_support :=
    representationZeroResidualSupportEveryEvenFiber_of_branchWeightGenerator
  every_fiber_to_representation :=
    su7RepresentationAllowedSectorLaw_of_branchWeightGenerator
  every_fiber_to_confinement :=
    confinementResidualSplitLaw_of_branchWeightGenerator
  every_fiber_to_no_gap :=
    traceSpectrumNoGap_of_branchWeightGenerator
  every_fiber_to_unit_bracket :=
    unitBracketProducer_of_branchWeightGenerator
  every_fiber_to_goldbach :=
    evenGoldbach_of_branchWeightGenerator


end
end StandardModelConstraint
end SaturationMonoid
