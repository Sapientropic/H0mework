import H0mework.Arithmetic.PrimeShadow.P860

/-!
# Proposition 861: branch-weight coverage is the remaining color-loop throat

P860 made the per-fiber object honest: a branch certificate stores branch cells
and a weight-hit proof, then computes the trace-zero loop.

This file names the next lower producer target.  A branch family is a finite
list of SU(7) / color-orbit branch cells.  Its coverage condition is purely a
branch-weight condition:

`branchWeightResidual = 0`, equivalently `p + q = 2n`.

Lean proves that this branch-weight coverage is exactly the data needed to
construct P860's `SU7PrimeEdgeBranchingCertificate`, and therefore it is the
precise remaining throat before no-gap / unit-bracket / confinement readouts.
-/

namespace SaturationMonoid
namespace StandardModelConstraint

noncomputable section

open SaturationMonoid.AffineRelaxation

set_option linter.defProp false

/-! ## Branch families and residual weights -/

/-- A finite SU(7) branch family over the even fiber `2n`.

It stores branch cells only; no trace-zero loop and no SU(7)-filtered fiber is
stored here. -/
structure SU7PrimeEdgeBranchFamily (n : ℕ) where
  branchCells : List (SU7PrimeEdgeBranchCell n)

/-- The integer residual of a branch cell's prime-edge weight against the
even-fiber target. -/
def branchWeightResidual {n : ℕ} (B : SU7PrimeEdgeBranchCell n) : ℤ :=
  (B.branchWeight : ℤ) -
    (SU7PrimeEdgeBranchCell.evenFiberWeight n : ℤ)

/-- THEOREM 1: zero branch residual is exactly the trace-neutral
prime-edge weight equation. -/
theorem branchWeightResidual_eq_zero_iff_traceNeutral
    {n : ℕ} (B : SU7PrimeEdgeBranchCell n) :
    branchWeightResidual B = 0 ↔ B.traceNeutral := by
  unfold branchWeightResidual SU7PrimeEdgeBranchCell.traceNeutral
  constructor <;> intro h <;> omega

/-- Branch-weight coverage: some branch cell in the family has zero residual.

This is the producer throat we actually need.  It is expressed only in terms
of branch cells, their prime-edge weights, and the even-fiber target. -/
def SU7PrimeEdgeBranchWeightCoverage
    {n : ℕ} (F : SU7PrimeEdgeBranchFamily n) : Prop :=
  ∃ B : SU7PrimeEdgeBranchCell n,
    B ∈ F.branchCells ∧ branchWeightResidual B = 0

/-! ## Coverage computes P860 certificates -/

/-- THEOREM 2: branch-weight coverage computes a P860 branch certificate. -/
def branchingCertificate_of_branchWeightCoverage
    {n : ℕ} (F : SU7PrimeEdgeBranchFamily n)
    (hF : SU7PrimeEdgeBranchWeightCoverage F) :
    SU7PrimeEdgeBranchingCertificate n :=
  let B : SU7PrimeEdgeBranchCell n := Classical.choose hF
  let hB :
      B ∈ F.branchCells ∧ branchWeightResidual B = 0 :=
    Classical.choose_spec hF
  { branchCells := F.branchCells
    selected := B
    selected_mem := hB.1
    selected_traceNeutral :=
      (branchWeightResidual_eq_zero_iff_traceNeutral B).mp hB.2 }

/-- THEOREM 3: a P860 branch certificate has an underlying branch family with
branch-weight coverage. -/
def branchWeightCoverage_of_branchingCertificate
    {n : ℕ} (C : SU7PrimeEdgeBranchingCertificate n) :
    ∃ F : SU7PrimeEdgeBranchFamily n,
      SU7PrimeEdgeBranchWeightCoverage F := by
  refine ⟨{ branchCells := C.branchCells }, ?_⟩
  refine ⟨C.selected, C.selected_mem, ?_⟩
  exact (branchWeightResidual_eq_zero_iff_traceNeutral C.selected).mpr
    C.selected_traceNeutral

/-- THEOREM 4: per-fiber branch-weight coverage is exactly per-fiber P860
branch certificate inhabitance. -/
theorem nonemptyBranchingCertificate_iff_exists_branchWeightCoverage
    (n : ℕ) :
    Nonempty (SU7PrimeEdgeBranchingCertificate n) ↔
      ∃ F : SU7PrimeEdgeBranchFamily n,
        SU7PrimeEdgeBranchWeightCoverage F := by
  constructor
  · intro hC
    rcases hC with ⟨C⟩
    exact branchWeightCoverage_of_branchingCertificate C
  · intro hF
    rcases hF with ⟨F, hcov⟩
    exact ⟨branchingCertificate_of_branchWeightCoverage F hcov⟩

/-! ## Fiberwise coverage is exactly the global P860 producer -/

/-- Every even fiber has SU(7) branch-weight coverage. -/
def SU7PrimeEdgeBranchWeightCoverageEveryEvenFiber : Prop :=
  ∀ n : ℕ, 2 ≤ n ->
    ∃ F : SU7PrimeEdgeBranchFamily n,
      SU7PrimeEdgeBranchWeightCoverage F

/-- THEOREM 5: fiberwise branch-weight coverage produces P860's branch
certificates on every even fiber. -/
theorem branchingEveryEvenFiber_of_branchWeightCoverageEveryEvenFiber
    (H : SU7PrimeEdgeBranchWeightCoverageEveryEvenFiber) :
    SU7PrimeEdgeBranchingEveryEvenFiber := by
  intro n hn
  exact
    (nonemptyBranchingCertificate_iff_exists_branchWeightCoverage n).mpr
      (H n hn)

/-- THEOREM 6: P860 branch certificates give fiberwise branch-weight
coverage. -/
theorem branchWeightCoverageEveryEvenFiber_of_branchingEveryEvenFiber
    (H : SU7PrimeEdgeBranchingEveryEvenFiber) :
    SU7PrimeEdgeBranchWeightCoverageEveryEvenFiber := by
  intro n hn
  exact
    (nonemptyBranchingCertificate_iff_exists_branchWeightCoverage n).mp
      (H n hn)

/-- THEOREM 7: branch-weight coverage is exactly P860's global branch
certificate producer. -/
theorem branchWeightCoverageEveryEvenFiber_iff_branchingEveryEvenFiber :
    SU7PrimeEdgeBranchWeightCoverageEveryEvenFiber ↔
      SU7PrimeEdgeBranchingEveryEvenFiber := by
  constructor
  · exact branchingEveryEvenFiber_of_branchWeightCoverageEveryEvenFiber
  · exact branchWeightCoverageEveryEvenFiber_of_branchingEveryEvenFiber

/-! ## Readouts from branch-weight coverage -/

/-- THEOREM 8: fiberwise branch-weight coverage gives trace-spectrum no-gap. -/
theorem traceSpectrumNoGap_of_branchWeightCoverageEveryEvenFiber
    (H : SU7PrimeEdgeBranchWeightCoverageEveryEvenFiber) :
    PrimeEdgeTraceSpectrumNoGap :=
  traceSpectrumNoGap_of_branchingEveryEvenFiber
    (branchingEveryEvenFiber_of_branchWeightCoverageEveryEvenFiber H)

/-- THEOREM 9: fiberwise branch-weight coverage forbids permanent color
holonomy. -/
theorem noPermanentColorHolonomy_of_branchWeightCoverageEveryEvenFiber
    (H : SU7PrimeEdgeBranchWeightCoverageEveryEvenFiber) :
    ¬ PermanentPrimeEdgeColorHolonomy :=
  noPermanentColorHolonomy_of_branchingEveryEvenFiber
    (branchingEveryEvenFiber_of_branchWeightCoverageEveryEvenFiber H)

/-- THEOREM 10: fiberwise branch-weight coverage gives the unit bracket. -/
theorem unitBracketProducer_of_branchWeightCoverageEveryEvenFiber
    (H : SU7PrimeEdgeBranchWeightCoverageEveryEvenFiber) :
    ColorLoopTraceUnitBracketProducer :=
  unitBracketProducer_of_branchingEveryEvenFiber
    (branchingEveryEvenFiber_of_branchWeightCoverageEveryEvenFiber H)

/-- THEOREM 11: fiberwise branch-weight coverage gives the fixed-point
producer. -/
theorem fixedPointProducer_of_branchWeightCoverageEveryEvenFiber
    (H : SU7PrimeEdgeBranchWeightCoverageEveryEvenFiber) :
    Nonempty EvenGoldbachDynamicalFixedPointProducer :=
  fixedPointProducer_of_branchingEveryEvenFiber
    (branchingEveryEvenFiber_of_branchWeightCoverageEveryEvenFiber H)

/-- THEOREM 12: fiberwise branch-weight coverage gives residual-split
confinement through the P860 branch route. -/
theorem confinementResidualSplit_of_branchWeightCoverageEveryEvenFiber
    (H : SU7PrimeEdgeBranchWeightCoverageEveryEvenFiber) :
    SU7ConfinementResidualSplitLaw :=
  confinementResidualSplit_of_branchingEveryEvenFiber
    (branchingEveryEvenFiber_of_branchWeightCoverageEveryEvenFiber H)

/-! ## Certificate -/

/-- P861 certificate: the current hard producer throat is branch-weight
coverage, not a trace-zero selector. -/
structure SU7PrimeEdgeBranchWeightCoverageThroatCertificate where
  residual_zero_iff_trace_neutral :
    ∀ {n : ℕ} (B : SU7PrimeEdgeBranchCell n),
      branchWeightResidual B = 0 ↔ B.traceNeutral
  coverage_to_certificate :
    ∀ {n : ℕ} (F : SU7PrimeEdgeBranchFamily n),
      SU7PrimeEdgeBranchWeightCoverage F ->
        SU7PrimeEdgeBranchingCertificate n
  certificate_to_coverage :
    ∀ {n : ℕ}, SU7PrimeEdgeBranchingCertificate n ->
      ∃ F : SU7PrimeEdgeBranchFamily n,
        SU7PrimeEdgeBranchWeightCoverage F
  per_fiber_iff :
    ∀ n : ℕ,
      Nonempty (SU7PrimeEdgeBranchingCertificate n) ↔
        ∃ F : SU7PrimeEdgeBranchFamily n,
          SU7PrimeEdgeBranchWeightCoverage F
  global_iff :
    SU7PrimeEdgeBranchWeightCoverageEveryEvenFiber ↔
      SU7PrimeEdgeBranchingEveryEvenFiber
  coverage_no_gap :
    SU7PrimeEdgeBranchWeightCoverageEveryEvenFiber ->
      PrimeEdgeTraceSpectrumNoGap
  coverage_unit_bracket :
    SU7PrimeEdgeBranchWeightCoverageEveryEvenFiber ->
      ColorLoopTraceUnitBracketProducer
  coverage_confinement :
    SU7PrimeEdgeBranchWeightCoverageEveryEvenFiber ->
      SU7ConfinementResidualSplitLaw

def su7PrimeEdgeBranchWeightCoverageThroatCertificate :
    SU7PrimeEdgeBranchWeightCoverageThroatCertificate where
  residual_zero_iff_trace_neutral :=
    branchWeightResidual_eq_zero_iff_traceNeutral
  coverage_to_certificate :=
    branchingCertificate_of_branchWeightCoverage
  certificate_to_coverage :=
    branchWeightCoverage_of_branchingCertificate
  per_fiber_iff :=
    nonemptyBranchingCertificate_iff_exists_branchWeightCoverage
  global_iff :=
    branchWeightCoverageEveryEvenFiber_iff_branchingEveryEvenFiber
  coverage_no_gap :=
    traceSpectrumNoGap_of_branchWeightCoverageEveryEvenFiber
  coverage_unit_bracket :=
    unitBracketProducer_of_branchWeightCoverageEveryEvenFiber
  coverage_confinement :=
    confinementResidualSplit_of_branchWeightCoverageEveryEvenFiber


end
end StandardModelConstraint
end SaturationMonoid
