import H0mework.Physics.ColorLoops.P859

/-!
# Proposition 860: branch-cell producer for SU(7) prime-edge zero fibers

P849 stored trace-zero cells directly.  P850 moved the input to computed
topology, but its realization map still returned a `TraceZeroPrimeEdgeLoop`.

This file pushes the producer one layer lower.  A branch certificate stores:

* Schubert branch cells of the color orbit;
* prime-edge labels carried by those cells;
* the branch weight `p + q`;
* a selected branch whose weight equals the even-fiber target `2n`.

Only after that weight equality is checked do we compute a
`TraceZeroPrimeEdgeLoop n`.  Thus the zero fiber is no longer an assumed cell;
it is the image of branch weights under the prime-edge realization law.
-/

namespace SaturationMonoid
namespace StandardModelConstraint

noncomputable section

open SaturationMonoid.AffineRelaxation
open SaturationMonoid.ComplexityProjection

set_option linter.defProp false

/-! ## Branch cells and weights -/

/-- One SU(7) / color-orbit branch cell over the even fiber `2n`.

The cell stores only its Schubert branch label and its two prime-edge labels.
It does not store a `TraceZeroPrimeEdgeLoop`. -/
structure SU7PrimeEdgeBranchCell (n : ℕ) where
  branch : SU3FlagSchubertCell
  leftPrime : PrimeExponent
  rightPrime : PrimeExponent

namespace SU7PrimeEdgeBranchCell

/-- The branch weight read from the prime-edge realization. -/
def branchWeight {n : ℕ} (B : SU7PrimeEdgeBranchCell n) : ℕ :=
  B.leftPrime.1 + B.rightPrime.1

/-- The target weight of the even fiber `2n`. -/
def evenFiberWeight (n : ℕ) : ℕ :=
  2 * n

/-- The branch is trace-neutral exactly when its prime-edge weight hits the
even-fiber target. -/
def traceNeutral {n : ℕ} (B : SU7PrimeEdgeBranchCell n) : Prop :=
  B.branchWeight = evenFiberWeight n

/-- The prime-edge matrix carried by the branch cell. -/
def matrix {n : ℕ} (B : SU7PrimeEdgeBranchCell n) : ColorLoopField :=
  primeEdgeColorLoopMatrix n B.leftPrime B.rightPrime

end SU7PrimeEdgeBranchCell

/-! ## From branch weights to trace-zero loops -/

/-- THEOREM 1: a trace-neutral branch cell computes a trace-zero prime-edge
loop.  The trace-zero object is produced here; it is not stored in the
certificate. -/
def traceZeroPrimeEdgeLoop_of_branchWeight
    {n : ℕ} (B : SU7PrimeEdgeBranchCell n)
    (hB : B.traceNeutral) :
    TraceZeroPrimeEdgeLoop n where
  leftPrime := B.leftPrime
  rightPrime := B.rightPrime
  trace_zero :=
    (primeEdgeColorLoop_trace_zero_iff n B.leftPrime B.rightPrime).mpr
      hB.symm

/-- THEOREM 2: the computed trace-zero loop preserves the left prime edge. -/
theorem traceZeroPrimeEdgeLoop_of_branchWeight_left
    {n : ℕ} (B : SU7PrimeEdgeBranchCell n) (hB : B.traceNeutral) :
    (traceZeroPrimeEdgeLoop_of_branchWeight B hB).leftPrime =
      B.leftPrime := rfl

/-- THEOREM 3: the computed trace-zero loop preserves the right prime edge. -/
theorem traceZeroPrimeEdgeLoop_of_branchWeight_right
    {n : ℕ} (B : SU7PrimeEdgeBranchCell n) (hB : B.traceNeutral) :
    (traceZeroPrimeEdgeLoop_of_branchWeight B hB).rightPrime =
      B.rightPrime := rfl

/-- THEOREM 4: the computed loop really lands in the trace-zero fiber. -/
theorem traceZeroPrimeEdgeLoop_of_branchWeight_trace_zero
    {n : ℕ} (B : SU7PrimeEdgeBranchCell n) (hB : B.traceNeutral) :
    ColorLoopTraceExact (B.matrix) := by
  exact (traceZeroPrimeEdgeLoop_of_branchWeight B hB).trace_zero

/-- THEOREM 5: a trace-neutral branch cell computes a SU(7)-allowed
prime-edge loop. -/
def su7AllowedPrimeEdgeLoop_of_branchWeight
    {n : ℕ} (B : SU7PrimeEdgeBranchCell n)
    (hB : B.traceNeutral) :
    SU7AllowedPrimeEdgeLoop n :=
  su7AllowedPrimeEdgeLoopOfTraceZero
    (traceZeroPrimeEdgeLoop_of_branchWeight B hB)

/-! ## Branching certificate -/

/-- A branch-cell certificate for the even fiber `2n`.

The certificate stores a finite branch-cell family and selects one branch
whose computed prime-edge weight equals `2n`.  It intentionally does not store
`TraceZeroPrimeEdgeLoop n`; the trace-zero loop is computed by
`traceZeroPrimeEdgeLoop_of_branchingCertificate`. -/
structure SU7PrimeEdgeBranchingCertificate (n : ℕ) where
  branchCells : List (SU7PrimeEdgeBranchCell n)
  selected : SU7PrimeEdgeBranchCell n
  selected_mem : selected ∈ branchCells
  selected_traceNeutral : selected.traceNeutral

/-- THEOREM 6: a branch certificate computes its trace-zero prime-edge loop. -/
def traceZeroPrimeEdgeLoop_of_branchingCertificate
    {n : ℕ} (C : SU7PrimeEdgeBranchingCertificate n) :
    TraceZeroPrimeEdgeLoop n :=
  traceZeroPrimeEdgeLoop_of_branchWeight
    C.selected C.selected_traceNeutral

/-- THEOREM 7: a branch certificate computes its SU(7)-allowed loop. -/
def su7AllowedPrimeEdgeLoop_of_branchingCertificate
    {n : ℕ} (C : SU7PrimeEdgeBranchingCertificate n) :
    SU7AllowedPrimeEdgeLoop n :=
  su7AllowedPrimeEdgeLoop_of_branchWeight
    C.selected C.selected_traceNeutral

/-- THEOREM 8: the branch certificate produces a SU(7)-filtered fiber point. -/
theorem filteredFiber_of_branchingCertificate
    {n : ℕ} (C : SU7PrimeEdgeBranchingCertificate n) :
    SU7FilteredTraceSpectrumFiber n := by
  refine ⟨C.selected.leftPrime, C.selected.rightPrime, ?_⟩
  exact (su7AllowedPrimeEdgeLoop_of_branchingCertificate C).allowed

/-- THEOREM 9: the branch certificate rules out a trace-spectrum gap on its
fiber. -/
theorem noTraceSpectrumGap_of_branchingCertificate
    {n : ℕ} (C : SU7PrimeEdgeBranchingCertificate n) :
    ¬ PrimeEdgeTraceSpectrumGap n := by
  intro hgap
  exact (primeEdgeTraceSpectrumGap_iff_no_su7FilteredFiber n).mp hgap
    (filteredFiber_of_branchingCertificate C)

/-- THEOREM 10: the branch certificate computes a dynamical fixed-point
witness on its fiber. -/
theorem fixedPoint_of_branchingCertificate
    {n : ℕ} (C : SU7PrimeEdgeBranchingCertificate n) :
    goldbachDynamicalFixedPoint (2 * n)
      (C.selected.leftPrime, C.selected.rightPrime) := by
  have hsum :
      2 * n = C.selected.leftPrime.1 + C.selected.rightPrime.1 :=
    C.selected_traceNeutral.symm
  exact (goldbachDynamicalFixedPoint_iff_sum
    (2 * n) (C.selected.leftPrime, C.selected.rightPrime)).mpr hsum

/-- THEOREM 11: the branch certificate computes zero Hamiltonian energy on
its fiber. -/
theorem zeroEnergy_of_branchingCertificate
    {n : ℕ} (C : SU7PrimeEdgeBranchingCertificate n) :
    hamiltonianEnergyReadout
      (goldbachEnergyState (2 * n)
        (C.selected.leftPrime, C.selected.rightPrime)) = 0 := by
  exact (goldbachDynamicalFixedPoint_iff_zeroEnergy
    (2 * n) (C.selected.leftPrime, C.selected.rightPrime)).mp
      (fixedPoint_of_branchingCertificate C)

/-! ## Fiberwise branch certificates give the global producer -/

/-- Every even fiber has a branch-cell certificate. -/
def SU7PrimeEdgeBranchingEveryEvenFiber : Prop :=
  ∀ n : ℕ, 2 ≤ n -> Nonempty (SU7PrimeEdgeBranchingCertificate n)

/-- THEOREM 12: fiberwise branch certificates produce no-gap. -/
theorem traceSpectrumNoGap_of_branchingEveryEvenFiber
    (H : SU7PrimeEdgeBranchingEveryEvenFiber) :
    PrimeEdgeTraceSpectrumNoGap := by
  intro n hn
  exact filteredFiber_of_branchingCertificate
    (Classical.choice (H n hn))

/-- THEOREM 13: fiberwise branch certificates produce the SU(7)-filtered
prime-edge loop producer. -/
theorem su7FilteredProducer_of_branchingEveryEvenFiber
    (H : SU7PrimeEdgeBranchingEveryEvenFiber) :
    SU7FilteredPrimeEdgeLoopProducer := by
  exact traceSpectrumNoGap_of_branchingEveryEvenFiber H

/-- THEOREM 14: fiberwise branch certificates forbid permanent color
holonomy. -/
theorem noPermanentColorHolonomy_of_branchingEveryEvenFiber
    (H : SU7PrimeEdgeBranchingEveryEvenFiber) :
    ¬ PermanentPrimeEdgeColorHolonomy :=
  (noPermanentPrimeEdgeColorHolonomy_iff_su7FilteredProducer).mpr
    (su7FilteredProducer_of_branchingEveryEvenFiber H)

/-- THEOREM 15: fiberwise branch certificates produce the unit bracket. -/
theorem unitBracketProducer_of_branchingEveryEvenFiber
    (H : SU7PrimeEdgeBranchingEveryEvenFiber) :
    ColorLoopTraceUnitBracketProducer :=
  (su7FilteredPrimeEdgeLoopProducer_iff_unitBracketProducer).mp
    (su7FilteredProducer_of_branchingEveryEvenFiber H)

/-- THEOREM 16: fiberwise branch certificates produce the fixed-point
producer. -/
theorem fixedPointProducer_of_branchingEveryEvenFiber
    (H : SU7PrimeEdgeBranchingEveryEvenFiber) :
    Nonempty EvenGoldbachDynamicalFixedPointProducer :=
  (su7FilteredPrimeEdgeLoopProducer_iff_fixedPointProducer).mp
    (su7FilteredProducer_of_branchingEveryEvenFiber H)

/-- THEOREM 17: fiberwise branch certificates construct the gauge-flow
trace-zero normalizer, with normal form computed from branch weights. -/
def gaugeFlowTraceZeroNormalizer_of_branchingEveryEvenFiber
    (H : SU7PrimeEdgeBranchingEveryEvenFiber) :
    SU7GaugeFlowTraceZeroNormalizer where
  normalForm := fun n hn =>
    traceZeroPrimeEdgeLoop_of_branchingCertificate
      (Classical.choice (H n hn))

/-- THEOREM 18: branch certificates give the residual-split confinement
throat through the gauge-flow producer. -/
theorem confinementResidualSplit_of_branchingEveryEvenFiber
    (H : SU7PrimeEdgeBranchingEveryEvenFiber) :
    SU7ConfinementResidualSplitLaw :=
  (gaugeFlowTraceZeroProducer_iff_confinementResidualSplitLaw).mp
    ⟨gaugeFlowTraceZeroNormalizer_of_branchingEveryEvenFiber H⟩

/-! ## Certificate -/

/-- P860 certificate: the hard producer target is branch-cell data, and all
trace-zero / no-gap / unit-bracket readouts are computed from branch weights. -/
structure SU7PrimeEdgeBranchingProducerCertificate where
  branch_to_trace_zero :
    ∀ {n : ℕ} (B : SU7PrimeEdgeBranchCell n),
      B.traceNeutral -> TraceZeroPrimeEdgeLoop n
  branch_to_su7_allowed :
    ∀ {n : ℕ} (B : SU7PrimeEdgeBranchCell n),
      B.traceNeutral -> SU7AllowedPrimeEdgeLoop n
  certificate_to_filtered_fiber :
    ∀ {n : ℕ}, SU7PrimeEdgeBranchingCertificate n ->
      SU7FilteredTraceSpectrumFiber n
  certificate_no_gap :
    ∀ {n : ℕ}, SU7PrimeEdgeBranchingCertificate n ->
      ¬ PrimeEdgeTraceSpectrumGap n
  certificate_fixed_point :
    ∀ {n : ℕ} (C : SU7PrimeEdgeBranchingCertificate n),
      goldbachDynamicalFixedPoint (2 * n)
        (C.selected.leftPrime, C.selected.rightPrime)
  certificate_zero_energy :
    ∀ {n : ℕ} (C : SU7PrimeEdgeBranchingCertificate n),
      hamiltonianEnergyReadout
        (goldbachEnergyState (2 * n)
          (C.selected.leftPrime, C.selected.rightPrime)) = 0
  every_fiber_no_gap :
    SU7PrimeEdgeBranchingEveryEvenFiber -> PrimeEdgeTraceSpectrumNoGap
  every_fiber_unit_bracket :
    SU7PrimeEdgeBranchingEveryEvenFiber -> ColorLoopTraceUnitBracketProducer
  every_fiber_fixed_point :
    SU7PrimeEdgeBranchingEveryEvenFiber ->
      Nonempty EvenGoldbachDynamicalFixedPointProducer
  every_fiber_confinement :
    SU7PrimeEdgeBranchingEveryEvenFiber ->
      SU7ConfinementResidualSplitLaw

def su7PrimeEdgeBranchingProducerCertificate :
    SU7PrimeEdgeBranchingProducerCertificate where
  branch_to_trace_zero := traceZeroPrimeEdgeLoop_of_branchWeight
  branch_to_su7_allowed := su7AllowedPrimeEdgeLoop_of_branchWeight
  certificate_to_filtered_fiber := filteredFiber_of_branchingCertificate
  certificate_no_gap := noTraceSpectrumGap_of_branchingCertificate
  certificate_fixed_point := fixedPoint_of_branchingCertificate
  certificate_zero_energy := zeroEnergy_of_branchingCertificate
  every_fiber_no_gap := traceSpectrumNoGap_of_branchingEveryEvenFiber
  every_fiber_unit_bracket := unitBracketProducer_of_branchingEveryEvenFiber
  every_fiber_fixed_point := fixedPointProducer_of_branchingEveryEvenFiber
  every_fiber_confinement := confinementResidualSplit_of_branchingEveryEvenFiber


end
end StandardModelConstraint
end SaturationMonoid
