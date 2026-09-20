import H0mework.Arithmetic.ShellSources.P900
import H0mework.Physics.ColorLoops.P850

/-!
# Proposition 901: prime-index pullback generates bounded shells

P900 made the finite-spectrum target precise: a bounded SU(7)
branching-decomposition energy shell generates the normalizer and therefore
the no-permanent-holonomy spine.

This file connects that shell target back to the computed trace-zero topology
route.  The missing bridge is the prime-index pullback:

```text
prime edge p
-> weight code count Nat.Prime p
-> Nat.nth Nat.Prime (count Nat.Prime p) = p
```

Thus a realized trace-zero prime-edge loop can be pulled back into a
branching-decomposition cell whose raw fields are only Schubert/incidence/weight
codes.  The pulled-back cell has zero decomposition residual, so it forms a
zero-energy bounded shell.  Composed with P850, computed orbit topology now
feeds the P900 bounded-shell spine rather than bypassing it.
-/

namespace SaturationMonoid
namespace StandardModelConstraint

noncomputable section

open SaturationMonoid.AffineRelaxation
open RunningSigmaBeta

set_option linter.defProp false

/-! ## Prime-index pullback into SU(7) weight codes -/

/-- The canonical SU(7) raw weight-code of a prime edge: its index in the
increasing Mathlib enumeration of primes. -/
def weightCodeOfPrimeEdge (p : PrimeExponent) : ℕ :=
  Nat.count Nat.Prime p.1

/-- THEOREM 1: reading the pulled-back weight code through the P879
prime-coded readout returns the original prime edge. -/
theorem su7PrimeCodeOfWeight_weightCodeOfPrimeEdge
    (p : PrimeExponent) :
    su7PrimeCodeOfWeight { code := weightCodeOfPrimeEdge p } = p.1 := by
  unfold su7PrimeCodeOfWeight weightCodeOfPrimeEdge
  exact Nat.nth_count p.2

/-- THEOREM 2: the physical atom readout of a pulled-back prime edge returns
that prime edge. -/
theorem su7PhysicalAtomCode_of_primeEdgePullback
    (p : PrimeExponent) (block : SU7CarrierBlock) :
    su7PhysicalAtomCode
        (su7AtomOfBranchingEndpoint
          (weightCodeOfPrimeEdge p) block) = p.1 := by
  unfold su7PhysicalAtomCode su7PrimeCodedAtomCode
    su7AtomOfBranchingEndpoint
  exact su7PrimeCodeOfWeight_weightCodeOfPrimeEdge p

/-! ## Pulling trace-zero loops back to decomposition cells -/

/-- A trace-zero prime-edge loop pulled back into a raw SU(7)
branching-decomposition cell.

The cell stores no `Nat.Prime` proof and no `PrimeExponent`.  It stores only:
Schubert branch label, SU(7) incidence, and the two prime-index weight codes.
-/
def branchingDecompositionCell_of_traceZeroPrimeEdgeLoop
    {n : ℕ} (Z : TraceZeroPrimeEdgeLoop n) :
    SU7BranchingDecompositionCell n where
  branch := SU3FlagSchubertCell.e
  incidence := SU7BlockIncidence.colorWeak
  leftWeightCode := weightCodeOfPrimeEdge Z.leftPrime
  rightWeightCode := weightCodeOfPrimeEdge Z.rightPrime

/-- THEOREM 3: the pulled-back decomposition cell has zero decomposition
residual. -/
theorem branchingDecompositionResidual_of_traceZeroPrimeEdgeLoop_eq_zero
    {n : ℕ} (Z : TraceZeroPrimeEdgeLoop n) :
    branchingDecompositionResidual
      (branchingDecompositionCell_of_traceZeroPrimeEdgeLoop Z) = 0 := by
  have hsum :
      2 * n = Z.leftPrime.1 + Z.rightPrime.1 :=
    (primeEdgeColorLoop_trace_zero_iff n Z.leftPrime Z.rightPrime).mp
      Z.trace_zero
  unfold branchingDecompositionResidual
    physicalBranchingSpectrumResidual
    physicalBranchingSpectrumCell_of_representationSupportSlot
    representationSupportSlot_of_branchingDecompositionCell
    leftAtomOfBranchingDecompositionCell
    rightAtomOfBranchingDecompositionCell
    colorLoopOfBranchingDecompositionCell
    branchingDecompositionCell_of_traceZeroPrimeEdgeLoop
  simp [SU7BlockIncidence.endpoints,
    su7PhysicalAtomCode_of_primeEdgePullback,
    hsum]

/-- THEOREM 4: the pulled-back cell has zero residual energy. -/
theorem branchingDecompositionResidualEnergy_of_traceZeroPrimeEdgeLoop_eq_zero
    {n : ℕ} (Z : TraceZeroPrimeEdgeLoop n) :
    branchingDecompositionResidualEnergy
      (branchingDecompositionCell_of_traceZeroPrimeEdgeLoop Z) = 0 := by
  unfold branchingDecompositionResidualEnergy
  rw [branchingDecompositionResidual_of_traceZeroPrimeEdgeLoop_eq_zero Z]
  rfl

/-! ## Zero-energy bounded shells generated from trace-zero loops -/

/-- A trace-zero prime-edge loop generates a zero-energy bounded SU(7)
branching shell.  The shell contains the pulled-back decomposition cell only;
its maximum active energy is `0`.

The impossible predecessor branches are discharged by `omega`: there is no
positive `e ≤ 0`. -/
def branchingBoundedEnergyShell_of_traceZeroPrimeEdgeLoop
    {n : ℕ} (Z : TraceZeroPrimeEdgeLoop n) :
    SU7BranchingBoundedEnergyShell n where
  spectrum :=
    { cells := [branchingDecompositionCell_of_traceZeroPrimeEdgeLoop Z] }
  startCell := branchingDecompositionCell_of_traceZeroPrimeEdgeLoop Z
  start_mem := by simp
  maxEnergy := 0
  energy_bound := by
    intro C hmem
    simp at hmem
    subst C
    rw [branchingDecompositionResidualEnergy_of_traceZeroPrimeEdgeLoop_eq_zero Z]
  lowerEnergyCell := by
    intro e hpos hle
    omega
  lowerEnergyCell_mem := by
    intro e hpos hle
    omega
  lowerEnergyCell_energy_eq_pred := by
    intro e hpos hle
    omega

/-- THEOREM 5: the zero-energy shell generated from a trace-zero loop has the
expected fixed-point law through P900. -/
theorem traceZeroPrimeEdgeLoop_shell_fixed_iff_residual_zero
    {n : ℕ} (Z : TraceZeroPrimeEdgeLoop n)
    (C : SU7BranchingDecompositionCell n)
    (hmem :
      C ∈
        (branchingBoundedEnergyShell_of_traceZeroPrimeEdgeLoop
          Z).spectrum.cells) :
    branchingBoundedEnergyShellNormalize
        (branchingBoundedEnergyShell_of_traceZeroPrimeEdgeLoop Z) C = C ↔
      branchingDecompositionResidual C = 0 :=
  branchingBoundedEnergyShell_fixed_iff_residual_zero
    (branchingBoundedEnergyShell_of_traceZeroPrimeEdgeLoop Z) C hmem

/-! ## Computed orbit topology feeds the P900 bounded-shell spine -/

/-- THEOREM 6: a computed orbit-topology obstruction generates a bounded
branching energy shell. -/
def branchingBoundedEnergyShell_of_computedOrbitTopology
    {n : ℕ} (H : ColorLoopComputedOrbitTopologicalObstruction n) :
    SU7BranchingBoundedEnergyShell n :=
  branchingBoundedEnergyShell_of_traceZeroPrimeEdgeLoop
    (traceZeroPrimeEdgeLoop_of_computedOrbitTopology H)

/-- THEOREM 7: fiberwise computed orbit topology generates bounded energy
shells on every even fiber. -/
theorem boundedEnergyShellsEveryEvenFiber_of_computedOrbitTopology
    (H : ColorLoopComputedOrbitTopologyEveryEvenFiber) :
    SU7BranchingBoundedEnergyShellEveryEvenFiber := by
  intro n hn
  exact ⟨branchingBoundedEnergyShell_of_computedOrbitTopology
    (Classical.choice (H n hn))⟩

/-- Computed-topology confinement data, now routed through P900's bounded
energy shells. -/
structure SU7ComputedOrbitBoundedShellConfinement where
  compact_gauge_orbit : SU7CompactGaugeOrbit
  lyapunov_residual_dissipation : SU7LyapunovResidualDissipation
  quantized_spectrum_no_escaping_boundary :
    SU7QuantizedSpectrumNoEscapingBoundary
  incidence_schedule_no_free :
    RunningSigmaBeta.SU7IncidenceScheduleNoFreeCertificate
  computed_orbit_topology : ColorLoopComputedOrbitTopologyEveryEvenFiber

/-- THEOREM 8: computed orbit topology generates P900 bounded-shell
confinement. -/
def branchingBoundedEnergyShellConfinement_of_computedOrbitTopology
    (D : SU7ComputedOrbitBoundedShellConfinement) :
    SU7BranchingBoundedEnergyShellConfinement where
  compact_gauge_orbit := D.compact_gauge_orbit
  lyapunov_residual_dissipation := D.lyapunov_residual_dissipation
  quantized_spectrum_no_escaping_boundary :=
    D.quantized_spectrum_no_escaping_boundary
  incidence_schedule_no_free := D.incidence_schedule_no_free
  bounded_energy_shells :=
    boundedEnergyShellsEveryEvenFiber_of_computedOrbitTopology
      D.computed_orbit_topology

/-- THEOREM 9: computed orbit topology reaches ordinary even Goldbach through
the bounded-shell spine. -/
theorem evenGoldbach_of_computedOrbitBoundedShellConfinement
    (D : SU7ComputedOrbitBoundedShellConfinement) :
    EvenGoldbachStatement :=
  evenGoldbach_of_branchingBoundedEnergyShellConfinement
    (branchingBoundedEnergyShellConfinement_of_computedOrbitTopology D)

/-! ## Certificate -/

/-- P901 certificate: prime-index pullback converts computed trace-zero
topology into P900 finite bounded shells. -/
structure SU7PrimeIndexPullbackBoundedShellCertificate where
  prime_edge_weight_code_readout :
    ∀ p : PrimeExponent,
      su7PrimeCodeOfWeight { code := weightCodeOfPrimeEdge p } = p.1
  trace_zero_to_decomposition_cell :
    ∀ {n : ℕ}, TraceZeroPrimeEdgeLoop n ->
      SU7BranchingDecompositionCell n
  trace_zero_pullback_residual_zero :
    ∀ {n : ℕ} (Z : TraceZeroPrimeEdgeLoop n),
      branchingDecompositionResidual
        (branchingDecompositionCell_of_traceZeroPrimeEdgeLoop Z) = 0
  trace_zero_to_bounded_shell :
    ∀ {n : ℕ}, TraceZeroPrimeEdgeLoop n ->
      SU7BranchingBoundedEnergyShell n
  computed_topology_to_bounded_shells :
    ColorLoopComputedOrbitTopologyEveryEvenFiber ->
      SU7BranchingBoundedEnergyShellEveryEvenFiber
  computed_topology_confinement_to_goldbach :
    SU7ComputedOrbitBoundedShellConfinement -> EvenGoldbachStatement

def su7PrimeIndexPullbackBoundedShellCertificate :
    SU7PrimeIndexPullbackBoundedShellCertificate where
  prime_edge_weight_code_readout :=
    su7PrimeCodeOfWeight_weightCodeOfPrimeEdge
  trace_zero_to_decomposition_cell :=
    branchingDecompositionCell_of_traceZeroPrimeEdgeLoop
  trace_zero_pullback_residual_zero :=
    branchingDecompositionResidual_of_traceZeroPrimeEdgeLoop_eq_zero
  trace_zero_to_bounded_shell :=
    branchingBoundedEnergyShell_of_traceZeroPrimeEdgeLoop
  computed_topology_to_bounded_shells :=
    boundedEnergyShellsEveryEvenFiber_of_computedOrbitTopology
  computed_topology_confinement_to_goldbach :=
    evenGoldbach_of_computedOrbitBoundedShellConfinement


end
end StandardModelConstraint
end SaturationMonoid
