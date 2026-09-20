import H0mework.Arithmetic.PrimeShadow.P892

/-!
# Proposition 893: physical confinement rules generate transition systems

P884 used a `SU7PhysicalBranchingSpectrumTransitionSystem` as the producer
object: it stored a step relation plus preservation and descent fields.  That
was already below prime-edge storage, but the step relation was still a
transition-system primitive.

This file lowers that primitive to a physical confinement rule on a finite
branch-spectrum family.  The rule contains:

* one finite physical branch-spectrum family;
* a positive-weight start cell;
* the no-permanent-holonomy successor law inside that family.

The actual transition relation is then canonical:

```lean
next is a step from C iff
  next is in the same family
  and next has positive representation weight
  and next has strictly lower physical residual energy.
```

So P884's transition system is generated from the branch family and the
confinement successor law; the transition relation is no longer a free field.
-/

namespace SaturationMonoid
namespace StandardModelConstraint

noncomputable section

open SaturationMonoid.AffineRelaxation

set_option linter.defProp false

/-! ## Confinement rules below transition-system storage -/

/-- A physical confinement rule on one even fiber.

This is lower than P884's transition system: it stores no arbitrary `step`
relation.  It states only that every positive-weight nonzero-residual cell has
some positive-weight lower-energy successor inside the same finite family. -/
structure SU7PhysicalBranchingSpectrumConfinementRule (n : ℕ) where
  family : SU7PhysicalBranchingSpectrumFamily n
  startCell : SU7PhysicalBranchingSpectrumCell n
  start_mem : startCell ∈ family.spectrumCells
  start_weight_positive : 0 < family.representationWeight startCell
  no_permanent_physical_holonomy :
    ∀ C : SU7PhysicalBranchingSpectrumCell n,
      C ∈ family.spectrumCells ->
        0 < family.representationWeight C ->
          physicalBranchingSpectrumResidual C ≠ 0 ->
            ∃ next : SU7PhysicalBranchingSpectrumCell n,
              next ∈ family.spectrumCells ∧
                0 < family.representationWeight next ∧
                  physicalBranchingSpectrumResidualEnergy next <
                    physicalBranchingSpectrumResidualEnergy C

/-- Canonical physical successor relation induced by a confinement rule. -/
def physicalConfinementStep
    {n : ℕ} (R : SU7PhysicalBranchingSpectrumConfinementRule n)
    (C next : SU7PhysicalBranchingSpectrumCell n) : Prop :=
  next ∈ R.family.spectrumCells ∧
    0 < R.family.representationWeight next ∧
      physicalBranchingSpectrumResidualEnergy next <
        physicalBranchingSpectrumResidualEnergy C

/-- THEOREM 1: the canonical physical confinement step preserves family
membership. -/
theorem physicalConfinementStep_mem_preserves
    {n : ℕ} (R : SU7PhysicalBranchingSpectrumConfinementRule n)
    (C next : SU7PhysicalBranchingSpectrumCell n)
    (_hmem : C ∈ R.family.spectrumCells)
    (_hwt : 0 < R.family.representationWeight C)
    (hstep : physicalConfinementStep R C next) :
    next ∈ R.family.spectrumCells :=
  hstep.1

/-- THEOREM 2: the canonical physical confinement step preserves positive
representation weight. -/
theorem physicalConfinementStep_weight_positive_preserves
    {n : ℕ} (R : SU7PhysicalBranchingSpectrumConfinementRule n)
    (C next : SU7PhysicalBranchingSpectrumCell n)
    (_hmem : C ∈ R.family.spectrumCells)
    (_hwt : 0 < R.family.representationWeight C)
    (hstep : physicalConfinementStep R C next) :
    0 < R.family.representationWeight next :=
  hstep.2.1

/-- THEOREM 3: the canonical physical confinement step strictly decreases
physical residual energy. -/
theorem physicalConfinementStep_strictly_decreases_energy
    {n : ℕ} (R : SU7PhysicalBranchingSpectrumConfinementRule n)
    (C next : SU7PhysicalBranchingSpectrumCell n)
    (_hmem : C ∈ R.family.spectrumCells)
    (_hwt : 0 < R.family.representationWeight C)
    (hstep : physicalConfinementStep R C next) :
    physicalBranchingSpectrumResidualEnergy next <
      physicalBranchingSpectrumResidualEnergy C :=
  hstep.2.2

/-- THEOREM 4: the no-permanent-holonomy law supplies a canonical successor
for every nonzero residual cell. -/
theorem physicalConfinementStep_no_terminal_nonzero
    {n : ℕ} (R : SU7PhysicalBranchingSpectrumConfinementRule n)
    (C : SU7PhysicalBranchingSpectrumCell n)
    (hmem : C ∈ R.family.spectrumCells)
    (hwt : 0 < R.family.representationWeight C)
    (hnonzero : physicalBranchingSpectrumResidual C ≠ 0) :
    ∃ next : SU7PhysicalBranchingSpectrumCell n,
      physicalConfinementStep R C next := by
  rcases R.no_permanent_physical_holonomy C hmem hwt hnonzero with
    ⟨next, hnext_mem, hnext_wt, hnext_lt⟩
  exact ⟨next, hnext_mem, hnext_wt, hnext_lt⟩

/-! ## Generated P884 transition systems -/

/-- THEOREM 5: a physical confinement rule generates P884's transition system.

The `step` relation is definitionally the lower-energy successor relation, not
a stored primitive. -/
def physicalTransitionSystem_of_confinementRule
    {n : ℕ} (R : SU7PhysicalBranchingSpectrumConfinementRule n) :
    SU7PhysicalBranchingSpectrumTransitionSystem n where
  family := R.family
  startCell := R.startCell
  start_mem := R.start_mem
  start_weight_positive := R.start_weight_positive
  step := physicalConfinementStep R
  step_mem_preserves :=
    physicalConfinementStep_mem_preserves R
  step_weight_positive_preserves :=
    physicalConfinementStep_weight_positive_preserves R
  step_strictly_decreases_energy :=
    physicalConfinementStep_strictly_decreases_energy R
  no_terminal_nonzero :=
    physicalConfinementStep_no_terminal_nonzero R

/-- THEOREM 6: the generated transition system produces a positive-weight
zero-residual physical branch-spectrum cell. -/
theorem exists_zeroCell_of_physicalConfinementRule
    {n : ℕ} (R : SU7PhysicalBranchingSpectrumConfinementRule n) :
    ∃ Z : SU7PhysicalBranchingSpectrumCell n,
      Z ∈ R.family.spectrumCells ∧
        0 < R.family.representationWeight Z ∧
          physicalBranchingSpectrumResidual Z = 0 :=
  exists_zeroCell_of_physicalTransitionSystem
    (physicalTransitionSystem_of_confinementRule R)

/-- THEOREM 7: a physical confinement rule computes a trace-zero prime-edge
loop through P892's non-storing projection. -/
def traceZeroPrimeEdgeLoop_of_physicalConfinementRule
    {n : ℕ} (R : SU7PhysicalBranchingSpectrumConfinementRule n) :
    TraceZeroPrimeEdgeLoop n :=
  traceZeroPrimeEdgeLoop_of_physicalTransitionSystem
    (physicalTransitionSystem_of_confinementRule R)

/-! ## Fiberwise confinement rules -/

/-- Every even fiber carries a physical confinement rule. -/
def SU7PhysicalBranchingSpectrumConfinementRuleEveryEvenFiber : Prop :=
  ∀ n : ℕ, 2 ≤ n ->
    Nonempty (SU7PhysicalBranchingSpectrumConfinementRule n)

/-- THEOREM 8: fiberwise physical confinement rules generate P884 transition
systems on every even fiber. -/
theorem transitionSystemEveryEvenFiber_of_confinementRules
    (H : SU7PhysicalBranchingSpectrumConfinementRuleEveryEvenFiber) :
    SU7PhysicalBranchingSpectrumTransitionSystemEveryEvenFiber := by
  intro n hn
  rcases H n hn with ⟨R⟩
  exact ⟨physicalTransitionSystem_of_confinementRule R⟩

/-- Physical branch-rule confinement data: the physical law names plus a
finite branch-family no-permanent-holonomy rule on every even fiber. -/
structure SU7PhysicalBranchRuleConfinement where
  compact_gauge_orbit : SU7CompactGaugeOrbit
  lyapunov_residual_dissipation : SU7LyapunovResidualDissipation
  quantized_spectrum_no_escaping_boundary :
    SU7QuantizedSpectrumNoEscapingBoundary
  confinement_rules :
    SU7PhysicalBranchingSpectrumConfinementRuleEveryEvenFiber

/-- THEOREM 9: physical branch-rule confinement generates P884's transition
confinement object. -/
def physicalTransitionConfinement_of_branchRuleConfinement
    (D : SU7PhysicalBranchRuleConfinement) :
    SU7PhysicalBranchingSpectrumTransitionConfinement where
  compact_gauge_orbit := D.compact_gauge_orbit
  lyapunov_residual_dissipation := D.lyapunov_residual_dissipation
  quantized_spectrum_no_escaping_boundary :=
    D.quantized_spectrum_no_escaping_boundary
  transition_systems :=
    transitionSystemEveryEvenFiber_of_confinementRules D.confinement_rules

/-- THEOREM 10: physical branch-rule confinement gives the prime-coded support
confinement route. -/
def primeCodedSpectrumSupportConfinement_of_branchRuleConfinement
    (D : SU7PhysicalBranchRuleConfinement) :
    SU7PrimeCodedSpectrumSupportConfinement :=
  primeCodedSpectrumSupportConfinement_of_physicalTransitions
    (physicalTransitionConfinement_of_branchRuleConfinement D)

/-- THEOREM 11: physical branch-rule confinement gives the trace-zero
prime-edge loop on every even fiber. -/
def traceZeroPrimeEdgeLoopEveryEvenFiber_of_branchRuleConfinement
    (D : SU7PhysicalBranchRuleConfinement) :
    ∀ n : ℕ, 2 ≤ n -> TraceZeroPrimeEdgeLoop n := by
  intro n hn
  let R : SU7PhysicalBranchingSpectrumConfinementRule n :=
    Classical.choice (D.confinement_rules n hn)
  exact traceZeroPrimeEdgeLoop_of_physicalConfinementRule R

/-- THEOREM 12: physical branch-rule confinement gives ordinary even Goldbach
through the P884/P892 projection chain. -/
theorem evenGoldbach_of_physicalBranchRuleConfinement
    (D : SU7PhysicalBranchRuleConfinement) :
    EvenGoldbachStatement :=
  evenGoldbach_of_physicalBranchingSpectrumTransitionConfinement
    (physicalTransitionConfinement_of_branchRuleConfinement D)

/-! ## Certificate -/

/-- P893 certificate: a finite physical branch-family confinement rule
generates P884's transition systems; `step` is canonical lower-energy
transport, not an input transition relation. -/
structure SU7PhysicalBranchRuleConfinementProducerCertificate where
  step_mem :
    ∀ {n : ℕ} (R : SU7PhysicalBranchingSpectrumConfinementRule n)
      (C next : SU7PhysicalBranchingSpectrumCell n),
      C ∈ R.family.spectrumCells ->
        0 < R.family.representationWeight C ->
          physicalConfinementStep R C next ->
            next ∈ R.family.spectrumCells
  step_weight :
    ∀ {n : ℕ} (R : SU7PhysicalBranchingSpectrumConfinementRule n)
      (C next : SU7PhysicalBranchingSpectrumCell n),
      C ∈ R.family.spectrumCells ->
        0 < R.family.representationWeight C ->
          physicalConfinementStep R C next ->
            0 < R.family.representationWeight next
  step_energy :
    ∀ {n : ℕ} (R : SU7PhysicalBranchingSpectrumConfinementRule n)
      (C next : SU7PhysicalBranchingSpectrumCell n),
      C ∈ R.family.spectrumCells ->
        0 < R.family.representationWeight C ->
          physicalConfinementStep R C next ->
            physicalBranchingSpectrumResidualEnergy next <
              physicalBranchingSpectrumResidualEnergy C
  rule_to_transition :
    ∀ {n : ℕ}, SU7PhysicalBranchingSpectrumConfinementRule n ->
      SU7PhysicalBranchingSpectrumTransitionSystem n
  rule_to_zero_cell :
    ∀ {n : ℕ} (R : SU7PhysicalBranchingSpectrumConfinementRule n),
      ∃ Z : SU7PhysicalBranchingSpectrumCell n,
        Z ∈ R.family.spectrumCells ∧
          0 < R.family.representationWeight Z ∧
            physicalBranchingSpectrumResidual Z = 0
  rule_to_trace_zero :
    ∀ {n : ℕ}, SU7PhysicalBranchingSpectrumConfinementRule n ->
      TraceZeroPrimeEdgeLoop n
  branch_rule_to_support :
    SU7PhysicalBranchRuleConfinement ->
      SU7PrimeCodedSpectrumSupportConfinement
  branch_rule_to_goldbach :
    SU7PhysicalBranchRuleConfinement -> EvenGoldbachStatement

def su7PhysicalBranchRuleConfinementProducerCertificate :
    SU7PhysicalBranchRuleConfinementProducerCertificate where
  step_mem := physicalConfinementStep_mem_preserves
  step_weight := physicalConfinementStep_weight_positive_preserves
  step_energy := physicalConfinementStep_strictly_decreases_energy
  rule_to_transition := physicalTransitionSystem_of_confinementRule
  rule_to_zero_cell := exists_zeroCell_of_physicalConfinementRule
  rule_to_trace_zero := traceZeroPrimeEdgeLoop_of_physicalConfinementRule
  branch_rule_to_support :=
    primeCodedSpectrumSupportConfinement_of_branchRuleConfinement
  branch_rule_to_goldbach := evenGoldbach_of_physicalBranchRuleConfinement


end
end StandardModelConstraint
end SaturationMonoid
