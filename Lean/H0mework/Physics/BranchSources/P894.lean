import H0mework.Physics.BranchSources.P893

/-!
# Proposition 894: physical family gaps are permanent holonomy

P893 lowered P884's transition system to a finite physical branch-family
confinement rule, but that rule still stated the successor law directly.

This file names the obstruction at that same level:

```text
gap = positive-weight nonzero residual cell with no lower-energy successor
```

and proves that this gap is exactly permanent physical color holonomy inside
the finite branch-spectrum family.  Therefore the successor law used by P893 is
not an extra operational field: it is equivalent to confinement forbidding
permanent holonomy.
-/

namespace SaturationMonoid
namespace StandardModelConstraint

noncomputable section

open SaturationMonoid.AffineRelaxation

set_option linter.defProp false

/-! ## Permanent holonomy inside a finite physical branch family -/

/-- A permanent physical branch-spectrum holonomy cell inside a finite family.

It is exactly a gap in residual transport: the cell is active in the family,
has nonzero physical residual, and no active family cell has strictly lower
physical residual energy. -/
def SU7PhysicalBranchingSpectrumPermanentHolonomyCell
    {n : ℕ} (F : SU7PhysicalBranchingSpectrumFamily n)
    (C : SU7PhysicalBranchingSpectrumCell n) : Prop :=
  C ∈ F.spectrumCells ∧
    0 < F.representationWeight C ∧
      physicalBranchingSpectrumResidual C ≠ 0 ∧
        ∀ next : SU7PhysicalBranchingSpectrumCell n,
          next ∈ F.spectrumCells ->
            0 < F.representationWeight next ->
              ¬ physicalBranchingSpectrumResidualEnergy next <
                physicalBranchingSpectrumResidualEnergy C

/-- A finite physical branch-spectrum family forbids permanent holonomy. -/
def SU7PhysicalBranchingSpectrumFamilyForbidsPermanentHolonomy
    {n : ℕ} (F : SU7PhysicalBranchingSpectrumFamily n) : Prop :=
  ∀ C : SU7PhysicalBranchingSpectrumCell n,
    ¬ SU7PhysicalBranchingSpectrumPermanentHolonomyCell F C

/-- The explicit successor law on a finite physical branch-spectrum family. -/
def SU7PhysicalBranchingSpectrumFamilySuccessorLaw
    {n : ℕ} (F : SU7PhysicalBranchingSpectrumFamily n) : Prop :=
  ∀ C : SU7PhysicalBranchingSpectrumCell n,
    C ∈ F.spectrumCells ->
      0 < F.representationWeight C ->
        physicalBranchingSpectrumResidual C ≠ 0 ->
          ∃ next : SU7PhysicalBranchingSpectrumCell n,
            next ∈ F.spectrumCells ∧
              0 < F.representationWeight next ∧
                physicalBranchingSpectrumResidualEnergy next <
                  physicalBranchingSpectrumResidualEnergy C

/-- THEOREM 1: forbidding permanent physical branch-spectrum holonomy is
exactly the successor law used by P893. -/
theorem noPhysicalFamilyPermanentHolonomy_iff_successorLaw
    {n : ℕ} (F : SU7PhysicalBranchingSpectrumFamily n) :
    SU7PhysicalBranchingSpectrumFamilyForbidsPermanentHolonomy F ↔
      SU7PhysicalBranchingSpectrumFamilySuccessorLaw F := by
  constructor
  · intro H C hmem hwt hnonzero
    by_contra hnone
    have hterminal :
        ∀ next : SU7PhysicalBranchingSpectrumCell n,
          next ∈ F.spectrumCells ->
            0 < F.representationWeight next ->
              ¬ physicalBranchingSpectrumResidualEnergy next <
                physicalBranchingSpectrumResidualEnergy C := by
      intro next hnext_mem hnext_wt hlt
      exact hnone ⟨next, hnext_mem, hnext_wt, hlt⟩
    exact H C ⟨hmem, hwt, hnonzero, hterminal⟩
  · intro H C hperm
    rcases hperm with ⟨hmem, hwt, hnonzero, hterminal⟩
    rcases H C hmem hwt hnonzero with
      ⟨next, hnext_mem, hnext_wt, hnext_lt⟩
    exact hterminal next hnext_mem hnext_wt hnext_lt

/-- THEOREM 2: a nonzero residual active cell with no active lower-energy
successor is a permanent-holonomy cell. -/
theorem permanentHolonomyCell_of_no_lower_successor
    {n : ℕ} {F : SU7PhysicalBranchingSpectrumFamily n}
    {C : SU7PhysicalBranchingSpectrumCell n}
    (hmem : C ∈ F.spectrumCells)
    (hwt : 0 < F.representationWeight C)
    (hnonzero : physicalBranchingSpectrumResidual C ≠ 0)
    (hterminal :
      ∀ next : SU7PhysicalBranchingSpectrumCell n,
        next ∈ F.spectrumCells ->
          0 < F.representationWeight next ->
            ¬ physicalBranchingSpectrumResidualEnergy next <
              physicalBranchingSpectrumResidualEnergy C) :
    SU7PhysicalBranchingSpectrumPermanentHolonomyCell F C :=
  ⟨hmem, hwt, hnonzero, hterminal⟩

/-- THEOREM 3: absence of permanent holonomy extracts an active lower-energy
successor for every active nonzero-residual cell. -/
theorem successor_of_noPhysicalFamilyPermanentHolonomy
    {n : ℕ} {F : SU7PhysicalBranchingSpectrumFamily n}
    (H : SU7PhysicalBranchingSpectrumFamilyForbidsPermanentHolonomy F)
    (C : SU7PhysicalBranchingSpectrumCell n)
    (hmem : C ∈ F.spectrumCells)
    (hwt : 0 < F.representationWeight C)
    (hnonzero : physicalBranchingSpectrumResidual C ≠ 0) :
    ∃ next : SU7PhysicalBranchingSpectrumCell n,
      next ∈ F.spectrumCells ∧
        0 < F.representationWeight next ∧
          physicalBranchingSpectrumResidualEnergy next <
            physicalBranchingSpectrumResidualEnergy C :=
  (noPhysicalFamilyPermanentHolonomy_iff_successorLaw F).mp H
    C hmem hwt hnonzero

/-! ## Holonomy-form confinement rules generate P893 rules -/

/-- A physical branch-family confinement rule stated as holonomy elimination,
not as a successor law. -/
structure SU7PhysicalBranchingSpectrumHolonomyConfinementRule (n : ℕ) where
  family : SU7PhysicalBranchingSpectrumFamily n
  startCell : SU7PhysicalBranchingSpectrumCell n
  start_mem : startCell ∈ family.spectrumCells
  start_weight_positive : 0 < family.representationWeight startCell
  forbids_permanent_holonomy :
    SU7PhysicalBranchingSpectrumFamilyForbidsPermanentHolonomy family

/-- THEOREM 4: a holonomy-form rule generates P893's successor-form
confinement rule. -/
def physicalConfinementRule_of_holonomyConfinementRule
    {n : ℕ} (R : SU7PhysicalBranchingSpectrumHolonomyConfinementRule n) :
    SU7PhysicalBranchingSpectrumConfinementRule n where
  family := R.family
  startCell := R.startCell
  start_mem := R.start_mem
  start_weight_positive := R.start_weight_positive
  no_permanent_physical_holonomy := by
    intro C hmem hwt hnonzero
    exact successor_of_noPhysicalFamilyPermanentHolonomy
      R.forbids_permanent_holonomy C hmem hwt hnonzero

/-- THEOREM 5: a holonomy-form rule generates P884's transition system. -/
def physicalTransitionSystem_of_holonomyConfinementRule
    {n : ℕ} (R : SU7PhysicalBranchingSpectrumHolonomyConfinementRule n) :
    SU7PhysicalBranchingSpectrumTransitionSystem n :=
  physicalTransitionSystem_of_confinementRule
    (physicalConfinementRule_of_holonomyConfinementRule R)

/-- THEOREM 6: a holonomy-form rule generates a zero physical residual cell.
-/
theorem exists_zeroCell_of_holonomyConfinementRule
    {n : ℕ} (R : SU7PhysicalBranchingSpectrumHolonomyConfinementRule n) :
    ∃ Z : SU7PhysicalBranchingSpectrumCell n,
      Z ∈ R.family.spectrumCells ∧
        0 < R.family.representationWeight Z ∧
          physicalBranchingSpectrumResidual Z = 0 :=
  exists_zeroCell_of_physicalConfinementRule
    (physicalConfinementRule_of_holonomyConfinementRule R)

/-- THEOREM 7: a holonomy-form rule computes a trace-zero prime-edge loop. -/
def traceZeroPrimeEdgeLoop_of_holonomyConfinementRule
    {n : ℕ} (R : SU7PhysicalBranchingSpectrumHolonomyConfinementRule n) :
    TraceZeroPrimeEdgeLoop n :=
  traceZeroPrimeEdgeLoop_of_physicalConfinementRule
    (physicalConfinementRule_of_holonomyConfinementRule R)

/-! ## Fiberwise holonomy confinement -/

/-- Every even fiber carries a holonomy-form physical confinement rule. -/
def SU7PhysicalBranchingSpectrumHolonomyConfinementRuleEveryEvenFiber : Prop :=
  ∀ n : ℕ, 2 ≤ n ->
    Nonempty (SU7PhysicalBranchingSpectrumHolonomyConfinementRule n)

/-- THEOREM 8: fiberwise holonomy-form rules generate P893's successor-form
rules on every even fiber. -/
theorem confinementRuleEveryEvenFiber_of_holonomyRules
    (H : SU7PhysicalBranchingSpectrumHolonomyConfinementRuleEveryEvenFiber) :
    SU7PhysicalBranchingSpectrumConfinementRuleEveryEvenFiber := by
  intro n hn
  let R : SU7PhysicalBranchingSpectrumHolonomyConfinementRule n :=
    Classical.choice (H n hn)
  exact ⟨physicalConfinementRule_of_holonomyConfinementRule R⟩

/-- Physical holonomy confinement data: the physical law names plus
holonomy-form rules on every even fiber. -/
structure SU7PhysicalHolonomyBranchRuleConfinement where
  compact_gauge_orbit : SU7CompactGaugeOrbit
  lyapunov_residual_dissipation : SU7LyapunovResidualDissipation
  quantized_spectrum_no_escaping_boundary :
    SU7QuantizedSpectrumNoEscapingBoundary
  holonomy_rules :
    SU7PhysicalBranchingSpectrumHolonomyConfinementRuleEveryEvenFiber

/-- THEOREM 9: holonomy-form branch confinement generates P893 branch-rule
confinement. -/
def branchRuleConfinement_of_holonomyBranchRuleConfinement
    (D : SU7PhysicalHolonomyBranchRuleConfinement) :
    SU7PhysicalBranchRuleConfinement where
  compact_gauge_orbit := D.compact_gauge_orbit
  lyapunov_residual_dissipation := D.lyapunov_residual_dissipation
  quantized_spectrum_no_escaping_boundary :=
    D.quantized_spectrum_no_escaping_boundary
  confinement_rules :=
    confinementRuleEveryEvenFiber_of_holonomyRules D.holonomy_rules

/-- THEOREM 10: holonomy-form branch confinement computes trace-zero loops on
every even fiber. -/
def traceZeroPrimeEdgeLoopEveryEvenFiber_of_holonomyBranchRuleConfinement
    (D : SU7PhysicalHolonomyBranchRuleConfinement) :
    ∀ n : ℕ, 2 ≤ n -> TraceZeroPrimeEdgeLoop n :=
  traceZeroPrimeEdgeLoopEveryEvenFiber_of_branchRuleConfinement
    (branchRuleConfinement_of_holonomyBranchRuleConfinement D)

/-- THEOREM 11: holonomy-form branch confinement gives ordinary even Goldbach
through the P894 -> P893 -> P884 -> P892 route. -/
theorem evenGoldbach_of_physicalHolonomyBranchRuleConfinement
    (D : SU7PhysicalHolonomyBranchRuleConfinement) :
    EvenGoldbachStatement :=
  evenGoldbach_of_physicalBranchRuleConfinement
    (branchRuleConfinement_of_holonomyBranchRuleConfinement D)

/-! ## Certificate -/

/-- P894 certificate: at the finite physical branch-family level, a gap is
exactly permanent holonomy, and forbidding it generates the successor law used
by P893. -/
structure SU7PhysicalHolonomyGapProducerCertificate where
  no_gap_iff_successor :
    ∀ {n : ℕ} (F : SU7PhysicalBranchingSpectrumFamily n),
      SU7PhysicalBranchingSpectrumFamilyForbidsPermanentHolonomy F ↔
        SU7PhysicalBranchingSpectrumFamilySuccessorLaw F
  no_lower_successor_is_holonomy :
    ∀ {n : ℕ} {F : SU7PhysicalBranchingSpectrumFamily n}
      {C : SU7PhysicalBranchingSpectrumCell n},
      C ∈ F.spectrumCells ->
        0 < F.representationWeight C ->
          physicalBranchingSpectrumResidual C ≠ 0 ->
            (∀ next : SU7PhysicalBranchingSpectrumCell n,
              next ∈ F.spectrumCells ->
                0 < F.representationWeight next ->
                  ¬ physicalBranchingSpectrumResidualEnergy next <
                    physicalBranchingSpectrumResidualEnergy C) ->
              SU7PhysicalBranchingSpectrumPermanentHolonomyCell F C
  holonomy_rule_to_confinement_rule :
    ∀ {n : ℕ},
      SU7PhysicalBranchingSpectrumHolonomyConfinementRule n ->
        SU7PhysicalBranchingSpectrumConfinementRule n
  holonomy_rule_to_transition :
    ∀ {n : ℕ},
      SU7PhysicalBranchingSpectrumHolonomyConfinementRule n ->
        SU7PhysicalBranchingSpectrumTransitionSystem n
  holonomy_rule_to_zero_cell :
    ∀ {n : ℕ} (R : SU7PhysicalBranchingSpectrumHolonomyConfinementRule n),
      ∃ Z : SU7PhysicalBranchingSpectrumCell n,
        Z ∈ R.family.spectrumCells ∧
          0 < R.family.representationWeight Z ∧
            physicalBranchingSpectrumResidual Z = 0
  holonomy_rule_to_trace_zero :
    ∀ {n : ℕ},
      SU7PhysicalBranchingSpectrumHolonomyConfinementRule n ->
        TraceZeroPrimeEdgeLoop n
  holonomy_confinement_to_goldbach :
    SU7PhysicalHolonomyBranchRuleConfinement -> EvenGoldbachStatement

def su7PhysicalHolonomyGapProducerCertificate :
    SU7PhysicalHolonomyGapProducerCertificate where
  no_gap_iff_successor :=
    noPhysicalFamilyPermanentHolonomy_iff_successorLaw
  no_lower_successor_is_holonomy :=
    permanentHolonomyCell_of_no_lower_successor
  holonomy_rule_to_confinement_rule :=
    physicalConfinementRule_of_holonomyConfinementRule
  holonomy_rule_to_transition :=
    physicalTransitionSystem_of_holonomyConfinementRule
  holonomy_rule_to_zero_cell :=
    exists_zeroCell_of_holonomyConfinementRule
  holonomy_rule_to_trace_zero :=
    traceZeroPrimeEdgeLoop_of_holonomyConfinementRule
  holonomy_confinement_to_goldbach :=
    evenGoldbach_of_physicalHolonomyBranchRuleConfinement


end
end StandardModelConstraint
end SaturationMonoid
