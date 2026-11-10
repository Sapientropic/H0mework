import H0mework.Versions.Re60a8605.ReleaseMaterials.RepresentationArithmeticAtomProjectionDefect.Lean.Positive.SU7GeneratedProjectionPositiveExtraction
import H0mework.Arithmetic.ShellSources.CheckedShellSource

/-!
# Pre-holonomy current SU7 source datum and the thin-datum boundary

`GeneratedRawEnergyShellRealized` already produces an explicit Boolean-atomic
SU7 source cell at one energy shell.  The existing
`SU7ThinSourceFeasibleDatum`, however, is strictly stronger: its
`SU7ProducedActiveCell` contains a canonical-rich witness, whose source lift
contains a generated P950 permanent-holonomy cell.

This module introduces the exact lower current-shell object that exists before
that upgrade.  It stores only the generated raw source cell and its affine
energy readout.  Lean proves that this datum is equivalent to pointwise raw
shell realization.

The completed P948 `(3,3)` source cell then gives a concrete separation: it is
a generated pre-holonomy source datum at bound `5`, but P950 is false for its
source pair because the same generated grammar contains the `(2,5)` one-unit
repair.  Therefore no universal conversion to `SU7ThinSourceFeasibleDatum`
can preserve the exact source pair.

The module then proves the stronger completed-source boundary: any generated
unit-successor or flow/quantization completion excludes every current thin
datum at the same fiber and bound, because that datum necessarily carries a
P950 terminal.  The correct completion target is therefore the pre-holonomy
current cell plus a legal zero-energy terminal or, on a positive shell, an
actual generated repair trace, not a P950/canonical-rich upgrade.  P948
supplies an exact-same-source positive/negative model: bound
`3` has no repair, while bound `5` retains the same `(3,3)` cell and generates
the `(2,5)` repair.
-/

namespace SaturationMonoid
namespace PhysicsCore
namespace SU7PreHolonomyCurrentSourceBoundary

open StandardModelConstraint
open RepresentationArithmeticAtomProjectionDefect
open SU7GeneratedProjectionPositiveExtraction

noncomputable section

/-- The exact current-shell source payload available below P950.  No
holonomy, canonical-rich witness, coverage certificate, endpoint projection,
normalizer, or repair witness is stored. -/
structure SU7PreHolonomyCurrentSourceDatum
    (n sourceBound sourceEnergy : Nat) where
  sourceCell : SU7BooleanAtomicRawBranchingCell n
  source_mem :
    sourceCell ∈ booleanAtomicRawBranchingCandidateList n sourceBound
  source_energy :
    rawAtomCodeBranchingDecompositionResidualEnergy sourceCell.cell =
      sourceEnergy

namespace SU7PreHolonomyCurrentSourceDatum

variable {n sourceBound sourceEnergy : Nat}

def sourcePair
    (D : SU7PreHolonomyCurrentSourceDatum n sourceBound sourceEnergy) :
    Nat × Nat :=
  (D.sourceCell.cell.leftWeightCode,
    D.sourceCell.cell.rightWeightCode)

theorem generatedRawEnergyShellRealized
    (D : SU7PreHolonomyCurrentSourceDatum n sourceBound sourceEnergy) :
    GeneratedRawEnergyShellRealized n sourceBound sourceEnergy :=
  ⟨D.sourceCell, D.source_mem, D.source_energy⟩

/-- A pointwise raw-shell witness produces exactly the pre-holonomy datum,
without strengthening it to an active/P950 cell. -/
def ofGeneratedRawEnergyShellRealized
    (H : GeneratedRawEnergyShellRealized n sourceBound sourceEnergy) :
    SU7PreHolonomyCurrentSourceDatum n sourceBound sourceEnergy where
  sourceCell := Classical.choose H
  source_mem := (Classical.choose_spec H).1
  source_energy := (Classical.choose_spec H).2

@[simp] theorem ofGeneratedRawEnergyShellRealized_sourceCell
    (H : GeneratedRawEnergyShellRealized n sourceBound sourceEnergy) :
    (ofGeneratedRawEnergyShellRealized H).sourceCell = Classical.choose H :=
  rfl

theorem generatedRawEnergyShellRealized_iff_nonempty :
    GeneratedRawEnergyShellRealized n sourceBound sourceEnergy ↔
      Nonempty
        (SU7PreHolonomyCurrentSourceDatum
          n sourceBound sourceEnergy) := by
  constructor
  · exact fun H => ⟨ofGeneratedRawEnergyShellRealized H⟩
  · rintro ⟨D⟩
    exact D.generatedRawEnergyShellRealized

/-- The source-pair readout carries exactly the stored raw shell energy. -/
theorem sourcePair_energy
    (D : SU7PreHolonomyCurrentSourceDatum n sourceBound sourceEnergy) :
    rawCodePairResidualEnergy n D.sourcePair.1 D.sourcePair.2 =
      sourceEnergy := by
  simpa [sourcePair, rawBranchingResidualEnergy_eq_codePair]
    using D.source_energy

end SU7PreHolonomyCurrentSourceDatum

/-! ## Completed-source versus P950-thin incompatibility -/

/-- Every current `SU7ThinSourceFeasibleDatum` still exposes a generated P950
permanent-holonomy witness.  This theorem is kept local to the lower source
boundary so downstream physics code does not need to import the observed-state
wrappers merely to audit the datum's actual type strength. -/
theorem thinSourceDatum_exposes_generatedP950
    {K : Type*} [Field K]
    {sigma : K} {hsigma : sigma ≠ 1}
    {n sourceBound sourceEnergy : Nat}
    (D :
      SU7ThinSourceFeasibleDatum
        sigma hsigma n sourceBound sourceEnergy) :
    Nonempty
      {p : Nat × Nat //
        BoolGaugeFilteredRawCodePairUnitPermanentHolonomyCell
          n sourceBound
          (generatedNoPrimeAllowedPredicate n sourceBound)
          p.1 p.2} :=
  ⟨⟨D.toProducedActiveCell.p,
    D.toProducedActiveCell.witness.source_lift.holonomy⟩⟩

/-- A generated allowed-sector unit-successor law is incompatible with the
current P950-bearing thin datum at the same fiber and bound.

This is a diagnostic no-go, not a producer premise: the successor law is used
to expose the carrier mismatch.  A completed source carrier must keep the raw
current source and its generated successor/repair trace without packaging a
permanent-holonomy witness that the same completion rules out. -/
theorem no_thinSourceDatum_of_generatedRawCodePairUnitSuccessor
    {K : Type*} [Field K]
    {sigma : K} {hsigma : sigma ≠ 1}
    {n sourceBound sourceEnergy : Nat}
    (Hsucc :
      BoolGaugeFilteredRawCodePairEnergyUnitSuccessorLaw
        n sourceBound
        (generatedNoPrimeAllowedPredicate n sourceBound)) :
    ¬ Nonempty
      (SU7ThinSourceFeasibleDatum
        sigma hsigma n sourceBound sourceEnergy) := by
  rintro ⟨D⟩
  exact
    (noGeneratedFilteredRawCodePairHolonomy_of_rawCodePairUnitSuccessor
      Hsucc)
      (thinSourceDatum_exposes_generatedP950 D)

/-- The concrete P962 flow/quantization source objects therefore cannot
coexist with a thin datum at the same generated source bound. -/
theorem no_thinSourceDatum_of_flow_and_quantizedBridge
    {K : Type*} [Field K]
    {sigma : K} {hsigma : sigma ≠ 1}
    {n sourceBound sourceEnergy : Nat}
    (F :
      NoPrimeBranchingConfiningResidualFlow
        (generatedNoPrimeBranchingCells n sourceBound))
    (Q :
      NoPrimeBranchingQuantizedUnitBridge
        (generatedNoPrimeBranchingCells n sourceBound)) :
    ¬ Nonempty
      (SU7ThinSourceFeasibleDatum
        sigma hsigma n sourceBound sourceEnergy) := by
  exact
    no_thinSourceDatum_of_generatedRawCodePairUnitSuccessor
      (generatedRawCodePairUnitSuccessor_of_flow_and_quantizedBridge F Q)

/-- Certificate-level form of the same boundary: a fully generated
flow/quantization completion and the current P950-bearing thin datum cannot
inhabit the same SU7 fiber/bound slice. -/
theorem no_thinSourceDatum_of_flowQuantizationCertificate
    {K : Type*} [Field K]
    {sigma : K} {hsigma : sigma ≠ 1}
    {n sourceEnergy : Nat}
    (G : SU7GeneratedNoPrimeFlowQuantizationCertificate n) :
    ¬ Nonempty
      (SU7ThinSourceFeasibleDatum
        sigma hsigma n G.codeBound sourceEnergy) := by
  exact
    no_thinSourceDatum_of_generatedRawCodePairUnitSuccessor
      (generatedRawCodePairUnitSuccessor_of_flowQuantizationCertificate G)

/-! ## Operations-only pointwise current-source completion -/

/-- Pointwise completion of one pre-holonomy current source, computed from the
generated filtered raw-cell list at the same fiber and bound.

The first conjunct keeps the exact current source cell in the filtered room.
The second conjunct accepts zero raw energy as a legal terminal; every
positive source instead requires an actual generated repair cell one
raw-energy unit below it.  No thin datum, P950 witness, coverage statement,
compatibility field, normalizer, endpoint projection, or final admissibility
proof is an input. -/
def GeneratedCurrentSourceCompleted
    {n sourceBound sourceEnergy : Nat}
    (D : SU7PreHolonomyCurrentSourceDatum n sourceBound sourceEnergy) : Prop :=
  D.sourceCell ∈
      gaugeFilteredBooleanAtomicRawBranchingCandidateList
        n sourceBound
        (generatedNoPrimeAllowedPredicate n sourceBound) ∧
    (sourceEnergy = 0 ∨
      ∃ repair : SU7BooleanAtomicRawBranchingCell n,
        repair ∈
            gaugeFilteredBooleanAtomicRawBranchingCandidateList
              n sourceBound
              (generatedNoPrimeAllowedPredicate n sourceBound) ∧
          rawAtomCodeBranchingDecompositionResidualEnergy repair.cell + 1 =
            sourceEnergy)

namespace GeneratedCurrentSourceCompleted

variable {n sourceBound sourceEnergy : Nat}
variable {D : SU7PreHolonomyCurrentSourceDatum n sourceBound sourceEnergy}

theorem source_mem
    (H : GeneratedCurrentSourceCompleted D) :
    D.sourceCell ∈
      gaugeFilteredBooleanAtomicRawBranchingCandidateList
        n sourceBound
        (generatedNoPrimeAllowedPredicate n sourceBound) :=
  H.1

theorem exists_unitRepair
    (H : GeneratedCurrentSourceCompleted D)
    (hpositive : sourceEnergy ≠ 0) :
    ∃ repair : SU7BooleanAtomicRawBranchingCell n,
      repair ∈
          gaugeFilteredBooleanAtomicRawBranchingCandidateList
            n sourceBound
            (generatedNoPrimeAllowedPredicate n sourceBound) ∧
        rawAtomCodeBranchingDecompositionResidualEnergy repair.cell + 1 =
          sourceEnergy :=
  H.2.resolve_left hpositive

/-- Pointwise generated completion rules out P950 for the exact source pair,
without asserting global coverage of every shell. -/
theorem not_p950_at_sourcePair
    (H : GeneratedCurrentSourceCompleted D) :
    ¬ BoolGaugeFilteredRawCodePairUnitPermanentHolonomyCell
      n sourceBound
      (generatedNoPrimeAllowedPredicate n sourceBound)
      D.sourcePair.1 D.sourcePair.2 := by
  rcases H.2 with hzero | ⟨repair, hrepair_mem, hrepair_energy⟩
  · intro hp
    rcases hp with
      ⟨_hallowed, _hleft, _hright, _hleftCheck, _hrightCheck,
        hnonzero, _hterminal⟩
    exact hnonzero (by rw [D.sourcePair_energy, hzero])
  · apply not_generatedNoPrimeP950_of_completedRepairWitness
    have hparts :
        repair ∈ booleanAtomicRawBranchingCandidateList n sourceBound ∧
          generatedNoPrimeAllowedPredicate n sourceBound
            repair.cell.leftWeightCode repair.cell.rightWeightCode = true := by
      simpa [gaugeFilteredBooleanAtomicRawBranchingCandidateList]
        using (List.mem_filter.mp hrepair_mem)
    refine
      ⟨repair.cell.leftWeightCode, repair.cell.rightWeightCode,
        hparts.2,
        booleanAtomicCell_left_mem_rawCodeBoundedList_of_mem_generated hparts.1,
        booleanAtomicCell_right_mem_rawCodeBoundedList_of_mem_generated hparts.1,
        repair.left_check, repair.right_check, ?_⟩
    calc
      rawCodePairResidualEnergy n
            repair.cell.leftWeightCode repair.cell.rightWeightCode + 1 =
          rawAtomCodeBranchingDecompositionResidualEnergy repair.cell + 1 := by
            rw [rawBranchingResidualEnergy_eq_codePair]
      _ = sourceEnergy := hrepair_energy
      _ = rawCodePairResidualEnergy n D.sourcePair.1 D.sourcePair.2 :=
        D.sourcePair_energy.symm

/-- A completed current source cannot be represented by a current thin datum
at the same exact source pair.  Any such representation would reintroduce the
P950 terminal that completion has just eliminated. -/
theorem no_sameSource_thinDatum
    {K : Type*} [Field K]
    {sigma : K} {hsigma : sigma ≠ 1}
    (H : GeneratedCurrentSourceCompleted D)
    (T :
      SU7ThinSourceFeasibleDatum
        sigma hsigma n sourceBound sourceEnergy)
    (hpair : T.toProducedActiveCell.p = D.sourcePair) :
    False := by
  have hp := T.toProducedActiveCell.witness.source_lift.holonomy
  rw [hpair] at hp
  exact H.not_p950_at_sourcePair hp

end GeneratedCurrentSourceCompleted

/-! ## Completed P948 source separation -/

/-- The original P948 boundary source before endpoint-room completion. -/
def p948BoundarySourceDatum :
    SU7PreHolonomyCurrentSourceDatum 6 3 6 where
  sourceCell :=
    booleanAtomicCellOfRawCodePair 6 3 3
      natMultiplicativelyAtomicCheck_three
      natMultiplicativelyAtomicCheck_three
  source_mem := by
    apply booleanAtomicCellOfRawCodePair_mem_generated
    · exact three_mem_rawCodeBoundedList_three
    · exact three_mem_rawCodeBoundedList_three
  source_energy := by
    rw [booleanAtomicCellOfRawCodePair_energy_eq,
      rawCodePairResidualEnergy_six_three_three]

@[simp] theorem p948BoundarySourceDatum_sourcePair :
    p948BoundarySourceDatum.sourcePair = (3, 3) := by
  simp [SU7PreHolonomyCurrentSourceDatum.sourcePair,
    p948BoundarySourceDatum, booleanAtomicCellOfRawCodePair,
    canonicalRawCodePairBranchingCell]

def p948CompletedSourceDatum :
    SU7PreHolonomyCurrentSourceDatum 6 5 6 where
  sourceCell :=
    booleanAtomicCellOfRawCodePair 6 3 3
      natMultiplicativelyAtomicCheck_three
      natMultiplicativelyAtomicCheck_three
  source_mem := by
    apply booleanAtomicCellOfRawCodePair_mem_generated
    · norm_num [rawCodeBoundedList]
    · norm_num [rawCodeBoundedList]
  source_energy := by
    rw [booleanAtomicCellOfRawCodePair_energy_eq,
      rawCodePairResidualEnergy_six_three_three]

@[simp] theorem p948CompletedSourceDatum_sourcePair :
    p948CompletedSourceDatum.sourcePair = (3, 3) := by
  simp [SU7PreHolonomyCurrentSourceDatum.sourcePair,
    p948CompletedSourceDatum, booleanAtomicCellOfRawCodePair,
    canonicalRawCodePairBranchingCell]

/-- Endpoint-room completion keeps the complete raw source cell, not merely
its two scalar endpoint codes. -/
theorem p948Completion_preserves_sourceCell :
    p948BoundarySourceDatum.sourceCell =
      p948CompletedSourceDatum.sourceCell :=
  rfl

theorem p948Completion_preserves_sourcePair :
    p948BoundarySourceDatum.sourcePair =
      p948CompletedSourceDatum.sourcePair := by
  rw [p948BoundarySourceDatum_sourcePair,
    p948CompletedSourceDatum_sourcePair]

/-- The bound-three P948 source has no generated one-unit repair cell in its
current filtered room. -/
theorem p948BoundarySourceDatum_not_completed :
    ¬ GeneratedCurrentSourceCompleted p948BoundarySourceDatum := by
  rintro ⟨_hsource, hzero | ⟨repair, hrepair_mem, hrepair_energy⟩⟩
  · norm_num at hzero
  have hparts :
      repair ∈ booleanAtomicRawBranchingCandidateList 6 3 ∧
        generatedNoPrimeAllowedPredicate 6 3
          repair.cell.leftWeightCode repair.cell.rightWeightCode = true := by
    simpa [gaugeFilteredBooleanAtomicRawBranchingCandidateList]
      using (List.mem_filter.mp hrepair_mem)
  have hrepair_pair_energy :
      rawCodePairResidualEnergy 6
        repair.cell.leftWeightCode repair.cell.rightWeightCode = 5 := by
    have hraw :
        rawAtomCodeBranchingDecompositionResidualEnergy repair.cell = 5 := by
      omega
    simpa [rawBranchingResidualEnergy_eq_codePair] using hraw
  exact no_rawCodePairResidualEnergy_five_six_bound_three
    ⟨repair.cell.leftWeightCode, repair.cell.rightWeightCode,
      booleanAtomicCell_left_mem_rawCodeBoundedList_of_mem_generated hparts.1,
      booleanAtomicCell_right_mem_rawCodeBoundedList_of_mem_generated hparts.1,
      repair.left_check, repair.right_check, hrepair_pair_energy⟩

/-- The same exact `(3,3)` source becomes pointwise completed at bound five:
the generated `(2,5)` Boolean source cell is its one-unit repair. -/
theorem p948CompletedSourceDatum_completed :
    GeneratedCurrentSourceCompleted p948CompletedSourceDatum := by
  constructor
  · exact
      booleanAtomicCellOfRawCodePair_mem_gaugeFiltered
        generatedNoPrimeBoundFive_preserves_three_three_from_bound_three
        (by norm_num [rawCodeBoundedList])
        (by norm_num [rawCodeBoundedList])
        natMultiplicativelyAtomicCheck_three
        natMultiplicativelyAtomicCheck_three
  · let repair :=
      booleanAtomicCellOfRawCodePair 6 2 5
        natMultiplicativelyAtomicCheck_two
        natMultiplicativelyAtomicCheck_five
    refine Or.inr ⟨repair, ?_, ?_⟩
    · dsimp [repair]
      exact
        booleanAtomicCellOfRawCodePair_mem_gaugeFiltered
          (generatedNoPrimeAllowedPredicate_two_five
            (n := 6) (bound := 5) le_rfl)
          (two_mem_rawCodeBoundedList (by norm_num))
          (five_mem_rawCodeBoundedList le_rfl)
          natMultiplicativelyAtomicCheck_two
          natMultiplicativelyAtomicCheck_five
    · dsimp [repair]
      rw [booleanAtomicCellOfRawCodePair_energy_eq,
        rawCodePairResidualEnergy_six_two_five]

/-- Only the generated completion room changes: the exact source cell is
preserved while pointwise repair availability changes from false to true. -/
theorem p948_sameSource_completion_separation :
    p948BoundarySourceDatum.sourceCell =
        p948CompletedSourceDatum.sourceCell ∧
      ¬ GeneratedCurrentSourceCompleted p948BoundarySourceDatum ∧
      GeneratedCurrentSourceCompleted p948CompletedSourceDatum :=
  ⟨p948Completion_preserves_sourceCell,
    p948BoundarySourceDatum_not_completed,
    p948CompletedSourceDatum_completed⟩

theorem p948CompletedSourceDatum_rawShell :
    GeneratedRawEnergyShellRealized 6 5 6 :=
  p948CompletedSourceDatum.generatedRawEnergyShellRealized

/-- The completed P948 source cannot be upgraded to a thin datum while
preserving its exact source pair.  A thin datum would expose the forbidden
P950 cell already stored in its canonical-rich source lift. -/
theorem no_sourcePairPreserving_thinSourceUpgrade
    {K : Type*} [Field K]
    {sigma : K} {hsigma : sigma ≠ 1}
    (upgrade :
      SU7PreHolonomyCurrentSourceDatum 6 5 6 →
        SU7ThinSourceFeasibleDatum sigma hsigma 6 5 6)
    (sourcePair_preserved :
      ∀ D,
        (upgrade D).toProducedActiveCell.p = D.sourcePair) :
    False := by
  let thin := upgrade p948CompletedSourceDatum
  have hpair : thin.toProducedActiveCell.p = (3, 3) := by
    exact (sourcePair_preserved p948CompletedSourceDatum).trans
      p948CompletedSourceDatum_sourcePair
  have hholonomy := thin.toProducedActiveCell.witness.source_lift.holonomy
  rw [hpair] at hholonomy
  exact not_generatedNoPrimeBoundFive_P950_three_three hholonomy

/-- Function-level contradiction form: there is no faithful universal
raw-shell-to-thin upgrade on this completed source slice. -/
theorem no_sourcePairPreserving_thinSourceUpgrade_exists
    {K : Type*} [Field K]
    {sigma : K} {hsigma : sigma ≠ 1} :
    ¬ ∃ upgrade :
        SU7PreHolonomyCurrentSourceDatum 6 5 6 →
          SU7ThinSourceFeasibleDatum sigma hsigma 6 5 6,
      ∀ D, (upgrade D).toProducedActiveCell.p = D.sourcePair := by
  rintro ⟨upgrade, hpreserved⟩
  exact no_sourcePairPreserving_thinSourceUpgrade upgrade hpreserved

end
end SU7PreHolonomyCurrentSourceBoundary
end PhysicsCore
end SaturationMonoid
