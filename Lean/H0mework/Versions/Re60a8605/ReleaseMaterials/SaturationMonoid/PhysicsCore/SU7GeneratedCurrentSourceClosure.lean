import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.PhysicsCore.SU7PreHolonomyCurrentSourceBoundary

/-!
# Generated global current-source closure and active-sector repair steps

This module strengthens pointwise current-source completion to the existing
finite generated allowed-sector unit-successor law.  The law is still stated
entirely in native raw-code operations: bounded endpoint enumeration, Boolean
atomicity, the generated no-prime predicate, and raw residual energy.

The fiber `n = 3`, bound `3` is a nontrivial positive model.  Its Boolean-
atomic endpoints are `2,3`, and the generated energy chain closes as
`(2,2):2 -> (2,3):1 -> (3,3):0`.  At bound `2`, the exact same `(2,2)` source
cell has no energy-one repair, yielding a same-source closure-only boundary.

Global endpoint closure implies the corrected pointwise completion predicate:
zero energy is a legal terminal, while every positive current source obtains
an actual generated repair cell.  If the current source is in the canonical
active branch/incidence sector, that repair preserves both coordinates.

Boundary: this closes the finite generated raw-cell successor layer.  It does
not yet identify the repair step with a native A6/root/center-cover path or
prove confluence of all such repair choices.
-/

namespace SaturationMonoid
namespace PhysicsCore
namespace SU7GeneratedCurrentSourceClosure

open StandardModelConstraint
open SU7PreHolonomyCurrentSourceBoundary

noncomputable section

/-- Global unit-successor closure of the generated allowed raw-code sector. -/
def GeneratedSourceClosure (n sourceBound : Nat) : Prop :=
  BoolGaugeFilteredRawCodePairEnergyUnitSuccessorLaw
    n sourceBound (generatedNoPrimeAllowedPredicate n sourceBound)

/-- The current raw source lies in the canonical active Schubert branch. -/
def CurrentSourceBranchActive
    {n sourceBound sourceEnergy : Nat}
    (D : SU7PreHolonomyCurrentSourceDatum n sourceBound sourceEnergy) : Prop :=
  D.sourceCell.cell.branch = SU3FlagSchubertCell.e

/-- The current raw source lies in the canonical charged block-incidence
sector. -/
def CurrentSourceIncidenceActive
    {n sourceBound sourceEnergy : Nat}
    (D : SU7PreHolonomyCurrentSourceDatum n sourceBound sourceEnergy) : Prop :=
  D.sourceCell.cell.incidence =
    (.colorWeak : RunningSigmaBeta.SU7BlockIncidence)

/-- One generated one-unit current-source repair that also preserves the
current branch and incidence coordinates. -/
def GeneratedCurrentSourceStep
    {n sourceBound sourceEnergy : Nat}
    (D : SU7PreHolonomyCurrentSourceDatum n sourceBound sourceEnergy)
    (repair : SU7BooleanAtomicRawBranchingCell n) : Prop :=
  repair ∈
      gaugeFilteredBooleanAtomicRawBranchingCandidateList
        n sourceBound (generatedNoPrimeAllowedPredicate n sourceBound) ∧
    repair.cell.branch = D.sourceCell.cell.branch ∧
      repair.cell.incidence = D.sourceCell.cell.incidence ∧
        rawAtomCodeBranchingDecompositionResidualEnergy repair.cell + 1 =
          sourceEnergy

/-- Global generated closure retains every pre-holonomy current source and
produces its pointwise completion. -/
theorem generatedSourceClosure_implies_currentSourceCompleted
    {n sourceBound sourceEnergy : Nat}
    (D : SU7PreHolonomyCurrentSourceDatum n sourceBound sourceEnergy)
    (H : GeneratedSourceClosure n sourceBound) :
    GeneratedCurrentSourceCompleted D := by
  have hleft_mem :
      D.sourceCell.cell.leftWeightCode ∈ rawCodeBoundedList sourceBound :=
    booleanAtomicCell_left_mem_rawCodeBoundedList_of_mem_generated
      D.source_mem
  have hright_mem :
      D.sourceCell.cell.rightWeightCode ∈ rawCodeBoundedList sourceBound :=
    booleanAtomicCell_right_mem_rawCodeBoundedList_of_mem_generated
      D.source_mem
  have hallowed :
      generatedNoPrimeAllowedPredicate n sourceBound
          D.sourceCell.cell.leftWeightCode
          D.sourceCell.cell.rightWeightCode = true :=
    generatedNoPrimeAllowedPredicate_of_boundedAtomicRawCodePair
      hleft_mem hright_mem D.sourceCell.left_check D.sourceCell.right_check
  constructor
  · exact List.mem_filter.mpr ⟨D.source_mem, by simpa using hallowed⟩
  · by_cases hzero : sourceEnergy = 0
    · exact Or.inl hzero
    · have hpair_nonzero :
          rawCodePairResidualEnergy n
              D.sourceCell.cell.leftWeightCode
              D.sourceCell.cell.rightWeightCode ≠ 0 := by
        have hsource := D.source_energy
        rw [rawBranchingResidualEnergy_eq_codePair] at hsource
        rw [hsource]
        exact hzero
      rcases
          H D.sourceCell.cell.leftWeightCode
            D.sourceCell.cell.rightWeightCode
            hallowed hleft_mem hright_mem
            D.sourceCell.left_check D.sourceCell.right_check hpair_nonzero with
        ⟨left, right, hrepair_allowed, hleft, hright,
          hleft_check, hright_check, henergy⟩
      let repair :=
        booleanAtomicCellOfRawCodePair n left right
          hleft_check hright_check
      refine Or.inr ⟨repair, ?_, ?_⟩
      · dsimp [repair]
        exact booleanAtomicCellOfRawCodePair_mem_gaugeFiltered
          hrepair_allowed hleft hright hleft_check hright_check
      · dsimp [repair]
        rw [booleanAtomicCellOfRawCodePair_energy_eq]
        calc
          rawCodePairResidualEnergy n left right + 1 =
              rawCodePairResidualEnergy n
                D.sourceCell.cell.leftWeightCode
                D.sourceCell.cell.rightWeightCode := henergy
          _ = sourceEnergy := by
            rw [← rawBranchingResidualEnergy_eq_codePair]
            exact D.source_energy

/-- On the canonical active sector, global closure produces an actual repair
step preserving branch and incidence, not merely endpoint energy. -/
theorem generatedSourceClosure_produces_activeStep
    {n sourceBound sourceEnergy : Nat}
    (D : SU7PreHolonomyCurrentSourceDatum n sourceBound sourceEnergy)
    (H : GeneratedSourceClosure n sourceBound)
    (hpositive : sourceEnergy ≠ 0)
    (hbranch : CurrentSourceBranchActive D)
    (hincidence : CurrentSourceIncidenceActive D) :
    ∃ repair : SU7BooleanAtomicRawBranchingCell n,
      GeneratedCurrentSourceStep D repair := by
  have hleft_mem :
      D.sourceCell.cell.leftWeightCode ∈ rawCodeBoundedList sourceBound :=
    booleanAtomicCell_left_mem_rawCodeBoundedList_of_mem_generated
      D.source_mem
  have hright_mem :
      D.sourceCell.cell.rightWeightCode ∈ rawCodeBoundedList sourceBound :=
    booleanAtomicCell_right_mem_rawCodeBoundedList_of_mem_generated
      D.source_mem
  have hallowed :
      generatedNoPrimeAllowedPredicate n sourceBound
          D.sourceCell.cell.leftWeightCode
          D.sourceCell.cell.rightWeightCode = true :=
    generatedNoPrimeAllowedPredicate_of_boundedAtomicRawCodePair
      hleft_mem hright_mem D.sourceCell.left_check D.sourceCell.right_check
  have hpair_nonzero :
      rawCodePairResidualEnergy n
          D.sourceCell.cell.leftWeightCode
          D.sourceCell.cell.rightWeightCode ≠ 0 := by
    rw [← rawBranchingResidualEnergy_eq_codePair, D.source_energy]
    exact hpositive
  rcases
      H D.sourceCell.cell.leftWeightCode
        D.sourceCell.cell.rightWeightCode
        hallowed hleft_mem hright_mem
        D.sourceCell.left_check D.sourceCell.right_check hpair_nonzero with
    ⟨left, right, hrepair_allowed, hleft, hright,
      hleft_check, hright_check, henergy⟩
  let repair :=
    booleanAtomicCellOfRawCodePair n left right
      hleft_check hright_check
  refine ⟨repair, ?_, ?_, ?_, ?_⟩
  · dsimp [repair]
    exact booleanAtomicCellOfRawCodePair_mem_gaugeFiltered
      hrepair_allowed hleft hright hleft_check hright_check
  · simpa [repair, booleanAtomicCellOfRawCodePair,
      canonicalRawCodePairBranchingCell] using hbranch.symm
  · simpa [repair, booleanAtomicCellOfRawCodePair,
      canonicalRawCodePairBranchingCell] using hincidence.symm
  · dsimp [repair]
    rw [booleanAtomicCellOfRawCodePair_energy_eq]
    calc
      rawCodePairResidualEnergy n left right + 1 =
          rawCodePairResidualEnergy n
            D.sourceCell.cell.leftWeightCode
            D.sourceCell.cell.rightWeightCode := henergy
      _ = sourceEnergy := by
        rw [← rawBranchingResidualEnergy_eq_codePair]
        exact D.source_energy

/-! ## A nontrivial globally closed generated sector -/

theorem atomic_endpoint_cases_bound_three
    {value : Nat}
    (hmem : value ∈ rawCodeBoundedList 3)
    (hcheck : natMultiplicativelyAtomicCheck value = true) :
    value = 2 ∨ value = 3 := by
  have hle : value ≤ 3 := by
    have hlt : value < 4 := by
      simpa [rawCodeBoundedList] using hmem
    omega
  have htwo : 2 ≤ value := by
    by_contra hnot
    have hcases : value = 0 ∨ value = 1 := by omega
    rcases hcases with rfl | rfl <;>
      norm_num [natMultiplicativelyAtomicCheck,
        natHasNontrivialDivisorCheck] at hcheck
  omega

theorem generatedSourceClosure_three_three :
    GeneratedSourceClosure 3 3 := by
  intro left right _hallowed hleft_mem hright_mem
    hleft_check hright_check hnonzero
  have hleft_cases :=
    atomic_endpoint_cases_bound_three hleft_mem hleft_check
  have hright_cases :=
    atomic_endpoint_cases_bound_three hright_mem hright_check
  rcases hleft_cases with rfl | rfl <;>
    rcases hright_cases with rfl | rfl
  · refine ⟨2, 3, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · exact generatedNoPrimeAllowedPredicate_of_boundedAtomicRawCodePair
        (by norm_num [rawCodeBoundedList])
        (by norm_num [rawCodeBoundedList])
        natMultiplicativelyAtomicCheck_two
        natMultiplicativelyAtomicCheck_three
    · norm_num [rawCodeBoundedList]
    · norm_num [rawCodeBoundedList]
    · exact natMultiplicativelyAtomicCheck_two
    · exact natMultiplicativelyAtomicCheck_three
    · norm_num [rawCodePairResidualEnergy, rawCodePairResidual]
  · refine ⟨3, 3, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · exact generatedNoPrimeAllowedPredicate_three_three le_rfl
    · norm_num [rawCodeBoundedList]
    · norm_num [rawCodeBoundedList]
    · exact natMultiplicativelyAtomicCheck_three
    · exact natMultiplicativelyAtomicCheck_three
    · norm_num [rawCodePairResidualEnergy, rawCodePairResidual]
  · refine ⟨3, 3, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · exact generatedNoPrimeAllowedPredicate_three_three le_rfl
    · norm_num [rawCodeBoundedList]
    · norm_num [rawCodeBoundedList]
    · exact natMultiplicativelyAtomicCheck_three
    · exact natMultiplicativelyAtomicCheck_three
    · norm_num [rawCodePairResidualEnergy, rawCodePairResidual]
  · exact (hnonzero (by
      norm_num [rawCodePairResidualEnergy, rawCodePairResidual])).elim

/-- The endpoint closure lifts to actual generated Boolean-cell successor
dynamics through the canonical SU7 branch/incidence constructor. -/
theorem generatedBooleanAtomicSourceClosure_three_three :
    GaugeFilteredGeneratedBooleanAtomicUnitSuccessorLaw
      3 3 (generatedNoPrimeAllowedPredicate 3 3) :=
  gaugeFilteredBooleanAtomicLaw_of_rawCodePairLaw
    generatedSourceClosure_three_three

/-- The same closure reaches generated no-prime branching-cell dynamics. -/
theorem generatedNoPrimeCellSourceClosure_three_three :
    NoPrimeBranchingCellUnitSuccessorLaw
      (generatedNoPrimeBranchingCells 3 3) :=
  generatedNoPrimeCellUnitSuccessorLaw_of_rawCodePairUnitSuccessor
    generatedSourceClosure_three_three

/-- The `(2,2)` shell in any explicitly chosen branch/incidence sector of the
`n=3`, bound-three generated list.  This is used to test branch and incidence
as independent raw source coordinates without changing endpoints or energy. -/
def threeBoundThreeSourceDatumOfSector
    (branch : SU3FlagSchubertCell)
    (incidence : RunningSigmaBeta.SU7BlockIncidence) :
    SU7PreHolonomyCurrentSourceDatum 3 3 2 where
  sourceCell :=
    { cell :=
        { branch := branch
          incidence := incidence
          leftWeightCode := 2
          rightWeightCode := 2 }
      left_check := natMultiplicativelyAtomicCheck_two
      right_check := natMultiplicativelyAtomicCheck_two }
  source_mem := by
    unfold booleanAtomicRawBranchingCandidateList
    simp only [List.mem_filterMap]
    refine
      ⟨{ branch := branch
         incidence := incidence
         leftWeightCode := 2
         rightWeightCode := 2 }, ?_, ?_⟩
    · cases branch <;> cases incidence <;>
        simp [rawBranchingCandidateCells, rawCodeBoundedList,
          SU3FlagSchubertCell.all, SU7BlockIncidence.all]
    · simp [booleanAtomicCellOfCandidate?,
        natMultiplicativelyAtomicCheck_two]
  source_energy := by
    rw [rawBranchingResidualEnergy_eq_codePair]
    norm_num [rawCodePairResidualEnergy, rawCodePairResidual]

def threeBoundTwoSourceDatum :
    SU7PreHolonomyCurrentSourceDatum 3 2 2 where
  sourceCell :=
    booleanAtomicCellOfRawCodePair 3 2 2
      natMultiplicativelyAtomicCheck_two
      natMultiplicativelyAtomicCheck_two
  source_mem := by
    apply booleanAtomicCellOfRawCodePair_mem_generated
    · norm_num [rawCodeBoundedList]
    · norm_num [rawCodeBoundedList]
  source_energy := by
    rw [booleanAtomicCellOfRawCodePair_energy_eq]
    norm_num [rawCodePairResidualEnergy, rawCodePairResidual]

def threeBoundThreeSourceDatum :
    SU7PreHolonomyCurrentSourceDatum 3 3 2 :=
  threeBoundThreeSourceDatumOfSector .e .colorWeak

def threeBoundThreeBranchFailureDatum :
    SU7PreHolonomyCurrentSourceDatum 3 3 2 :=
  threeBoundThreeSourceDatumOfSector .s₁ .colorWeak

def threeBoundThreeIncidenceFailureDatum :
    SU7PreHolonomyCurrentSourceDatum 3 3 2 :=
  threeBoundThreeSourceDatumOfSector .e .colorPositiveSinglet

@[simp] theorem threeBoundThreeSourceDatum_branch_active :
    CurrentSourceBranchActive threeBoundThreeSourceDatum :=
  rfl

@[simp] theorem threeBoundThreeSourceDatum_incidence_active :
    CurrentSourceIncidenceActive threeBoundThreeSourceDatum :=
  rfl

@[simp] theorem threeBoundThreeBranchFailureDatum_not_branch_active :
    ¬ CurrentSourceBranchActive threeBoundThreeBranchFailureDatum := by
  intro h
  change SU3FlagSchubertCell.s₁ = SU3FlagSchubertCell.e at h
  cases h

@[simp] theorem threeBoundThreeBranchFailureDatum_incidence_active :
    CurrentSourceIncidenceActive threeBoundThreeBranchFailureDatum :=
  rfl

@[simp] theorem threeBoundThreeIncidenceFailureDatum_branch_active :
    CurrentSourceBranchActive threeBoundThreeIncidenceFailureDatum :=
  rfl

@[simp] theorem threeBoundThreeIncidenceFailureDatum_not_incidence_active :
    ¬ CurrentSourceIncidenceActive threeBoundThreeIncidenceFailureDatum := by
  intro h
  change
    RunningSigmaBeta.SU7BlockIncidence.colorPositiveSinglet =
      RunningSigmaBeta.SU7BlockIncidence.colorWeak at h
  cases h

theorem threeBoundCompletion_preserves_sourceCell :
    threeBoundTwoSourceDatum.sourceCell =
      threeBoundThreeSourceDatum.sourceCell :=
  rfl

theorem threeBoundThreeSourceDatum_completed :
    GeneratedCurrentSourceCompleted threeBoundThreeSourceDatum :=
  generatedSourceClosure_implies_currentSourceCompleted
    threeBoundThreeSourceDatum generatedSourceClosure_three_three

/-! ## Same-source global-closure boundary -/

theorem no_rawCodePairResidualEnergy_one_three_bound_two :
    ¬ ∃ left right : Nat,
      left ∈ rawCodeBoundedList 2 ∧
        right ∈ rawCodeBoundedList 2 ∧
          natMultiplicativelyAtomicCheck left = true ∧
            natMultiplicativelyAtomicCheck right = true ∧
              rawCodePairResidualEnergy 3 left right = 1 := by
  rintro ⟨left, right, hleft, hright,
    hleft_check, hright_check, henergy⟩
  simp [rawCodeBoundedList] at hleft hright
  interval_cases left <;> interval_cases right <;>
    norm_num [natMultiplicativelyAtomicCheck,
      natHasNontrivialDivisorCheck,
      rawCodePairResidualEnergy, rawCodePairResidual] at *

theorem not_generatedSourceClosure_three_two :
    ¬ GeneratedSourceClosure 3 2 := by
  intro H
  have hallowed :
      generatedNoPrimeAllowedPredicate 3 2 2 2 = true :=
    generatedNoPrimeAllowedPredicate_two_two le_rfl
  have hnonzero : rawCodePairResidualEnergy 3 2 2 ≠ 0 := by
    norm_num [rawCodePairResidualEnergy, rawCodePairResidual]
  rcases
      H 2 2 hallowed
        (by norm_num [rawCodeBoundedList])
        (by norm_num [rawCodeBoundedList])
        natMultiplicativelyAtomicCheck_two
        natMultiplicativelyAtomicCheck_two hnonzero with
    ⟨left, right, _hallowed, hleft, hright,
      hleft_check, hright_check, hunit⟩
  have henergy : rawCodePairResidualEnergy 3 left right = 1 := by
    have hsource : rawCodePairResidualEnergy 3 2 2 = 2 := by
      norm_num [rawCodePairResidualEnergy, rawCodePairResidual]
    rw [hsource] at hunit
    omega
  exact no_rawCodePairResidualEnergy_one_three_bound_two
    ⟨left, right, hleft, hright,
      hleft_check, hright_check, henergy⟩

/-- Exact source identity is unchanged while global closure changes. -/
theorem three_sameSource_globalClosure_separation :
    threeBoundTwoSourceDatum.sourceCell =
        threeBoundThreeSourceDatum.sourceCell ∧
      ¬ GeneratedSourceClosure 3 2 ∧
      GeneratedSourceClosure 3 3 :=
  ⟨threeBoundCompletion_preserves_sourceCell,
    not_generatedSourceClosure_three_two,
    generatedSourceClosure_three_three⟩

end
end SU7GeneratedCurrentSourceClosure
end PhysicsCore
end SaturationMonoid
