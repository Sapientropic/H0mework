import H0mework.Arithmetic.CodePairs.P944

/-!
# Proposition 945: the finite generated spectrum supplies its own top cell

P944 reduced generated coverage to:

```text
top residual cell at generated maxEnergy
+ unit permanent holonomy forbidden
```

This file removes the top cell as a supplied field.  Since `maxEnergy` is
computed from the finite generated spectrum list, any nonempty generated
spectrum contains a cell attaining that maximum.

The remaining producer datum is now:

```text
generated spectrum nonempty
+ unit permanent holonomy forbidden
```

No prime pair, trace-zero loop, coverage Bool, active-gap support, or top cell
is stored.
-/

namespace SaturationMonoid
namespace StandardModelConstraint

noncomputable section

open SaturationMonoid.AffineRelaxation
open RunningSigmaBeta

set_option linter.defProp false

/-! ## Max-energy attainment in finite raw cell lists -/

/-- A nonempty finite raw branch-cell list contains a cell attaining the
recursive maximum residual energy of the list. -/
theorem exists_mem_energy_eq_maxRawResidualEnergyOfCells_of_ne_nil
    {n : ℕ} :
    ∀ xs : List (SU7BranchingDecompositionCell n),
      xs ≠ [] ->
        ∃ c : SU7BranchingDecompositionCell n,
          c ∈ xs ∧
            rawAtomCodeBranchingDecompositionResidualEnergy c =
              maxRawResidualEnergyOfCells xs := by
  intro xs
  induction xs with
  | nil =>
      intro hne
      exact False.elim (hne rfl)
  | cons x xs ih =>
      intro _hne
      by_cases htail : xs = []
      · subst xs
        refine ⟨x, ?_, ?_⟩
        · simp
        · simp [maxRawResidualEnergyOfCells]
      · rcases ih htail with ⟨c, hmem, henergy⟩
        by_cases hle :
            maxRawResidualEnergyOfCells xs ≤
              rawAtomCodeBranchingDecompositionResidualEnergy x
        · refine ⟨x, ?_, ?_⟩
          · simp
          · simp [maxRawResidualEnergyOfCells, max_eq_left hle]
        · have hright :
              rawAtomCodeBranchingDecompositionResidualEnergy x ≤
                maxRawResidualEnergyOfCells xs := by
            exact Nat.le_of_lt (Nat.lt_of_not_ge hle)
          refine ⟨c, ?_, ?_⟩
          · simp [hmem]
          · simp [maxRawResidualEnergyOfCells, max_eq_right hright,
              henergy]

/-- A nonempty generated raw branching spectrum contains a cell at its computed
max energy. -/
theorem exists_topCell_of_booleanGeneratedRawBranchingSpectrum_nonempty
    {n bound : ℕ}
    (hne : (booleanGeneratedRawBranchingSpectrum n bound).cells ≠ []) :
    ∃ c : SU7BranchingDecompositionCell n,
      c ∈ (booleanGeneratedRawBranchingSpectrum n bound).cells ∧
        rawAtomCodeBranchingDecompositionResidualEnergy c =
          generatedRawBranchingMaxEnergy n bound := by
  unfold generatedRawBranchingMaxEnergy
  exact exists_mem_energy_eq_maxRawResidualEnergyOfCells_of_ne_nil
    (booleanGeneratedRawBranchingSpectrum n bound).cells hne

/-! ## Generated nonempty top-confinement certificates -/

/-- A generated raw branching certificate whose top cell is selected from the
computed finite spectrum itself. -/
structure SU7GeneratedBooleanRawBranchingNonemptyConfinementCertificate
    (n : ℕ) where
  codeBound : ℕ
  spectrum_nonempty :
    (booleanGeneratedRawBranchingSpectrum n codeBound).cells ≠ []
  forbids_unit_permanent_holonomy :
    SU7RawBranchingSpectrumForbidsUnitPermanentHolonomy
      (booleanGeneratedRawBranchingSpectrum n codeBound)

/-- A nonempty generated confinement certificate produces the P944
top-confinement certificate by selecting a max-energy cell. -/
def topConfinementCertificate_of_nonemptyConfinementCertificate
    {n : ℕ}
    (G : SU7GeneratedBooleanRawBranchingNonemptyConfinementCertificate n) :
    SU7GeneratedBooleanRawBranchingTopConfinementCertificate n :=
  let htop :=
    exists_topCell_of_booleanGeneratedRawBranchingSpectrum_nonempty
      G.spectrum_nonempty
  let topCell := Classical.choose htop
  let hspec := Classical.choose_spec htop
  { codeBound := G.codeBound
    startCell := topCell
    start_mem := hspec.1
    start_energy_top := hspec.2
    forbids_unit_permanent_holonomy :=
      G.forbids_unit_permanent_holonomy }

/-- A nonempty generated confinement certificate produces a no-gap certificate.
-/
def noGapCertificate_of_nonemptyConfinementCertificate
    {n : ℕ}
    (G : SU7GeneratedBooleanRawBranchingNonemptyConfinementCertificate n) :
    SU7GeneratedBooleanRawBranchingNoGapCertificate n :=
  noGapCertificate_of_topConfinementCertificate
    (topConfinementCertificate_of_nonemptyConfinementCertificate G)

/-- A nonempty generated confinement certificate computes a trace-zero
prime-edge loop. -/
def traceZeroPrimeEdgeLoop_of_nonemptyConfinementCertificate
    {n : ℕ}
    (G : SU7GeneratedBooleanRawBranchingNonemptyConfinementCertificate n) :
    TraceZeroPrimeEdgeLoop n :=
  traceZeroPrimeEdgeLoop_of_topConfinementCertificate
    (topConfinementCertificate_of_nonemptyConfinementCertificate G)

/-- Every even fiber carries a generated nonempty confinement certificate. -/
def SU7GeneratedNonemptyConfinementEveryEvenFiber : Prop :=
  ∀ n : ℕ, 2 ≤ n ->
    Nonempty (SU7GeneratedBooleanRawBranchingNonemptyConfinementCertificate n)

/-- Fiberwise nonempty generated confinement gives ordinary even Goldbach. -/
theorem evenGoldbach_of_generatedNonemptyConfinement
    (H : SU7GeneratedNonemptyConfinementEveryEvenFiber) :
    EvenGoldbachStatement :=
  evenGoldbach_of_generatedTopConfinement
    (by
      intro n hn
      exact
        ⟨topConfinementCertificate_of_nonemptyConfinementCertificate
          (Classical.choice (H n hn))⟩)

/-! ## Certificate -/

/-- P945 certificate: finite generated spectra supply their own top cells, so
nonemptiness plus unit-holonomy confinement is enough to generate coverage. -/
structure SU7GeneratedNonemptyConfinementProducerCertificate where
  finite_list_max_attained :
    ∀ {n : ℕ} (xs : List (SU7BranchingDecompositionCell n)),
      xs ≠ [] ->
        ∃ c : SU7BranchingDecompositionCell n,
          c ∈ xs ∧
            rawAtomCodeBranchingDecompositionResidualEnergy c =
              maxRawResidualEnergyOfCells xs
  generated_spectrum_top_cell :
    ∀ {n bound : ℕ},
      (booleanGeneratedRawBranchingSpectrum n bound).cells ≠ [] ->
        ∃ c : SU7BranchingDecompositionCell n,
          c ∈ (booleanGeneratedRawBranchingSpectrum n bound).cells ∧
            rawAtomCodeBranchingDecompositionResidualEnergy c =
              generatedRawBranchingMaxEnergy n bound
  nonempty_confinement_to_top_confinement :
    ∀ {n : ℕ},
      SU7GeneratedBooleanRawBranchingNonemptyConfinementCertificate n ->
        SU7GeneratedBooleanRawBranchingTopConfinementCertificate n
  nonempty_confinement_to_no_gap :
    ∀ {n : ℕ},
      SU7GeneratedBooleanRawBranchingNonemptyConfinementCertificate n ->
        SU7GeneratedBooleanRawBranchingNoGapCertificate n
  nonempty_confinement_to_trace_zero :
    ∀ {n : ℕ},
      SU7GeneratedBooleanRawBranchingNonemptyConfinementCertificate n ->
        TraceZeroPrimeEdgeLoop n
  every_fiber_to_goldbach :
    SU7GeneratedNonemptyConfinementEveryEvenFiber ->
      EvenGoldbachStatement

/-- Canonical P945 generated nonempty confinement producer certificate. -/
def su7GeneratedNonemptyConfinementProducerCertificate :
    SU7GeneratedNonemptyConfinementProducerCertificate where
  finite_list_max_attained :=
    exists_mem_energy_eq_maxRawResidualEnergyOfCells_of_ne_nil
  generated_spectrum_top_cell :=
    exists_topCell_of_booleanGeneratedRawBranchingSpectrum_nonempty
  nonempty_confinement_to_top_confinement :=
    topConfinementCertificate_of_nonemptyConfinementCertificate
  nonempty_confinement_to_no_gap :=
    noGapCertificate_of_nonemptyConfinementCertificate
  nonempty_confinement_to_trace_zero :=
    traceZeroPrimeEdgeLoop_of_nonemptyConfinementCertificate
  every_fiber_to_goldbach :=
    evenGoldbach_of_generatedNonemptyConfinement


end
end StandardModelConstraint
end SaturationMonoid
