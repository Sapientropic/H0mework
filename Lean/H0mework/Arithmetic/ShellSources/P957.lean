import H0mework.Arithmetic.ShellSources.P956

/-!
# Proposition 957: no-prime coverage failure is filtered holonomy

P956 transported successful raw generated coverage through the no-prime
branch-cell lift.  This file records the complementary failure readout.

If a no-prime endpoint-energy shell is missing, and an active branch cell sits
one unit above that shell, then that branch cell has no one-unit successor.  By
P951/P950, the same source cell projects to a filtered raw code-pair permanent
holonomy witness.  Thus a coverage failure is not a loose Boolean miss: it is a
confinement-visible residual obstruction.
-/

namespace SaturationMonoid
namespace StandardModelConstraint

noncomputable section

open SaturationMonoid.AffineRelaxation
open RunningSigmaBeta

set_option linter.defProp false

/-! ## No-prime endpoint-energy gaps -/

/-- A missing endpoint residual-energy shell in a no-prime branch-cell list. -/
structure NoPrimeBranchingEndpointEnergyShellGap
    {C : SU7WeightTensorCoding} {n : ℕ}
    (xs : List (SU7NoPrimeBranchingSpectrumCell C n))
    (maxEnergy : ℕ) where
  level : ℕ
  level_lt : level < maxEnergy
  hasEndpoint_false :
    noPrimeBranchingCellHasEndpointEnergy xs level = false

/-- A no-prime branch-cell list forbids endpoint-energy gaps when every
checked residual shell is represented. -/
def NoPrimeBranchingEndpointEnergyShellForbidsGap
    {C : SU7WeightTensorCoding} {n : ℕ}
    (xs : List (SU7NoPrimeBranchingSpectrumCell C n))
    (maxEnergy : ℕ) : Prop :=
  ∀ _gap : NoPrimeBranchingEndpointEnergyShellGap xs maxEnergy, False

/-- A true no-prime endpoint coverage check is exactly absence of missing
endpoint-energy shell obstructions. -/
theorem noPrimeBranchingEnergyShellCoverageCheck_true_iff_forbidsGap
    {C : SU7WeightTensorCoding} {n : ℕ}
    (xs : List (SU7NoPrimeBranchingSpectrumCell C n))
    (maxEnergy : ℕ) :
    noPrimeBranchingEnergyShellCoverageCheck xs maxEnergy = true ↔
      NoPrimeBranchingEndpointEnergyShellForbidsGap xs maxEnergy := by
  constructor
  · intro hcheck gap
    unfold noPrimeBranchingEnergyShellCoverageCheck at hcheck
    have hhas :
        noPrimeBranchingCellHasEndpointEnergy xs gap.level = true :=
      (List.all_eq_true.mp hcheck) gap.level
        (List.mem_range.mpr gap.level_lt)
    rw [gap.hasEndpoint_false] at hhas
    contradiction
  · intro hforbid
    unfold noPrimeBranchingEnergyShellCoverageCheck
    apply List.all_eq_true.mpr
    intro k hk
    cases hhas : noPrimeBranchingCellHasEndpointEnergy xs k
    · exact False.elim
        (hforbid
          { level := k
            level_lt := List.mem_range.mp hk
            hasEndpoint_false := hhas })
    · rfl

/-- A false no-prime endpoint coverage check is exactly a nonempty missing
endpoint-shell obstruction. -/
theorem noPrimeBranchingEnergyShellCoverageCheck_false_iff_gap
    {C : SU7WeightTensorCoding} {n : ℕ}
    (xs : List (SU7NoPrimeBranchingSpectrumCell C n))
    (maxEnergy : ℕ) :
    noPrimeBranchingEnergyShellCoverageCheck xs maxEnergy = false ↔
      Nonempty (NoPrimeBranchingEndpointEnergyShellGap xs maxEnergy) := by
  constructor
  · intro hfalse
    by_contra hnone
    have hforbid :
        NoPrimeBranchingEndpointEnergyShellForbidsGap xs maxEnergy := by
      intro gap
      exact hnone ⟨gap⟩
    have htrue :
        noPrimeBranchingEnergyShellCoverageCheck xs maxEnergy = true :=
      (noPrimeBranchingEnergyShellCoverageCheck_true_iff_forbidsGap
        xs maxEnergy).mpr hforbid
    rw [hfalse] at htrue
    contradiction
  · intro hgap
    cases hcheck : noPrimeBranchingEnergyShellCoverageCheck xs maxEnergy
    · rfl
    · have hforbid :
          NoPrimeBranchingEndpointEnergyShellForbidsGap xs maxEnergy :=
        (noPrimeBranchingEnergyShellCoverageCheck_true_iff_forbidsGap
          xs maxEnergy).mp hcheck
      exact False.elim (hforbid (Classical.choice hgap))

/-- If a branch cell with endpoint residual energy `k` is present in a
no-prime source list, the Boolean endpoint-energy shell check returns `true`.
-/
theorem noPrimeBranchingCellHasEndpointEnergy_eq_true_of_mem_energy
    {C : SU7WeightTensorCoding} {n : ℕ}
    {xs : List (SU7NoPrimeBranchingSpectrumCell C n)}
    {B : SU7NoPrimeBranchingSpectrumCell C n} {k : ℕ}
    (hmem : B ∈ xs)
    (henergy : noPrimeBranchingEndpointResidualEnergy B = k) :
    noPrimeBranchingCellHasEndpointEnergy xs k = true := by
  unfold noPrimeBranchingCellHasEndpointEnergy
  exact List.any_eq_true.mpr
    ⟨B, hmem, decide_eq_true_eq.mpr henergy⟩

/-! ## No-prime unit permanent holonomy -/

/-- A no-prime branch cell with nonzero endpoint residual energy and no
one-unit lower successor in the source list. -/
def NoPrimeBranchingCellUnitPermanentHolonomy
    {C : SU7WeightTensorCoding} {n : ℕ}
    (xs : List (SU7NoPrimeBranchingSpectrumCell C n))
    (B : SU7NoPrimeBranchingSpectrumCell C n) : Prop :=
  B ∈ xs ∧
    noPrimeBranchingEndpointResidualEnergy B ≠ 0 ∧
      ∀ B' : SU7NoPrimeBranchingSpectrumCell C n,
        B' ∈ xs ->
          noPrimeBranchingEndpointResidualEnergy B' + 1 ≠
            noPrimeBranchingEndpointResidualEnergy B

/-- The source no-prime branch-cell list forbids unit permanent holonomy. -/
def NoPrimeBranchingCellsForbidUnitPermanentHolonomy
    {C : SU7WeightTensorCoding} {n : ℕ}
    (xs : List (SU7NoPrimeBranchingSpectrumCell C n)) : Prop :=
  ∀ B : SU7NoPrimeBranchingSpectrumCell C n,
    ¬ NoPrimeBranchingCellUnitPermanentHolonomy xs B

/-- Absence of no-prime unit permanent holonomy is exactly the branch-cell
unit successor law. -/
theorem noPrimeNoUnitHolonomy_iff_cellUnitSuccessorLaw
    {C : SU7WeightTensorCoding} {n : ℕ}
    (xs : List (SU7NoPrimeBranchingSpectrumCell C n)) :
    NoPrimeBranchingCellsForbidUnitPermanentHolonomy xs ↔
      NoPrimeBranchingCellUnitSuccessorLaw xs := by
  constructor
  · intro H B hmem hnonzero
    by_contra hnone
    have hterminal :
        ∀ B' : SU7NoPrimeBranchingSpectrumCell C n,
          B' ∈ xs ->
            noPrimeBranchingEndpointResidualEnergy B' + 1 ≠
              noPrimeBranchingEndpointResidualEnergy B := by
      intro B' hB'mem hsucc
      exact hnone ⟨B', hB'mem, hsucc⟩
    exact H B ⟨hmem, hnonzero, hterminal⟩
  · intro H B hperm
    rcases hperm with ⟨hmem, hnonzero, hterminal⟩
    rcases H B hmem hnonzero with ⟨B', hB'mem, hsucc⟩
    exact hterminal B' hB'mem hsucc

/-! ## Missing shells generate no-prime unit holonomy -/

/-- A missing endpoint shell hit by an active no-prime branch cell one energy
unit above it. -/
structure NoPrimeBranchingEndpointGapUpperCell
    {C : SU7WeightTensorCoding} {n : ℕ}
    (xs : List (SU7NoPrimeBranchingSpectrumCell C n))
    (maxEnergy : ℕ) where
  gap : NoPrimeBranchingEndpointEnergyShellGap xs maxEnergy
  upperCell : SU7NoPrimeBranchingSpectrumCell C n
  upper_mem : upperCell ∈ xs
  upper_nonzero :
    noPrimeBranchingEndpointResidualEnergy upperCell ≠ 0
  upper_energy :
    noPrimeBranchingEndpointResidualEnergy upperCell =
      gap.level + 1

/-- A missing predecessor shell hit by an active upper no-prime cell is a
unit permanent holonomy cell. -/
theorem noPrimeUnitHolonomy_of_endpointGapUpperCell
    {C : SU7WeightTensorCoding} {n : ℕ}
    {xs : List (SU7NoPrimeBranchingSpectrumCell C n)}
    {maxEnergy : ℕ}
    (G : NoPrimeBranchingEndpointGapUpperCell xs maxEnergy) :
    NoPrimeBranchingCellUnitPermanentHolonomy xs G.upperCell := by
  refine ⟨G.upper_mem, G.upper_nonzero, ?_⟩
  intro lower hlower_mem hsucc
  have hlower_energy :
      noPrimeBranchingEndpointResidualEnergy lower = G.gap.level := by
    have hsucc' :
        noPrimeBranchingEndpointResidualEnergy lower + 1 =
          G.gap.level + 1 := by
      rw [hsucc, G.upper_energy]
    exact Nat.succ.inj hsucc'
  have hhas :
      noPrimeBranchingCellHasEndpointEnergy xs G.gap.level = true :=
    noPrimeBranchingCellHasEndpointEnergy_eq_true_of_mem_energy
      hlower_mem hlower_energy
  rw [G.gap.hasEndpoint_false] at hhas
  contradiction

/-- Every endpoint gap is hit by an active no-prime branch cell one energy
unit above the missing shell. -/
structure NoPrimeBranchingEndpointGapActiveSupport
    {C : SU7WeightTensorCoding} {n : ℕ}
    (xs : List (SU7NoPrimeBranchingSpectrumCell C n))
    (maxEnergy : ℕ) where
  upper_of_gap :
    ∀ gap : NoPrimeBranchingEndpointEnergyShellGap xs maxEnergy,
      ∃ upperCell : SU7NoPrimeBranchingSpectrumCell C n,
        upperCell ∈ xs ∧
          noPrimeBranchingEndpointResidualEnergy upperCell ≠ 0 ∧
            noPrimeBranchingEndpointResidualEnergy upperCell =
              gap.level + 1

/-- Active support packages any endpoint gap into a unit-holonomy upper-cell
configuration. -/
def endpointGapUpperCell_of_activeSupport
    {C : SU7WeightTensorCoding} {n : ℕ}
    {xs : List (SU7NoPrimeBranchingSpectrumCell C n)}
    {maxEnergy : ℕ}
    (A : NoPrimeBranchingEndpointGapActiveSupport xs maxEnergy)
    (gap : NoPrimeBranchingEndpointEnergyShellGap xs maxEnergy) :
    NoPrimeBranchingEndpointGapUpperCell xs maxEnergy :=
  let upperCell := Classical.choose (A.upper_of_gap gap)
  let hspec := Classical.choose_spec (A.upper_of_gap gap)
  { gap := gap
    upperCell := upperCell
    upper_mem := hspec.1
    upper_nonzero := hspec.2.1
    upper_energy := hspec.2.2 }

/-- Failed no-prime endpoint coverage, plus active support, produces an
explicit no-prime unit permanent holonomy witness. -/
theorem exists_noPrimeUnitHolonomy_of_failedEndpointCoverage_and_activeSupport
    {C : SU7WeightTensorCoding} {n : ℕ}
    {xs : List (SU7NoPrimeBranchingSpectrumCell C n)}
    {maxEnergy : ℕ}
    (hfalse :
      noPrimeBranchingEnergyShellCoverageCheck xs maxEnergy = false)
    (A : NoPrimeBranchingEndpointGapActiveSupport xs maxEnergy) :
    Nonempty
      {B : SU7NoPrimeBranchingSpectrumCell C n //
        NoPrimeBranchingCellUnitPermanentHolonomy xs B} := by
  have hgap :
      Nonempty (NoPrimeBranchingEndpointEnergyShellGap xs maxEnergy) :=
    (noPrimeBranchingEnergyShellCoverageCheck_false_iff_gap
      xs maxEnergy).mp hfalse
  let gap := Classical.choice hgap
  let G := endpointGapUpperCell_of_activeSupport A gap
  exact ⟨⟨G.upperCell, noPrimeUnitHolonomy_of_endpointGapUpperCell G⟩⟩

/-! ## Projection to filtered raw code-pair holonomy -/

/-- A no-prime branch-cell unit-holonomy witness projects to the P950
filtered raw code-pair permanent-holonomy witness. -/
theorem filteredRawCodePairHolonomy_of_noPrimeUnitHolonomy
    {C : SU7WeightTensorCoding} {n bound : ℕ}
    {xs : List (SU7NoPrimeBranchingSpectrumCell C n)}
    {B : SU7NoPrimeBranchingSpectrumCell C n}
    (hbounded : NoPrimeBranchingCellsWithinBound bound xs)
    (H : NoPrimeBranchingCellUnitPermanentHolonomy xs B) :
    BoolGaugeFilteredRawCodePairUnitPermanentHolonomyCell
      n bound (noPrimeBranchingAllowedPredicate xs)
      (atomCode B.leftAtom.toSU7Atom)
      (atomCode B.rightAtom.toSU7Atom) := by
  rcases H with ⟨hmem, hnonzero, hterminal⟩
  refine filteredRawCodePairPermanentHolonomyCell_of_no_unit_successor
    (noPrimeBranchingAllowedPredicate_of_mem hmem)
    (hbounded B hmem).1
    (hbounded B hmem).2
    (noPrimeBranchingCell_left_atomicCheck B)
    (noPrimeBranchingCell_right_atomicCheck B)
    ?_
    ?_
  · unfold noPrimeBranchingEndpointResidualEnergy at hnonzero
    exact hnonzero
  · intro left' right' hallowed _hleft'_mem _hright'_mem
      _hleft'_check _hright'_check hsucc
    rcases exists_noPrimeBranchingCell_of_allowedPredicate
        (C := C) (n := n) (xs := xs) hallowed with
      ⟨B', hB'mem, hleft', hright'⟩
    have hsucc_B :
        noPrimeBranchingEndpointResidualEnergy B' + 1 =
          noPrimeBranchingEndpointResidualEnergy B := by
      unfold noPrimeBranchingEndpointResidualEnergy
      simpa [hleft', hright'] using hsucc
    exact hterminal B' hB'mem hsucc_B

/-- Failed no-prime endpoint coverage, plus active support and boundedness,
produces a concrete filtered raw code-pair permanent-holonomy witness. -/
theorem exists_filteredRawCodePairHolonomy_of_failedEndpointCoverage
    {C : SU7WeightTensorCoding} {n bound : ℕ}
    {xs : List (SU7NoPrimeBranchingSpectrumCell C n)}
    {maxEnergy : ℕ}
    (hbounded : NoPrimeBranchingCellsWithinBound bound xs)
    (hfalse :
      noPrimeBranchingEnergyShellCoverageCheck xs maxEnergy = false)
    (A : NoPrimeBranchingEndpointGapActiveSupport xs maxEnergy) :
    Nonempty
      {p : ℕ × ℕ //
        BoolGaugeFilteredRawCodePairUnitPermanentHolonomyCell
          n bound (noPrimeBranchingAllowedPredicate xs) p.1 p.2} := by
  rcases
      exists_noPrimeUnitHolonomy_of_failedEndpointCoverage_and_activeSupport
        hfalse A with
    ⟨⟨B, HB⟩⟩
  exact
    ⟨⟨(atomCode B.leftAtom.toSU7Atom,
        atomCode B.rightAtom.toSU7Atom),
      filteredRawCodePairHolonomy_of_noPrimeUnitHolonomy
        hbounded HB⟩⟩

/-! ## Certificate -/

/-- P957 certificate: no-prime endpoint coverage failure is exactly a missing
energy-shell obstruction, and active support turns it into filtered code-pair
permanent holonomy. -/
structure SU7NoPrimeCoverageFailureHolonomyCertificate where
  false_iff_endpoint_gap :
    ∀ {C : SU7WeightTensorCoding} {n : ℕ}
      (xs : List (SU7NoPrimeBranchingSpectrumCell C n))
      (maxEnergy : ℕ),
      noPrimeBranchingEnergyShellCoverageCheck xs maxEnergy = false ↔
        Nonempty
          (NoPrimeBranchingEndpointEnergyShellGap xs maxEnergy)
  no_unit_holonomy_iff_successor :
    ∀ {C : SU7WeightTensorCoding} {n : ℕ}
      (xs : List (SU7NoPrimeBranchingSpectrumCell C n)),
      NoPrimeBranchingCellsForbidUnitPermanentHolonomy xs ↔
        NoPrimeBranchingCellUnitSuccessorLaw xs
  gap_upper_to_unit_holonomy :
    ∀ {C : SU7WeightTensorCoding} {n : ℕ}
      {xs : List (SU7NoPrimeBranchingSpectrumCell C n)}
      {maxEnergy : ℕ},
      NoPrimeBranchingEndpointGapUpperCell xs maxEnergy ->
        {B : SU7NoPrimeBranchingSpectrumCell C n //
          NoPrimeBranchingCellUnitPermanentHolonomy xs B}
  failed_coverage_to_unit_holonomy :
    ∀ {C : SU7WeightTensorCoding} {n : ℕ}
      {xs : List (SU7NoPrimeBranchingSpectrumCell C n)}
      {maxEnergy : ℕ},
      noPrimeBranchingEnergyShellCoverageCheck xs maxEnergy = false ->
        NoPrimeBranchingEndpointGapActiveSupport xs maxEnergy ->
          Nonempty
            {B : SU7NoPrimeBranchingSpectrumCell C n //
              NoPrimeBranchingCellUnitPermanentHolonomy xs B}
  unit_holonomy_to_filtered_code_pair_holonomy :
    ∀ {C : SU7WeightTensorCoding} {n bound : ℕ}
      {xs : List (SU7NoPrimeBranchingSpectrumCell C n)}
      {B : SU7NoPrimeBranchingSpectrumCell C n},
      NoPrimeBranchingCellsWithinBound bound xs ->
        NoPrimeBranchingCellUnitPermanentHolonomy xs B ->
          BoolGaugeFilteredRawCodePairUnitPermanentHolonomyCell
            n bound (noPrimeBranchingAllowedPredicate xs)
            (atomCode B.leftAtom.toSU7Atom)
            (atomCode B.rightAtom.toSU7Atom)
  failed_coverage_to_filtered_code_pair_holonomy :
    ∀ {C : SU7WeightTensorCoding} {n bound : ℕ}
      {xs : List (SU7NoPrimeBranchingSpectrumCell C n)}
      {maxEnergy : ℕ},
      NoPrimeBranchingCellsWithinBound bound xs ->
        noPrimeBranchingEnergyShellCoverageCheck xs maxEnergy = false ->
          NoPrimeBranchingEndpointGapActiveSupport xs maxEnergy ->
            Nonempty
              {p : ℕ × ℕ //
                BoolGaugeFilteredRawCodePairUnitPermanentHolonomyCell
                  n bound (noPrimeBranchingAllowedPredicate xs) p.1 p.2}

/-- Canonical P957 no-prime coverage-failure holonomy certificate. -/
def su7NoPrimeCoverageFailureHolonomyCertificate :
    SU7NoPrimeCoverageFailureHolonomyCertificate where
  false_iff_endpoint_gap :=
    noPrimeBranchingEnergyShellCoverageCheck_false_iff_gap
  no_unit_holonomy_iff_successor :=
    noPrimeNoUnitHolonomy_iff_cellUnitSuccessorLaw
  gap_upper_to_unit_holonomy := by
    intro C n xs maxEnergy G
    exact ⟨G.upperCell, noPrimeUnitHolonomy_of_endpointGapUpperCell G⟩
  failed_coverage_to_unit_holonomy :=
    exists_noPrimeUnitHolonomy_of_failedEndpointCoverage_and_activeSupport
  unit_holonomy_to_filtered_code_pair_holonomy :=
    filteredRawCodePairHolonomy_of_noPrimeUnitHolonomy
  failed_coverage_to_filtered_code_pair_holonomy :=
    exists_filteredRawCodePairHolonomy_of_failedEndpointCoverage


end
end StandardModelConstraint
end SaturationMonoid
