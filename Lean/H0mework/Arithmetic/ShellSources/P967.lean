import H0mework.Arithmetic.ShellSources.P966

/-!
# Proposition 967: generated no-prime confinement covers the generated max

P966 asks the SU(7) no-prime source list to cover every residual shell below
`generatedRawBranchingMaxEnergy`.  Earlier no-prime confinement certificates
produce endpoint coverage up to the no-prime list's own maximum.

For the canonical generated no-prime source list these two maxima are equal:
the list is the no-prime tensor-irreducible lift of the Boolean generated raw
cells, and the lift preserves residual energy.  Therefore generated
Lyapunov/confinement is strong enough to feed the P966 allowed-sector shell
producer directly.
-/

namespace SaturationMonoid
namespace StandardModelConstraint

noncomputable section

open SaturationMonoid.AffineRelaxation
open RunningSigmaBeta

set_option linter.defProp false

/-! ## Generated raw and no-prime maxima agree -/

/-- If every member of a raw branch-cell list has residual energy bounded by
`bound`, then the recursive maximum of the list is also bounded by `bound`. -/
theorem maxRawResidualEnergyOfCells_le_of_mem_bound
    {n bound : ℕ}
    {xs : List (SU7BranchingDecompositionCell n)}
    (hbound :
      ∀ c : SU7BranchingDecompositionCell n,
        c ∈ xs -> rawAtomCodeBranchingDecompositionResidualEnergy c ≤ bound) :
    maxRawResidualEnergyOfCells xs ≤ bound := by
  induction xs with
  | nil =>
      simp [maxRawResidualEnergyOfCells]
  | cons c cs ih =>
      rw [maxRawResidualEnergyOfCells]
      apply max_le
      · exact hbound c (by simp)
      · apply ih
        intro c' hc'
        exact hbound c' (by simp [hc'])

/-- Every raw generated branch cell has a no-prime generated lift with the
same residual energy; hence its energy is bounded by the no-prime maximum. -/
theorem generatedRawEndpointEnergy_le_generatedNoPrimeMaxEnergy
    {n bound : ℕ}
    {c : SU7BranchingDecompositionCell n}
    (hmem : c ∈ (booleanGeneratedRawBranchingSpectrum n bound).cells) :
    rawAtomCodeBranchingDecompositionResidualEnergy c ≤
      maxNoPrimeBranchingEndpointResidualEnergyOfCells
        (generatedNoPrimeBranchingCells n bound) := by
  rcases exists_booleanAtomicCell_of_mem_booleanGeneratedSpectrum
      (n := n) (bound := bound) hmem with
    ⟨x, hxmem, hxcell⟩
  subst c
  let B := noPrimeBranchingCellOfBooleanAtomicRawCell x
  have hBmem : B ∈ generatedNoPrimeBranchingCells n bound := by
    unfold generatedNoPrimeBranchingCells
      noPrimeBranchingCellsOfBooleanAtomicRawCells
    exact List.mem_map.mpr ⟨x, hxmem, rfl⟩
  have hle :
      noPrimeBranchingEndpointResidualEnergy B ≤
        maxNoPrimeBranchingEndpointResidualEnergyOfCells
          (generatedNoPrimeBranchingCells n bound) :=
    noPrimeBranchingEndpointEnergy_le_maxOfCells hBmem
  have henergy :
      noPrimeBranchingEndpointResidualEnergy B =
        rawAtomCodeBranchingDecompositionResidualEnergy x.cell := by
    exact noPrimeBranchingCellOfBooleanAtomicRawCell_energy_eq x
  simpa [B, henergy] using hle

/-- The raw generated maximum is bounded by the no-prime generated maximum. -/
theorem generatedRawMaxEnergy_le_generatedNoPrimeMaxEnergy
    (n bound : ℕ) :
    generatedRawBranchingMaxEnergy n bound ≤
      maxNoPrimeBranchingEndpointResidualEnergyOfCells
        (generatedNoPrimeBranchingCells n bound) := by
  unfold generatedRawBranchingMaxEnergy
  exact
    maxRawResidualEnergyOfCells_le_of_mem_bound
      (by
        intro c hmem
        exact generatedRawEndpointEnergy_le_generatedNoPrimeMaxEnergy hmem)

/-- The generated raw maximum and generated no-prime maximum are equal. -/
theorem generatedRawMaxEnergy_eq_generatedNoPrimeMaxEnergy
    (n bound : ℕ) :
    generatedRawBranchingMaxEnergy n bound =
      maxNoPrimeBranchingEndpointResidualEnergyOfCells
        (generatedNoPrimeBranchingCells n bound) := by
  exact le_antisymm
    (generatedRawMaxEnergy_le_generatedNoPrimeMaxEnergy n bound)
    (generatedNoPrimeMaxEnergy_le_generatedRawMaxEnergy n bound)

/-! ## No-prime coverage checks cover P966's generated-max shells -/

/-- A true generated no-prime endpoint coverage check covers every shell below
the raw generated maximum, because the two generated maxima are equal. -/
theorem noPrimeEndpointShellCoverageUpToGeneratedMax_of_generatedNoPrimeCoverageCheck
    {n bound : ℕ}
    (hcheck :
      noPrimeBranchingEnergyShellCoverageCheck
          (generatedNoPrimeBranchingCells n bound)
          (maxNoPrimeBranchingEndpointResidualEnergyOfCells
            (generatedNoPrimeBranchingCells n bound)) = true) :
    NoPrimeBranchingEndpointShellCoverageUpToGeneratedMax
      bound (generatedNoPrimeBranchingCells n bound) := by
  intro k hk
  have hk_noPrime :
      k <
        maxNoPrimeBranchingEndpointResidualEnergyOfCells
          (generatedNoPrimeBranchingCells n bound) := by
    rwa [generatedRawMaxEnergy_eq_generatedNoPrimeMaxEnergy] at hk
  have hhas :
      noPrimeBranchingCellHasEndpointEnergy
          (generatedNoPrimeBranchingCells n bound) k = true :=
    (List.all_eq_true.mp hcheck) k (List.mem_range.mpr hk_noPrime)
  exact
    exists_noPrimeBranchingCell_of_hasEndpointEnergy_eq_true
      (generatedNoPrimeBranchingCells n bound) k hhas

/-- A generated Lyapunov/confinement certificate covers P966's generated-max
shells. -/
theorem noPrimeEndpointShellCoverageUpToGeneratedMax_of_lyapunovCertificate
    {n : ℕ}
    (G : SU7GeneratedNoPrimeLyapunovConfinementCertificate n) :
    NoPrimeBranchingEndpointShellCoverageUpToGeneratedMax
      G.codeBound (generatedNoPrimeBranchingCells n G.codeBound) :=
  noPrimeEndpointShellCoverageUpToGeneratedMax_of_generatedNoPrimeCoverageCheck
    (generatedNoPrimeCoverageCheck_of_lyapunovCertificate G)

/-- Generated Lyapunov/confinement directly produces P965's allowed-sector
shell coverage for the canonical generated no-prime list. -/
theorem boolGaugeFilteredCoverage_of_generatedNoPrimeLyapunov
    {n : ℕ}
    (G : SU7GeneratedNoPrimeLyapunovConfinementCertificate n) :
    BoolGaugeFilteredRawCodePairEnergyCoverage
      n G.codeBound
      (noPrimeBranchingAllowedPredicate
        (generatedNoPrimeBranchingCells n G.codeBound)) :=
  boolGaugeFilteredCoverage_of_noPrimeEndpointCoverage
    (generatedNoPrimeBranchingCellsWithinBound n G.codeBound)
    (noPrimeEndpointShellCoverageUpToGeneratedMax_of_lyapunovCertificate G)

/-- Generated Lyapunov/confinement directly feeds the P964/P965
flow-quantization throat. -/
def generatedNoPrimeFlowQuantizationCertificate_of_generatedNoPrimeLyapunov
    {n : ℕ}
    (G : SU7GeneratedNoPrimeLyapunovConfinementCertificate n) :
    SU7GeneratedNoPrimeFlowQuantizationCertificate n :=
  generatedNoPrimeFlowQuantizationCertificate_of_noPrimeEndpointCoverage
    G.codeBound_ge_two
    (generatedNoPrimeBranchingCellsWithinBound n G.codeBound)
    (noPrimeEndpointShellCoverageUpToGeneratedMax_of_lyapunovCertificate G)

/-! ## Certificate -/

/-- P967 certificate: generated no-prime Lyapunov/confinement is now connected
to P966's generated-max shell coverage, not merely to the no-prime list's own
coverage check. -/
structure SU7GeneratedNoPrimeLyapunovToGeneratedMaxCoverageCertificate where
  raw_max_le_no_prime_max :
    ∀ n bound : ℕ,
      generatedRawBranchingMaxEnergy n bound ≤
        maxNoPrimeBranchingEndpointResidualEnergyOfCells
          (generatedNoPrimeBranchingCells n bound)
  generated_max_eq :
    ∀ n bound : ℕ,
      generatedRawBranchingMaxEnergy n bound =
        maxNoPrimeBranchingEndpointResidualEnergyOfCells
          (generatedNoPrimeBranchingCells n bound)
  coverage_check_to_generated_max_shells :
    ∀ {n bound : ℕ},
      noPrimeBranchingEnergyShellCoverageCheck
          (generatedNoPrimeBranchingCells n bound)
          (maxNoPrimeBranchingEndpointResidualEnergyOfCells
            (generatedNoPrimeBranchingCells n bound)) = true ->
        NoPrimeBranchingEndpointShellCoverageUpToGeneratedMax
          bound (generatedNoPrimeBranchingCells n bound)
  lyapunov_to_generated_max_shells :
    ∀ {n : ℕ}
      (G : SU7GeneratedNoPrimeLyapunovConfinementCertificate n),
        NoPrimeBranchingEndpointShellCoverageUpToGeneratedMax
          G.codeBound (generatedNoPrimeBranchingCells n G.codeBound)
  lyapunov_to_allowed_coverage :
    ∀ {n : ℕ}
      (G : SU7GeneratedNoPrimeLyapunovConfinementCertificate n),
        BoolGaugeFilteredRawCodePairEnergyCoverage
          n G.codeBound
          (noPrimeBranchingAllowedPredicate
            (generatedNoPrimeBranchingCells n G.codeBound))
  lyapunov_to_flow_quantization :
    ∀ {n : ℕ},
      SU7GeneratedNoPrimeLyapunovConfinementCertificate n ->
        SU7GeneratedNoPrimeFlowQuantizationCertificate n

/-- Canonical P967 generated-max coverage certificate. -/
def su7GeneratedNoPrimeLyapunovToGeneratedMaxCoverageCertificate :
    SU7GeneratedNoPrimeLyapunovToGeneratedMaxCoverageCertificate where
  raw_max_le_no_prime_max :=
    generatedRawMaxEnergy_le_generatedNoPrimeMaxEnergy
  generated_max_eq :=
    generatedRawMaxEnergy_eq_generatedNoPrimeMaxEnergy
  coverage_check_to_generated_max_shells :=
    noPrimeEndpointShellCoverageUpToGeneratedMax_of_generatedNoPrimeCoverageCheck
  lyapunov_to_generated_max_shells :=
    noPrimeEndpointShellCoverageUpToGeneratedMax_of_lyapunovCertificate
  lyapunov_to_allowed_coverage :=
    boolGaugeFilteredCoverage_of_generatedNoPrimeLyapunov
  lyapunov_to_flow_quantization :=
    generatedNoPrimeFlowQuantizationCertificate_of_generatedNoPrimeLyapunov


end
end StandardModelConstraint
end SaturationMonoid
