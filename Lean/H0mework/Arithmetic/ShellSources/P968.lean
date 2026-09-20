import H0mework.Arithmetic.ShellSources.P967

/-!
# Proposition 968: a single endpoint-shell kernel produces flow and unit bridge

P962 named two producer objects for the no-prime branch-cell throat:

```text
confining residual flow
quantized unit bridge
```

P968 lowers both to one common object.  An endpoint-shell kernel chooses, for
each residual-energy shell below a bound, an actual no-prime branch cell in
that shell.  From that single kernel Lean constructs:

* the strict Lyapunov lower-cell flow;
* the one-unit bridge at the top of every strict descent;
* the generated P962 flow/quantization certificate.

Thus the remaining producer debt is not two independent fields.  It is exactly
the no-gap statement that every residual shell is occupied by a generated
no-prime branch cell.
-/

namespace SaturationMonoid
namespace StandardModelConstraint

noncomputable section

open SaturationMonoid.AffineRelaxation
open RunningSigmaBeta

set_option linter.defProp false

/-! ## Endpoint-shell kernels -/

/-- A functional endpoint-shell kernel for a no-prime branch-cell list.

For every shell `k < maxEnergy`, it returns an in-list cell whose endpoint
residual energy is exactly `k`.  This is the single no-gap object from which
both residual-flow descent and one-unit quantization are read. -/
structure NoPrimeBranchingEndpointShellKernel
    {C : SU7WeightTensorCoding} {n : ℕ}
    (xs : List (SU7NoPrimeBranchingSpectrumCell C n))
    (maxEnergy : ℕ) where
  shellCell :
    ∀ k : ℕ, k < maxEnergy ->
      SU7NoPrimeBranchingSpectrumCell C n
  shellCell_mem :
    ∀ k hk, shellCell k hk ∈ xs
  shellCell_energy :
    ∀ k hk,
      noPrimeBranchingEndpointResidualEnergy
          (shellCell k hk) = k

/-- Transparent endpoint-energy shell coverage produces the functional shell
kernel by choosing the representative in each shell. -/
def endpointShellKernel_of_endpointCoverage
    {C : SU7WeightTensorCoding} {n maxEnergy : ℕ}
    {xs : List (SU7NoPrimeBranchingSpectrumCell C n)}
    (H : NoPrimeBranchingEndpointEnergyShellCoverage xs maxEnergy) :
    NoPrimeBranchingEndpointShellKernel xs maxEnergy where
  shellCell := by
    intro k hk
    exact Classical.choose (H (k + 1) (by omega) (by omega))
  shellCell_mem := by
    intro k hk
    exact (Classical.choose_spec (H (k + 1) (by omega) (by omega))).1
  shellCell_energy := by
    intro k hk
    have henergy :
        noPrimeBranchingEndpointResidualEnergy
            (Classical.choose (H (k + 1) (by omega) (by omega))) =
          k + 1 - 1 :=
      (Classical.choose_spec (H (k + 1) (by omega) (by omega))).2
    have hpred : k + 1 - 1 = k := by omega
    simpa [hpred] using henergy

/-- Coverage below the generated raw maximum produces a shell kernel whenever
the no-prime list's own maximum is below that generated maximum. -/
def endpointShellKernel_of_generatedMaxCoverage
    {C : SU7WeightTensorCoding} {n bound : ℕ}
    {xs : List (SU7NoPrimeBranchingSpectrumCell C n)}
    (H : NoPrimeBranchingEndpointShellCoverageUpToGeneratedMax bound xs)
    (hmax :
      maxNoPrimeBranchingEndpointResidualEnergyOfCells xs ≤
        generatedRawBranchingMaxEnergy n bound) :
    NoPrimeBranchingEndpointShellKernel xs
      (maxNoPrimeBranchingEndpointResidualEnergyOfCells xs) where
  shellCell := by
    intro k hk
    exact Classical.choose (H k (Nat.lt_of_lt_of_le hk hmax))
  shellCell_mem := by
    intro k hk
    exact (Classical.choose_spec
      (H k (Nat.lt_of_lt_of_le hk hmax))).1
  shellCell_energy := by
    intro k hk
    exact (Classical.choose_spec
      (H k (Nat.lt_of_lt_of_le hk hmax))).2

/-! ## One kernel produces both P962 objects -/

/-- An endpoint-shell kernel constructs the strict residual-flow object. -/
def confiningResidualFlow_of_endpointShellKernel
    {C : SU7WeightTensorCoding} {n maxEnergy : ℕ}
    {xs : List (SU7NoPrimeBranchingSpectrumCell C n)}
    (K : NoPrimeBranchingEndpointShellKernel xs maxEnergy)
    (hbound :
      ∀ B : SU7NoPrimeBranchingSpectrumCell C n,
        B ∈ xs -> noPrimeBranchingEndpointResidualEnergy B ≤ maxEnergy) :
    NoPrimeBranchingConfiningResidualFlow xs where
  lowerCell := by
    intro B hmem hnonzero
    exact
      K.shellCell
        (noPrimeBranchingEndpointResidualEnergy B - 1)
        (by
          have hpos :
              0 < noPrimeBranchingEndpointResidualEnergy B := by
            exact Nat.pos_of_ne_zero hnonzero
          have hle := hbound B hmem
          omega)
  lower_mem := by
    intro B hmem hnonzero
    exact K.shellCell_mem
      (noPrimeBranchingEndpointResidualEnergy B - 1)
      (by
        have hpos :
            0 < noPrimeBranchingEndpointResidualEnergy B := by
          exact Nat.pos_of_ne_zero hnonzero
        have hle := hbound B hmem
        omega)
  lower_energy_lt := by
    intro B hmem hnonzero
    have hpos :
        0 < noPrimeBranchingEndpointResidualEnergy B := by
      exact Nat.pos_of_ne_zero hnonzero
    have hle := hbound B hmem
    have henergy := K.shellCell_energy
      (noPrimeBranchingEndpointResidualEnergy B - 1)
      (by omega)
    rw [henergy]
    omega

/-- The same endpoint-shell kernel constructs the quantized one-unit bridge.
-/
def quantizedUnitBridge_of_endpointShellKernel
    {C : SU7WeightTensorCoding} {n maxEnergy : ℕ}
    {xs : List (SU7NoPrimeBranchingSpectrumCell C n)}
    (K : NoPrimeBranchingEndpointShellKernel xs maxEnergy)
    (hbound :
      ∀ B : SU7NoPrimeBranchingSpectrumCell C n,
        B ∈ xs -> noPrimeBranchingEndpointResidualEnergy B ≤ maxEnergy) :
    NoPrimeBranchingQuantizedUnitBridge xs where
  unitStep := by
    intro B lower hBmem _hlower_mem hlt
    exact
      K.shellCell
        (noPrimeBranchingEndpointResidualEnergy B - 1)
        (by
          have hle := hbound B hBmem
          omega)
  unitStep_mem := by
    intro B lower hBmem _hlower_mem hlt
    exact K.shellCell_mem
      (noPrimeBranchingEndpointResidualEnergy B - 1)
      (by
        have hle := hbound B hBmem
        omega)
  unitStep_energy := by
    intro B lower hBmem _hlower_mem hlt
    have hle := hbound B hBmem
    have henergy := K.shellCell_energy
      (noPrimeBranchingEndpointResidualEnergy B - 1)
      (by omega)
    rw [henergy]
    omega

/-! ## Generated no-prime specialization -/

/-- A shell kernel on the generated no-prime list produces P962's generated
flow/quantization certificate. -/
def generatedNoPrimeFlowQuantizationCertificate_of_endpointShellKernel
    {n bound : ℕ}
    (hbound : 2 ≤ bound)
    (K :
      NoPrimeBranchingEndpointShellKernel
        (generatedNoPrimeBranchingCells n bound)
        (maxNoPrimeBranchingEndpointResidualEnergyOfCells
          (generatedNoPrimeBranchingCells n bound))) :
    SU7GeneratedNoPrimeFlowQuantizationCertificate n where
  codeBound := bound
  codeBound_ge_two := hbound
  residual_flow :=
    confiningResidualFlow_of_endpointShellKernel K
      (by
        intro B hmem
        exact noPrimeBranchingEndpointEnergy_le_maxOfCells hmem)
  quantized_unit_bridge :=
    quantizedUnitBridge_of_endpointShellKernel K
      (by
        intro B hmem
        exact noPrimeBranchingEndpointEnergy_le_maxOfCells hmem)

/-- P966/P967 generated-max coverage produces the single shell kernel for the
canonical generated no-prime list. -/
def endpointShellKernel_of_noPrimeGeneratedMaxCoverage
    {n bound : ℕ}
    (H :
      NoPrimeBranchingEndpointShellCoverageUpToGeneratedMax
        bound (generatedNoPrimeBranchingCells n bound)) :
    NoPrimeBranchingEndpointShellKernel
      (generatedNoPrimeBranchingCells n bound)
      (maxNoPrimeBranchingEndpointResidualEnergyOfCells
        (generatedNoPrimeBranchingCells n bound)) :=
  endpointShellKernel_of_generatedMaxCoverage H
    (generatedNoPrimeMaxEnergy_le_generatedRawMaxEnergy n bound)

/-- P966/P967 generated-max coverage produces P962's generated
flow/quantization certificate through the single shell kernel. -/
def generatedNoPrimeFlowQuantizationCertificate_of_noPrimeGeneratedMaxCoverage
    {n bound : ℕ}
    (hbound : 2 ≤ bound)
    (H :
      NoPrimeBranchingEndpointShellCoverageUpToGeneratedMax
        bound (generatedNoPrimeBranchingCells n bound)) :
    SU7GeneratedNoPrimeFlowQuantizationCertificate n :=
  generatedNoPrimeFlowQuantizationCertificate_of_endpointShellKernel hbound
    (endpointShellKernel_of_noPrimeGeneratedMaxCoverage H)

/-- A generated Lyapunov/confinement certificate produces the same shell
kernel; the two P962 fields are therefore shared readouts of one no-gap
occupancy law. -/
def endpointShellKernel_of_generatedNoPrimeLyapunov
    {n : ℕ}
    (G : SU7GeneratedNoPrimeLyapunovConfinementCertificate n) :
    NoPrimeBranchingEndpointShellKernel
      (generatedNoPrimeBranchingCells n G.codeBound)
      (maxNoPrimeBranchingEndpointResidualEnergyOfCells
        (generatedNoPrimeBranchingCells n G.codeBound)) :=
  endpointShellKernel_of_noPrimeGeneratedMaxCoverage
    (noPrimeEndpointShellCoverageUpToGeneratedMax_of_lyapunovCertificate G)

/-- Generated Lyapunov/confinement produces flow/quantization through the
single shell-kernel route. -/
def generatedNoPrimeFlowQuantizationCertificate_of_lyapunovShellKernel
    {n : ℕ}
    (G : SU7GeneratedNoPrimeLyapunovConfinementCertificate n) :
    SU7GeneratedNoPrimeFlowQuantizationCertificate n :=
  generatedNoPrimeFlowQuantizationCertificate_of_endpointShellKernel
    G.codeBound_ge_two
    (endpointShellKernel_of_generatedNoPrimeLyapunov G)

/-! ## Certificate -/

/-- P968 certificate: one endpoint-shell kernel is the shared producer for
strict residual flow and the quantized unit bridge.  The Lyapunov route is
kept dependent on `G.codeBound`, because that is the real generated fiber
rather than an erased placeholder. -/
structure SU7EndpointShellKernelDependentProducerCertificate where
  endpoint_coverage_to_kernel :
    ∀ {C : SU7WeightTensorCoding} {n maxEnergy : ℕ}
      {xs : List (SU7NoPrimeBranchingSpectrumCell C n)},
      NoPrimeBranchingEndpointEnergyShellCoverage xs maxEnergy ->
        NoPrimeBranchingEndpointShellKernel xs maxEnergy
  generated_max_coverage_to_kernel :
    ∀ {C : SU7WeightTensorCoding} {n bound : ℕ}
      {xs : List (SU7NoPrimeBranchingSpectrumCell C n)},
      NoPrimeBranchingEndpointShellCoverageUpToGeneratedMax bound xs ->
        maxNoPrimeBranchingEndpointResidualEnergyOfCells xs ≤
          generatedRawBranchingMaxEnergy n bound ->
            NoPrimeBranchingEndpointShellKernel xs
              (maxNoPrimeBranchingEndpointResidualEnergyOfCells xs)
  kernel_to_flow :
    ∀ {C : SU7WeightTensorCoding} {n maxEnergy : ℕ}
      {xs : List (SU7NoPrimeBranchingSpectrumCell C n)},
      NoPrimeBranchingEndpointShellKernel xs maxEnergy ->
        (∀ B : SU7NoPrimeBranchingSpectrumCell C n,
          B ∈ xs -> noPrimeBranchingEndpointResidualEnergy B ≤ maxEnergy) ->
            NoPrimeBranchingConfiningResidualFlow xs
  kernel_to_quantized_bridge :
    ∀ {C : SU7WeightTensorCoding} {n maxEnergy : ℕ}
      {xs : List (SU7NoPrimeBranchingSpectrumCell C n)},
      NoPrimeBranchingEndpointShellKernel xs maxEnergy ->
        (∀ B : SU7NoPrimeBranchingSpectrumCell C n,
          B ∈ xs -> noPrimeBranchingEndpointResidualEnergy B ≤ maxEnergy) ->
            NoPrimeBranchingQuantizedUnitBridge xs
  generated_kernel_to_flow_quantization :
    ∀ {n bound : ℕ},
      2 ≤ bound ->
        NoPrimeBranchingEndpointShellKernel
          (generatedNoPrimeBranchingCells n bound)
          (maxNoPrimeBranchingEndpointResidualEnergyOfCells
            (generatedNoPrimeBranchingCells n bound)) ->
          SU7GeneratedNoPrimeFlowQuantizationCertificate n
  generated_max_coverage_to_flow_quantization :
    ∀ {n bound : ℕ},
      2 ≤ bound ->
        NoPrimeBranchingEndpointShellCoverageUpToGeneratedMax
          bound (generatedNoPrimeBranchingCells n bound) ->
            SU7GeneratedNoPrimeFlowQuantizationCertificate n
  lyapunov_to_shell_kernel :
    ∀ {n : ℕ}
      (G : SU7GeneratedNoPrimeLyapunovConfinementCertificate n),
        NoPrimeBranchingEndpointShellKernel
          (generatedNoPrimeBranchingCells n G.codeBound)
          (maxNoPrimeBranchingEndpointResidualEnergyOfCells
            (generatedNoPrimeBranchingCells n G.codeBound))
  lyapunov_to_flow_quantization_via_kernel :
    ∀ {n : ℕ},
      SU7GeneratedNoPrimeLyapunovConfinementCertificate n ->
        SU7GeneratedNoPrimeFlowQuantizationCertificate n

/-- Canonical P968 endpoint-shell-kernel producer certificate. -/
def su7EndpointShellKernelDependentProducerCertificate :
    SU7EndpointShellKernelDependentProducerCertificate where
  endpoint_coverage_to_kernel := endpointShellKernel_of_endpointCoverage
  generated_max_coverage_to_kernel := by
    intro C n bound xs H hmax
    exact endpointShellKernel_of_generatedMaxCoverage
      (n := n) (bound := bound) H hmax
  kernel_to_flow := confiningResidualFlow_of_endpointShellKernel
  kernel_to_quantized_bridge := quantizedUnitBridge_of_endpointShellKernel
  generated_kernel_to_flow_quantization := by
    intro n bound hbound K
    exact generatedNoPrimeFlowQuantizationCertificate_of_endpointShellKernel
      hbound K
  generated_max_coverage_to_flow_quantization := by
    intro n bound hbound H
    exact
      generatedNoPrimeFlowQuantizationCertificate_of_noPrimeGeneratedMaxCoverage
        hbound H
  lyapunov_to_shell_kernel := endpointShellKernel_of_generatedNoPrimeLyapunov
  lyapunov_to_flow_quantization_via_kernel :=
    generatedNoPrimeFlowQuantizationCertificate_of_lyapunovShellKernel


end
end StandardModelConstraint
end SaturationMonoid
