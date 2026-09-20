import H0mework.Arithmetic.AtomicCodes.P930
import H0mework.Arithmetic.ShellSources.P968

/-!
# Proposition 974: the no-gap throat's zero shell is exactly bounded Goldbach

P929/P930 show that raw code-pair zero energy is exactly a bounded Goldbach
pair.  P955/P966/P967/P968 then transport raw generated shells into the
no-prime SU(7) endpoint-shell / Lyapunov-confinement throat.

This file pins the hard zero layer of that throat:

* generated raw shell `0` is exactly a bounded Goldbach pair;
* generated no-prime endpoint shell `0` is exactly a bounded Goldbach pair;
* any generated no-prime shell coverage or Lyapunov/confinement certificate
  whose generated maximum includes shell `0` therefore produces the bounded
  Goldbach pair.

So a future SU(7) producer cannot hide the zero-fiber obligation in an
endpoint-coverage or Lyapunov field.  The producer must generate this shell.
-/

namespace SaturationMonoid
namespace StandardModelConstraint

noncomputable section

set_option linter.defProp false

/-! ## Zero raw shell -/

/-- THEOREM 1: generated raw shell `0` is exactly the bounded Goldbach-pair
predicate. -/
theorem generatedRawZeroShell_iff_boundedGoldbachPair
    (n bound : ℕ) :
    GeneratedRawEnergyShellRealized n bound 0 ↔
      BoundedGoldbachPair n bound := by
  calc
    GeneratedRawEnergyShellRealized n bound 0
        ↔ RawCodePairEnergyShellRealized n bound 0 :=
      generatedRawEnergyShell_iff_codePairShell n bound 0
    _ ↔ BoundedGoldbachPair n bound :=
      rawCodePairZeroShell_iff_boundedGoldbachPair n bound

/-! ## Zero generated no-prime endpoint shell -/

/-- A bounded Goldbach pair lifts to a generated no-prime endpoint shell at
energy `0`. -/
theorem generatedNoPrimeEndpointZeroShell_of_boundedGoldbachPair
    {n bound : ℕ}
    (h : BoundedGoldbachPair n bound) :
    NoPrimeBranchingEndpointShellRealizedUpToGeneratedMax
      (generatedNoPrimeBranchingCells n bound) 0 := by
  exact
    noPrimeEndpointEnergyShell_of_generatedRawEnergyShell
      ((generatedRawZeroShell_iff_boundedGoldbachPair n bound).mpr h)

/-- A generated no-prime endpoint shell at energy `0` projects back to a
bounded Goldbach pair. -/
theorem boundedGoldbachPair_of_generatedNoPrimeEndpointZeroShell
    {n bound : ℕ}
    (h :
      NoPrimeBranchingEndpointShellRealizedUpToGeneratedMax
        (generatedNoPrimeBranchingCells n bound) 0) :
    BoundedGoldbachPair n bound := by
  rcases h with ⟨B, hBmem, hBenergy⟩
  rcases exists_booleanAtomicRawCell_of_mem_generatedNoPrimeBranchingCells
      hBmem with
    ⟨x, hxmem, hxB⟩
  subst B
  have hxenergy :
      rawAtomCodeBranchingDecompositionResidualEnergy x.cell = 0 := by
    rw [← noPrimeBranchingCellOfBooleanAtomicRawCell_energy_eq x]
    exact hBenergy
  exact
    (generatedRawZeroShell_iff_boundedGoldbachPair n bound).mp
      ⟨x, hxmem, hxenergy⟩

/-- THEOREM 2: generated no-prime endpoint shell `0` is exactly the bounded
Goldbach-pair predicate. -/
theorem generatedNoPrimeEndpointZeroShell_iff_boundedGoldbachPair
    (n bound : ℕ) :
    NoPrimeBranchingEndpointShellRealizedUpToGeneratedMax
        (generatedNoPrimeBranchingCells n bound) 0 ↔
      BoundedGoldbachPair n bound := by
  constructor
  · exact boundedGoldbachPair_of_generatedNoPrimeEndpointZeroShell
  · exact generatedNoPrimeEndpointZeroShell_of_boundedGoldbachPair

/-! ## Coverage / Lyapunov throat forces zero-shell production -/

/-- THEOREM 3: generated no-prime endpoint-shell coverage forces a bounded
Goldbach pair whenever its generated maximum includes shell `0`. -/
theorem boundedGoldbachPair_of_noPrimeEndpointShellCoverage
    {n bound : ℕ}
    (hmax : 0 < generatedRawBranchingMaxEnergy n bound)
    (H :
      NoPrimeBranchingEndpointShellCoverageUpToGeneratedMax
        bound (generatedNoPrimeBranchingCells n bound)) :
    BoundedGoldbachPair n bound :=
  (generatedNoPrimeEndpointZeroShell_iff_boundedGoldbachPair n bound).mp
    (H 0 hmax)

/-- THEOREM 4: a generated no-prime Lyapunov/confinement certificate forces a
bounded Goldbach pair whenever its generated maximum includes shell `0`. -/
theorem boundedGoldbachPair_of_generatedNoPrimeLyapunovCertificate
    {n : ℕ}
    (G : SU7GeneratedNoPrimeLyapunovConfinementCertificate n)
    (hmax : 0 < generatedRawBranchingMaxEnergy n G.codeBound) :
    BoundedGoldbachPair n G.codeBound :=
  boundedGoldbachPair_of_noPrimeEndpointShellCoverage hmax
    (noPrimeEndpointShellCoverageUpToGeneratedMax_of_lyapunovCertificate G)

/-- THEOREM 5: the endpoint-shell kernel itself forces the bounded Goldbach
pair at shell `0`, because the kernel returns an actual generated no-prime cell
at that shell. -/
theorem boundedGoldbachPair_of_generatedEndpointShellKernel
    {n bound : ℕ}
    (hmax :
      0 <
        maxNoPrimeBranchingEndpointResidualEnergyOfCells
          (generatedNoPrimeBranchingCells n bound))
    (K :
      NoPrimeBranchingEndpointShellKernel
        (generatedNoPrimeBranchingCells n bound)
        (maxNoPrimeBranchingEndpointResidualEnergyOfCells
          (generatedNoPrimeBranchingCells n bound))) :
    BoundedGoldbachPair n bound :=
  (generatedNoPrimeEndpointZeroShell_iff_boundedGoldbachPair n bound).mp
    ⟨K.shellCell 0 hmax, K.shellCell_mem 0 hmax,
      K.shellCell_energy 0 hmax⟩

/-! ## Certificate -/

/-- P974 certificate: the zero shell of the generated no-prime confinement
throat is exactly bounded Goldbach-pair production. -/
structure SU7NoPrimeZeroShellGoldbachThroatCertificate where
  generated_raw_zero_iff_bounded_pair :
    ∀ n bound : ℕ,
      GeneratedRawEnergyShellRealized n bound 0 ↔
        BoundedGoldbachPair n bound
  generated_no_prime_zero_iff_bounded_pair :
    ∀ n bound : ℕ,
      NoPrimeBranchingEndpointShellRealizedUpToGeneratedMax
          (generatedNoPrimeBranchingCells n bound) 0 ↔
        BoundedGoldbachPair n bound
  coverage_forces_bounded_pair :
    ∀ {n bound : ℕ},
      0 < generatedRawBranchingMaxEnergy n bound ->
        NoPrimeBranchingEndpointShellCoverageUpToGeneratedMax
          bound (generatedNoPrimeBranchingCells n bound) ->
          BoundedGoldbachPair n bound
  lyapunov_forces_bounded_pair :
    ∀ {n : ℕ},
      (G : SU7GeneratedNoPrimeLyapunovConfinementCertificate n) ->
        0 < generatedRawBranchingMaxEnergy n G.codeBound ->
          BoundedGoldbachPair n G.codeBound
  shell_kernel_forces_bounded_pair :
    ∀ {n bound : ℕ},
      0 <
        maxNoPrimeBranchingEndpointResidualEnergyOfCells
          (generatedNoPrimeBranchingCells n bound) ->
        NoPrimeBranchingEndpointShellKernel
          (generatedNoPrimeBranchingCells n bound)
          (maxNoPrimeBranchingEndpointResidualEnergyOfCells
            (generatedNoPrimeBranchingCells n bound)) ->
          BoundedGoldbachPair n bound

/-- Canonical P974 zero-shell throat certificate. -/
def su7NoPrimeZeroShellGoldbachThroatCertificate :
    SU7NoPrimeZeroShellGoldbachThroatCertificate where
  generated_raw_zero_iff_bounded_pair :=
    generatedRawZeroShell_iff_boundedGoldbachPair
  generated_no_prime_zero_iff_bounded_pair :=
    generatedNoPrimeEndpointZeroShell_iff_boundedGoldbachPair
  coverage_forces_bounded_pair := by
    intro n bound hmax H
    exact boundedGoldbachPair_of_noPrimeEndpointShellCoverage hmax H
  lyapunov_forces_bounded_pair := by
    intro n G hmax
    exact boundedGoldbachPair_of_generatedNoPrimeLyapunovCertificate G hmax
  shell_kernel_forces_bounded_pair := by
    intro n bound hmax K
    exact boundedGoldbachPair_of_generatedEndpointShellKernel hmax K


end
end StandardModelConstraint
end SaturationMonoid
