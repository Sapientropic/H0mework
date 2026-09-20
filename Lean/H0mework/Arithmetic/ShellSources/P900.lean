import H0mework.Physics.BranchSources.P899

/-!
# Proposition 900: bounded energy shells generate branching normalizers

P899 used an unbounded energy ladder: for every positive natural number `e`,
it asked for a same-spectrum representative at energy `e - 1`.  That is clean
as algebra, but too strong for a genuinely finite SU(7) branching spectrum.

This file tightens the producer interface.  A bounded energy shell only needs:

* a finite decomposition spectrum;
* a maximum residual-energy bound for cells in that spectrum;
* a predecessor representative for every positive energy level that can
  actually occur below that bound.

The normalizer is still computed, not stored.  On spectrum cells, it reads the
current residual-energy value `e`, uses the bounded-shell witness `e ≤ max`, and
moves to the representative at energy `e - 1`.  Outside the spectrum it is
irrelevant and left inert.

This is the finite-spectrum form of the no-escaping-boundary route:

```text
finite quantized residual-energy shell
-> actual energy e has bound e ≤ maxEnergy
-> predecessor representative e - 1
-> generated normalizer
-> P898/P897/P896 no-permanent-holonomy spine
```
-/

namespace SaturationMonoid
namespace StandardModelConstraint

noncomputable section

open SaturationMonoid.AffineRelaxation

set_option linter.defProp false

/-! ## Bounded quantized energy shells -/

/-- A finite SU(7) branching-decomposition spectrum with a bounded residual
energy shell.

Unlike P899's unbounded ladder, the predecessor cell is required only for
energy values `e` that lie below `maxEnergy`.  The bound is supplied by the
finite spectrum itself, which is the Lean shape of "quantized spectrum has no
escaping boundary". -/
structure SU7BranchingBoundedEnergyShell (n : ℕ) where
  spectrum : SU7BranchingDecompositionSpectrum n
  startCell : SU7BranchingDecompositionCell n
  start_mem : startCell ∈ spectrum.cells
  maxEnergy : ℕ
  energy_bound :
    ∀ C : SU7BranchingDecompositionCell n,
      C ∈ spectrum.cells ->
        branchingDecompositionResidualEnergy C ≤ maxEnergy
  lowerEnergyCell :
    (e : ℕ) -> 0 < e -> e ≤ maxEnergy ->
      SU7BranchingDecompositionCell n
  lowerEnergyCell_mem :
    ∀ (e : ℕ) (hpos : 0 < e) (hle : e ≤ maxEnergy),
      lowerEnergyCell e hpos hle ∈ spectrum.cells
  lowerEnergyCell_energy_eq_pred :
    ∀ (e : ℕ) (hpos : 0 < e) (hle : e ≤ maxEnergy),
      branchingDecompositionResidualEnergy
          (lowerEnergyCell e hpos hle) = e - 1

/-- The normalizer computed from a bounded energy shell.

For cells in the shell, the nonzero branch can use the shell's energy bound to
select the predecessor representative.  Cells outside the shell are inert; the
P898 normalizer laws are only required on active shell members. -/
def branchingBoundedEnergyShellNormalize
    {n : ℕ} (L : SU7BranchingBoundedEnergyShell n)
    (C : SU7BranchingDecompositionCell n) :
    SU7BranchingDecompositionCell n :=
  if hzero : branchingDecompositionResidual C = 0 then
    C
  else
    if hmem : C ∈ L.spectrum.cells then
      L.lowerEnergyCell
        (branchingDecompositionResidualEnergy C)
        (branchingDecompositionResidualEnergy_pos_of_nonzero C hzero)
        (L.energy_bound C hmem)
    else
      C

/-- THEOREM 1: bounded-shell normalization preserves spectrum membership on
active spectrum cells. -/
theorem branchingBoundedEnergyShellNormalize_mem_preserves
    {n : ℕ} (L : SU7BranchingBoundedEnergyShell n)
    (C : SU7BranchingDecompositionCell n)
    (hmem : C ∈ L.spectrum.cells) :
    branchingBoundedEnergyShellNormalize L C ∈ L.spectrum.cells := by
  by_cases hzero : branchingDecompositionResidual C = 0
  · simp [branchingBoundedEnergyShellNormalize, hzero, hmem]
  · have hpos :
        0 < branchingDecompositionResidualEnergy C :=
      branchingDecompositionResidualEnergy_pos_of_nonzero C hzero
    have hle :
        branchingDecompositionResidualEnergy C ≤ L.maxEnergy :=
      L.energy_bound C hmem
    simp [branchingBoundedEnergyShellNormalize, hzero, hmem,
      L.lowerEnergyCell_mem _ hpos hle]

/-- THEOREM 2: bounded-shell normalization strictly lowers nonzero residual
energy on active spectrum cells. -/
theorem branchingBoundedEnergyShellNormalize_strictly_decreases_nonzero
    {n : ℕ} (L : SU7BranchingBoundedEnergyShell n)
    (C : SU7BranchingDecompositionCell n)
    (hmem : C ∈ L.spectrum.cells)
    (hnonzero : branchingDecompositionResidual C ≠ 0) :
    branchingDecompositionResidualEnergy
        (branchingBoundedEnergyShellNormalize L C) <
      branchingDecompositionResidualEnergy C := by
  have hpos :
      0 < branchingDecompositionResidualEnergy C :=
    branchingDecompositionResidualEnergy_pos_of_nonzero C hnonzero
  have hle :
      branchingDecompositionResidualEnergy C ≤ L.maxEnergy :=
    L.energy_bound C hmem
  have henergy :
      branchingDecompositionResidualEnergy
          (branchingBoundedEnergyShellNormalize L C) =
        branchingDecompositionResidualEnergy C - 1 := by
    simp [branchingBoundedEnergyShellNormalize, hnonzero, hmem,
      L.lowerEnergyCell_energy_eq_pred _ hpos hle]
  omega

/-- THEOREM 3: zero residual cells are fixed by bounded-shell
normalization. -/
theorem branchingBoundedEnergyShellNormalize_fixed_of_zero
    {n : ℕ} (L : SU7BranchingBoundedEnergyShell n)
    (C : SU7BranchingDecompositionCell n)
    (_hmem : C ∈ L.spectrum.cells)
    (hzero : branchingDecompositionResidual C = 0) :
    branchingBoundedEnergyShellNormalize L C = C := by
  simp [branchingBoundedEnergyShellNormalize, hzero]

/-- THEOREM 4: a bounded energy shell generates P898's branching
normalizer. -/
def branchingNormalizer_of_boundedEnergyShell
    {n : ℕ} (L : SU7BranchingBoundedEnergyShell n) :
    SU7BranchingDecompositionNormalizer n where
  spectrum := L.spectrum
  startCell := L.startCell
  start_mem := L.start_mem
  normalize := branchingBoundedEnergyShellNormalize L
  normalize_mem_preserves :=
    branchingBoundedEnergyShellNormalize_mem_preserves L
  normalize_strictly_decreases_nonzero :=
    branchingBoundedEnergyShellNormalize_strictly_decreases_nonzero L
  normalize_fixed_of_zero :=
    branchingBoundedEnergyShellNormalize_fixed_of_zero L

/-- THEOREM 5: a bounded energy shell inherits P898's fixed-point law. -/
theorem branchingBoundedEnergyShell_fixed_iff_residual_zero
    {n : ℕ} (L : SU7BranchingBoundedEnergyShell n)
    (C : SU7BranchingDecompositionCell n)
    (hmem : C ∈ L.spectrum.cells) :
    branchingBoundedEnergyShellNormalize L C = C ↔
      branchingDecompositionResidual C = 0 :=
  branchingNormalizer_fixed_iff_residual_zero
    (branchingNormalizer_of_boundedEnergyShell L) C hmem

/-- THEOREM 6: a bounded energy shell produces a zero decomposition-residual
cell through the P900 -> P898 -> P897 spine. -/
theorem exists_zeroCell_of_branchingBoundedEnergyShell
    {n : ℕ} (L : SU7BranchingBoundedEnergyShell n) :
    ∃ Z : SU7BranchingDecompositionCell n,
      Z ∈ L.spectrum.cells ∧
        branchingDecompositionResidual Z = 0 :=
  exists_zeroCell_of_branchingNormalizer
    (branchingNormalizer_of_boundedEnergyShell L)

/-- THEOREM 7: a bounded energy shell forbids permanent decomposition
holonomy. -/
theorem branchingBoundedEnergyShell_forbidsPermanentHolonomy
    {n : ℕ} (L : SU7BranchingBoundedEnergyShell n) :
    SU7BranchingDecompositionSpectrumForbidsPermanentHolonomy
      L.spectrum :=
  branchingNormalizer_forbidsPermanentHolonomy
    (branchingNormalizer_of_boundedEnergyShell L)

/-! ## Fiberwise bounded-shell confinement -/

/-- Every even fiber carries a bounded quantized energy shell. -/
def SU7BranchingBoundedEnergyShellEveryEvenFiber : Prop :=
  ∀ n : ℕ, 2 ≤ n ->
    Nonempty (SU7BranchingBoundedEnergyShell n)

/-- THEOREM 8: fiberwise bounded shells generate P898 normalizers on every
even fiber. -/
theorem normalizersEveryEvenFiber_of_boundedEnergyShells
    (H : SU7BranchingBoundedEnergyShellEveryEvenFiber) :
    SU7BranchingDecompositionNormalizerEveryEvenFiber := by
  intro n hn
  let L : SU7BranchingBoundedEnergyShell n :=
    Classical.choice (H n hn)
  exact ⟨branchingNormalizer_of_boundedEnergyShell L⟩

/-- Physical bounded-shell confinement data.  This is the finite-spectrum
version of P899's ladder confinement: every active residual energy is bounded
inside the same SU(7) branch shell and has a predecessor representative. -/
structure SU7BranchingBoundedEnergyShellConfinement where
  compact_gauge_orbit : SU7CompactGaugeOrbit
  lyapunov_residual_dissipation : SU7LyapunovResidualDissipation
  quantized_spectrum_no_escaping_boundary :
    SU7QuantizedSpectrumNoEscapingBoundary
  incidence_schedule_no_free :
    RunningSigmaBeta.SU7IncidenceScheduleNoFreeCertificate
  bounded_energy_shells : SU7BranchingBoundedEnergyShellEveryEvenFiber

/-- THEOREM 9: bounded-shell confinement generates P898 normalizer
confinement. -/
def branchingNormalizerConfinement_of_boundedEnergyShellConfinement
    (D : SU7BranchingBoundedEnergyShellConfinement) :
    SU7BranchingNormalizerConfinement where
  compact_gauge_orbit := D.compact_gauge_orbit
  lyapunov_residual_dissipation := D.lyapunov_residual_dissipation
  quantized_spectrum_no_escaping_boundary :=
    D.quantized_spectrum_no_escaping_boundary
  incidence_schedule_no_free := D.incidence_schedule_no_free
  normalizers :=
    normalizersEveryEvenFiber_of_boundedEnergyShells
      D.bounded_energy_shells

/-- THEOREM 10: bounded-shell confinement computes trace-zero prime-edge
loops on every even fiber. -/
def traceZeroPrimeEdgeLoopEveryEvenFiber_of_boundedEnergyShellConfinement
    (D : SU7BranchingBoundedEnergyShellConfinement) :
    ∀ n : ℕ, 2 ≤ n -> TraceZeroPrimeEdgeLoop n :=
  traceZeroPrimeEdgeLoopEveryEvenFiber_of_branchingNormalizerConfinement
    (branchingNormalizerConfinement_of_boundedEnergyShellConfinement D)

/-- THEOREM 11: bounded-shell confinement gives ordinary even Goldbach through
the non-storing branch-decomposition projection chain. -/
theorem evenGoldbach_of_branchingBoundedEnergyShellConfinement
    (D : SU7BranchingBoundedEnergyShellConfinement) :
    EvenGoldbachStatement :=
  evenGoldbach_of_branchingNormalizerConfinement
    (branchingNormalizerConfinement_of_boundedEnergyShellConfinement D)

/-! ## Certificate -/

/-- P900 certificate: finite bounded energy shells generate the normalizer and
downstream no-gap spine. -/
structure SU7BranchingBoundedEnergyShellProducerCertificate where
  bounded_shell_to_normalizer :
    ∀ {n : ℕ}, SU7BranchingBoundedEnergyShell n ->
      SU7BranchingDecompositionNormalizer n
  bounded_shell_fixed_iff_residual_zero :
    ∀ {n : ℕ} (L : SU7BranchingBoundedEnergyShell n)
      (C : SU7BranchingDecompositionCell n),
      C ∈ L.spectrum.cells ->
        (branchingBoundedEnergyShellNormalize L C = C ↔
          branchingDecompositionResidual C = 0)
  bounded_shell_to_zero_cell :
    ∀ {n : ℕ} (L : SU7BranchingBoundedEnergyShell n),
      ∃ Z : SU7BranchingDecompositionCell n,
        Z ∈ L.spectrum.cells ∧
          branchingDecompositionResidual Z = 0
  bounded_shell_forbids_permanent_holonomy :
    ∀ {n : ℕ} (L : SU7BranchingBoundedEnergyShell n),
      SU7BranchingDecompositionSpectrumForbidsPermanentHolonomy L.spectrum
  bounded_shell_confinement_to_goldbach :
    SU7BranchingBoundedEnergyShellConfinement -> EvenGoldbachStatement

def su7BranchingBoundedEnergyShellProducerCertificate :
    SU7BranchingBoundedEnergyShellProducerCertificate where
  bounded_shell_to_normalizer :=
    branchingNormalizer_of_boundedEnergyShell
  bounded_shell_fixed_iff_residual_zero :=
    branchingBoundedEnergyShell_fixed_iff_residual_zero
  bounded_shell_to_zero_cell :=
    exists_zeroCell_of_branchingBoundedEnergyShell
  bounded_shell_forbids_permanent_holonomy :=
    branchingBoundedEnergyShell_forbidsPermanentHolonomy
  bounded_shell_confinement_to_goldbach :=
    evenGoldbach_of_branchingBoundedEnergyShellConfinement


end
end StandardModelConstraint
end SaturationMonoid
