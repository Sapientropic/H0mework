import H0mework.Arithmetic.ShellSources.P901

/-!
# Proposition 902: decomposition-valued topology generates bounded shells

P901 connected P850's trace-zero topology to P900's bounded-shell spine by a
prime-index pullback.  This file pushes one layer lower again: the computed
topology realization can land directly in raw SU(7) branching-decomposition
cells.

The topology still supplies the force: a Poincare-Hopf / Betti / Morse weighted
sum equals the computed nonzero Schubert invariant of `SU(3)/T²`, so a zero or
critical point exists.  But its realization is now

```text
zero point -> SU7BranchingDecompositionCell n
```

plus a proof that the realized cell has zero decomposition residual.  From
there Lean builds the P900 zero-energy bounded shell without passing through
`TraceZeroPrimeEdgeLoop`.
-/

namespace SaturationMonoid
namespace StandardModelConstraint

noncomputable section

open SaturationMonoid.AffineRelaxation

set_option linter.defProp false

/-! ## Zero decomposition cells generate zero-energy bounded shells -/

/-- A zero decomposition-residual cell generates a zero-energy bounded
branching shell. -/
def branchingBoundedEnergyShell_of_zeroDecompositionCell
    {n : ℕ} (Z : SU7BranchingDecompositionCell n)
    (hzero : branchingDecompositionResidual Z = 0) :
    SU7BranchingBoundedEnergyShell n where
  spectrum := { cells := [Z] }
  startCell := Z
  start_mem := by simp
  maxEnergy := 0
  energy_bound := by
    intro C hmem
    simp at hmem
    subst C
    unfold branchingDecompositionResidualEnergy
    rw [hzero]
    rfl
  lowerEnergyCell := by
    intro e hpos hle
    omega
  lowerEnergyCell_mem := by
    intro e hpos hle
    omega
  lowerEnergyCell_energy_eq_pred := by
    intro e hpos hle
    omega

/-- THEOREM 1: the zero-cell shell has the P900 fixed-point law. -/
theorem zeroDecompositionCell_shell_fixed_iff_residual_zero
    {n : ℕ} (Z : SU7BranchingDecompositionCell n)
    (hzero : branchingDecompositionResidual Z = 0)
    (C : SU7BranchingDecompositionCell n)
    (hmem :
      C ∈
        (branchingBoundedEnergyShell_of_zeroDecompositionCell
          Z hzero).spectrum.cells) :
    branchingBoundedEnergyShellNormalize
        (branchingBoundedEnergyShell_of_zeroDecompositionCell Z hzero) C =
        C ↔
      branchingDecompositionResidual C = 0 :=
  branchingBoundedEnergyShell_fixed_iff_residual_zero
    (branchingBoundedEnergyShell_of_zeroDecompositionCell Z hzero) C hmem

/-! ## Decomposition-valued computed topology -/

/-- Poincare-Hopf data whose realization lands directly in a raw SU(7)
branching-decomposition cell. -/
structure ColorLoopDecompositionPoincareHopfIndexData (n : ℕ) where
  ZeroPoint : Type
  zeroPoints : List ZeroPoint
  localIndex : ZeroPoint -> ℤ
  poincareHopf :
    (zeroPoints.map localIndex).sum =
      SU3FlagSchubertCell.eulerCharacteristic
  realizeZero : ZeroPoint -> SU7BranchingDecompositionCell n
  realizeZero_residual_zero :
    ∀ z : ZeroPoint,
      branchingDecompositionResidual (realizeZero z) = 0

/-- Homology data whose basis realization lands directly in raw SU(7)
branching-decomposition cells. -/
structure ColorLoopDecompositionBettiHomologyData (n : ℕ) where
  HomologyClass : Type
  basis : List HomologyClass
  bettiWeight : HomologyClass -> ℤ
  bettiIndex :
    (basis.map bettiWeight).sum =
      SU3FlagSchubertCell.bettiTotal
  realizeClass : HomologyClass -> SU7BranchingDecompositionCell n
  realizeClass_residual_zero :
    ∀ h : HomologyClass,
      branchingDecompositionResidual (realizeClass h) = 0

/-- Morse data whose critical-point realization lands directly in raw SU(7)
branching-decomposition cells. -/
structure ColorLoopDecompositionMorseIndexData (n : ℕ) where
  CriticalPoint : Type
  criticalPoints : List CriticalPoint
  morseIndex : CriticalPoint -> ℤ
  morseIndexFormula :
    (criticalPoints.map morseIndex).sum =
      SU3FlagSchubertCell.eulerCharacteristic
  realizeCritical : CriticalPoint -> SU7BranchingDecompositionCell n
  realizeCritical_residual_zero :
    ∀ c : CriticalPoint,
      branchingDecompositionResidual (realizeCritical c) = 0

/-- The three computed-topology doors with decomposition-valued
realization. -/
inductive ColorLoopDecompositionComputedOrbitTopology
    (n : ℕ) : Type 2
  | poincareHopf :
      ColorLoopDecompositionPoincareHopfIndexData n ->
        ColorLoopDecompositionComputedOrbitTopology n
  | betti :
      ColorLoopDecompositionBettiHomologyData n ->
        ColorLoopDecompositionComputedOrbitTopology n
  | morse :
      ColorLoopDecompositionMorseIndexData n ->
        ColorLoopDecompositionComputedOrbitTopology n

/-! ## Nonzero topology forces a zero decomposition cell -/

/-- THEOREM 2: Poincare-Hopf data forces a realized zero decomposition
cell. -/
theorem zeroDecompositionCell_of_poincareHopfData
    {n : ℕ} (P : ColorLoopDecompositionPoincareHopfIndexData n) :
    ∃ Z : SU7BranchingDecompositionCell n,
      branchingDecompositionResidual Z = 0 := by
  have hsum :
      (P.zeroPoints.map P.localIndex).sum ≠ 0 := by
    rw [P.poincareHopf]
    exact SU3FlagSchubertCell.eulerCharacteristic_ne_zero
  rcases exists_mem_of_list_sum_ne_zero (xs := P.zeroPoints)
      (w := P.localIndex) hsum with ⟨z, _hz⟩
  exact ⟨P.realizeZero z, P.realizeZero_residual_zero z⟩

/-- THEOREM 3: Betti data forces a realized zero decomposition cell. -/
theorem zeroDecompositionCell_of_bettiData
    {n : ℕ} (B : ColorLoopDecompositionBettiHomologyData n) :
    ∃ Z : SU7BranchingDecompositionCell n,
      branchingDecompositionResidual Z = 0 := by
  have hsum :
      (B.basis.map B.bettiWeight).sum ≠ 0 := by
    rw [B.bettiIndex]
    exact SU3FlagSchubertCell.bettiTotal_ne_zero
  rcases exists_mem_of_list_sum_ne_zero (xs := B.basis)
      (w := B.bettiWeight) hsum with ⟨z, _hz⟩
  exact ⟨B.realizeClass z, B.realizeClass_residual_zero z⟩

/-- THEOREM 4: Morse data forces a realized zero decomposition cell. -/
theorem zeroDecompositionCell_of_morseData
    {n : ℕ} (M : ColorLoopDecompositionMorseIndexData n) :
    ∃ Z : SU7BranchingDecompositionCell n,
      branchingDecompositionResidual Z = 0 := by
  have hsum :
      (M.criticalPoints.map M.morseIndex).sum ≠ 0 := by
    rw [M.morseIndexFormula]
    exact SU3FlagSchubertCell.eulerCharacteristic_ne_zero
  rcases exists_mem_of_list_sum_ne_zero (xs := M.criticalPoints)
      (w := M.morseIndex) hsum with ⟨z, _hz⟩
  exact ⟨M.realizeCritical z, M.realizeCritical_residual_zero z⟩

/-- THEOREM 5: any decomposition-valued computed topology produces a zero
decomposition cell. -/
def zeroDecompositionCell_of_decompositionComputedTopology
    {n : ℕ} :
    ColorLoopDecompositionComputedOrbitTopology n ->
      { Z : SU7BranchingDecompositionCell n //
        branchingDecompositionResidual Z = 0 }
  | .poincareHopf P =>
      let h := zeroDecompositionCell_of_poincareHopfData P
      ⟨Classical.choose h, Classical.choose_spec h⟩
  | .betti B =>
      let h := zeroDecompositionCell_of_bettiData B
      ⟨Classical.choose h, Classical.choose_spec h⟩
  | .morse M =>
      let h := zeroDecompositionCell_of_morseData M
      ⟨Classical.choose h, Classical.choose_spec h⟩

/-- THEOREM 6: decomposition-valued computed topology produces a bounded
energy shell directly. -/
def branchingBoundedEnergyShell_of_decompositionComputedTopology
    {n : ℕ} (H : ColorLoopDecompositionComputedOrbitTopology n) :
    SU7BranchingBoundedEnergyShell n :=
  let Z := zeroDecompositionCell_of_decompositionComputedTopology H
  branchingBoundedEnergyShell_of_zeroDecompositionCell Z.1 Z.2

/-! ## Fiberwise decomposition-valued topology -/

/-- Every even fiber carries decomposition-valued computed orbit topology. -/
def ColorLoopDecompositionComputedOrbitTopologyEveryEvenFiber : Prop :=
  ∀ n : ℕ, 2 ≤ n ->
    Nonempty (ColorLoopDecompositionComputedOrbitTopology n)

/-- THEOREM 7: decomposition-valued computed topology generates bounded
energy shells on every even fiber. -/
theorem boundedEnergyShellsEveryEvenFiber_of_decompositionComputedTopology
    (H : ColorLoopDecompositionComputedOrbitTopologyEveryEvenFiber) :
    SU7BranchingBoundedEnergyShellEveryEvenFiber := by
  intro n hn
  exact ⟨branchingBoundedEnergyShell_of_decompositionComputedTopology
    (Classical.choice (H n hn))⟩

/-- Decomposition-valued computed topology confinement data. -/
structure SU7DecompositionComputedTopologyConfinement where
  compact_gauge_orbit : SU7CompactGaugeOrbit
  lyapunov_residual_dissipation : SU7LyapunovResidualDissipation
  quantized_spectrum_no_escaping_boundary :
    SU7QuantizedSpectrumNoEscapingBoundary
  incidence_schedule_no_free :
    RunningSigmaBeta.SU7IncidenceScheduleNoFreeCertificate
  decomposition_topology :
    ColorLoopDecompositionComputedOrbitTopologyEveryEvenFiber

/-- THEOREM 8: decomposition-valued computed topology generates P900
bounded-shell confinement. -/
def branchingBoundedEnergyShellConfinement_of_decompositionComputedTopology
    (D : SU7DecompositionComputedTopologyConfinement) :
    SU7BranchingBoundedEnergyShellConfinement where
  compact_gauge_orbit := D.compact_gauge_orbit
  lyapunov_residual_dissipation := D.lyapunov_residual_dissipation
  quantized_spectrum_no_escaping_boundary :=
    D.quantized_spectrum_no_escaping_boundary
  incidence_schedule_no_free := D.incidence_schedule_no_free
  bounded_energy_shells :=
    boundedEnergyShellsEveryEvenFiber_of_decompositionComputedTopology
      D.decomposition_topology

/-- THEOREM 9: decomposition-valued computed topology reaches ordinary
even Goldbach through P900's bounded-shell spine. -/
theorem evenGoldbach_of_decompositionComputedTopologyConfinement
    (D : SU7DecompositionComputedTopologyConfinement) :
    EvenGoldbachStatement :=
  evenGoldbach_of_branchingBoundedEnergyShellConfinement
    (branchingBoundedEnergyShellConfinement_of_decompositionComputedTopology D)

/-! ## Certificate -/

/-- P902 certificate: computed topology can realize directly into raw
branching-decomposition cells and then into P900 bounded shells. -/
structure SU7DecompositionTopologyBoundedShellCertificate where
  zero_cell_to_bounded_shell :
    ∀ {n : ℕ} (Z : SU7BranchingDecompositionCell n),
      branchingDecompositionResidual Z = 0 ->
        SU7BranchingBoundedEnergyShell n
  topology_to_zero_cell :
    ∀ {n : ℕ}, ColorLoopDecompositionComputedOrbitTopology n ->
      { Z : SU7BranchingDecompositionCell n //
        branchingDecompositionResidual Z = 0 }
  topology_to_bounded_shell :
    ∀ {n : ℕ}, ColorLoopDecompositionComputedOrbitTopology n ->
      SU7BranchingBoundedEnergyShell n
  fiberwise_topology_to_bounded_shells :
    ColorLoopDecompositionComputedOrbitTopologyEveryEvenFiber ->
      SU7BranchingBoundedEnergyShellEveryEvenFiber
  topology_confinement_to_goldbach :
    SU7DecompositionComputedTopologyConfinement -> EvenGoldbachStatement

def su7DecompositionTopologyBoundedShellCertificate :
    SU7DecompositionTopologyBoundedShellCertificate where
  zero_cell_to_bounded_shell :=
    branchingBoundedEnergyShell_of_zeroDecompositionCell
  topology_to_zero_cell :=
    zeroDecompositionCell_of_decompositionComputedTopology
  topology_to_bounded_shell :=
    branchingBoundedEnergyShell_of_decompositionComputedTopology
  fiberwise_topology_to_bounded_shells :=
    boundedEnergyShellsEveryEvenFiber_of_decompositionComputedTopology
  topology_confinement_to_goldbach :=
    evenGoldbach_of_decompositionComputedTopologyConfinement


end
end StandardModelConstraint
end SaturationMonoid
