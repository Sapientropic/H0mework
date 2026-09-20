import H0mework.Physics.BranchSources.P909

/-!
# Proposition 910: raw branching filters generate tensor bounded shells

P909 consumes a `SU7TensorIrreducibleBoundedEnergyShell`.  This file lowers
that shell one step toward the actual SU(7) branching data.

The input is a bounded shell of raw branching-decomposition cells, measured by
`rawAtomCodeBranchingDecompositionResidual` from P903, plus a tensor
irreducibility filter for the two endpoint codes.  No prime fields and no
trace-zero loop are stored.  The filter lifts every raw branching cell to a
tensor-irreducible cell with the same raw residual, hence produces the P908
bounded tensor shell and the P909 physical-branch-cell readout.
-/

namespace SaturationMonoid
namespace StandardModelConstraint

noncomputable section

open SaturationMonoid.AffineRelaxation
open RunningSigmaBeta

set_option linter.defProp false

/-! ## Raw atom-code residual energy on branching cells -/

/-- Residual energy of a branching-decomposition cell measured by raw
`atomCode`, not by the older canonical prime-coded readout. -/
def rawAtomCodeBranchingDecompositionResidualEnergy
    {n : ℕ} (c : SU7BranchingDecompositionCell n) : ℕ :=
  Int.natAbs (rawAtomCodeBranchingDecompositionResidual c)

/-- Zero raw atom-code residual energy is exactly zero raw atom-code residual.
-/
theorem rawAtomCodeBranchingDecompositionResidualEnergy_eq_zero_iff
    {n : ℕ} (c : SU7BranchingDecompositionCell n) :
    rawAtomCodeBranchingDecompositionResidualEnergy c = 0 ↔
      rawAtomCodeBranchingDecompositionResidual c = 0 := by
  unfold rawAtomCodeBranchingDecompositionResidualEnergy
  rw [Int.natAbs_eq_zero]

/-- Nonzero raw atom-code residual has positive raw residual energy. -/
theorem rawAtomCodeBranchingDecompositionResidualEnergy_pos_of_nonzero
    {n : ℕ} (c : SU7BranchingDecompositionCell n)
    (hnonzero : rawAtomCodeBranchingDecompositionResidual c ≠ 0) :
    0 < rawAtomCodeBranchingDecompositionResidualEnergy c := by
  apply Nat.pos_of_ne_zero
  intro henergy
  exact hnonzero
    ((rawAtomCodeBranchingDecompositionResidualEnergy_eq_zero_iff c).mp
      henergy)

/-! ## Tensor lift of raw branching-decomposition cells -/

/-- Tensor irreducibility filter for raw branching-decomposition endpoint
codes in one fiber.

This is a representation-theoretic filter: it contains tensor irreducibility of
the raw endpoint codes, not `Nat.Prime` and not a Goldbach pair. -/
structure SU7BranchingTensorIrreducibilityFilter
    (C : SU7WeightTensorCoding) (n : ℕ) where
  left_tensor_irreducible :
    ∀ c : SU7BranchingDecompositionCell n,
      SU7TensorIrreducible C { code := c.leftWeightCode }
  right_tensor_irreducible :
    ∀ c : SU7BranchingDecompositionCell n,
      SU7TensorIrreducible C { code := c.rightWeightCode }

/-- Lift a raw branching-decomposition cell to a tensor-irreducible cell by
applying the endpoint-code irreducibility filter. -/
def tensorIrreducibleCell_of_rawBranchingDecompositionCell
    {C : SU7WeightTensorCoding} {n : ℕ}
    (F : SU7BranchingTensorIrreducibilityFilter C n)
    (c : SU7BranchingDecompositionCell n) :
    SU7TensorIrreducibleBranchingSpectrumCell C n where
  branch := c.branch
  leftAtom :=
    { weight := { code := c.leftWeightCode }
      tensor_irreducible := F.left_tensor_irreducible c
      sector := sectorOfSU7CarrierBlock
        (SU7BlockIncidence.endpoints c.incidence).1 }
  rightAtom :=
    { weight := { code := c.rightWeightCode }
      tensor_irreducible := F.right_tensor_irreducible c
      sector := sectorOfSU7CarrierBlock
        (SU7BlockIncidence.endpoints c.incidence).2 }

/-- The tensor lift preserves the raw atom-code residual exactly. -/
theorem tensorIrreducibleCell_rawResidual_eq
    {C : SU7WeightTensorCoding} {n : ℕ}
    (F : SU7BranchingTensorIrreducibilityFilter C n)
    (c : SU7BranchingDecompositionCell n) :
    tensorIrreducibleBranchingSpectrumResidual
        (tensorIrreducibleCell_of_rawBranchingDecompositionCell F c) =
      rawAtomCodeBranchingDecompositionResidual c := by
  rfl

/-- The tensor lift preserves raw residual energy exactly. -/
theorem tensorIrreducibleCell_rawResidualEnergy_eq
    {C : SU7WeightTensorCoding} {n : ℕ}
    (F : SU7BranchingTensorIrreducibilityFilter C n)
    (c : SU7BranchingDecompositionCell n) :
    tensorIrreducibleBranchingSpectrumResidualEnergy
        (tensorIrreducibleCell_of_rawBranchingDecompositionCell F c) =
      rawAtomCodeBranchingDecompositionResidualEnergy c := by
  unfold tensorIrreducibleBranchingSpectrumResidualEnergy
    rawAtomCodeBranchingDecompositionResidualEnergy
  rw [tensorIrreducibleCell_rawResidual_eq F c]

/-! ## Raw bounded shells -/

/-- A bounded raw atom-code branching shell.

It is the raw-code analogue of P908's bounded tensor shell.  The shell carries
only branching-decomposition cells, a raw residual-energy bound, predecessor
representatives, and a tensor irreducibility filter for endpoint codes. -/
structure SU7RawBranchingTensorFilteredBoundedEnergyShell
    (C : SU7WeightTensorCoding) (n : ℕ) where
  spectrum : SU7BranchingDecompositionSpectrum n
  startCell : SU7BranchingDecompositionCell n
  start_mem : startCell ∈ spectrum.cells
  tensor_filter : SU7BranchingTensorIrreducibilityFilter C n
  maxEnergy : ℕ
  energy_bound :
    ∀ c : SU7BranchingDecompositionCell n,
      c ∈ spectrum.cells ->
        rawAtomCodeBranchingDecompositionResidualEnergy c ≤ maxEnergy
  lowerEnergyCell :
    (e : ℕ) -> 0 < e -> e ≤ maxEnergy ->
      SU7BranchingDecompositionCell n
  lowerEnergyCell_mem :
    ∀ (e : ℕ) (hpos : 0 < e) (hle : e ≤ maxEnergy),
      lowerEnergyCell e hpos hle ∈ spectrum.cells
  lowerEnergyCell_rawEnergy_eq_pred :
    ∀ (e : ℕ) (hpos : 0 < e) (hle : e ≤ maxEnergy),
      rawAtomCodeBranchingDecompositionResidualEnergy
          (lowerEnergyCell e hpos hle) = e - 1

/-- Tensor spectrum generated from a raw branching shell by the tensor
irreducibility filter. -/
def tensorSpectrum_of_rawBranchingShell
    {C : SU7WeightTensorCoding} {n : ℕ}
    (L : SU7RawBranchingTensorFilteredBoundedEnergyShell C n) :
    SU7TensorIrreducibleBranchingSpectrum C n where
  cells :=
    L.spectrum.cells.map
      (tensorIrreducibleCell_of_rawBranchingDecompositionCell
        L.tensor_filter)
  representationWeight := fun _ => 1

/-- The lifted start cell is a member of the generated tensor spectrum. -/
theorem tensorStart_mem_of_rawBranchingShell
    {C : SU7WeightTensorCoding} {n : ℕ}
    (L : SU7RawBranchingTensorFilteredBoundedEnergyShell C n) :
    tensorIrreducibleCell_of_rawBranchingDecompositionCell
        L.tensor_filter L.startCell ∈
      (tensorSpectrum_of_rawBranchingShell L).cells := by
  unfold tensorSpectrum_of_rawBranchingShell
  exact List.mem_map.mpr ⟨L.startCell, L.start_mem, rfl⟩

/-- Membership in the generated tensor spectrum gives an underlying raw
branching cell. -/
theorem exists_rawCell_of_mem_tensorSpectrum
    {C : SU7WeightTensorCoding} {n : ℕ}
    (L : SU7RawBranchingTensorFilteredBoundedEnergyShell C n)
    {B : SU7TensorIrreducibleBranchingSpectrumCell C n}
    (hB : B ∈ (tensorSpectrum_of_rawBranchingShell L).cells) :
    ∃ c : SU7BranchingDecompositionCell n,
      c ∈ L.spectrum.cells ∧
        B =
          tensorIrreducibleCell_of_rawBranchingDecompositionCell
            L.tensor_filter c := by
  unfold tensorSpectrum_of_rawBranchingShell at hB
  rcases List.mem_map.mp hB with ⟨c, hc, hBc⟩
  exact ⟨c, hc, hBc.symm⟩

/-- A raw branching shell generates P908's bounded tensor energy shell. -/
def tensorIrreducibleBoundedEnergyShell_of_rawBranchingShell
    {C : SU7WeightTensorCoding} {n : ℕ}
    (L : SU7RawBranchingTensorFilteredBoundedEnergyShell C n) :
    SU7TensorIrreducibleBoundedEnergyShell C n where
  spectrum := tensorSpectrum_of_rawBranchingShell L
  startCell :=
    tensorIrreducibleCell_of_rawBranchingDecompositionCell
      L.tensor_filter L.startCell
  start_mem := tensorStart_mem_of_rawBranchingShell L
  start_weight_positive := Nat.zero_lt_one
  maxEnergy := L.maxEnergy
  energy_bound := by
    intro B hB
    rcases exists_rawCell_of_mem_tensorSpectrum L hB with
      ⟨c, hc, hBc⟩
    rw [hBc, tensorIrreducibleCell_rawResidualEnergy_eq]
    exact L.energy_bound c hc
  lowerEnergyCell := by
    intro e hpos hle
    exact
      tensorIrreducibleCell_of_rawBranchingDecompositionCell
        L.tensor_filter
        (L.lowerEnergyCell e hpos hle)
  lowerEnergyCell_mem := by
    intro e hpos hle
    unfold tensorSpectrum_of_rawBranchingShell
    exact List.mem_map.mpr
      ⟨L.lowerEnergyCell e hpos hle,
        L.lowerEnergyCell_mem e hpos hle, rfl⟩
  lowerEnergyCell_weight_positive := by
    intro _ _ _
    exact Nat.zero_lt_one
  lowerEnergyCell_energy_eq_pred := by
    intro e hpos hle
    rw [tensorIrreducibleCell_rawResidualEnergy_eq]
    exact L.lowerEnergyCell_rawEnergy_eq_pred e hpos hle

/-- A raw branching shell computes a generated physical zero branch cell
through P910 -> P908 -> P909. -/
def generatedPhysicalZeroBranchCell_of_rawBranchingShell
    {C : SU7WeightTensorCoding} {n : ℕ}
    (L : SU7RawBranchingTensorFilteredBoundedEnergyShell C n) :
    SU7GeneratedPhysicalZeroBranchCell n :=
  generatedPhysicalZeroBranchCell_of_tensorIrreducibleBoundedEnergyShell
    (tensorIrreducibleBoundedEnergyShell_of_rawBranchingShell L)

/-- A raw branching shell computes a trace-zero prime-edge loop through the
non-storing physical branch-cell projection. -/
def traceZeroPrimeEdgeLoop_of_rawBranchingShell
    {C : SU7WeightTensorCoding} {n : ℕ}
    (L : SU7RawBranchingTensorFilteredBoundedEnergyShell C n) :
    TraceZeroPrimeEdgeLoop n :=
  traceZeroPrimeEdgeLoop_of_generatedPhysicalZeroBranchCell
    (generatedPhysicalZeroBranchCell_of_rawBranchingShell L)

/-! ## Fiberwise raw shell producer -/

/-- Every even fiber carries a raw tensor-filtered branching bounded shell. -/
def SU7RawBranchingTensorFilteredBoundedEnergyShellEveryEvenFiber
    (C : SU7WeightTensorCoding) : Prop :=
  ∀ n : ℕ, 2 ≤ n ->
    Nonempty (SU7RawBranchingTensorFilteredBoundedEnergyShell C n)

/-- Fiberwise raw branching shells generate P908 tensor shells on every even
fiber. -/
def tensorShellEveryEvenFiber_of_rawBranchingShells
    {C : SU7WeightTensorCoding}
    (H : SU7RawBranchingTensorFilteredBoundedEnergyShellEveryEvenFiber C) :
    SU7TensorIrreducibleBoundedEnergyShellEveryEvenFiber C := by
  intro n hn
  exact ⟨tensorIrreducibleBoundedEnergyShell_of_rawBranchingShell
    (Classical.choice (H n hn))⟩

/-- Fiberwise raw branching shells compute generated physical zero branch
cells on every even fiber. -/
def generatedPhysicalZeroBranchCellEveryEvenFiber_of_rawBranchingShells
    {C : SU7WeightTensorCoding}
    (H : SU7RawBranchingTensorFilteredBoundedEnergyShellEveryEvenFiber C) :
    ∀ n : ℕ, 2 ≤ n -> SU7GeneratedPhysicalZeroBranchCell n := by
  intro n hn
  exact generatedPhysicalZeroBranchCell_of_rawBranchingShell
    (Classical.choice (H n hn))

/-- Fiberwise raw branching shells give ordinary even Goldbach through the
same P909 physical-cell readout. -/
theorem evenGoldbach_of_rawBranchingTensorFilteredShells
    {C : SU7WeightTensorCoding}
    (H : SU7RawBranchingTensorFilteredBoundedEnergyShellEveryEvenFiber C) :
    EvenGoldbachStatement :=
  evenGoldbach_of_tensorShells_generatedPhysicalCells
    (tensorShellEveryEvenFiber_of_rawBranchingShells H)

/-! ## Certificate -/

/-- P910 certificate: raw branching shells plus a tensor irreducibility filter
generate P908 tensor shells and P909 physical zero cells, without storing
prime edges or Goldbach pairs. -/
structure SU7RawBranchingTensorFilterProducerCertificate where
  raw_energy_zero_iff :
    ∀ {n : ℕ} (c : SU7BranchingDecompositionCell n),
      rawAtomCodeBranchingDecompositionResidualEnergy c = 0 ↔
        rawAtomCodeBranchingDecompositionResidual c = 0
  tensor_lift_preserves_residual :
    ∀ {C : SU7WeightTensorCoding} {n : ℕ}
      (F : SU7BranchingTensorIrreducibilityFilter C n)
      (c : SU7BranchingDecompositionCell n),
      tensorIrreducibleBranchingSpectrumResidual
          (tensorIrreducibleCell_of_rawBranchingDecompositionCell F c) =
        rawAtomCodeBranchingDecompositionResidual c
  raw_shell_to_tensor_shell :
    ∀ {C : SU7WeightTensorCoding} {n : ℕ},
      SU7RawBranchingTensorFilteredBoundedEnergyShell C n ->
        SU7TensorIrreducibleBoundedEnergyShell C n
  raw_shell_to_generated_physical_zero :
    ∀ {C : SU7WeightTensorCoding} {n : ℕ},
      SU7RawBranchingTensorFilteredBoundedEnergyShell C n ->
        SU7GeneratedPhysicalZeroBranchCell n
  raw_shell_to_trace_zero :
    ∀ {C : SU7WeightTensorCoding} {n : ℕ},
      SU7RawBranchingTensorFilteredBoundedEnergyShell C n ->
        TraceZeroPrimeEdgeLoop n
  every_fiber_to_goldbach :
    ∀ {C : SU7WeightTensorCoding},
      SU7RawBranchingTensorFilteredBoundedEnergyShellEveryEvenFiber C ->
        EvenGoldbachStatement

/-- Canonical P910 producer certificate. -/
def su7RawBranchingTensorFilterProducerCertificate :
    SU7RawBranchingTensorFilterProducerCertificate where
  raw_energy_zero_iff :=
    rawAtomCodeBranchingDecompositionResidualEnergy_eq_zero_iff
  tensor_lift_preserves_residual :=
    tensorIrreducibleCell_rawResidual_eq
  raw_shell_to_tensor_shell :=
    tensorIrreducibleBoundedEnergyShell_of_rawBranchingShell
  raw_shell_to_generated_physical_zero :=
    generatedPhysicalZeroBranchCell_of_rawBranchingShell
  raw_shell_to_trace_zero :=
    traceZeroPrimeEdgeLoop_of_rawBranchingShell
  every_fiber_to_goldbach :=
    evenGoldbach_of_rawBranchingTensorFilteredShells


end
end StandardModelConstraint
end SaturationMonoid
