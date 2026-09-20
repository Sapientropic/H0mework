import H0mework.Arithmetic.AtomicCodes.P907

/-!
# Proposition 908: tensor residual-transport normalizers produce confinement

P907 proved that a finite tensor-irreducible spectrum with no active nonzero
terminal holonomy computes a zero residual cell.  This file lowers that
no-terminal condition to an actual residual-transport normalizer:

```text
normalize preserves the finite active spectrum
normalize strictly lowers residual energy off the zero fiber
normalize fixes the zero fiber
```

Such a normalizer forbids permanent holonomy automatically.  A bounded
quantized energy shell then computes such a normalizer by selecting, for each
active positive energy level, an active representative at `e - 1`.

No object introduced here stores `Nat.Prime`, `PrimeExponent`, a Goldbach pair,
or a trace-zero loop.  Those remain P906/P907 readouts after the zero residual
cell is generated.
-/

namespace SaturationMonoid
namespace StandardModelConstraint

noncomputable section

open SaturationMonoid.AffineRelaxation

set_option linter.defProp false

/-! ## Tensor residual-transport normalizers -/

/-- A concrete residual-transport normalizer on a finite tensor-irreducible
branch spectrum.

The normalizer is the local dynamics.  On active spectrum cells it preserves
the active spectrum, strictly lowers residual energy unless the residual is
already zero, and fixes zero residual cells. -/
structure SU7TensorIrreducibleSpectrumNormalizer
    (C : SU7WeightTensorCoding) (n : ℕ) where
  spectrum : SU7TensorIrreducibleBranchingSpectrum C n
  startCell : SU7TensorIrreducibleBranchingSpectrumCell C n
  start_mem : startCell ∈ spectrum.cells
  start_weight_positive : 0 < spectrum.representationWeight startCell
  normalize :
    SU7TensorIrreducibleBranchingSpectrumCell C n ->
      SU7TensorIrreducibleBranchingSpectrumCell C n
  normalize_mem_preserves :
    ∀ B : SU7TensorIrreducibleBranchingSpectrumCell C n,
      B ∈ spectrum.cells ->
        0 < spectrum.representationWeight B ->
          normalize B ∈ spectrum.cells
  normalize_weight_positive_preserves :
    ∀ B : SU7TensorIrreducibleBranchingSpectrumCell C n,
      B ∈ spectrum.cells ->
        0 < spectrum.representationWeight B ->
          0 < spectrum.representationWeight (normalize B)
  normalize_strictly_decreases_nonzero :
    ∀ B : SU7TensorIrreducibleBranchingSpectrumCell C n,
      B ∈ spectrum.cells ->
        0 < spectrum.representationWeight B ->
          tensorIrreducibleBranchingSpectrumResidual B ≠ 0 ->
            tensorIrreducibleBranchingSpectrumResidualEnergy (normalize B) <
              tensorIrreducibleBranchingSpectrumResidualEnergy B
  normalize_fixed_of_zero :
    ∀ B : SU7TensorIrreducibleBranchingSpectrumCell C n,
      B ∈ spectrum.cells ->
        0 < spectrum.representationWeight B ->
          tensorIrreducibleBranchingSpectrumResidual B = 0 ->
            normalize B = B

/-- Fixed points of an active tensor normalizer are exactly zero residual
cells. -/
theorem tensorIrreducibleNormalizer_fixed_iff_residual_zero
    {C : SU7WeightTensorCoding} {n : ℕ}
    (N : SU7TensorIrreducibleSpectrumNormalizer C n)
    (B : SU7TensorIrreducibleBranchingSpectrumCell C n)
    (hmem : B ∈ N.spectrum.cells)
    (hwt : 0 < N.spectrum.representationWeight B) :
    N.normalize B = B ↔
      tensorIrreducibleBranchingSpectrumResidual B = 0 := by
  constructor
  · intro hfixed
    by_contra hnonzero
    have hlt :
        tensorIrreducibleBranchingSpectrumResidualEnergy (N.normalize B) <
          tensorIrreducibleBranchingSpectrumResidualEnergy B :=
      N.normalize_strictly_decreases_nonzero B hmem hwt hnonzero
    rw [hfixed] at hlt
    exact (Nat.lt_irrefl _) hlt
  · intro hzero
    exact N.normalize_fixed_of_zero B hmem hwt hzero

/-- A tensor normalizer forbids active nonzero terminal holonomy in its
spectrum. -/
theorem tensorIrreducibleNormalizer_forbidsPermanentHolonomy
    {C : SU7WeightTensorCoding} {n : ℕ}
    (N : SU7TensorIrreducibleSpectrumNormalizer C n) :
    SU7TensorIrreducibleSpectrumForbidsPermanentHolonomy N.spectrum := by
  intro B hperm
  exact hperm.no_lower_active (N.normalize B)
    (N.normalize_mem_preserves B hperm.mem hperm.weight_positive)
    (N.normalize_weight_positive_preserves B hperm.mem
      hperm.weight_positive)
    (N.normalize_strictly_decreases_nonzero B hperm.mem
      hperm.weight_positive hperm.residual_nonzero)

/-- A tensor normalizer generates P907's confinement rule. -/
def tensorIrreducibleSpectrumConfinementRule_of_normalizer
    {C : SU7WeightTensorCoding} {n : ℕ}
    (N : SU7TensorIrreducibleSpectrumNormalizer C n) :
    SU7TensorIrreducibleSpectrumConfinementRule C n where
  spectrum := N.spectrum
  startCell := N.startCell
  start_mem := N.start_mem
  start_weight_positive := N.start_weight_positive
  forbids_permanent_holonomy :=
    tensorIrreducibleNormalizer_forbidsPermanentHolonomy N

/-- A tensor normalizer computes a positive-weight zero residual cell. -/
theorem exists_zeroCell_of_tensorIrreducibleNormalizer
    {C : SU7WeightTensorCoding} {n : ℕ}
    (N : SU7TensorIrreducibleSpectrumNormalizer C n) :
    ∃ Z : SU7TensorIrreducibleBranchingSpectrumCell C n,
      Z ∈ N.spectrum.cells ∧
        0 < N.spectrum.representationWeight Z ∧
          tensorIrreducibleBranchingSpectrumResidual Z = 0 :=
  exists_zeroCell_of_tensorIrreducibleSpectrumConfinementRule
    (tensorIrreducibleSpectrumConfinementRule_of_normalizer N)

/-- A tensor normalizer computes a trace-zero prime-edge loop. -/
def traceZeroPrimeEdgeLoop_of_tensorIrreducibleNormalizer
    {C : SU7WeightTensorCoding} {n : ℕ}
    (N : SU7TensorIrreducibleSpectrumNormalizer C n) :
    TraceZeroPrimeEdgeLoop n :=
  traceZeroPrimeEdgeLoop_of_tensorIrreducibleSpectrumConfinementRule
    (tensorIrreducibleSpectrumConfinementRule_of_normalizer N)

/-! ## Bounded quantized tensor energy shells -/

/-- A finite tensor-irreducible spectrum with a bounded residual-energy shell.

The shell supplies active predecessor representatives for every positive
energy value that can occur under the spectrum bound.  This is the finite
quantized version of "no escaping boundary": the normalizer can always move an
active nonzero cell to an active same-spectrum representative of energy
`e - 1`. -/
structure SU7TensorIrreducibleBoundedEnergyShell
    (C : SU7WeightTensorCoding) (n : ℕ) where
  spectrum : SU7TensorIrreducibleBranchingSpectrum C n
  startCell : SU7TensorIrreducibleBranchingSpectrumCell C n
  start_mem : startCell ∈ spectrum.cells
  start_weight_positive : 0 < spectrum.representationWeight startCell
  maxEnergy : ℕ
  energy_bound :
    ∀ B : SU7TensorIrreducibleBranchingSpectrumCell C n,
      B ∈ spectrum.cells ->
        tensorIrreducibleBranchingSpectrumResidualEnergy B ≤ maxEnergy
  lowerEnergyCell :
    (e : ℕ) -> 0 < e -> e ≤ maxEnergy ->
      SU7TensorIrreducibleBranchingSpectrumCell C n
  lowerEnergyCell_mem :
    ∀ (e : ℕ) (hpos : 0 < e) (hle : e ≤ maxEnergy),
      lowerEnergyCell e hpos hle ∈ spectrum.cells
  lowerEnergyCell_weight_positive :
    ∀ (e : ℕ) (hpos : 0 < e) (hle : e ≤ maxEnergy),
      0 < spectrum.representationWeight
        (lowerEnergyCell e hpos hle)
  lowerEnergyCell_energy_eq_pred :
    ∀ (e : ℕ) (hpos : 0 < e) (hle : e ≤ maxEnergy),
      tensorIrreducibleBranchingSpectrumResidualEnergy
          (lowerEnergyCell e hpos hle) = e - 1

/-- Normalization computed from a bounded tensor energy shell. -/
def tensorIrreducibleBoundedEnergyShellNormalize
    {C : SU7WeightTensorCoding} {n : ℕ}
    (L : SU7TensorIrreducibleBoundedEnergyShell C n)
    (B : SU7TensorIrreducibleBranchingSpectrumCell C n) :
    SU7TensorIrreducibleBranchingSpectrumCell C n := by
  classical
  by_cases hzero : tensorIrreducibleBranchingSpectrumResidual B = 0
  · exact B
  · by_cases hmem : B ∈ L.spectrum.cells
    · by_cases hwt : 0 < L.spectrum.representationWeight B
      · exact
          L.lowerEnergyCell
            (tensorIrreducibleBranchingSpectrumResidualEnergy B)
            (tensorIrreducibleBranchingSpectrumResidualEnergy_pos_of_nonzero
              B hzero)
            (L.energy_bound B hmem)
      · exact B
    · exact B

/-- Bounded-shell normalization preserves spectrum membership on active
spectrum cells. -/
theorem tensorIrreducibleBoundedEnergyShellNormalize_mem_preserves
    {C : SU7WeightTensorCoding} {n : ℕ}
    (L : SU7TensorIrreducibleBoundedEnergyShell C n)
    (B : SU7TensorIrreducibleBranchingSpectrumCell C n)
    (hmem : B ∈ L.spectrum.cells)
    (hwt : 0 < L.spectrum.representationWeight B) :
    tensorIrreducibleBoundedEnergyShellNormalize L B ∈
      L.spectrum.cells := by
  by_cases hzero : tensorIrreducibleBranchingSpectrumResidual B = 0
  · simp [tensorIrreducibleBoundedEnergyShellNormalize, hzero, hmem]
  · have hpos :
        0 < tensorIrreducibleBranchingSpectrumResidualEnergy B :=
      tensorIrreducibleBranchingSpectrumResidualEnergy_pos_of_nonzero
        B hzero
    have hle :
        tensorIrreducibleBranchingSpectrumResidualEnergy B ≤
          L.maxEnergy :=
      L.energy_bound B hmem
    simp [tensorIrreducibleBoundedEnergyShellNormalize, hzero, hmem, hwt,
      L.lowerEnergyCell_mem _ hpos hle]

/-- Bounded-shell normalization preserves positive representation weight on
active spectrum cells. -/
theorem tensorIrreducibleBoundedEnergyShellNormalize_weight_positive_preserves
    {C : SU7WeightTensorCoding} {n : ℕ}
    (L : SU7TensorIrreducibleBoundedEnergyShell C n)
    (B : SU7TensorIrreducibleBranchingSpectrumCell C n)
    (hmem : B ∈ L.spectrum.cells)
    (hwt : 0 < L.spectrum.representationWeight B) :
    0 < L.spectrum.representationWeight
      (tensorIrreducibleBoundedEnergyShellNormalize L B) := by
  by_cases hzero : tensorIrreducibleBranchingSpectrumResidual B = 0
  · simp [tensorIrreducibleBoundedEnergyShellNormalize, hzero, hwt]
  · have hpos :
        0 < tensorIrreducibleBranchingSpectrumResidualEnergy B :=
      tensorIrreducibleBranchingSpectrumResidualEnergy_pos_of_nonzero
        B hzero
    have hle :
        tensorIrreducibleBranchingSpectrumResidualEnergy B ≤
          L.maxEnergy :=
      L.energy_bound B hmem
    simp [tensorIrreducibleBoundedEnergyShellNormalize, hzero, hmem, hwt,
      L.lowerEnergyCell_weight_positive _ hpos hle]

/-- Bounded-shell normalization strictly lowers nonzero residual energy on
active spectrum cells. -/
theorem tensorIrreducibleBoundedEnergyShellNormalize_strictly_decreases_nonzero
    {C : SU7WeightTensorCoding} {n : ℕ}
    (L : SU7TensorIrreducibleBoundedEnergyShell C n)
    (B : SU7TensorIrreducibleBranchingSpectrumCell C n)
    (hmem : B ∈ L.spectrum.cells)
    (hwt : 0 < L.spectrum.representationWeight B)
    (hnonzero : tensorIrreducibleBranchingSpectrumResidual B ≠ 0) :
    tensorIrreducibleBranchingSpectrumResidualEnergy
        (tensorIrreducibleBoundedEnergyShellNormalize L B) <
      tensorIrreducibleBranchingSpectrumResidualEnergy B := by
  have hpos :
      0 < tensorIrreducibleBranchingSpectrumResidualEnergy B :=
    tensorIrreducibleBranchingSpectrumResidualEnergy_pos_of_nonzero
      B hnonzero
  have hle :
      tensorIrreducibleBranchingSpectrumResidualEnergy B ≤
        L.maxEnergy :=
    L.energy_bound B hmem
  have henergy :
      tensorIrreducibleBranchingSpectrumResidualEnergy
          (tensorIrreducibleBoundedEnergyShellNormalize L B) =
        tensorIrreducibleBranchingSpectrumResidualEnergy B - 1 := by
    simp [tensorIrreducibleBoundedEnergyShellNormalize, hnonzero, hmem,
      hwt, L.lowerEnergyCell_energy_eq_pred _ hpos hle]
  omega

/-- Zero residual cells are fixed by bounded-shell normalization. -/
theorem tensorIrreducibleBoundedEnergyShellNormalize_fixed_of_zero
    {C : SU7WeightTensorCoding} {n : ℕ}
    (L : SU7TensorIrreducibleBoundedEnergyShell C n)
    (B : SU7TensorIrreducibleBranchingSpectrumCell C n)
    (_hmem : B ∈ L.spectrum.cells)
    (_hwt : 0 < L.spectrum.representationWeight B)
    (hzero : tensorIrreducibleBranchingSpectrumResidual B = 0) :
    tensorIrreducibleBoundedEnergyShellNormalize L B = B := by
  simp [tensorIrreducibleBoundedEnergyShellNormalize, hzero]

/-- A bounded tensor energy shell computes a tensor normalizer. -/
def tensorIrreducibleNormalizer_of_boundedEnergyShell
    {C : SU7WeightTensorCoding} {n : ℕ}
    (L : SU7TensorIrreducibleBoundedEnergyShell C n) :
    SU7TensorIrreducibleSpectrumNormalizer C n where
  spectrum := L.spectrum
  startCell := L.startCell
  start_mem := L.start_mem
  start_weight_positive := L.start_weight_positive
  normalize := tensorIrreducibleBoundedEnergyShellNormalize L
  normalize_mem_preserves :=
    tensorIrreducibleBoundedEnergyShellNormalize_mem_preserves L
  normalize_weight_positive_preserves :=
    tensorIrreducibleBoundedEnergyShellNormalize_weight_positive_preserves L
  normalize_strictly_decreases_nonzero :=
    tensorIrreducibleBoundedEnergyShellNormalize_strictly_decreases_nonzero L
  normalize_fixed_of_zero :=
    tensorIrreducibleBoundedEnergyShellNormalize_fixed_of_zero L

/-- A bounded tensor energy shell forbids permanent holonomy. -/
theorem tensorIrreducibleBoundedEnergyShell_forbidsPermanentHolonomy
    {C : SU7WeightTensorCoding} {n : ℕ}
    (L : SU7TensorIrreducibleBoundedEnergyShell C n) :
    SU7TensorIrreducibleSpectrumForbidsPermanentHolonomy L.spectrum :=
  tensorIrreducibleNormalizer_forbidsPermanentHolonomy
    (tensorIrreducibleNormalizer_of_boundedEnergyShell L)

/-- A bounded tensor energy shell computes a zero residual cell. -/
theorem exists_zeroCell_of_tensorIrreducibleBoundedEnergyShell
    {C : SU7WeightTensorCoding} {n : ℕ}
    (L : SU7TensorIrreducibleBoundedEnergyShell C n) :
    ∃ Z : SU7TensorIrreducibleBranchingSpectrumCell C n,
      Z ∈ L.spectrum.cells ∧
        0 < L.spectrum.representationWeight Z ∧
          tensorIrreducibleBranchingSpectrumResidual Z = 0 :=
  exists_zeroCell_of_tensorIrreducibleNormalizer
    (tensorIrreducibleNormalizer_of_boundedEnergyShell L)

/-- A bounded tensor energy shell computes a trace-zero prime-edge loop. -/
def traceZeroPrimeEdgeLoop_of_tensorIrreducibleBoundedEnergyShell
    {C : SU7WeightTensorCoding} {n : ℕ}
    (L : SU7TensorIrreducibleBoundedEnergyShell C n) :
    TraceZeroPrimeEdgeLoop n :=
  traceZeroPrimeEdgeLoop_of_tensorIrreducibleNormalizer
    (tensorIrreducibleNormalizer_of_boundedEnergyShell L)

/-! ## Fiberwise bounded-shell confinement -/

/-- Every even fiber carries a bounded tensor energy shell. -/
def SU7TensorIrreducibleBoundedEnergyShellEveryEvenFiber
    (C : SU7WeightTensorCoding) : Prop :=
  ∀ n : ℕ, 2 ≤ n ->
    Nonempty (SU7TensorIrreducibleBoundedEnergyShell C n)

/-- Fiberwise bounded tensor shells compute trace-zero loops on every even
fiber. -/
def traceZeroPrimeEdgeLoopEveryEvenFiber_of_tensorIrreducibleBoundedEnergyShells
    {C : SU7WeightTensorCoding}
    (H : SU7TensorIrreducibleBoundedEnergyShellEveryEvenFiber C) :
    ∀ n : ℕ, 2 ≤ n -> TraceZeroPrimeEdgeLoop n := by
  intro n hn
  exact traceZeroPrimeEdgeLoop_of_tensorIrreducibleBoundedEnergyShell
    (Classical.choice (H n hn))

/-- Fiberwise bounded tensor shells give ordinary even Goldbach through the
P908 -> P907 -> P906 route. -/
theorem evenGoldbach_of_tensorIrreducibleBoundedEnergyShells
    {C : SU7WeightTensorCoding}
    (H : SU7TensorIrreducibleBoundedEnergyShellEveryEvenFiber C) :
    EvenGoldbachStatement :=
  evenGoldbach_of_traceZeroPrimeEdgeLoopEveryEvenFiber
    (traceZeroPrimeEdgeLoopEveryEvenFiber_of_tensorIrreducibleBoundedEnergyShells
      H)

/-! ## Certificate -/

/-- P908 certificate: active tensor residual-transport normalizers and bounded
quantized energy shells generate the P907 no-holonomy confinement rule. -/
structure SU7TensorIrreducibleResidualTransportProducerCertificate where
  normalizer_fixed_iff_zero :
    ∀ {C : SU7WeightTensorCoding} {n : ℕ}
      (N : SU7TensorIrreducibleSpectrumNormalizer C n)
      (B : SU7TensorIrreducibleBranchingSpectrumCell C n),
      B ∈ N.spectrum.cells ->
        0 < N.spectrum.representationWeight B ->
          (N.normalize B = B ↔
            tensorIrreducibleBranchingSpectrumResidual B = 0)
  normalizer_forbids_holonomy :
    ∀ {C : SU7WeightTensorCoding} {n : ℕ}
      (N : SU7TensorIrreducibleSpectrumNormalizer C n),
      SU7TensorIrreducibleSpectrumForbidsPermanentHolonomy N.spectrum
  normalizer_to_zero_cell :
    ∀ {C : SU7WeightTensorCoding} {n : ℕ}
      (N : SU7TensorIrreducibleSpectrumNormalizer C n),
      ∃ Z : SU7TensorIrreducibleBranchingSpectrumCell C n,
        Z ∈ N.spectrum.cells ∧
          0 < N.spectrum.representationWeight Z ∧
            tensorIrreducibleBranchingSpectrumResidual Z = 0
  bounded_shell_to_normalizer :
    ∀ {C : SU7WeightTensorCoding} {n : ℕ},
      SU7TensorIrreducibleBoundedEnergyShell C n ->
        SU7TensorIrreducibleSpectrumNormalizer C n
  bounded_shell_forbids_holonomy :
    ∀ {C : SU7WeightTensorCoding} {n : ℕ}
      (L : SU7TensorIrreducibleBoundedEnergyShell C n),
      SU7TensorIrreducibleSpectrumForbidsPermanentHolonomy L.spectrum
  bounded_shell_to_zero_cell :
    ∀ {C : SU7WeightTensorCoding} {n : ℕ}
      (L : SU7TensorIrreducibleBoundedEnergyShell C n),
      ∃ Z : SU7TensorIrreducibleBranchingSpectrumCell C n,
        Z ∈ L.spectrum.cells ∧
          0 < L.spectrum.representationWeight Z ∧
            tensorIrreducibleBranchingSpectrumResidual Z = 0
  bounded_shell_to_trace_zero :
    ∀ {C : SU7WeightTensorCoding} {n : ℕ},
      SU7TensorIrreducibleBoundedEnergyShell C n ->
        TraceZeroPrimeEdgeLoop n
  bounded_shells_to_goldbach :
    ∀ {C : SU7WeightTensorCoding},
      SU7TensorIrreducibleBoundedEnergyShellEveryEvenFiber C ->
        EvenGoldbachStatement

/-- Canonical P908 residual-transport producer certificate. -/
def su7TensorIrreducibleResidualTransportProducerCertificate :
    SU7TensorIrreducibleResidualTransportProducerCertificate where
  normalizer_fixed_iff_zero :=
    tensorIrreducibleNormalizer_fixed_iff_residual_zero
  normalizer_forbids_holonomy :=
    tensorIrreducibleNormalizer_forbidsPermanentHolonomy
  normalizer_to_zero_cell :=
    exists_zeroCell_of_tensorIrreducibleNormalizer
  bounded_shell_to_normalizer :=
    tensorIrreducibleNormalizer_of_boundedEnergyShell
  bounded_shell_forbids_holonomy :=
    tensorIrreducibleBoundedEnergyShell_forbidsPermanentHolonomy
  bounded_shell_to_zero_cell :=
    exists_zeroCell_of_tensorIrreducibleBoundedEnergyShell
  bounded_shell_to_trace_zero :=
    traceZeroPrimeEdgeLoop_of_tensorIrreducibleBoundedEnergyShell
  bounded_shells_to_goldbach :=
    evenGoldbach_of_tensorIrreducibleBoundedEnergyShells


end
end StandardModelConstraint
end SaturationMonoid
