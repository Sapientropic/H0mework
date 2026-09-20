import H0mework.Physics.BranchSources.P883

/-!
# Proposition 884: non-storing physical SU(7) branch-spectrum transitions

P883 generates a zero support cell from a finite spectrum-level Lyapunov
descent orbit, but that spectrum object is already named prime-coded.

This file pushes the producer below that naming layer.  A
`SU7PhysicalBranchingSpectrumCell` stores only:

* an SU(3) branch label;
* two physical SU(7) atoms;
* the color loop and its gauge-allowed proof.

It stores no `PrimeExponent`, no `Nat.Prime`, and no Goldbach pair.  The
prime-valued readout enters only through the canonical P879 atom projection.

The producer content is now a transition system on these physical cells:
nonzero residual cells have a spectrum-internal successor of strictly lower
energy.  Strong induction extracts a physical zero cell, and only then does
the faithful atom projection read it as a prime-edge Goldbach witness.
-/

namespace SaturationMonoid
namespace StandardModelConstraint

noncomputable section

open SaturationMonoid.AffineRelaxation

set_option linter.defProp false

/-! ## Physical branch-spectrum cells, below prime-edge readout -/

/-- Canonical physical atom code used at the readout boundary.

The atom itself still stores only SU(7) representation data.  This function is
the faithful projection from that representation datum into the prime-indexed
natural carrier supplied by P879. -/
def su7PhysicalAtomCode (a : SU7Atom) : ℕ :=
  su7PrimeCodedAtomCode a

/-- THEOREM 1: the faithful physical atom code is prime-valued. -/
theorem su7PhysicalAtomCode_prime (a : SU7Atom) :
    Nat.Prime (su7PhysicalAtomCode a) := by
  unfold su7PhysicalAtomCode
  exact su7PrimeCodedAtomCode_prime a

/-- A physical SU(7) branch-spectrum cell.

This structure intentionally stores no `PrimeExponent` and no `Nat.Prime`
proof.  Primality is a theorem of the projection, not a field of the cell. -/
structure SU7PhysicalBranchingSpectrumCell (n : ℕ) where
  branch : SU3FlagSchubertCell
  leftAtom : SU7Atom
  rightAtom : SU7Atom
  colorLoop : SU7ColorLoop
  allowed : GaugeAllowed colorLoop
  loop_fiber : colorLoop.fiber = n
  loop_left : colorLoop.leftAtom = leftAtom
  loop_right : colorLoop.rightAtom = rightAtom

/-- The physical branch cell obtained by forgetting the branch label. -/
def physicalBranchCell_of_physicalSpectrumCell
    {n : ℕ} (C : SU7PhysicalBranchingSpectrumCell n) :
    SU7PhysicalBranchCell n where
  leftAtom := C.leftAtom
  rightAtom := C.rightAtom
  colorLoop := C.colorLoop
  allowed := C.allowed
  loop_fiber := C.loop_fiber
  loop_left := C.loop_left
  loop_right := C.loop_right

/-- Physical-spectrum residual measured by the canonical atom projection. -/
def physicalBranchingSpectrumResidual
    {n : ℕ} (C : SU7PhysicalBranchingSpectrumCell n) : ℤ :=
  ((su7PhysicalAtomCode C.leftAtom +
      su7PhysicalAtomCode C.rightAtom : ℕ) : ℤ) -
    ((2 * n : ℕ) : ℤ)

/-- Physical-spectrum residual energy. -/
def physicalBranchingSpectrumResidualEnergy
    {n : ℕ} (C : SU7PhysicalBranchingSpectrumCell n) : ℕ :=
  Int.natAbs (physicalBranchingSpectrumResidual C)

/-- THEOREM 2: zero physical-spectrum residual is exactly even-fiber balance
under the faithful atom projection. -/
theorem physicalBranchingSpectrumResidual_zero_to_sum
    {n : ℕ} (C : SU7PhysicalBranchingSpectrumCell n)
    (hzero : physicalBranchingSpectrumResidual C = 0) :
    su7PhysicalAtomCode C.leftAtom +
      su7PhysicalAtomCode C.rightAtom = 2 * n := by
  unfold physicalBranchingSpectrumResidual at hzero
  omega

/-- THEOREM 3: zero physical-spectrum residual energy is zero residual. -/
theorem physicalBranchingSpectrumResidualEnergy_eq_zero_iff
    {n : ℕ} (C : SU7PhysicalBranchingSpectrumCell n) :
    physicalBranchingSpectrumResidualEnergy C = 0 ↔
      physicalBranchingSpectrumResidual C = 0 := by
  unfold physicalBranchingSpectrumResidualEnergy
  rw [Int.natAbs_eq_zero]

/-- THEOREM 4: nonzero residual gives positive residual energy. -/
theorem physicalBranchingSpectrumResidualEnergy_pos_of_nonzero
    {n : ℕ} (C : SU7PhysicalBranchingSpectrumCell n)
    (hnonzero : physicalBranchingSpectrumResidual C ≠ 0) :
    0 < physicalBranchingSpectrumResidualEnergy C := by
  apply Nat.pos_of_ne_zero
  intro henergy
  exact hnonzero
    ((physicalBranchingSpectrumResidualEnergy_eq_zero_iff C).mp henergy)

/-! ## Projection to the existing prime-coded spectrum layer -/

/-- Projection from a non-storing physical spectrum cell to P881's
prime-coded spectrum cell.  This projection computes prime labels; it does
not recover them from stored fields. -/
def primeCodedSpectrumCell_of_physicalSpectrumCell
    {n : ℕ} (C : SU7PhysicalBranchingSpectrumCell n) :
    SU7PrimeCodedBranchingSpectrumCell n where
  branch := C.branch
  leftAtom := C.leftAtom
  rightAtom := C.rightAtom

/-- THEOREM 5: prime-coded residual is the same residual read through the
physical atom code. -/
theorem primeCodedResidual_of_physicalSpectrumCell_eq
    {n : ℕ} (C : SU7PhysicalBranchingSpectrumCell n) :
    (primeCodedSpectrumCell_of_physicalSpectrumCell C).primeCodedResidual =
      physicalBranchingSpectrumResidual C := by
  rfl

/-- THEOREM 6: zero physical residual projects to zero P881 prime-coded
spectrum residual. -/
theorem primeCodedResidual_zero_of_physicalSpectrumCell
    {n : ℕ} (C : SU7PhysicalBranchingSpectrumCell n)
    (hzero : physicalBranchingSpectrumResidual C = 0) :
    (primeCodedSpectrumCell_of_physicalSpectrumCell C).primeCodedResidual =
      0 := by
  simpa [primeCodedResidual_of_physicalSpectrumCell_eq C] using hzero

/-! ## Physical transition systems -/

/-- A finite family of physical branch-spectrum cells. -/
structure SU7PhysicalBranchingSpectrumFamily (n : ℕ) where
  spectrumCells : List (SU7PhysicalBranchingSpectrumCell n)
  representationWeight : SU7PhysicalBranchingSpectrumCell n -> ℕ

/-- A physical transition system on one even fiber.

The data says: inside a finite positive-weight spectrum, every nonzero
residual cell has a gauge-dynamical successor of strictly lower residual
energy.  No zero cell is stored. -/
structure SU7PhysicalBranchingSpectrumTransitionSystem (n : ℕ) where
  family : SU7PhysicalBranchingSpectrumFamily n
  startCell : SU7PhysicalBranchingSpectrumCell n
  start_mem : startCell ∈ family.spectrumCells
  start_weight_positive : 0 < family.representationWeight startCell
  step :
    SU7PhysicalBranchingSpectrumCell n ->
      SU7PhysicalBranchingSpectrumCell n -> Prop
  step_mem_preserves :
    ∀ C next : SU7PhysicalBranchingSpectrumCell n,
      C ∈ family.spectrumCells ->
        0 < family.representationWeight C ->
          step C next ->
            next ∈ family.spectrumCells
  step_weight_positive_preserves :
    ∀ C next : SU7PhysicalBranchingSpectrumCell n,
      C ∈ family.spectrumCells ->
        0 < family.representationWeight C ->
          step C next ->
            0 < family.representationWeight next
  step_strictly_decreases_energy :
    ∀ C next : SU7PhysicalBranchingSpectrumCell n,
      C ∈ family.spectrumCells ->
        0 < family.representationWeight C ->
          step C next ->
            physicalBranchingSpectrumResidualEnergy next <
              physicalBranchingSpectrumResidualEnergy C
  no_terminal_nonzero :
    ∀ C : SU7PhysicalBranchingSpectrumCell n,
      C ∈ family.spectrumCells ->
        0 < family.representationWeight C ->
          physicalBranchingSpectrumResidual C ≠ 0 ->
            ∃ next : SU7PhysicalBranchingSpectrumCell n, step C next

/-- THEOREM 7: a physical transition system generates a positive-weight
zero-residual physical spectrum cell. -/
theorem exists_zeroCell_of_physicalTransitionSystem
    {n : ℕ} (T : SU7PhysicalBranchingSpectrumTransitionSystem n) :
    ∃ Z : SU7PhysicalBranchingSpectrumCell n,
      Z ∈ T.family.spectrumCells ∧
        0 < T.family.representationWeight Z ∧
          physicalBranchingSpectrumResidual Z = 0 := by
  let motive : ℕ -> Prop := fun e =>
    ∀ C : SU7PhysicalBranchingSpectrumCell n,
      C ∈ T.family.spectrumCells ->
        0 < T.family.representationWeight C ->
          physicalBranchingSpectrumResidualEnergy C = e ->
            ∃ Z : SU7PhysicalBranchingSpectrumCell n,
              Z ∈ T.family.spectrumCells ∧
                0 < T.family.representationWeight Z ∧
                  physicalBranchingSpectrumResidual Z = 0
  have hstep : ∀ e : ℕ, (∀ e' < e, motive e') -> motive e := by
    intro e ih C hmem hwt henergy
    by_cases hzero : physicalBranchingSpectrumResidual C = 0
    · exact ⟨C, hmem, hwt, hzero⟩
    · rcases T.no_terminal_nonzero C hmem hwt hzero with ⟨next, hnext_step⟩
      have hnext_mem : next ∈ T.family.spectrumCells :=
        T.step_mem_preserves C next hmem hwt hnext_step
      have hnext_wt : 0 < T.family.representationWeight next :=
        T.step_weight_positive_preserves C next hmem hwt hnext_step
      have hnext_lt :
          physicalBranchingSpectrumResidualEnergy next <
            physicalBranchingSpectrumResidualEnergy C :=
        T.step_strictly_decreases_energy C next hmem hwt hnext_step
      exact ih (physicalBranchingSpectrumResidualEnergy next)
        (by simpa [henergy] using hnext_lt)
        next hnext_mem hnext_wt rfl
  have hstart :
      motive
        (physicalBranchingSpectrumResidualEnergy T.startCell) :=
    Nat.strong_induction_on
      (physicalBranchingSpectrumResidualEnergy T.startCell) hstep
  exact hstart T.startCell T.start_mem T.start_weight_positive rfl

/-- THEOREM 8: a physical transition system computes P881's generator without
storing a zero support cell as primitive data. -/
def primeCodedSpectrumGenerator_of_physicalTransitionSystem
    {n : ℕ} (T : SU7PhysicalBranchingSpectrumTransitionSystem n) :
    SU7PrimeCodedBranchingSpectrumGenerator n :=
  let Z := Classical.choose (exists_zeroCell_of_physicalTransitionSystem T)
  let hZ := Classical.choose_spec
    (exists_zeroCell_of_physicalTransitionSystem T)
  let PZ := primeCodedSpectrumCell_of_physicalSpectrumCell Z
  { family :=
      { spectrumCells := [PZ]
        representationWeight := fun _ => 1 }
    supportCell := PZ
    support_mem := by simp
    support_weight_positive := Nat.zero_lt_one
    support_primeCodedResidual_zero :=
      primeCodedResidual_zero_of_physicalSpectrumCell Z hZ.2.2 }

/-! ## Fiberwise physical dynamics -/

/-- Every even fiber carries a physical branch-spectrum transition system. -/
def SU7PhysicalBranchingSpectrumTransitionSystemEveryEvenFiber : Prop :=
  ∀ n : ℕ, 2 ≤ n ->
    Nonempty (SU7PhysicalBranchingSpectrumTransitionSystem n)

/-- THEOREM 9: physical transition systems on every even fiber produce
P881's prime-coded spectrum generators on every even fiber. -/
theorem primeCodedSpectrumGeneratorEveryEvenFiber_of_physicalTransitionSystems
    (H : SU7PhysicalBranchingSpectrumTransitionSystemEveryEvenFiber) :
    SU7PrimeCodedBranchingSpectrumGeneratorEveryEvenFiber := by
  intro n hn
  rcases H n hn with ⟨T⟩
  exact ⟨primeCodedSpectrumGenerator_of_physicalTransitionSystem T⟩

/-- Physical transition confinement data.  The named SU(7) physical laws are
kept separate from the finite transition producer. -/
structure SU7PhysicalBranchingSpectrumTransitionConfinement where
  compact_gauge_orbit : SU7CompactGaugeOrbit
  lyapunov_residual_dissipation : SU7LyapunovResidualDissipation
  quantized_spectrum_no_escaping_boundary :
    SU7QuantizedSpectrumNoEscapingBoundary
  transition_systems :
    SU7PhysicalBranchingSpectrumTransitionSystemEveryEvenFiber

/-- THEOREM 10: physical transition confinement produces P882's
spectrum-support confinement route. -/
def primeCodedSpectrumSupportConfinement_of_physicalTransitions
    (D : SU7PhysicalBranchingSpectrumTransitionConfinement) :
    SU7PrimeCodedSpectrumSupportConfinement where
  compact_gauge_orbit := D.compact_gauge_orbit
  lyapunov_residual_dissipation := D.lyapunov_residual_dissipation
  quantized_spectrum_no_escaping_boundary :=
    D.quantized_spectrum_no_escaping_boundary
  spectrum_generator :=
    primeCodedSpectrumGeneratorEveryEvenFiber_of_physicalTransitionSystems
      D.transition_systems

/-- THEOREM 11: physical transition confinement gives the ordinary even
Goldbach readout through the canonical atom projection. -/
theorem evenGoldbach_of_physicalBranchingSpectrumTransitionConfinement
    (D : SU7PhysicalBranchingSpectrumTransitionConfinement) :
    EvenGoldbachStatement :=
  evenGoldbach_of_primeCodedSpectrumSupportConfinement
    (primeCodedSpectrumSupportConfinement_of_physicalTransitions D)

/-! ## Certificate -/

/-- The zero-cell property generated from a physical transition system. -/
def SU7PhysicalTransitionZeroCellGenerated
    {n : ℕ} (T : SU7PhysicalBranchingSpectrumTransitionSystem n) : Prop :=
  ∃ Z : SU7PhysicalBranchingSpectrumCell n,
    Z ∈ T.family.spectrumCells ∧
      0 < T.family.representationWeight Z ∧
        physicalBranchingSpectrumResidual Z = 0

/-- P884 certificate: non-storing physical SU(7) branch-spectrum transitions
generate the prime-edge readout only after the physical zero residual is
computed. -/
structure SU7PhysicalBranchingSpectrumTransitionProducerCertificate where
  atom_code_prime :
    ∀ a : SU7Atom, Nat.Prime (su7PhysicalAtomCode a)
  residual_zero_to_sum :
    ∀ {n : ℕ} (C : SU7PhysicalBranchingSpectrumCell n),
      physicalBranchingSpectrumResidual C = 0 ->
        su7PhysicalAtomCode C.leftAtom +
          su7PhysicalAtomCode C.rightAtom = 2 * n
  transition_to_zero_cell :
    ∀ {n : ℕ} (T : SU7PhysicalBranchingSpectrumTransitionSystem n),
      SU7PhysicalTransitionZeroCellGenerated T
  transition_to_generator :
    ∀ {n : ℕ}, SU7PhysicalBranchingSpectrumTransitionSystem n ->
      SU7PrimeCodedBranchingSpectrumGenerator n
  every_fiber_to_generator :
    SU7PhysicalBranchingSpectrumTransitionSystemEveryEvenFiber ->
      SU7PrimeCodedBranchingSpectrumGeneratorEveryEvenFiber
  transition_confinement_to_support :
    SU7PhysicalBranchingSpectrumTransitionConfinement ->
      SU7PrimeCodedSpectrumSupportConfinement
  transition_confinement_to_goldbach :
    SU7PhysicalBranchingSpectrumTransitionConfinement ->
      EvenGoldbachStatement

def su7PhysicalBranchingSpectrumTransitionProducerCertificate :
    SU7PhysicalBranchingSpectrumTransitionProducerCertificate where
  atom_code_prime := su7PhysicalAtomCode_prime
  residual_zero_to_sum := physicalBranchingSpectrumResidual_zero_to_sum
  transition_to_zero_cell := exists_zeroCell_of_physicalTransitionSystem
  transition_to_generator :=
    primeCodedSpectrumGenerator_of_physicalTransitionSystem
  every_fiber_to_generator :=
    primeCodedSpectrumGeneratorEveryEvenFiber_of_physicalTransitionSystems
  transition_confinement_to_support :=
    primeCodedSpectrumSupportConfinement_of_physicalTransitions
  transition_confinement_to_goldbach :=
    evenGoldbach_of_physicalBranchingSpectrumTransitionConfinement


end
end StandardModelConstraint
end SaturationMonoid
