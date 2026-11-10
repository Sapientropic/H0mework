import H0mework.Versions.Re60a8605.ReleaseMaterials.RepresentationArithmeticAtomProjectionDefect.Lean.Positive.SourceCodeFormulaPositiveSteps
import H0mework.Versions.Re60a8605.ReleaseMaterials.RepresentationArithmeticAtomProjectionDefect.Lean.NatMultiplicativeAtomPrimeBridge
import H0mework.Arithmetic.ShellSources.RepresentationRepair

/-!
# SU7 generated projection positive extraction

This file connects the SU7 generated-source-label / endpoint-projection-core
layer to the atom-projection positive extraction socket.

The important boundary is that a pointwise SU7 projection core is only one
source-generated endpoint projection.  It can materialize an atom-pair witness
for that shell, but it does not by itself provide a bounded all-shell
successor family.  The positive extraction socket is filled only after a
bounded family supplies one generated projection core for each successor
shell.
-/

namespace RepresentationArithmeticAtomProjectionDefect

namespace SU7GeneratedProjectionPositiveExtraction

universe u

abbrev SU7Label :=
  SaturationMonoid.StandardModelConstraint.SU7A6WeightLabel

def su7LeftCode (target : SU7Label) : Nat :=
  SaturationMonoid.StandardModelConstraint.su7A6ConcreteEndpointSourceGrammar.leftCodeOf
    target

def su7RightCode (target : SU7Label) : Nat :=
  SaturationMonoid.StandardModelConstraint.su7A6ConcreteEndpointSourceGrammar.rightCodeOf
    target

abbrev su7RawCodePairResidualEnergy
    (n left right : Nat) : Nat :=
  SaturationMonoid.StandardModelConstraint.rawCodePairResidualEnergy n left right

abbrev SU7EndpointProjectionCore
    (n : Nat) (target : SU7Label) : Prop :=
  SaturationMonoid.StandardModelConstraint.SU7A6EndpointProjectionCore n target

abbrev SU7SourceProjectionCore
    (n : Nat) (source target : SU7Label) :=
  SaturationMonoid.StandardModelConstraint.SU7A6SourceLabelUnitCenterCoverProjectionCore
    n source target

abbrev SU7GeneratedProjectionCoreLaw
    {K : Type u} [Field K]
    (σ : K) (hσ : σ ≠ 1) (n sourceBound : Nat) :=
  SaturationMonoid.StandardModelConstraint.SU7A6GeneratedSourceLabelUnitCenterCoverProjectionCoreLaw
    σ hσ n sourceBound

abbrev SU7ActiveCell
    {K : Type u} [Field K]
    (σ : K) (hσ : σ ≠ 1) (n sourceBound : Nat) :=
  SaturationMonoid.StandardModelConstraint.SU7ProducedActiveCell
    σ hσ n sourceBound

abbrev SU7CanonicalRichHolonomyWitness
    {K : Type u} [Field K]
    (σ : K) (hσ : σ ≠ 1)
    (n sourceBound : Nat) (p : Nat × Nat) :=
  SaturationMonoid.StandardModelConstraint.GeneratedFilteredRawCodePairCanonicalRichHolonomyWitness
    σ hσ n sourceBound p

abbrev SU7GeneratedHolonomyCell
    (n sourceBound : Nat) (p : Nat × Nat) : Prop :=
  SaturationMonoid.StandardModelConstraint.BoolGaugeFilteredRawCodePairUnitPermanentHolonomyCell
    n sourceBound
    (SaturationMonoid.StandardModelConstraint.generatedNoPrimeAllowedPredicate
      n sourceBound)
    p.1 p.2

/-- A bare canonical-rich source/phase witness carries the same raw endpoint
residual as the active source cell it produces.

This is the scalar calibration needed by the current-shell grammar mouth:
the observed/source-phase side may expose the produced active-cell energy,
while the lower native wrapper indexes the same witness by its raw coordinate
pair.  No endpoint coverage or selected `su7_left_descent` field is involved. -/
theorem canonicalRichHolonomyWitness_producedActiveCell_energy_eq_raw_pair
    {K : Type u} [Field K]
    {σ : K} {hσ : σ ≠ 1}
    {n sourceBound : Nat}
    {p : Nat × Nat}
    (W : SU7CanonicalRichHolonomyWitness σ hσ n sourceBound p) :
    (SaturationMonoid.StandardModelConstraint.producedActiveCell_of_canonicalRichHolonomyWitness
        W).energy =
      su7RawCodePairResidualEnergy n p.1 p.2 := by
  let A :=
    SaturationMonoid.StandardModelConstraint.producedActiveCell_of_canonicalRichHolonomyWitness
      W
  have hleft :
      A.sourceCell.cell.leftWeightCode = p.1 := by
    simpa [A,
      SaturationMonoid.StandardModelConstraint.producedActiveCell_of_canonicalRichHolonomyWitness,
      SaturationMonoid.StandardModelConstraint.SU7ProducedActiveCell.sourceCell,
      SaturationMonoid.StandardModelConstraint.SU7ProducedActiveCell.sourceLift]
      using W.source_lift.source_left
  have hright :
      A.sourceCell.cell.rightWeightCode = p.2 := by
    simpa [A,
      SaturationMonoid.StandardModelConstraint.producedActiveCell_of_canonicalRichHolonomyWitness,
      SaturationMonoid.StandardModelConstraint.SU7ProducedActiveCell.sourceCell,
      SaturationMonoid.StandardModelConstraint.SU7ProducedActiveCell.sourceLift]
      using W.source_lift.source_right
  have henergy :
      A.energy =
        su7RawCodePairResidualEnergy n p.1 p.2 := by
    rw [SaturationMonoid.StandardModelConstraint.SU7ProducedActiveCell.energy_eq_raw_source_pair A,
      hleft, hright]
  simpa [A] using henergy

abbrev SU7GeneratedNoPrimeBranchingCell (n : Nat) :=
  SaturationMonoid.StandardModelConstraint.SU7NoPrimeBranchingSpectrumCell
    SaturationMonoid.StandardModelConstraint.rawCodeTensorCoding n

abbrev SU7GeneratedStrictBranchingHolonomy
    (n sourceBound : Nat)
    (B : SU7GeneratedNoPrimeBranchingCell n) : Prop :=
  SaturationMonoid.StandardModelConstraint.NoPrimeBranchingCellStrictPermanentHolonomy
    (SaturationMonoid.StandardModelConstraint.generatedNoPrimeBranchingCells
      n sourceBound)
    B

def su7NoPrimeBranchingPair
    {n : Nat} (B : SU7GeneratedNoPrimeBranchingCell n) : Nat × Nat :=
  (SaturationMonoid.StandardModelConstraint.atomCode B.leftAtom.toSU7Atom,
    SaturationMonoid.StandardModelConstraint.atomCode B.rightAtom.toSU7Atom)

def endpointCodePairOfSU7NoPrimeBranchingCell
    {n : Nat} (B : SU7GeneratedNoPrimeBranchingCell n) :
    EndpointCodePair n where
  leftCode := (su7NoPrimeBranchingPair B).1
  rightCode := (su7NoPrimeBranchingPair B).2

theorem su7NoPrimeBranchingPair_raw_energy_eq
    {n : Nat} (B : SU7GeneratedNoPrimeBranchingCell n) :
    su7RawCodePairResidualEnergy n
        (su7NoPrimeBranchingPair B).1
        (su7NoPrimeBranchingPair B).2 =
      SaturationMonoid.StandardModelConstraint.noPrimeBranchingEndpointResidualEnergy
        B := by
  rfl

abbrev SU7GeneratedNoPrimeBranchingUnitSuccessorLaw
    (n sourceBound : Nat) : Prop :=
  SaturationMonoid.StandardModelConstraint.NoPrimeBranchingCellUnitSuccessorLaw
    (SaturationMonoid.StandardModelConstraint.generatedNoPrimeBranchingCells
      n sourceBound)

/-!
## Boolean SU7 endpoint checks to local multiplicative atom certificates
-/

/-- The SU7 Boolean multiplicative-atomic checker gives the local atom
predicate used by the atom-projection bridge.

The route goes through the existing SU7 checker correctness theorem and the
local `NatMultiplicativelyAtomic` / `Nat.Prime` compatibility theorem.  The
endpoint object still stores local multiplicative atomhood, not a naked prime
pair. -/
theorem nat_multiplicatively_atomic_of_su7_check
    {m : Nat}
    (hcheck :
      SaturationMonoid.StandardModelConstraint.natMultiplicativelyAtomicCheck
        m = true) :
    NatMultiplicativelyAtomic m :=
  nat_multiplicatively_atomic_of_prime
    (SaturationMonoid.StandardModelConstraint.natMultiplicativelyAtomicCheck_eq_true_iff_prime.mp
      hcheck)

/-- Our endpoint-code energy agrees with SU7's raw code-pair residual energy.

The two residuals have opposite signs, but both are read through `Int.natAbs`.
-/
theorem endpointCodePair_energy_eq_su7_rawCodePairResidualEnergy
    (n left right : Nat) :
    EndpointCodePair.energy
        ({ leftCode := left, rightCode := right } : EndpointCodePair n) =
      su7RawCodePairResidualEnergy n left right := by
  unfold EndpointCodePair.energy EndpointCodePair.residual
  unfold su7RawCodePairResidualEnergy
  unfold
    SaturationMonoid.StandardModelConstraint.rawCodePairResidualEnergy
    SaturationMonoid.StandardModelConstraint.rawCodePairResidual
  have hneg :
      (((2 * n : Nat) : Int) - ((left + right : Nat) : Int)) =
        -(((left + right : Nat) : Int) - ((2 * n : Nat) : Int)) := by
    ring
  rw [hneg, Int.natAbs_neg]

theorem atom_pair_realization_of_su7_no_prime_branching_cell
    {n : Nat} (B : SU7GeneratedNoPrimeBranchingCell n) :
    ∃ p : ArithmeticAtomPair NatMultiplicativelyAtomic n,
      ArithmeticAtomPair.energy p =
        SaturationMonoid.StandardModelConstraint.noPrimeBranchingEndpointResidualEnergy
          B := by
  let c := endpointCodePairOfSU7NoPrimeBranchingCell B
  refine
    ⟨atomPairOfEndpointCodePair
        c
        (nat_multiplicatively_atomic_of_prime
          (SaturationMonoid.StandardModelConstraint.noPrimeBranchingAtom_atomCode_prime
            B.leftAtom))
        (nat_multiplicatively_atomic_of_prime
          (SaturationMonoid.StandardModelConstraint.noPrimeBranchingAtom_atomCode_prime
            B.rightAtom)),
      ?_⟩
  dsimp [c, endpointCodePairOfSU7NoPrimeBranchingCell]
  erw [atomPairOfEndpointCodePair_energy]
  calc
    EndpointCodePair.energy
        ({ leftCode := (su7NoPrimeBranchingPair B).1,
           rightCode := (su7NoPrimeBranchingPair B).2 } :
          EndpointCodePair n) =
        su7RawCodePairResidualEnergy n
          (su7NoPrimeBranchingPair B).1
          (su7NoPrimeBranchingPair B).2 :=
      endpointCodePair_energy_eq_su7_rawCodePairResidualEnergy n
        (su7NoPrimeBranchingPair B).1
        (su7NoPrimeBranchingPair B).2
    _ =
        SaturationMonoid.StandardModelConstraint.noPrimeBranchingEndpointResidualEnergy
          B :=
      su7NoPrimeBranchingPair_raw_energy_eq B

/-!
## Pointwise SU7 endpoint projection core
-/

/-- Raw endpoint-code pair read from a SU7 target label. -/
def endpointCodePairOfSU7Target
    (n : Nat) (target : SU7Label) :
    EndpointCodePair n where
  leftCode := su7LeftCode target
  rightCode := su7RightCode target

/-- A SU7 endpoint projection core supplies a realized atom pair at the raw
endpoint residual shell of its target label. -/
theorem atom_pair_realization_of_su7_endpoint_projection_core
    {n : Nat} {target : SU7Label}
    (C : SU7EndpointProjectionCore n target) :
    ∃ p : ArithmeticAtomPair NatMultiplicativelyAtomic n,
      ArithmeticAtomPair.energy p =
        su7RawCodePairResidualEnergy n
          (su7LeftCode target) (su7RightCode target) := by
  let c := endpointCodePairOfSU7Target n target
  refine
    ⟨atomPairOfEndpointCodePair
        c
        (nat_multiplicatively_atomic_of_su7_check C.left_check)
        (nat_multiplicatively_atomic_of_su7_check C.right_check),
      ?_⟩
  dsimp [c, endpointCodePairOfSU7Target]
  erw [atomPairOfEndpointCodePair_energy]
  exact
    endpointCodePair_energy_eq_su7_rawCodePairResidualEnergy n
      (su7LeftCode target) (su7RightCode target)

/-- A SU7 source/projection core carries the same pointwise endpoint
materialization, now tied to a representation-generated source/target move. -/
theorem atom_pair_realization_of_su7_source_projection_core
    {n : Nat} {source target : SU7Label}
    (C : SU7SourceProjectionCore n source target) :
    ∃ p : ArithmeticAtomPair NatMultiplicativelyAtomic n,
      ArithmeticAtomPair.energy p =
        su7RawCodePairResidualEnergy n
          (su7LeftCode target) (su7RightCode target) :=
  atom_pair_realization_of_su7_endpoint_projection_core
    C.endpoint_projection_core

/-!
## Generated projection families for the positive extraction socket
-/

/-- A bounded SU7-generated projection family for one arithmetic fiber.

This is the lawful input needed by the positive extraction socket: for every
successor shell below the bound, representation dynamics generates a source
label, a target label, a source/projection core, and a proof that the target's
raw endpoint residual is exactly the successor shell.

This field is intentionally stronger than one pointwise endpoint core and
weaker than a downstream `SU7GeneratedRepairCell`. -/
structure SU7GeneratedBoundedProjectionFamily (n bound : Nat) where
  sourceLabel : Nat -> SU7Label
  targetLabel : Nat -> SU7Label
  source_target_core :
    ∀ {k : Nat}, k < bound ->
      SU7SourceProjectionCore n (sourceLabel k) (targetLabel k)
  target_raw_energy :
    ∀ {k : Nat}, k < bound ->
      su7RawCodePairResidualEnergy n
        (su7LeftCode (targetLabel k)) (su7RightCode (targetLabel k)) =
          k + 1

namespace SU7GeneratedBoundedProjectionFamily

/-- A SU7-generated bounded projection family directly materializes the
successor shell `k + 1`.

Unlike the positive-step transport theorem, this does not need a predecessor
realization at shell `k`; the witness is read from the generated
source/projection core at the selected index. -/
theorem atom_pair_realization_at_successor
    {n bound : Nat}
    (F : SU7GeneratedBoundedProjectionFamily n bound)
    {k : Nat} (hk : k < bound) :
    ∃ p : ArithmeticAtomPair NatMultiplicativelyAtomic n,
      ArithmeticAtomPair.energy p = k + 1 := by
  rcases
    atom_pair_realization_of_su7_source_projection_core
      (n := n) (source := F.sourceLabel k) (target := F.targetLabel k)
      (F.source_target_core hk) with
    ⟨p, hp⟩
  exact ⟨p, by rw [hp, F.target_raw_energy hk]⟩

/-- Factorized single-step readout from a SU7-generated bounded projection
family. -/
theorem factorized_atom_pair_realization_at_successor
    {n bound : Nat}
    (F : SU7GeneratedBoundedProjectionFamily n bound)
    {k : Nat} (hk : k < bound) :
    FactorizedAtomPairRealization
      NatMultiplicativelyAtomic natMultiplicativeAtomFactorizationCategory
      n (k + 1) := by
  rcases F.atom_pair_realization_at_successor hk with ⟨p, hp⟩
  exact
    factorizedAtomPairRealizationOfPair
      natMultiplicativeAtomFactorizationCategory p hp

/-- A SU7-generated bounded projection family supplies the positive successor
realization steps required by the extraction socket. -/
theorem bounded_successor_steps
    {n bound : Nat}
    (F : SU7GeneratedBoundedProjectionFamily n bound) :
    BoundedAtomPairRealizationSuccessorSteps
      NatMultiplicativelyAtomic n bound where
  lift_realization := by
    intro k hk _hRealized
    exact F.atom_pair_realization_at_successor hk

end SU7GeneratedBoundedProjectionFamily

/-!
## Native branching positive successor dynamics
-/

/-- Bounded source selector inside the generated no-prime SU7 branching
spectrum.

This is a positive source-dynamics socket: for each successor shell it selects
a generated no-prime branching source cell whose endpoint residual is one unit
above the target shell. -/
structure SU7NativeBranchingSourceSelector
    (n sourceBound targetBound : Nat) where
  sourceCell :
    ∀ (k : Nat), k < targetBound ->
      SU7GeneratedNoPrimeBranchingCell n
  source_mem :
    ∀ {k : Nat} (hk : k < targetBound),
      sourceCell k hk ∈
        SaturationMonoid.StandardModelConstraint.generatedNoPrimeBranchingCells
          n sourceBound
  source_energy_successor :
    ∀ {k : Nat} (hk : k < targetBound),
      SaturationMonoid.StandardModelConstraint.noPrimeBranchingEndpointResidualEnergy
        (sourceCell k hk) =
          k + 2

namespace SU7NativeBranchingSourceSelector

variable {n sourceBound targetBound : Nat}

/-- Selected source cells have nonzero residual energy, so the unit successor
law can fire. -/
theorem source_energy_ne_zero
    (S : SU7NativeBranchingSourceSelector n sourceBound targetBound)
    {k : Nat} (hk : k < targetBound) :
    SaturationMonoid.StandardModelConstraint.noPrimeBranchingEndpointResidualEnergy
        (S.sourceCell k hk) ≠ 0 := by
  rw [S.source_energy_successor hk]
  omega

end SU7NativeBranchingSourceSelector

/-- Bounded generated no-prime branching unit-successor family.

For every source cell at energy `k + 2`, native branching dynamics supplies a
generated repair cell one unit lower.  The repair cell's endpoint atoms are the
arithmetic atom-pair witness at shell `k + 1`. -/
structure SU7NativeBranchingUnitSuccessorFamily
    (n sourceBound targetBound : Nat) where
  sourceCell :
    ∀ (k : Nat), k < targetBound ->
      SU7GeneratedNoPrimeBranchingCell n
  repairCell :
    ∀ (k : Nat), k < targetBound ->
      SU7GeneratedNoPrimeBranchingCell n
  source_mem :
    ∀ {k : Nat} (hk : k < targetBound),
      sourceCell k hk ∈
        SaturationMonoid.StandardModelConstraint.generatedNoPrimeBranchingCells
          n sourceBound
  repair_mem :
    ∀ {k : Nat} (hk : k < targetBound),
      repairCell k hk ∈
        SaturationMonoid.StandardModelConstraint.generatedNoPrimeBranchingCells
          n sourceBound
  unit_successor :
    ∀ {k : Nat} (hk : k < targetBound),
      SaturationMonoid.StandardModelConstraint.noPrimeBranchingEndpointResidualEnergy
          (repairCell k hk) + 1 =
        SaturationMonoid.StandardModelConstraint.noPrimeBranchingEndpointResidualEnergy
          (sourceCell k hk)
  source_energy_successor :
    ∀ {k : Nat} (hk : k < targetBound),
      SaturationMonoid.StandardModelConstraint.noPrimeBranchingEndpointResidualEnergy
        (sourceCell k hk) =
          k + 2

namespace SU7NativeBranchingUnitSuccessorFamily

variable {n sourceBound targetBound : Nat}

/-- A global generated no-prime branching unit-successor law turns a bounded
source selector into a bounded repair successor family. -/
noncomputable def ofSourceSelector
    (S : SU7NativeBranchingSourceSelector n sourceBound targetBound)
    (Hsucc : SU7GeneratedNoPrimeBranchingUnitSuccessorLaw n sourceBound) :
    SU7NativeBranchingUnitSuccessorFamily n sourceBound targetBound where
  sourceCell := S.sourceCell
  repairCell := by
    intro k hk
    exact
      Classical.choose
        (Hsucc
          (S.sourceCell k hk)
          (S.source_mem hk)
          (S.source_energy_ne_zero hk))
  source_mem := S.source_mem
  repair_mem := by
    intro k hk
    exact
      (Classical.choose_spec
        (Hsucc
          (S.sourceCell k hk)
          (S.source_mem hk)
          (S.source_energy_ne_zero hk))).1
  unit_successor := by
    intro k hk
    exact
      (Classical.choose_spec
        (Hsucc
          (S.sourceCell k hk)
          (S.source_mem hk)
          (S.source_energy_ne_zero hk))).2
  source_energy_successor := S.source_energy_successor

/-- The repair cell selected by native branching unit-successor dynamics lands
at the target successor shell `k + 1`. -/
theorem repair_energy_successor
    (F : SU7NativeBranchingUnitSuccessorFamily n sourceBound targetBound)
    {k : Nat} (hk : k < targetBound) :
    SaturationMonoid.StandardModelConstraint.noPrimeBranchingEndpointResidualEnergy
        (F.repairCell k hk) =
      k + 1 := by
  have hunit := F.unit_successor hk
  rw [F.source_energy_successor hk] at hunit
  omega

/-- Native branching unit-successor dynamics directly materializes the
successor shell `k + 1` from the generated repair cell. -/
theorem atom_pair_realization_at_successor
    (F : SU7NativeBranchingUnitSuccessorFamily n sourceBound targetBound)
    {k : Nat} (hk : k < targetBound) :
    ∃ p : ArithmeticAtomPair NatMultiplicativelyAtomic n,
      ArithmeticAtomPair.energy p = k + 1 := by
  rcases
    atom_pair_realization_of_su7_no_prime_branching_cell
      (F.repairCell k hk) with
    ⟨p, hp⟩
  exact ⟨p, by rw [hp, F.repair_energy_successor hk]⟩

/-- Factorized single-step readout from native branching unit-successor
dynamics. -/
theorem factorized_atom_pair_realization_at_successor
    (F : SU7NativeBranchingUnitSuccessorFamily n sourceBound targetBound)
    {k : Nat} (hk : k < targetBound) :
    FactorizedAtomPairRealization
      NatMultiplicativelyAtomic natMultiplicativeAtomFactorizationCategory
      n (k + 1) := by
  rcases F.atom_pair_realization_at_successor hk with ⟨p, hp⟩
  exact
    factorizedAtomPairRealizationOfPair
      natMultiplicativeAtomFactorizationCategory p hp

/-- Native branching unit-successor dynamics supplies the positive atom-pair
successor steps required by target-shell extraction. -/
theorem bounded_successor_steps
    (F : SU7NativeBranchingUnitSuccessorFamily n sourceBound targetBound) :
    BoundedAtomPairRealizationSuccessorSteps
      NatMultiplicativelyAtomic n targetBound where
  lift_realization := by
    intro k hk _hRealized
    exact F.atom_pair_realization_at_successor hk

end SU7NativeBranchingUnitSuccessorFamily

/-- Native branching unit-successor positive extraction: shell zero plus a
bounded source/repair successor family extracts the target-shell atom pair. -/
theorem atom_pair_realization_of_native_branching_unit_successor_family
    {n sourceBound targetBound : Nat}
    (F :
      SU7NativeBranchingUnitSuccessorFamily
        n sourceBound targetBound)
    (hzero :
      ∃ p : ArithmeticAtomPair NatMultiplicativelyAtomic n,
        ArithmeticAtomPair.energy p = 0) :
    ∃ p : ArithmeticAtomPair NatMultiplicativelyAtomic n,
      ArithmeticAtomPair.energy p = targetBound :=
  atom_pair_realization_at_bound_of_zero_and_successor_steps
    hzero targetBound F.bounded_successor_steps

/-- Factorized readout for native branching unit-successor extraction. -/
theorem factorized_atom_pair_realization_of_native_branching_unit_successor_family
    {n sourceBound targetBound : Nat}
    (F :
      SU7NativeBranchingUnitSuccessorFamily
        n sourceBound targetBound)
    (hzero :
      ∃ p : ArithmeticAtomPair NatMultiplicativelyAtomic n,
        ArithmeticAtomPair.energy p = 0) :
    FactorizedAtomPairRealization
      NatMultiplicativelyAtomic natMultiplicativeAtomFactorizationCategory
      n targetBound := by
  rcases
    atom_pair_realization_of_native_branching_unit_successor_family F hzero with
    ⟨p, hp⟩
  exact
    factorizedAtomPairRealizationOfPair
      natMultiplicativeAtomFactorizationCategory p hp

/-- Direct extraction from a bounded generated branching source selector and a
global generated no-prime branching unit-successor law.

This is the compact positive source-dynamics API: source cells at `k + 2`
plus a native unit-successor law produce repair cells at `k + 1`, whose
generated no-prime endpoints read as arithmetic atom-pair witnesses. -/
theorem atom_pair_realization_of_native_branching_source_selector
    {n sourceBound targetBound : Nat}
    (S :
      SU7NativeBranchingSourceSelector
        n sourceBound targetBound)
    (Hsucc :
      SU7GeneratedNoPrimeBranchingUnitSuccessorLaw n sourceBound)
    (hzero :
      ∃ p : ArithmeticAtomPair NatMultiplicativelyAtomic n,
        ArithmeticAtomPair.energy p = 0) :
    ∃ p : ArithmeticAtomPair NatMultiplicativelyAtomic n,
      ArithmeticAtomPair.energy p = targetBound :=
  atom_pair_realization_of_native_branching_unit_successor_family
    (SU7NativeBranchingUnitSuccessorFamily.ofSourceSelector S Hsucc)
    hzero

/-- Factorized direct extraction from a bounded generated branching source
selector and global generated no-prime branching unit-successor law. -/
theorem factorized_atom_pair_realization_of_native_branching_source_selector
    {n sourceBound targetBound : Nat}
    (S :
      SU7NativeBranchingSourceSelector
        n sourceBound targetBound)
    (Hsucc :
      SU7GeneratedNoPrimeBranchingUnitSuccessorLaw n sourceBound)
    (hzero :
      ∃ p : ArithmeticAtomPair NatMultiplicativelyAtomic n,
        ArithmeticAtomPair.energy p = 0) :
    FactorizedAtomPairRealization
      NatMultiplicativelyAtomic natMultiplicativeAtomFactorizationCategory
      n targetBound :=
  factorized_atom_pair_realization_of_native_branching_unit_successor_family
    (SU7NativeBranchingUnitSuccessorFamily.ofSourceSelector S Hsucc)
    hzero

/-- Direct single-step extraction from a bounded generated branching source
selector and a global generated no-prime branching unit-successor law. -/
theorem atom_pair_realization_at_successor_of_native_branching_source_selector
    {n sourceBound targetBound : Nat}
    (S :
      SU7NativeBranchingSourceSelector
        n sourceBound targetBound)
    (Hsucc :
      SU7GeneratedNoPrimeBranchingUnitSuccessorLaw n sourceBound)
    {k : Nat} (hk : k < targetBound) :
    ∃ p : ArithmeticAtomPair NatMultiplicativelyAtomic n,
      ArithmeticAtomPair.energy p = k + 1 :=
  (SU7NativeBranchingUnitSuccessorFamily.ofSourceSelector S Hsucc)
    |>.atom_pair_realization_at_successor hk

/-- Factorized direct single-step extraction from a bounded generated
branching source selector and global generated no-prime branching
unit-successor law. -/
theorem factorized_atom_pair_realization_at_successor_of_native_branching_source_selector
    {n sourceBound targetBound : Nat}
    (S :
      SU7NativeBranchingSourceSelector
        n sourceBound targetBound)
    (Hsucc :
      SU7GeneratedNoPrimeBranchingUnitSuccessorLaw n sourceBound)
    {k : Nat} (hk : k < targetBound) :
    FactorizedAtomPairRealization
      NatMultiplicativelyAtomic natMultiplicativeAtomFactorizationCategory
      n (k + 1) :=
  (SU7NativeBranchingUnitSuccessorFamily.ofSourceSelector S Hsucc)
    |>.factorized_atom_pair_realization_at_successor hk

/-!
## From generated SU7 laws to bounded positive families
-/

/-- Bounded selector of generated SU7 source cells for the positive extraction
socket.

For target successor shell `k + 1`, the selected produced source cell must
have source energy `k + 2`: a SU7 unit center-cover projection core reads the
target raw endpoint residual one unit below the source signed height. -/
structure SU7GeneratedActiveCellSuccessorSelector
    {K : Type u} [Field K]
    (σ : K) (hσ : σ ≠ 1)
    (n sourceBound targetBound : Nat) where
  fallbackLabel : SU7Label
  activeCell :
    ∀ (k : Nat), k < targetBound ->
      SU7ActiveCell σ hσ n sourceBound
  activeCellPos :
    ∀ {k : Nat} (hk : k < targetBound),
      (activeCell k hk).energy ≠ 0
  source_energy_successor :
    ∀ {k : Nat} (hk : k < targetBound),
      (activeCell k hk).energy = k + 2

/-- Native active-cell successor dynamics.

This is the minimal source-side payload needed to prove the selector: SU7 /
GT / crystal / branching dynamics must generate bounded active source cells
with the affine residual readout `E = k + 2`.  The selector's positivity field
is then derived here, not passed as an extra upstream obligation. -/
structure SU7NativeActiveCellSuccessorDynamics
    {K : Type u} [Field K]
    (σ : K) (hσ : σ ≠ 1)
    (n sourceBound targetBound : Nat) where
  fallbackLabel : SU7Label
  activeCell :
    ∀ (k : Nat), k < targetBound ->
      SU7ActiveCell σ hσ n sourceBound
  source_energy_successor :
    ∀ {k : Nat} (hk : k < targetBound),
      (activeCell k hk).energy = k + 2

namespace SU7NativeActiveCellSuccessorDynamics

variable {K : Type u} [Field K]
variable {σ : K} {hσ : σ ≠ 1}
variable {n sourceBound targetBound : Nat}

/-- The affine successor readout excludes terminal zero automatically. -/
theorem activeCellPos
    (D :
      SU7NativeActiveCellSuccessorDynamics
        σ hσ n sourceBound targetBound)
    {k : Nat} (hk : k < targetBound) :
    (D.activeCell k hk).energy ≠ 0 := by
  rw [D.source_energy_successor hk]
  omega

/-- Native active-cell dynamics proves the generated active-cell successor
selector. -/
def toActiveCellSuccessorSelector
    (D :
      SU7NativeActiveCellSuccessorDynamics
        σ hσ n sourceBound targetBound) :
    SU7GeneratedActiveCellSuccessorSelector
      σ hσ n sourceBound targetBound where
  fallbackLabel := D.fallbackLabel
  activeCell := D.activeCell
  activeCellPos := D.activeCellPos
  source_energy_successor := D.source_energy_successor

/-- Nonempty theorem form for downstream theorem statements that want the
selector as a produced object rather than a chosen definition. -/
theorem nonempty_active_cell_successor_selector
    (D :
      SU7NativeActiveCellSuccessorDynamics
        σ hσ n sourceBound targetBound) :
    Nonempty
      (SU7GeneratedActiveCellSuccessorSelector
        σ hσ n sourceBound targetBound) :=
  ⟨D.toActiveCellSuccessorSelector⟩

end SU7NativeActiveCellSuccessorDynamics

namespace SU7GeneratedActiveCellSuccessorSelector

variable {K : Type u} [Field K]
variable {σ : K} {hσ : σ ≠ 1}
variable {n sourceBound targetBound : Nat}

/-- A generated active-cell selector exposes the minimal native dynamics.

Gate classification: selected-family coherence theorem (Gate B).  This is the
source-only normalization from the generated selector surface to the native
active-cell dynamics surface used by the selected-key path.  It forgets only
the explicit positivity field, which is already implied by the affine
`k+2` energy law downstream; it does not introduce projection support,
atomhood, primality, endpoint coverage, normalizers, or repair-cell witnesses.
-/
def toNativeActiveCellSuccessorDynamics
    (S :
      SU7GeneratedActiveCellSuccessorSelector
        σ hσ n sourceBound targetBound) :
    SU7NativeActiveCellSuccessorDynamics
      σ hσ n sourceBound targetBound where
  fallbackLabel := S.fallbackLabel
  activeCell := S.activeCell
  source_energy_successor := S.source_energy_successor

/-- Theorem form: generated active-cell selectors produce native active-cell
dynamics. -/
theorem nonempty_native_active_cell_successor_dynamics
    (S :
      SU7GeneratedActiveCellSuccessorSelector
        σ hσ n sourceBound targetBound) :
    Nonempty
      (SU7NativeActiveCellSuccessorDynamics
        σ hσ n sourceBound targetBound) :=
  ⟨S.toNativeActiveCellSuccessorDynamics⟩

end SU7GeneratedActiveCellSuccessorSelector

/-- Concrete endpoint-source readout carried by a produced SU7 active cell.

This is the thin positive socket boundary: a source/GT/crystal/branching
constructor may hand us a produced active cell plus this endpoint readout and
an affine energy law.  Permanent/no-predecessor holonomy cells are diagnostic
objects, not this producer interface. -/
abbrev SU7EndpointSourceReadout
    {K : Type u} [Field K]
    {σ : K} {hσ : σ ≠ 1}
    {n sourceBound : Nat}
    (A : SU7ActiveCell σ hσ n sourceBound) :=
  SaturationMonoid.StandardModelConstraint.SU7ProducedActiveCellA6EndpointSourceReadout
    SaturationMonoid.StandardModelConstraint.su7A6ConcreteEndpointSourceGrammar.leftCodeOf
    SaturationMonoid.StandardModelConstraint.su7A6ConcreteEndpointSourceGrammar.rightCodeOf
    A

/-- Thin source feasible datum for one affine residual shell.

The datum is intentionally weaker than a repair law and stronger than a bare
endpoint pair: it contains a representation-generated produced active cell,
its faithful endpoint-source readout, and the affine energy calibration for
the current shell. -/
structure SU7ThinSourceFeasibleDatum
    {K : Type u} [Field K]
    (σ : K) (hσ : σ ≠ 1)
    (n sourceBound sourceEnergy : Nat) where
  producedCell : SU7ActiveCell σ hσ n sourceBound
  endpointReadout : SU7EndpointSourceReadout producedCell
  affine_energy : producedCell.energy = sourceEnergy

namespace SU7ThinSourceFeasibleDatum

variable {K : Type u} [Field K]
variable {σ : K} {hσ : σ ≠ 1}
variable {n sourceBound sourceEnergy : Nat}

/-- The thin datum returns the produced active SU7 cell it carries. -/
def toProducedActiveCell
    (D :
      SU7ThinSourceFeasibleDatum
        σ hσ n sourceBound sourceEnergy) :
    SU7ActiveCell σ hσ n sourceBound :=
  D.producedCell

/-- The produced active cell reads the datum's affine source energy. -/
theorem producedCell_energy_eq
    (D :
      SU7ThinSourceFeasibleDatum
        σ hσ n sourceBound sourceEnergy) :
    D.toProducedActiveCell.energy = sourceEnergy :=
  D.affine_energy

/-- The datum exposes exactly the positive constructor payload: a produced
active cell, its endpoint-source readout, and the affine source-energy law. -/
def toProducedActiveCellWithReadoutAndEnergy
    (D :
      SU7ThinSourceFeasibleDatum
        σ hσ n sourceBound sourceEnergy) :
    Sigma
      (fun A : SU7ActiveCell σ hσ n sourceBound =>
        Sigma
          (fun _R : SU7EndpointSourceReadout A =>
            PLift (A.energy = sourceEnergy))) :=
  ⟨D.producedCell, D.endpointReadout, ⟨D.affine_energy⟩⟩

/-- The endpoint readout preserves the raw endpoint-code residual energy. -/
theorem endpoint_raw_energy_eq
    (D :
      SU7ThinSourceFeasibleDatum
        σ hσ n sourceBound sourceEnergy) :
    su7RawCodePairResidualEnergy n
        (su7LeftCode D.endpointReadout.source_label)
        (su7RightCode D.endpointReadout.source_label) =
      sourceEnergy := by
  simpa [su7LeftCode, su7RightCode, su7RawCodePairResidualEnergy]
    using D.endpointReadout.raw_pair_energy_eq.trans D.affine_energy

/-- If a thin source datum is not on the source-below side, its raw-energy
readout forces the unique over-target mirror right code.

Gate classification: selected-family coherence source datum (Gate B).  This
does not choose an endpoint witness and does not use projection support,
atomhood, coverage, normalizers, or repair cells.  It only says that a
source-bearing datum cannot silently fail the selected branch test: failure of
`left + right < 2*n` has to leave the source-label/raw-unit trace
`right = 2*n + sourceEnergy - left`. -/
theorem sourceAboveRight_eq_of_not_sourceBelow
    (D :
      SU7ThinSourceFeasibleDatum
        σ hσ n sourceBound sourceEnergy)
    (hnot :
      ¬ su7LeftCode D.endpointReadout.source_label +
          su7RightCode D.endpointReadout.source_label <
        2 * n) :
    su7RightCode D.endpointReadout.source_label =
      2 * n + sourceEnergy -
        su7LeftCode D.endpointReadout.source_label := by
  let left := su7LeftCode D.endpointReadout.source_label
  let right := su7RightCode D.endpointReadout.source_label
  have hge : 2 * n ≤ left + right := by
    dsimp [left, right] at hnot ⊢
    omega
  have hraw :
      su7RawCodePairResidualEnergy n left right =
        left + right - 2 * n := by
    simpa [su7RawCodePairResidualEnergy, left, right]
      using
        SaturationMonoid.StandardModelConstraint.SU7ProducedActiveCellA6EndpointSourceReadout.rawCodePairResidualEnergy_eq_sum_sub_of_target_le_source
          (n := n) (left := left) (right := right) hge
  have henergy :
      left + right - 2 * n = sourceEnergy := by
    rw [← hraw]
    simpa [left, right] using D.endpoint_raw_energy_eq
  show right = 2 * n + sourceEnergy - left
  omega

/-- A thin source datum is either on the source-below side or it records the
over-target mirror branch exactly.

Gate classification: selected-family coherence source datum (Gate B).  This
is the source-only branch classification that keeps later SU7 work honest:
excluding the mirror branch is the remaining grammar selector obligation,
not an endpoint projection or coverage premise. -/
theorem sourceBelow_or_sourceAboveRight_eq
    (D :
      SU7ThinSourceFeasibleDatum
        σ hσ n sourceBound sourceEnergy) :
    su7LeftCode D.endpointReadout.source_label +
          su7RightCode D.endpointReadout.source_label <
        2 * n ∨
      su7RightCode D.endpointReadout.source_label =
        2 * n + sourceEnergy -
          su7LeftCode D.endpointReadout.source_label := by
  by_cases hbelow :
      su7LeftCode D.endpointReadout.source_label +
          su7RightCode D.endpointReadout.source_label <
        2 * n
  · exact Or.inl hbelow
  · exact Or.inr (D.sourceAboveRight_eq_of_not_sourceBelow hbelow)

/-- A finite source list cannot contain the over-target mirror branch once the
mirror right code lies beyond the generated source bound.

Gate classification: selected-family coherence source datum (Gate B).  This
is a source-list theorem: the right code is read from the produced source cell
and is therefore bounded by `sourceBound`.  No endpoint projection support,
atomhood, coverage, normalizer, or repair witness is used. -/
theorem sourceAboveRight_ne_of_sourceBound_lt_sourceAboveRight
    (D :
      SU7ThinSourceFeasibleDatum
        σ hσ n sourceBound sourceEnergy)
    (hroom :
      sourceBound <
        2 * n + sourceEnergy -
          su7LeftCode D.endpointReadout.source_label) :
    su7RightCode D.endpointReadout.source_label ≠
      2 * n + sourceEnergy -
        su7LeftCode D.endpointReadout.source_label := by
  intro hmirror
  have hright :
      su7RightCode D.endpointReadout.source_label =
        D.producedCell.sourceCell.cell.rightWeightCode := by
    simpa [su7RightCode] using D.endpointReadout.right_code_reads_source
  have hright_le :
      su7RightCode D.endpointReadout.source_label ≤ sourceBound := by
    rw [hright]
    exact
      SaturationMonoid.StandardModelConstraint.SU7ProducedActiveCellA6EndpointSourceReadout.su7ProducedActiveCell_sourceRight_le_bound
        D.producedCell
  omega

/-- A positive energy-room inequality rules out the over-target mirror branch.

This is the source-only completion-room form of the mirror exclusion.  Because
the selected left code is also generated inside `sourceBound`,
`2*sourceBound < 2*n + sourceEnergy` implies that the mirror right code would
fall outside the generated source list. -/
theorem sourceAboveRight_ne_of_twiceSourceBound_lt_targetPlusEnergy
    (D :
      SU7ThinSourceFeasibleDatum
        σ hσ n sourceBound sourceEnergy)
    (hroom : 2 * sourceBound < 2 * n + sourceEnergy) :
    su7RightCode D.endpointReadout.source_label ≠
      2 * n + sourceEnergy -
        su7LeftCode D.endpointReadout.source_label := by
  have hleft :
      su7LeftCode D.endpointReadout.source_label =
        D.producedCell.sourceCell.cell.leftWeightCode := by
    simpa [su7LeftCode] using D.endpointReadout.left_code_reads_source
  have hleft_le :
      su7LeftCode D.endpointReadout.source_label ≤ sourceBound := by
    rw [hleft]
    exact
      SaturationMonoid.StandardModelConstraint.SU7ProducedActiveCellA6EndpointSourceReadout.su7ProducedActiveCell_sourceLeft_le_bound
        D.producedCell
  exact
    D.sourceAboveRight_ne_of_sourceBound_lt_sourceAboveRight
      (by omega)

/-- If the source list has enough energy room, the selected thin source datum
must lie on the source-below side.

Gate classification: selected-family coherence source datum (Gate B).  This
is a shell-local strengthening of the closed lower-half sufficient condition:
positive residual headroom may enlarge the allowed source window at that shell,
but mirror still cannot be a generated source-bearing readout.  A full family
starting at `k = 0` still has to satisfy the lower-edge shell. -/
theorem sourceBelow_of_twiceSourceBound_lt_targetPlusEnergy
    (D :
      SU7ThinSourceFeasibleDatum
        σ hσ n sourceBound sourceEnergy)
    (hroom : 2 * sourceBound < 2 * n + sourceEnergy) :
    su7LeftCode D.endpointReadout.source_label +
        su7RightCode D.endpointReadout.source_label <
      2 * n := by
  cases D.sourceBelow_or_sourceAboveRight_eq with
  | inl hbelow => exact hbelow
  | inr hmirror =>
      exact False.elim
        (D.sourceAboveRight_ne_of_twiceSourceBound_lt_targetPlusEnergy
          hroom hmirror)

/-- Closed lower-half source room implies the full zero-origin native
energy-room family.

Gate classification: selected-family coherence boundary (Gate B).  This is
source-only arithmetic on the generated source window; it uses no endpoint
projection support, atom/prime predicate, endpoint coverage, normalizer, or
repair-cell witness. -/
theorem sourceRoomBound_of_sourceBound_le_evenHalf
    {n sourceBound targetBound : Nat}
    (hbound : sourceBound ≤ n) :
    ∀ {k : Nat} (_hk : k < targetBound),
      2 * sourceBound < 2 * n + (k + 2) := by
  intro k _hk
  omega

/-- A nonempty full zero-origin native energy-room family collapses back to the
closed lower-half source window.

Gate classification: selected-family coherence boundary (Gate B).  This
prevents treating the full-family energy-room premise as a separate global
producer: the lowest shell already forces the closed lower-half source room.
-/
theorem sourceBound_le_evenHalf_of_sourceRoomBound
    {n sourceBound targetBound : Nat}
    (htarget : 0 < targetBound)
    (Hroom :
      ∀ {k : Nat} (_hk : k < targetBound),
        2 * sourceBound < 2 * n + (k + 2)) :
    sourceBound ≤ n := by
  have hroom0 : 2 * sourceBound < 2 * n + (0 + 2) :=
    Hroom (k := 0) htarget
  omega

/-- For a nonempty native family indexed from `k = 0`, the full energy-room
premise is equivalent to the closed lower-half source window.

Gate classification: selected-family coherence boundary (Gate B).  The
pointwise `k`-local energy-room theorem remains useful; the full-domain version
does not create a new global route beyond `sourceBound ≤ n`. -/
theorem sourceRoomBound_iff_sourceBound_le_evenHalf_of_positiveTargetBound
    {n sourceBound targetBound : Nat}
    (htarget : 0 < targetBound) :
    (∀ {k : Nat} (_hk : k < targetBound),
        2 * sourceBound < 2 * n + (k + 2)) ↔
      sourceBound ≤ n := by
  constructor
  · exact sourceBound_le_evenHalf_of_sourceRoomBound htarget
  · exact sourceRoomBound_of_sourceBound_le_evenHalf

/-- Closed lower-half source room also rules out the exact source-label
mirror branch for a positive datum.

Gate classification: selected-family coherence source-room theorem (Gate B).
This is sharper than the coarse `2*sourceBound < 2*n + sourceEnergy` route:
it uses the generated source label's left code directly, so the mirror
right code `2*n + sourceEnergy - left` lies beyond the source list.  No
endpoint projection support, atom/prime predicate, endpoint coverage,
normalizer, or repair-cell witness is used. -/
theorem sourceLabelRoomBound_of_sourceBound_le_evenHalf_of_positiveEnergy
    (D :
      SU7ThinSourceFeasibleDatum
        σ hσ n sourceBound sourceEnergy)
    (henergy : sourceEnergy ≠ 0)
    (hbound : sourceBound ≤ n) :
    sourceBound < 2 * n + sourceEnergy -
      su7LeftCode D.endpointReadout.source_label := by
  have hleft :
      su7LeftCode D.endpointReadout.source_label =
        D.producedCell.sourceCell.cell.leftWeightCode := by
    simpa [su7LeftCode] using D.endpointReadout.left_code_reads_source
  have hleft_le :
      su7LeftCode D.endpointReadout.source_label ≤ sourceBound := by
    rw [hleft]
    exact
      SaturationMonoid.StandardModelConstraint.SU7ProducedActiveCellA6EndpointSourceReadout.su7ProducedActiveCell_sourceLeft_le_bound
        D.producedCell
  have henergy_pos : 0 < sourceEnergy := Nat.pos_of_ne_zero henergy
  omega

/-- Closed lower-half source room excludes the exact over-target mirror branch
for a positive datum.

Gate classification: selected-family coherence no-mirror theorem (Gate B).
This names the branch-forcing consequence of the source-room theorem above:
the only non-below branch would put the mirror right endpoint outside the
generated source list. -/
theorem sourceAboveRight_ne_of_sourceBound_le_evenHalf_of_positiveEnergy
    (D :
      SU7ThinSourceFeasibleDatum
        σ hσ n sourceBound sourceEnergy)
    (henergy : sourceEnergy ≠ 0)
    (hbound : sourceBound ≤ n) :
    su7RightCode D.endpointReadout.source_label ≠
      2 * n + sourceEnergy -
        su7LeftCode D.endpointReadout.source_label :=
  D.sourceAboveRight_ne_of_sourceBound_lt_sourceAboveRight
    (D.sourceLabelRoomBound_of_sourceBound_le_evenHalf_of_positiveEnergy
      henergy hbound)

/-- Datum-level source-below readout transfers to the canonical concrete
endpoint-source readout of the same produced cell.

Gate classification: selected-family coherence source datum (Gate B).  This
is a faithful source-label readback theorem, not projection support or
endpoint atomhood. -/
theorem concreteEndpointSourceBelow_of_sourceBelow
    (D :
      SU7ThinSourceFeasibleDatum
        σ hσ n sourceBound sourceEnergy)
    (hbelow :
      su7LeftCode D.endpointReadout.source_label +
          su7RightCode D.endpointReadout.source_label < 2 * n) :
    let R0 :=
      SaturationMonoid.StandardModelConstraint.su7A6ConcreteEndpointSourceReadout
        D.producedCell
    SaturationMonoid.StandardModelConstraint.su7A6EndpointSourceLeftCodeOf
        R0.source_label +
      SaturationMonoid.StandardModelConstraint.su7A6EndpointSourceRightCodeOf
        R0.source_label < 2 * n := by
  let A := D.producedCell
  let R0 :=
    SaturationMonoid.StandardModelConstraint.su7A6ConcreteEndpointSourceReadout
      A
  have hdatum_left :
      su7LeftCode D.endpointReadout.source_label =
        A.sourceCell.cell.leftWeightCode := by
    simpa [A, su7LeftCode] using D.endpointReadout.left_code_reads_source
  have hdatum_right :
      su7RightCode D.endpointReadout.source_label =
        A.sourceCell.cell.rightWeightCode := by
    simpa [A, su7RightCode] using D.endpointReadout.right_code_reads_source
  have hcell :
      A.sourceCell.cell.leftWeightCode +
          A.sourceCell.cell.rightWeightCode < 2 * n := by
    simpa [hdatum_left, hdatum_right] using hbelow
  have hleft :
      SaturationMonoid.StandardModelConstraint.su7A6EndpointSourceLeftCodeOf
          R0.source_label =
        A.sourceCell.cell.leftWeightCode := by
    simpa [R0,
      SaturationMonoid.StandardModelConstraint.su7A6ConcreteEndpointSourceGrammar]
      using R0.left_code_reads_source
  have hright :
      SaturationMonoid.StandardModelConstraint.su7A6EndpointSourceRightCodeOf
          R0.source_label =
        A.sourceCell.cell.rightWeightCode := by
    simpa [R0,
      SaturationMonoid.StandardModelConstraint.su7A6ConcreteEndpointSourceGrammar]
      using R0.right_code_reads_source
  simpa [A, R0, hleft, hright] using hcell

/-- A positive thin source datum in the closed lower-half source window reads
below the target hyperplane.

Gate classification: selected-family coherence source datum.  This is a
source/grammar readout theorem for the thin positive constructor itself: the
datum carries the produced active source cell, its endpoint-source readout,
and the affine nonzero residual.  No projection support, endpoint atomhood,
coverage, normalizer, or repair-cell witness is used. -/
theorem sourceBelow_of_sourceBound_le_evenHalf_of_positiveEnergy
    (D :
      SU7ThinSourceFeasibleDatum
        σ hσ n sourceBound sourceEnergy)
    (henergy : sourceEnergy ≠ 0)
    (hbound : sourceBound ≤ n) :
    su7LeftCode D.endpointReadout.source_label +
        su7RightCode D.endpointReadout.source_label <
      2 * n := by
  have hpos : D.producedCell.energy ≠ 0 := by
    intro hzero
    have hsource : sourceEnergy = 0 := by
      simpa [D.affine_energy] using hzero
    exact henergy hsource
  have hbelow :
      D.producedCell.sourceCell.cell.leftWeightCode +
          D.producedCell.sourceCell.cell.rightWeightCode <
        2 * n :=
    SaturationMonoid.StandardModelConstraint.SU7ProducedActiveCellA6EndpointSourceReadout.su7ProducedActiveCell_sourceBelow_of_sourceBound_le_evenHalf_of_positive
      D.producedCell hpos hbound
  have hleft :
      su7LeftCode D.endpointReadout.source_label =
        D.producedCell.sourceCell.cell.leftWeightCode := by
    simpa [su7LeftCode] using D.endpointReadout.left_code_reads_source
  have hright :
      su7RightCode D.endpointReadout.source_label =
        D.producedCell.sourceCell.cell.rightWeightCode := by
    simpa [su7RightCode] using D.endpointReadout.right_code_reads_source
  simpa [hleft, hright] using hbelow

/-- Any already produced active cell with the affine energy law gives the thin
source datum, using the canonical concrete endpoint-source readout. -/
def ofProducedActiveCell
    (A : SU7ActiveCell σ hσ n sourceBound)
    (henergy : A.energy = sourceEnergy) :
    SU7ThinSourceFeasibleDatum
      σ hσ n sourceBound sourceEnergy where
  producedCell := A
  endpointReadout :=
    SaturationMonoid.StandardModelConstraint.su7A6ConcreteEndpointSourceReadout
      A
  affine_energy := henergy

/-- A thin source datum exposes the canonical rich witness already carried by
its produced active cell.

Gate classification: missing-shell entry / selected-family coherence boundary.
This is not a new holonomy or downstream bridge: `SU7ProducedActiveCell`
stores the canonical rich source/phase witness by definition, so this theorem
only makes that source coordinate explicit for the same datum. -/
def canonicalRichHolonomyWitnessSigma
    (D :
      SU7ThinSourceFeasibleDatum
        σ hσ n sourceBound sourceEnergy) :
    Sigma
      (fun p : Nat × Nat =>
        SU7CanonicalRichHolonomyWitness σ hσ n sourceBound p) :=
  ⟨D.toProducedActiveCell.p, D.toProducedActiveCell.witness⟩

/-- The canonical rich witness read from a thin source datum produces exactly
the same active cell carried by that datum.

This is the small source-gluing fact needed downstream: once the observed
source-phase grammar supplies the thin datum, its canonical witness cannot
drift to another active cell. -/
theorem canonicalRichHolonomyWitness_producedActiveCell_eq
    (D :
      SU7ThinSourceFeasibleDatum
        σ hσ n sourceBound sourceEnergy) :
    SaturationMonoid.StandardModelConstraint.producedActiveCell_of_canonicalRichHolonomyWitness
        D.canonicalRichHolonomyWitnessSigma.2 =
      D.toProducedActiveCell := by
  let A := D.toProducedActiveCell
  change
    { p := A.p, witness := A.witness } = A
  cases A
  rfl

/-- The canonical rich witness read from a thin source datum has the datum's
affine shell energy. -/
theorem canonicalRichHolonomyWitness_energy_eq
    (D :
      SU7ThinSourceFeasibleDatum
        σ hσ n sourceBound sourceEnergy) :
    (SaturationMonoid.StandardModelConstraint.producedActiveCell_of_canonicalRichHolonomyWitness
        D.canonicalRichHolonomyWitnessSigma.2).energy =
      sourceEnergy := by
  rw [D.canonicalRichHolonomyWitness_producedActiveCell_eq]
  exact D.producedCell_energy_eq

end SU7ThinSourceFeasibleDatum

/-- Current-shell native active-cell successor dynamics.

This is the one-shell version of `SU7NativeActiveCellSuccessorDynamics`: the
lower SU7 source/phase, crystal, or incidence layer only has to generate the
current active source cell and its affine `k + 2` energy calibration.  It does
not require a bounded all-shell selector, endpoint coverage, atomhood,
normalizers, or repair-cell materialization. -/
structure SU7NativeCurrentActiveCellSuccessorDynamics
    {K : Type u} [Field K]
    (σ : K) (hσ : σ ≠ 1)
    (n sourceBound k : Nat) where
  activeCell :
    SU7ActiveCell σ hσ n sourceBound
  source_energy_successor :
    activeCell.energy = k + 2

namespace SU7NativeCurrentActiveCellSuccessorDynamics

variable {K : Type u} [Field K]
variable {σ : K} {hσ : σ ≠ 1}
variable {n sourceBound k : Nat}

/-- Exact current-shell constructor from the lower source coordinate.

This is the mouth the SU7 source/phase, crystal, or incidence layer must
fill if it avoids the generated-holonomy route: produce the current
representation active source cell and its affine `k + 2` energy calibration.
The endpoint-source readout and thin datum are then canonical readbacks of
that cell; no `rightCheck`, endpoint atomhood, coverage, or frozen
`su7_left_descent` selector is involved. -/
def ofProducedActiveCell
    (A : SU7ActiveCell σ hσ n sourceBound)
    (henergy : A.energy = k + 2) :
    SU7NativeCurrentActiveCellSuccessorDynamics
      σ hσ n sourceBound k where
  activeCell := A
  source_energy_successor := henergy

/-- The current-shell affine successor readout excludes zero energy. -/
theorem activeCellPos
    (D :
      SU7NativeCurrentActiveCellSuccessorDynamics
        σ hσ n sourceBound k) :
    D.activeCell.energy ≠ 0 := by
  rw [D.source_energy_successor]
  omega

/-- Current-shell native active-cell dynamics canonically produces the thin
source datum for that same shell. -/
def toThinSourceFeasibleDatum
    (D :
      SU7NativeCurrentActiveCellSuccessorDynamics
        σ hσ n sourceBound k) :
    SU7ThinSourceFeasibleDatum σ hσ n sourceBound (k + 2) :=
  SU7ThinSourceFeasibleDatum.ofProducedActiveCell
    D.activeCell D.source_energy_successor

/-- The exact produced-active-cell constructor generates the canonical thin
source datum for the same current shell. -/
theorem toThinSourceFeasibleDatum_ofProducedActiveCell
    (A : SU7ActiveCell σ hσ n sourceBound)
    (henergy : A.energy = k + 2) :
    (ofProducedActiveCell
        (σ := σ) (hσ := hσ) (n := n) (sourceBound := sourceBound) (k := k)
        A henergy).toThinSourceFeasibleDatum =
      SU7ThinSourceFeasibleDatum.ofProducedActiveCell A henergy := by
  rfl

/-- The current thin datum generated from native current dynamics carries
exactly the generated active cell. -/
theorem toThinSourceFeasibleDatum_activeCell
    (D :
      SU7NativeCurrentActiveCellSuccessorDynamics
        σ hσ n sourceBound k) :
    D.toThinSourceFeasibleDatum.toProducedActiveCell = D.activeCell := by
  rfl

/-- Theorem form: current-shell native active-cell dynamics produces the
current thin source datum. -/
theorem nonempty_thin_source_feasible_datum
    (D :
      SU7NativeCurrentActiveCellSuccessorDynamics
        σ hσ n sourceBound k) :
    Nonempty
      { T : SU7ThinSourceFeasibleDatum σ hσ n sourceBound (k + 2) //
        T.toProducedActiveCell = D.activeCell ∧
          T.toProducedActiveCell.energy = k + 2 } := by
  refine ⟨⟨D.toThinSourceFeasibleDatum, ?_⟩⟩
  exact ⟨rfl, D.source_energy_successor⟩

end SU7NativeCurrentActiveCellSuccessorDynamics

/-- Bounded thin source constructor family.

For each target successor shell `k + 1`, the source side supplies a produced
active datum whose faithful endpoint readout has affine energy `k + 2`.  This
is the positive producer route that feeds the existing active-cell dynamics;
it is not a permanent-holonomy/no-predecessor family. -/
structure SU7NativeThinSourceSuccessorFamily
    {K : Type u} [Field K]
    (σ : K) (hσ : σ ≠ 1)
    (n sourceBound targetBound : Nat) where
  fallbackLabel : SU7Label
  sourceDatum :
    ∀ (k : Nat), k < targetBound ->
      SU7ThinSourceFeasibleDatum σ hσ n sourceBound (k + 2)

namespace SU7NativeThinSourceSuccessorFamily

variable {K : Type u} [Field K]
variable {σ : K} {hσ : σ ≠ 1}
variable {n sourceBound targetBound : Nat}

/-- Active cell selected by the thin source constructor at shell `k`. -/
def activeCell
    (F :
      SU7NativeThinSourceSuccessorFamily
        σ hσ n sourceBound targetBound)
    (k : Nat) (hk : k < targetBound) :
    SU7ActiveCell σ hσ n sourceBound :=
  (F.sourceDatum k hk).toProducedActiveCell

/-- The thin source constructor supplies the affine successor calibration
required by native active-cell dynamics. -/
theorem activeCell_energy_eq
    (F :
      SU7NativeThinSourceSuccessorFamily
        σ hσ n sourceBound targetBound)
    {k : Nat} (hk : k < targetBound) :
    (F.activeCell k hk).energy = k + 2 :=
  (F.sourceDatum k hk).producedCell_energy_eq

/-- Restrict a bounded thin source family to the current-shell native
active-cell dynamics mouth.

This is only a shell restriction: the produced active cell and affine energy
law are read from the same thin datum family, with no endpoint coverage,
atomhood, normalizer, or repair witness added. -/
def toNativeCurrentActiveCellSuccessorDynamics
    (F :
      SU7NativeThinSourceSuccessorFamily
        σ hσ n sourceBound targetBound)
    {k : Nat} (hk : k < targetBound) :
    SU7NativeCurrentActiveCellSuccessorDynamics
      σ hσ n sourceBound k where
  activeCell := F.activeCell k hk
  source_energy_successor := F.activeCell_energy_eq hk

/-- The faithful endpoint readout of the selected thin source datum has raw
endpoint-code energy `k + 2`. -/
theorem endpoint_raw_energy_successor
    (F :
      SU7NativeThinSourceSuccessorFamily
        σ hσ n sourceBound targetBound)
    {k : Nat} (hk : k < targetBound) :
    su7RawCodePairResidualEnergy n
        (su7LeftCode (F.sourceDatum k hk).endpointReadout.source_label)
        (su7RightCode (F.sourceDatum k hk).endpointReadout.source_label) =
      k + 2 :=
  (F.sourceDatum k hk).endpoint_raw_energy_eq

/-- Each selected thin source datum is either under the target hyperplane or
records the exact over-target mirror branch.

Gate classification: selected-family coherence source-family theorem (Gate B).
The theorem keeps branch choice at the source-datum/readout layer; it does not
mention endpoint projection, atomhood, coverage, normalizers, or repair
materialization. -/
theorem sourceDatum_sourceBelow_or_sourceAboveRight_eq
    (F :
      SU7NativeThinSourceSuccessorFamily
        σ hσ n sourceBound targetBound)
    {k : Nat} (hk : k < targetBound) :
    su7LeftCode (F.sourceDatum k hk).endpointReadout.source_label +
          su7RightCode (F.sourceDatum k hk).endpointReadout.source_label <
        2 * n ∨
      su7RightCode (F.sourceDatum k hk).endpointReadout.source_label =
        2 * n + (k + 2) -
          su7LeftCode (F.sourceDatum k hk).endpointReadout.source_label :=
  (F.sourceDatum k hk).sourceBelow_or_sourceAboveRight_eq

/-- Excluding the exact over-target mirror branch forces the selected thin
source datum under the target hyperplane.

Gate classification: selected-family coherence source-family theorem (Gate B).
This is the sharp source/grammar selector mouth exposed by the mirror
decomposition: SU7 must rule out the mirror branch, not provide endpoint
projection support or coverage. -/
theorem sourceDatum_sourceBelow_of_not_sourceAboveRight
    (F :
      SU7NativeThinSourceSuccessorFamily
        σ hσ n sourceBound targetBound)
    {k : Nat} (hk : k < targetBound)
    (hnoMirror :
      su7RightCode (F.sourceDatum k hk).endpointReadout.source_label ≠
        2 * n + (k + 2) -
          su7LeftCode (F.sourceDatum k hk).endpointReadout.source_label) :
    su7LeftCode (F.sourceDatum k hk).endpointReadout.source_label +
        su7RightCode (F.sourceDatum k hk).endpointReadout.source_label <
      2 * n := by
  cases F.sourceDatum_sourceBelow_or_sourceAboveRight_eq hk with
  | inl hbelow => exact hbelow
  | inr hmirror => exact False.elim (hnoMirror hmirror)

/-- Shell-local source room rules out the exact mirror branch for the selected
thin source datum.

Gate classification: selected-family coherence source-family theorem (Gate B).
This exposes the source-list reason behind the no-mirror premise: the mirror
right code would be outside the generated source bound. -/
theorem sourceDatum_noSourceAboveRight_of_sourceRoomBound
    (F :
      SU7NativeThinSourceSuccessorFamily
        σ hσ n sourceBound targetBound)
    {k : Nat} (hk : k < targetBound)
    (hroom :
      sourceBound < 2 * n + (k + 2) -
        su7LeftCode (F.sourceDatum k hk).endpointReadout.source_label) :
    su7RightCode (F.sourceDatum k hk).endpointReadout.source_label ≠
      2 * n + (k + 2) -
        su7LeftCode (F.sourceDatum k hk).endpointReadout.source_label :=
  (F.sourceDatum k hk).sourceAboveRight_ne_of_sourceBound_lt_sourceAboveRight
    hroom

/-- Energy-room source list bounds rule out the exact mirror branch for the
selected thin source datum.

Gate classification: selected-family coherence source-family theorem (Gate B).
This is the native shell form of source-only completion room:
`2*sourceBound < 2*n + (k+2)` prevents the selected source datum from hiding
in the over-target mirror branch. -/
theorem sourceDatum_noSourceAboveRight_of_twiceSourceBound_lt_targetPlusEnergy
    (F :
      SU7NativeThinSourceSuccessorFamily
        σ hσ n sourceBound targetBound)
    {k : Nat} (hk : k < targetBound)
    (hroom : 2 * sourceBound < 2 * n + (k + 2)) :
    su7RightCode (F.sourceDatum k hk).endpointReadout.source_label ≠
      2 * n + (k + 2) -
        su7LeftCode (F.sourceDatum k hk).endpointReadout.source_label :=
  (F.sourceDatum k hk).sourceAboveRight_ne_of_twiceSourceBound_lt_targetPlusEnergy
    hroom

/-- Energy-room source list bounds force the selected thin source datum under
the target hyperplane.

Gate classification: selected-family coherence source-family theorem (Gate B).
This is a source-only route to datum-level source-below, strictly before
projection support, endpoint atomhood, coverage, normalizers, or repair
materialization. -/
theorem sourceDatum_sourceBelow_of_twiceSourceBound_lt_targetPlusEnergy
    (F :
      SU7NativeThinSourceSuccessorFamily
        σ hσ n sourceBound targetBound)
    {k : Nat} (hk : k < targetBound)
    (hroom : 2 * sourceBound < 2 * n + (k + 2)) :
    su7LeftCode (F.sourceDatum k hk).endpointReadout.source_label +
        su7RightCode (F.sourceDatum k hk).endpointReadout.source_label <
      2 * n := by
  exact
    (F.sourceDatum k hk).sourceBelow_of_twiceSourceBound_lt_targetPlusEnergy
      hroom

/-- The selected thin source datum at every shell reads below the target
hyperplane under the closed lower-half source window.

Gate classification: selected-family coherence source-family theorem.  This
keeps the selected source-left / energy / raw-unit entrance at the
source-constructor layer: the nonzero residual is the affine `k+2` carried by
the thin datum, not an endpoint coverage or repair premise. -/
theorem sourceDatum_sourceBelow_of_sourceBound_le_evenHalf
    (F :
      SU7NativeThinSourceSuccessorFamily
        σ hσ n sourceBound targetBound)
    (hbound : sourceBound ≤ n)
    {k : Nat} (hk : k < targetBound) :
    su7LeftCode (F.sourceDatum k hk).endpointReadout.source_label +
        su7RightCode (F.sourceDatum k hk).endpointReadout.source_label <
      2 * n := by
  exact
    (F.sourceDatum k hk).sourceBelow_of_sourceBound_le_evenHalf_of_positiveEnergy
      (by omega) hbound

/-- The selected thin source datum at every shell has exact source-label room
under the closed lower-half source window.

Gate classification: selected-family coherence source-family theorem (Gate B).
This is the closed-window production of the sharper mirror-exclusion input:
source label + energy + finite room already rule out the over-target mirror,
before projection support, atomhood, primality, endpoint coverage, normalizer,
or repair-cell materialization enter the picture. -/
theorem sourceDatum_sourceLabelRoomBound_of_sourceBound_le_evenHalf
    (F :
      SU7NativeThinSourceSuccessorFamily
        σ hσ n sourceBound targetBound)
    (hbound : sourceBound ≤ n)
    {k : Nat} (hk : k < targetBound) :
    sourceBound < 2 * n + (k + 2) -
      su7LeftCode (F.sourceDatum k hk).endpointReadout.source_label := by
  exact
    (F.sourceDatum k hk).sourceLabelRoomBound_of_sourceBound_le_evenHalf_of_positiveEnergy
      (by omega) hbound

/-- Under the closed lower-half source window, the selected thin source datum
cannot take the over-target mirror branch.

Gate classification: selected-family coherence no-mirror theorem (Gate B).
This is the family-level source/phase selector statement produced from source
label + energy + room; it still has no projection support, prime endpoint,
atomhood, endpoint coverage, normalizer, or repair-cell premise. -/
theorem sourceDatum_noSourceAboveRight_of_sourceBound_le_evenHalf
    (F :
      SU7NativeThinSourceSuccessorFamily
        σ hσ n sourceBound targetBound)
    (hbound : sourceBound ≤ n)
    {k : Nat} (hk : k < targetBound) :
    su7RightCode (F.sourceDatum k hk).endpointReadout.source_label ≠
      2 * n + (k + 2) -
        su7LeftCode (F.sourceDatum k hk).endpointReadout.source_label := by
  exact
    (F.sourceDatum k hk).sourceAboveRight_ne_of_sourceBound_le_evenHalf_of_positiveEnergy
      (by omega) hbound

/-- Thin source constructors adapt directly to the existing active-cell
successor dynamics. -/
def toNativeActiveCellSuccessorDynamics
    (F :
      SU7NativeThinSourceSuccessorFamily
        σ hσ n sourceBound targetBound) :
    SU7NativeActiveCellSuccessorDynamics
      σ hσ n sourceBound targetBound where
  fallbackLabel := F.fallbackLabel
  activeCell := F.activeCell
  source_energy_successor := by
    intro k hk
    exact F.activeCell_energy_eq hk

/-- Theorem form: thin source constructors produce native active-cell
successor dynamics. -/
theorem nonempty_native_active_cell_successor_dynamics
    (F :
      SU7NativeThinSourceSuccessorFamily
        σ hσ n sourceBound targetBound) :
    Nonempty
      (SU7NativeActiveCellSuccessorDynamics
        σ hσ n sourceBound targetBound) :=
  ⟨F.toNativeActiveCellSuccessorDynamics⟩

end SU7NativeThinSourceSuccessorFamily

namespace SU7NativeActiveCellSuccessorDynamics

variable {K : Type u} [Field K]
variable {σ : K} {hσ : σ ≠ 1}
variable {n sourceBound targetBound : Nat}

/-- Native active-cell dynamics canonically exposes the thin source family.

Gate classification: selected-family coherence theorem (Gate B).  This is the
source-only normalization from active SU7 source cells to the datum layer that
carries source label, affine energy, and finite-room/mirror readout.  It does
not introduce projection support, atomhood, primality, endpoint coverage,
normalizers, or repair-cell materialization. -/
def toNativeThinSourceSuccessorFamily
    (D :
      SU7NativeActiveCellSuccessorDynamics
        σ hσ n sourceBound targetBound) :
    SU7NativeThinSourceSuccessorFamily
      σ hσ n sourceBound targetBound where
  fallbackLabel := D.fallbackLabel
  sourceDatum := fun k hk =>
    SU7ThinSourceFeasibleDatum.ofProducedActiveCell
      (D.activeCell k hk)
      (D.source_energy_successor hk)

/-- Theorem form: native active-cell dynamics produces the canonical thin
source family. -/
theorem nonempty_native_thin_source_successor_family
    (D :
      SU7NativeActiveCellSuccessorDynamics
        σ hσ n sourceBound targetBound) :
    Nonempty
      (SU7NativeThinSourceSuccessorFamily
        σ hσ n sourceBound targetBound) :=
  ⟨D.toNativeThinSourceSuccessorFamily⟩

/-- Restrict bounded native active-cell dynamics to the current-shell native
mouth.

The adapter preserves the exact selected active cell and affine `k + 2`
readout at shell `k`; it is the bounded-to-current producer reduction used by
the current source/phase grammar gate. -/
def toNativeCurrentActiveCellSuccessorDynamics
    (D :
      SU7NativeActiveCellSuccessorDynamics
        σ hσ n sourceBound targetBound)
    {k : Nat} (hk : k < targetBound) :
    SU7NativeCurrentActiveCellSuccessorDynamics
      σ hσ n sourceBound k where
  activeCell := D.activeCell k hk
  source_energy_successor := D.source_energy_successor hk

end SU7NativeActiveCellSuccessorDynamics

/-- Native source-dynamics payload for the active-cell successor selector.

This packages the part that must come from SU7 / GT / crystal / branching
dynamics: for each bounded successor shell, produce a canonical-rich source
witness whose raw endpoint residual is one unit above the target shell.

This older adapter is kept as a diagnostic/source-readback bridge.  It should
not be used as the positive producer route after the holonomy/permanent
calibration: the positive socket is the thin source datum and active-cell
dynamics above. -/
structure SU7NativeCanonicalRichWitnessSuccessorFamily
    {K : Type u} [Field K]
    (σ : K) (hσ : σ ≠ 1)
    (n sourceBound targetBound : Nat) where
  fallbackLabel : SU7Label
  witnessPair :
    ∀ (k : Nat), k < targetBound -> Nat × Nat
  witness :
    ∀ (k : Nat) (hk : k < targetBound),
      SU7CanonicalRichHolonomyWitness
        σ hσ n sourceBound (witnessPair k hk)
  witness_energy_successor :
    ∀ {k : Nat} (hk : k < targetBound),
      su7RawCodePairResidualEnergy n
        (witnessPair k hk).1 (witnessPair k hk).2 =
          k + 2

namespace SU7NativeCanonicalRichWitnessSuccessorFamily

variable {K : Type u} [Field K]
variable {σ : K} {hσ : σ ≠ 1}
variable {n sourceBound targetBound : Nat}

/-- Turn a native canonical-rich source witness into the produced active cell
used by the generated projection-core law. -/
def activeCell
    (F :
      SU7NativeCanonicalRichWitnessSuccessorFamily
        σ hσ n sourceBound targetBound)
    (k : Nat) (hk : k < targetBound) :
    SU7ActiveCell σ hσ n sourceBound :=
  SaturationMonoid.StandardModelConstraint.producedActiveCell_of_canonicalRichHolonomyWitness
    (F.witness k hk)

/-- The produced active cell selected from the canonical-rich witness reads the
same raw endpoint residual as the witness pair. -/
theorem activeCell_energy_eq_raw_witnessPair
    (F :
      SU7NativeCanonicalRichWitnessSuccessorFamily
        σ hσ n sourceBound targetBound)
    {k : Nat} (hk : k < targetBound) :
    (F.activeCell k hk).energy =
      su7RawCodePairResidualEnergy n
        (F.witnessPair k hk).1 (F.witnessPair k hk).2 := by
  let W := F.witness k hk
  let A :=
    SaturationMonoid.StandardModelConstraint.producedActiveCell_of_canonicalRichHolonomyWitness
      W
  have hleft :
      A.sourceCell.cell.leftWeightCode = (F.witnessPair k hk).1 := by
    simpa [A,
      SaturationMonoid.StandardModelConstraint.producedActiveCell_of_canonicalRichHolonomyWitness,
      SaturationMonoid.StandardModelConstraint.SU7ProducedActiveCell.sourceCell,
      SaturationMonoid.StandardModelConstraint.SU7ProducedActiveCell.sourceLift]
      using W.source_lift.source_left
  have hright :
      A.sourceCell.cell.rightWeightCode = (F.witnessPair k hk).2 := by
    simpa [A,
      SaturationMonoid.StandardModelConstraint.producedActiveCell_of_canonicalRichHolonomyWitness,
      SaturationMonoid.StandardModelConstraint.SU7ProducedActiveCell.sourceCell,
      SaturationMonoid.StandardModelConstraint.SU7ProducedActiveCell.sourceLift]
      using W.source_lift.source_right
  have henergy :
      A.energy =
        su7RawCodePairResidualEnergy n
          (F.witnessPair k hk).1 (F.witnessPair k hk).2 := by
    rw [SaturationMonoid.StandardModelConstraint.SU7ProducedActiveCell.energy_eq_raw_source_pair A,
      hleft, hright]
  simpa [activeCell, W, A] using henergy

/-- The native witness family supplies the active source-energy calibration
required by the selector. -/
theorem activeCell_energy_eq
    (F :
      SU7NativeCanonicalRichWitnessSuccessorFamily
        σ hσ n sourceBound targetBound)
    {k : Nat} (hk : k < targetBound) :
    (F.activeCell k hk).energy = k + 2 :=
  (activeCell_energy_eq_raw_witnessPair F hk).trans
    (F.witness_energy_successor hk)

/-- Native canonical-rich source witnesses produce the minimal active-cell
successor dynamics: the active cell is generated from the witness, while the
affine `k + 2` calibration is inherited from the witness residual. -/
def toNativeActiveCellSuccessorDynamics
    (F :
      SU7NativeCanonicalRichWitnessSuccessorFamily
        σ hσ n sourceBound targetBound) :
    SU7NativeActiveCellSuccessorDynamics
      σ hσ n sourceBound targetBound where
  fallbackLabel := F.fallbackLabel
  activeCell := F.activeCell
  source_energy_successor := by
    intro k hk
    exact F.activeCell_energy_eq hk

/-- Native canonical-rich source witnesses prove the bounded active-cell
successor selector used by the SU7 generated projection extraction. -/
def toActiveCellSuccessorSelector
    (F :
      SU7NativeCanonicalRichWitnessSuccessorFamily
        σ hσ n sourceBound targetBound) :
    SU7GeneratedActiveCellSuccessorSelector
      σ hσ n sourceBound targetBound :=
  F.toNativeActiveCellSuccessorDynamics.toActiveCellSuccessorSelector

/-- Theorem form: native canonical-rich source dynamics produces the active
cell successor selector. -/
theorem nonempty_active_cell_successor_selector
    (F :
      SU7NativeCanonicalRichWitnessSuccessorFamily
        σ hσ n sourceBound targetBound) :
    Nonempty
      (SU7GeneratedActiveCellSuccessorSelector
        σ hσ n sourceBound targetBound) :=
  ⟨F.toActiveCellSuccessorSelector⟩

end SU7NativeCanonicalRichWitnessSuccessorFamily

/-- Current-shell native canonical-rich source witness.

This is the one-shell lower producer mouth between generated holonomy/source
coordinates and `SU7NativeCurrentActiveCellSuccessorDynamics`: it carries the
canonical-rich source witness for the current raw pair and the affine
`k + 2` residual law. -/
structure SU7NativeCurrentCanonicalRichWitness
    {K : Type u} [Field K]
    (σ : K) (hσ : σ ≠ 1)
    (n sourceBound k : Nat) where
  witnessPair : Nat × Nat
  witness :
    SU7CanonicalRichHolonomyWitness
      σ hσ n sourceBound witnessPair
  witness_energy_successor :
    su7RawCodePairResidualEnergy n witnessPair.1 witnessPair.2 =
      k + 2

namespace SU7NativeCurrentCanonicalRichWitness

variable {K : Type u} [Field K]
variable {σ : K} {hσ : σ ≠ 1}
variable {n sourceBound k : Nat}

/-- Package a bare canonical-rich source/phase witness as the current-shell
canonical-rich payload once its raw endpoint-code energy is calibrated to
`k + 2`.

This keeps the source mouth on the generated canonical-rich witness itself:
the wrapper adds only the current-shell affine energy index, not a selector or
endpoint coverage premise. -/
def ofCanonicalRichHolonomyWitness
    {p : Nat × Nat}
    (W : SU7CanonicalRichHolonomyWitness σ hσ n sourceBound p)
    (henergy :
      su7RawCodePairResidualEnergy n p.1 p.2 = k + 2) :
    SU7NativeCurrentCanonicalRichWitness
      σ hσ n sourceBound k where
  witnessPair := p
  witness := W
  witness_energy_successor := henergy

/-- Produced active cell read from the current canonical-rich witness. -/
def activeCell
    (C :
      SU7NativeCurrentCanonicalRichWitness
        σ hσ n sourceBound k) :
    SU7ActiveCell σ hσ n sourceBound :=
  SaturationMonoid.StandardModelConstraint.producedActiveCell_of_canonicalRichHolonomyWitness
    C.witness

/-- The current canonical-rich witness reads the same raw residual as its
source coordinate pair. -/
theorem activeCell_energy_eq_raw_witnessPair
    (C :
      SU7NativeCurrentCanonicalRichWitness
        σ hσ n sourceBound k) :
    C.activeCell.energy =
      su7RawCodePairResidualEnergy n
        C.witnessPair.1 C.witnessPair.2 := by
  let W := C.witness
  let A :=
    SaturationMonoid.StandardModelConstraint.producedActiveCell_of_canonicalRichHolonomyWitness
      W
  have hleft :
      A.sourceCell.cell.leftWeightCode = C.witnessPair.1 := by
    simpa [A,
      SaturationMonoid.StandardModelConstraint.producedActiveCell_of_canonicalRichHolonomyWitness,
      SaturationMonoid.StandardModelConstraint.SU7ProducedActiveCell.sourceCell,
      SaturationMonoid.StandardModelConstraint.SU7ProducedActiveCell.sourceLift]
      using W.source_lift.source_left
  have hright :
      A.sourceCell.cell.rightWeightCode = C.witnessPair.2 := by
    simpa [A,
      SaturationMonoid.StandardModelConstraint.producedActiveCell_of_canonicalRichHolonomyWitness,
      SaturationMonoid.StandardModelConstraint.SU7ProducedActiveCell.sourceCell,
      SaturationMonoid.StandardModelConstraint.SU7ProducedActiveCell.sourceLift]
      using W.source_lift.source_right
  have henergy :
      A.energy =
        su7RawCodePairResidualEnergy n
          C.witnessPair.1 C.witnessPair.2 := by
    rw [SaturationMonoid.StandardModelConstraint.SU7ProducedActiveCell.energy_eq_raw_source_pair A,
      hleft, hright]
  simpa [activeCell, W, A] using henergy

/-- The current canonical-rich witness supplies the affine energy law needed
by current native active-cell dynamics. -/
theorem activeCell_energy_eq
    (C :
      SU7NativeCurrentCanonicalRichWitness
        σ hσ n sourceBound k) :
    C.activeCell.energy = k + 2 :=
  C.activeCell_energy_eq_raw_witnessPair.trans
    C.witness_energy_successor

/-- Current canonical-rich source witnesses produce the current-shell native
active-cell dynamics. -/
def toNativeCurrentActiveCellSuccessorDynamics
    (C :
      SU7NativeCurrentCanonicalRichWitness
        σ hσ n sourceBound k) :
    SU7NativeCurrentActiveCellSuccessorDynamics
      σ hσ n sourceBound k where
  activeCell := C.activeCell
  source_energy_successor := C.activeCell_energy_eq

/-- Current canonical-rich source witnesses produce the current-shell thin
source datum directly. -/
def toThinSourceFeasibleDatum
    (C :
      SU7NativeCurrentCanonicalRichWitness
        σ hσ n sourceBound k) :
    SU7ThinSourceFeasibleDatum
      σ hσ n sourceBound (k + 2) :=
  C.toNativeCurrentActiveCellSuccessorDynamics.toThinSourceFeasibleDatum

end SU7NativeCurrentCanonicalRichWitness

/-- Current-shell generated-holonomy source payload.

This is the current-shell SU7 source/phase/crystal input: one generated P950
holonomy cell at residual `k + 2`.  The active sigma interval supplies the
canonical-rich lift, after which the current native active-cell payload is
produced without endpoint atomhood, coverage, normalizer, or repair data. -/
structure SU7NativeCurrentGeneratedHolonomy
    (n sourceBound k : Nat) where
  witnessPair : Nat × Nat
  holonomyCell :
    SU7GeneratedHolonomyCell n sourceBound witnessPair
  holonomy_energy_successor :
    su7RawCodePairResidualEnergy n witnessPair.1 witnessPair.2 =
      k + 2

namespace SU7NativeCurrentGeneratedHolonomy

variable {n sourceBound k : Nat}

/-- Package one generated P950 holonomy source cell as the current-shell
generated-holonomy payload once its raw endpoint-code energy is calibrated to
`k + 2`.

This is the lowest current-shell mouth in this file: a caller may produce the
actual generated holonomy cell directly, without first constructing active-cell
dynamics or endpoint readout data. -/
def ofGeneratedHolonomyCell
    {p : Nat × Nat}
    (H : SU7GeneratedHolonomyCell n sourceBound p)
    (henergy :
      su7RawCodePairResidualEnergy n p.1 p.2 = k + 2) :
    SU7NativeCurrentGeneratedHolonomy n sourceBound k where
  witnessPair := p
  holonomyCell := H
  holonomy_energy_successor := henergy

variable {K : Type u} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
variable {σ : K} (hσ0 : 0 < σ) (hσ1 : σ < 1)
variable {n sourceBound k : Nat}

/-- Current generated holonomy cells lift to current canonical-rich source
witnesses in the active sigma interval. -/
noncomputable def toCurrentCanonicalRichWitness
    (C :
      SU7NativeCurrentGeneratedHolonomy
        n sourceBound k) :
    SU7NativeCurrentCanonicalRichWitness
      σ (ne_of_lt hσ1) n sourceBound k where
  witnessPair := C.witnessPair
  witness :=
    Classical.choice
      ((SaturationMonoid.StandardModelConstraint.generatedFilteredRawCodePairCanonicalRichHolonomyLift_mem_Ioo
          hσ0 hσ1)
        C.witnessPair
        C.holonomyCell)
  witness_energy_successor := C.holonomy_energy_successor

/-- Current generated holonomy cells produce the current-shell native active
cell and affine energy payload. -/
noncomputable def toNativeCurrentActiveCellSuccessorDynamics
    (C :
      SU7NativeCurrentGeneratedHolonomy
        n sourceBound k) :
    SU7NativeCurrentActiveCellSuccessorDynamics
      σ (ne_of_lt hσ1) n sourceBound k :=
  (C.toCurrentCanonicalRichWitness hσ0 hσ1).toNativeCurrentActiveCellSuccessorDynamics

/-- Current generated holonomy cells produce the current-shell thin source
datum directly after the active-interval canonical-rich lift. -/
noncomputable def toThinSourceFeasibleDatum
    (C :
      SU7NativeCurrentGeneratedHolonomy
        n sourceBound k) :
    SU7ThinSourceFeasibleDatum
      σ (ne_of_lt hσ1) n sourceBound (k + 2) :=
  (C.toNativeCurrentActiveCellSuccessorDynamics hσ0 hσ1).toThinSourceFeasibleDatum

end SU7NativeCurrentGeneratedHolonomy

/-- Generated-holonomy source payload for the active-cell selector.

This is one layer closer to native SU7 branching dynamics than a canonical-rich
witness family: it asks for generated P950 holonomy source cells at the
required successor energies.  The canonical-rich phase/H1/sigma coordinates
are then supplied by the existing SU7 lift theorem on `0 < σ < 1`. -/
structure SU7NativeGeneratedHolonomySuccessorFamily
    (n sourceBound targetBound : Nat) where
  fallbackLabel : SU7Label
  witnessPair :
    ∀ (k : Nat), k < targetBound -> Nat × Nat
  holonomyCell :
    ∀ (k : Nat) (hk : k < targetBound),
      SU7GeneratedHolonomyCell n sourceBound (witnessPair k hk)
  holonomy_energy_successor :
    ∀ {k : Nat} (hk : k < targetBound),
      su7RawCodePairResidualEnergy n
        (witnessPair k hk).1 (witnessPair k hk).2 =
          k + 2

namespace SU7NativeGeneratedHolonomySuccessorFamily

variable {K : Type u} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
variable {σ : K} (hσ0 : 0 < σ) (hσ1 : σ < 1)
variable {n sourceBound targetBound : Nat}

/-- Restrict generated holonomy source dynamics to the current-shell generated
holonomy payload before performing the active-interval canonical-rich lift. -/
def toNativeCurrentGeneratedHolonomy
    (F :
      SU7NativeGeneratedHolonomySuccessorFamily
        n sourceBound targetBound)
    {k : Nat} (hk : k < targetBound) :
    SU7NativeCurrentGeneratedHolonomy n sourceBound k where
  witnessPair := F.witnessPair k hk
  holonomyCell := F.holonomyCell k hk
  holonomy_energy_successor := F.holonomy_energy_successor hk

/-- Generated holonomy cells in the active sigma interval lift to the native
canonical-rich witness family needed by the selector. -/
noncomputable def toCanonicalRichWitnessSuccessorFamily
    (F :
      SU7NativeGeneratedHolonomySuccessorFamily
        n sourceBound targetBound) :
    SU7NativeCanonicalRichWitnessSuccessorFamily
      σ (ne_of_lt hσ1) n sourceBound targetBound where
  fallbackLabel := F.fallbackLabel
  witnessPair := F.witnessPair
  witness := by
    intro k hk
    exact
      Classical.choice
        ((SaturationMonoid.StandardModelConstraint.generatedFilteredRawCodePairCanonicalRichHolonomyLift_mem_Ioo
            hσ0 hσ1)
          (F.witnessPair k hk)
          (F.holonomyCell k hk))
  witness_energy_successor := by
    intro k hk
    exact F.holonomy_energy_successor hk

/-- Generated holonomy source cells discharge the active-cell successor
selector after canonical-rich lifting. -/
noncomputable def toNativeActiveCellSuccessorDynamics
    (F :
      SU7NativeGeneratedHolonomySuccessorFamily
        n sourceBound targetBound) :
    SU7NativeActiveCellSuccessorDynamics
      σ (ne_of_lt hσ1) n sourceBound targetBound :=
  (toCanonicalRichWitnessSuccessorFamily hσ0 hσ1 F).toNativeActiveCellSuccessorDynamics

/-- Generated holonomy source cells prove the active-cell successor selector
after canonical-rich lifting. -/
noncomputable def toActiveCellSuccessorSelector
    (F :
      SU7NativeGeneratedHolonomySuccessorFamily
        n sourceBound targetBound) :
    SU7GeneratedActiveCellSuccessorSelector
      σ (ne_of_lt hσ1) n sourceBound targetBound :=
  (toNativeActiveCellSuccessorDynamics hσ0 hσ1 F).toActiveCellSuccessorSelector

/-- Restrict generated holonomy source dynamics to the current-shell native
active-cell payload. -/
noncomputable def toNativeCurrentActiveCellSuccessorDynamics
    (F :
      SU7NativeGeneratedHolonomySuccessorFamily
        n sourceBound targetBound)
    {k : Nat} (hk : k < targetBound) :
    SU7NativeCurrentActiveCellSuccessorDynamics
      σ (ne_of_lt hσ1) n sourceBound k :=
  (F.toNativeCurrentGeneratedHolonomy hk).toNativeCurrentActiveCellSuccessorDynamics
    hσ0 hσ1

/-- Theorem form: native generated holonomy source dynamics produces the
active-cell successor selector in the active sigma interval. -/
theorem nonempty_active_cell_successor_selector
    (hσ0 : 0 < σ)
    (F :
      SU7NativeGeneratedHolonomySuccessorFamily
        n sourceBound targetBound) :
    Nonempty
      (SU7GeneratedActiveCellSuccessorSelector
        σ (ne_of_lt hσ1) n sourceBound targetBound) :=
  ⟨F.toActiveCellSuccessorSelector hσ0 hσ1⟩

end SU7NativeGeneratedHolonomySuccessorFamily

/-- Strict terminality relative to one shell/window of generated branching
cells.

Unlike `NoPrimeBranchingCellStrictPermanentHolonomy`, this does not claim
global minimality in the full `generatedNoPrimeBranchingCells` list.  It is a
local terminal-tension object for a chosen window. -/
def SU7WindowedBranchingStrictHolonomy
    {n : Nat}
    (window : List (SU7GeneratedNoPrimeBranchingCell n))
    (B : SU7GeneratedNoPrimeBranchingCell n) : Prop :=
  B ∈ window ∧
    SaturationMonoid.StandardModelConstraint.noPrimeBranchingEndpointResidualEnergy
        B ≠ 0 ∧
      ∀ lower : SU7GeneratedNoPrimeBranchingCell n,
        lower ∈ window ->
          ¬
            SaturationMonoid.StandardModelConstraint.noPrimeBranchingEndpointResidualEnergy
                lower <
            SaturationMonoid.StandardModelConstraint.noPrimeBranchingEndpointResidualEnergy
                B

/-- Current-shell windowed strict branching source payload.

This is the one-shell version of
`SU7NativeWindowedStrictBranchingHolonomySuccessorFamily`: it carries one
generated branching cell, a local comparison window, and the affine source
energy `k + 2`.  It intentionally does not assert the generated P950 holonomy
projection; that remains the separate current projection law below. -/
structure SU7NativeCurrentWindowedStrictBranchingHolonomy
    (n sourceBound k : Nat) where
  fallbackLabel : SU7Label
  windowCells :
    List (SU7GeneratedNoPrimeBranchingCell n)
  branchingCell :
    SU7GeneratedNoPrimeBranchingCell n
  window_mem_generated :
    ∀ {B : SU7GeneratedNoPrimeBranchingCell n},
      B ∈ windowCells ->
        B ∈
          SaturationMonoid.StandardModelConstraint.generatedNoPrimeBranchingCells
            n sourceBound
  windowStrict :
    SU7WindowedBranchingStrictHolonomy windowCells branchingCell
  source_energy_successor :
    SaturationMonoid.StandardModelConstraint.noPrimeBranchingEndpointResidualEnergy
      branchingCell =
        k + 2

namespace SU7NativeCurrentWindowedStrictBranchingHolonomy

variable {n sourceBound k : Nat}

/-- The selected current windowed strict cell is generated in the ambient
no-prime branching list. -/
theorem cell_mem_generated
    (F :
      SU7NativeCurrentWindowedStrictBranchingHolonomy
        n sourceBound k) :
    F.branchingCell ∈
      SaturationMonoid.StandardModelConstraint.generatedNoPrimeBranchingCells
        n sourceBound :=
  F.window_mem_generated F.windowStrict.1

/-- Endpoint-code pair read from the current windowed branching cell. -/
def witnessPair
    (F :
      SU7NativeCurrentWindowedStrictBranchingHolonomy
        n sourceBound k) : Nat × Nat :=
  su7NoPrimeBranchingPair F.branchingCell

/-- The endpoint-code pair read from the current windowed branching cell has
the current affine source energy. -/
theorem holonomy_energy_successor
    (F :
      SU7NativeCurrentWindowedStrictBranchingHolonomy
        n sourceBound k) :
    su7RawCodePairResidualEnergy n
        F.witnessPair.1 F.witnessPair.2 =
      k + 2 := by
  rw [witnessPair, su7NoPrimeBranchingPair_raw_energy_eq,
    F.source_energy_successor]

/-- Singleton-window construction from one generated source cell.

This is useful for current-shell producers that already have the generated
branching cell and only need the local windowed-strict interface. -/
def ofGeneratedSourceCellSingletonWindow
    (fallbackLabel : SU7Label)
    (B : SU7GeneratedNoPrimeBranchingCell n)
    (hmem :
      B ∈
        SaturationMonoid.StandardModelConstraint.generatedNoPrimeBranchingCells
          n sourceBound)
    (henergy :
      SaturationMonoid.StandardModelConstraint.noPrimeBranchingEndpointResidualEnergy
        B =
          k + 2) :
    SU7NativeCurrentWindowedStrictBranchingHolonomy
      n sourceBound k where
  fallbackLabel := fallbackLabel
  windowCells := [B]
  branchingCell := B
  window_mem_generated := by
    intro B' hB'
    simp only [List.mem_singleton] at hB'
    rw [hB']
    exact hmem
  windowStrict := by
    refine ⟨?_, ?_, ?_⟩
    · simp
    · intro hzero
      have hsource : k + 2 = 0 := by
        rw [← henergy, hzero]
      omega
    · intro lower hlower hlt
      simp only [List.mem_singleton] at hlower
      rw [hlower] at hlt
      exact
        (Nat.lt_irrefl
          (SaturationMonoid.StandardModelConstraint.noPrimeBranchingEndpointResidualEnergy
            B)) hlt
  source_energy_successor := henergy

end SU7NativeCurrentWindowedStrictBranchingHolonomy

/-- Current-shell relative projection law for windowed strict branching.

The law is deliberately one shell wide: it turns the current windowed strict
source cell into the generated P950 holonomy payload for that same shell,
without asking for a bounded family or global strict minimality. -/
structure SU7CurrentWindowedStrictBranchingHolonomyProjectionLaw
    (n sourceBound k : Nat) where
  holonomyCell :
    ∀ (F :
        SU7NativeCurrentWindowedStrictBranchingHolonomy
          n sourceBound k),
      SU7GeneratedHolonomyCell n sourceBound
        (F.witnessPair)

namespace SU7NativeCurrentWindowedStrictBranchingHolonomy

variable {n sourceBound k : Nat}

/-- Current windowed strict branching plus its current projection law supplies
the current-shell generated P950 holonomy payload. -/
def toNativeCurrentGeneratedHolonomy
    (P :
      SU7CurrentWindowedStrictBranchingHolonomyProjectionLaw
        n sourceBound k)
    (F :
      SU7NativeCurrentWindowedStrictBranchingHolonomy
        n sourceBound k) :
    SU7NativeCurrentGeneratedHolonomy n sourceBound k where
  witnessPair := F.witnessPair
  holonomyCell := P.holonomyCell F
  holonomy_energy_successor := F.holonomy_energy_successor

/-- Current windowed strict branching plus a strict permanent-holonomy proof
for that same current source cell supplies the current-shell generated P950
holonomy payload.

This is the narrow, pointwise producer mouth below the projection-law wrapper:
it consumes only the strict terminal/holonomy fact for `F.branchingCell`, not a
global `∀ F` projection law and not endpoint atomhood, coverage, or selected
left-descent fields. -/
def toNativeCurrentGeneratedHolonomy_of_strictPermanentHolonomy
    (F :
      SU7NativeCurrentWindowedStrictBranchingHolonomy
        n sourceBound k)
    (Hstrict :
      SU7GeneratedStrictBranchingHolonomy
        n sourceBound F.branchingCell) :
    SU7NativeCurrentGeneratedHolonomy n sourceBound k where
  witnessPair := F.witnessPair
  holonomyCell := by
    dsimp [witnessPair, SU7GeneratedHolonomyCell, su7NoPrimeBranchingPair]
    simpa [SaturationMonoid.StandardModelConstraint.generatedNoPrimeAllowedPredicate]
      using
        SaturationMonoid.StandardModelConstraint.filteredRawCodePairHolonomy_of_noPrimeStrictHolonomy
          (SaturationMonoid.StandardModelConstraint.generatedNoPrimeBranchingCellsWithinBound
            n sourceBound)
          Hstrict
  holonomy_energy_successor := F.holonomy_energy_successor

/-- Current windowed strict branching plus its projection law produces the
current-shell native active-cell payload after the canonical-rich lift. -/
noncomputable def toNativeCurrentActiveCellSuccessorDynamics
    {K : Type u} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    {σ : K} (hσ0 : 0 < σ) (hσ1 : σ < 1)
    (P :
      SU7CurrentWindowedStrictBranchingHolonomyProjectionLaw
        n sourceBound k)
    (F :
      SU7NativeCurrentWindowedStrictBranchingHolonomy
        n sourceBound k) :
    SU7NativeCurrentActiveCellSuccessorDynamics
      σ (ne_of_lt hσ1) n sourceBound k :=
  (F.toNativeCurrentGeneratedHolonomy P).toNativeCurrentActiveCellSuccessorDynamics
    hσ0 hσ1

end SU7NativeCurrentWindowedStrictBranchingHolonomy

/-- Windowed strict branching source payload.

This is the relative-minimality replacement for the global strict branching
family.  Each successor shell has its own window, so cells at energies `2` and
`3` no longer have to be simultaneous global minima of one fixed list. -/
structure SU7NativeWindowedStrictBranchingHolonomySuccessorFamily
    (n sourceBound targetBound : Nat) where
  fallbackLabel : SU7Label
  windowCells :
    ∀ (k : Nat), k < targetBound ->
      List (SU7GeneratedNoPrimeBranchingCell n)
  branchingCell :
    ∀ (k : Nat), k < targetBound ->
      SU7GeneratedNoPrimeBranchingCell n
  window_mem_generated :
    ∀ {k : Nat} (hk : k < targetBound)
      {B : SU7GeneratedNoPrimeBranchingCell n},
      B ∈ windowCells k hk ->
        B ∈
          SaturationMonoid.StandardModelConstraint.generatedNoPrimeBranchingCells
            n sourceBound
  windowStrict :
    ∀ (k : Nat) (hk : k < targetBound),
      SU7WindowedBranchingStrictHolonomy
        (windowCells k hk) (branchingCell k hk)
  source_energy_successor :
    ∀ {k : Nat} (hk : k < targetBound),
      SaturationMonoid.StandardModelConstraint.noPrimeBranchingEndpointResidualEnergy
        (branchingCell k hk) =
          k + 2

namespace SU7NativeWindowedStrictBranchingHolonomySuccessorFamily

variable {n sourceBound targetBound : Nat}

/-- The selected windowed strict cell is still generated in the ambient
no-prime branching list. -/
theorem cell_mem_generated
    (F :
      SU7NativeWindowedStrictBranchingHolonomySuccessorFamily
        n sourceBound targetBound)
    {k : Nat} (hk : k < targetBound) :
    F.branchingCell k hk ∈
      SaturationMonoid.StandardModelConstraint.generatedNoPrimeBranchingCells
        n sourceBound := by
  exact F.window_mem_generated hk (F.windowStrict k hk).1

/-- Endpoint-code pair read from the selected windowed branching cell. -/
def witnessPair
    (F :
      SU7NativeWindowedStrictBranchingHolonomySuccessorFamily
        n sourceBound targetBound)
    (k : Nat) (hk : k < targetBound) : Nat × Nat :=
  su7NoPrimeBranchingPair (F.branchingCell k hk)

/-- The endpoint-code pair read from the windowed branching cell has the
successor source energy required by the generated holonomy family. -/
theorem holonomy_energy_successor
    (F :
      SU7NativeWindowedStrictBranchingHolonomySuccessorFamily
        n sourceBound targetBound)
    {k : Nat} (hk : k < targetBound) :
    su7RawCodePairResidualEnergy n
        (F.witnessPair k hk).1 (F.witnessPair k hk).2 =
      k + 2 := by
  rw [witnessPair, su7NoPrimeBranchingPair_raw_energy_eq,
    F.source_energy_successor hk]

/-- Singleton-window construction from a bounded branching source selector.

This is a positive construction showing that the windowed strict interface
does not repeat the global-minimality collision: each selected source cell is
minimal in its own singleton window. -/
def ofSourceSelectorSingletonWindow
    (fallbackLabel : SU7Label)
    (S :
      SU7NativeBranchingSourceSelector
        n sourceBound targetBound) :
    SU7NativeWindowedStrictBranchingHolonomySuccessorFamily
      n sourceBound targetBound where
  fallbackLabel := fallbackLabel
  windowCells := fun k hk => [S.sourceCell k hk]
  branchingCell := S.sourceCell
  window_mem_generated := by
    intro k hk B hmem
    simp only [List.mem_singleton] at hmem
    rw [hmem]
    exact S.source_mem hk
  windowStrict := by
    intro k hk
    refine ⟨?_, ?_, ?_⟩
    · simp
    · exact S.source_energy_ne_zero hk
    · intro lower hlower hlt
      simp only [List.mem_singleton] at hlower
      rw [hlower] at hlt
      exact (Nat.lt_irrefl
        (SaturationMonoid.StandardModelConstraint.noPrimeBranchingEndpointResidualEnergy
          (S.sourceCell k hk))) hlt
  source_energy_successor := S.source_energy_successor

end SU7NativeWindowedStrictBranchingHolonomySuccessorFamily

/-- Missing relative-to-global projection law for windowed strict branching.

This is the precise new SU7-side target if strict branching is to re-enter the
positive bounded route: a windowed terminal cell must project to the generated
raw-code holonomy cell without requiring global minimality in the whole
generated list. -/
structure SU7WindowedStrictBranchingHolonomyProjectionLaw
    (n sourceBound targetBound : Nat) where
  holonomyCell :
    ∀ (F :
        SU7NativeWindowedStrictBranchingHolonomySuccessorFamily
          n sourceBound targetBound)
      (k : Nat) (hk : k < targetBound),
      SU7GeneratedHolonomyCell n sourceBound
        (F.witnessPair k hk)

namespace SU7NativeWindowedStrictBranchingHolonomySuccessorFamily

variable {n sourceBound targetBound : Nat}

/-- Windowed strict branching plus its relative projection law supplies the
generated holonomy source family used by the positive route. -/
def toGeneratedHolonomySuccessorFamily
    (P :
      SU7WindowedStrictBranchingHolonomyProjectionLaw
        n sourceBound targetBound)
    (F :
      SU7NativeWindowedStrictBranchingHolonomySuccessorFamily
        n sourceBound targetBound) :
    SU7NativeGeneratedHolonomySuccessorFamily
      n sourceBound targetBound where
  fallbackLabel := F.fallbackLabel
  witnessPair := F.witnessPair
  holonomyCell := P.holonomyCell F
  holonomy_energy_successor := by
    intro k hk
    exact F.holonomy_energy_successor hk

/-- Windowed strict branching plus its relative projection law restricts
directly to the current-shell generated holonomy payload. -/
def toNativeCurrentGeneratedHolonomy
    (P :
      SU7WindowedStrictBranchingHolonomyProjectionLaw
        n sourceBound targetBound)
    (F :
      SU7NativeWindowedStrictBranchingHolonomySuccessorFamily
        n sourceBound targetBound)
    {k : Nat} (hk : k < targetBound) :
    SU7NativeCurrentGeneratedHolonomy n sourceBound k :=
  (F.toGeneratedHolonomySuccessorFamily P).toNativeCurrentGeneratedHolonomy hk

/-- Windowed strict branching plus its relative projection law produces the
current-shell native active-cell payload after the canonical-rich lift. -/
noncomputable def toNativeCurrentActiveCellSuccessorDynamics
    {K : Type u} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    {σ : K} (hσ0 : 0 < σ) (hσ1 : σ < 1)
    (P :
      SU7WindowedStrictBranchingHolonomyProjectionLaw
        n sourceBound targetBound)
    (F :
      SU7NativeWindowedStrictBranchingHolonomySuccessorFamily
        n sourceBound targetBound)
    {k : Nat} (hk : k < targetBound) :
    SU7NativeCurrentActiveCellSuccessorDynamics
      σ (ne_of_lt hσ1) n sourceBound k :=
  (F.toNativeCurrentGeneratedHolonomy P hk).toNativeCurrentActiveCellSuccessorDynamics
    hσ0 hσ1

/-- Windowed strict branching source cells adapt to the active-cell selector
once the relative projection law is supplied. -/
noncomputable def toActiveCellSuccessorSelector
    {K : Type u} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    {σ : K} (hσ0 : 0 < σ) (hσ1 : σ < 1)
    (P :
      SU7WindowedStrictBranchingHolonomyProjectionLaw
        n sourceBound targetBound)
    (F :
      SU7NativeWindowedStrictBranchingHolonomySuccessorFamily
        n sourceBound targetBound) :
    SU7GeneratedActiveCellSuccessorSelector
      σ (ne_of_lt hσ1) n sourceBound targetBound :=
  (F.toGeneratedHolonomySuccessorFamily P).toActiveCellSuccessorSelector
    hσ0 hσ1

end SU7NativeWindowedStrictBranchingHolonomySuccessorFamily

/-- Native strict branching terminal-tension payload.

This is not a bounded positive successor-family interface: strict permanent
holonomy is global-minimal in one fixed generated list, so two different
successor energies collide.  The structure is retained as a single-shell
terminal-tension diagnostic and as a warning about the needed relative/windowed
minimality redesign. -/
structure SU7NativeStrictBranchingHolonomySuccessorFamily
    (n sourceBound targetBound : Nat) where
  fallbackLabel : SU7Label
  branchingCell :
    ∀ (k : Nat), k < targetBound ->
      SU7GeneratedNoPrimeBranchingCell n
  strictHolonomy :
    ∀ (k : Nat) (hk : k < targetBound),
      SU7GeneratedStrictBranchingHolonomy
        n sourceBound (branchingCell k hk)
  source_energy_successor :
    ∀ {k : Nat} (hk : k < targetBound),
      SaturationMonoid.StandardModelConstraint.noPrimeBranchingEndpointResidualEnergy
        (branchingCell k hk) =
          k + 2

namespace SU7NativeStrictBranchingHolonomySuccessorFamily

variable {n sourceBound targetBound : Nat}

/-- A strict branching holonomy family cannot be a bounded successor family
across two distinct successor shells.

`NoPrimeBranchingCellStrictPermanentHolonomy xs B` says that `B` is a
nonzero global minimum of the same list `xs`.  If `targetBound >= 2`, the
fields at `k = 0` and `k = 1` force two selected cells in that same list to
have energies `2` and `3`.  Strict holonomy of the `3`-energy cell then
forbids the `2`-energy cell from being lower, contradiction. -/
theorem not_nonempty_of_two_le_targetBound
    (hbound : 2 ≤ targetBound) :
    ¬ Nonempty
        (SU7NativeStrictBranchingHolonomySuccessorFamily
          n sourceBound targetBound) := by
  rintro ⟨F⟩
  have hk0 : 0 < targetBound := by omega
  have hk1 : 1 < targetBound := by omega
  let B0 := F.branchingCell 0 hk0
  let B1 := F.branchingCell 1 hk1
  have H0 := F.strictHolonomy 0 hk0
  have H1 := F.strictHolonomy 1 hk1
  rcases H0 with ⟨hmem0, _henergy0, _hmin0⟩
  rcases H1 with ⟨_hmem1, _henergy1, hmin1⟩
  have hlt :
      SaturationMonoid.StandardModelConstraint.noPrimeBranchingEndpointResidualEnergy
          B0 <
        SaturationMonoid.StandardModelConstraint.noPrimeBranchingEndpointResidualEnergy
          B1 := by
    dsimp [B0, B1]
    rw [F.source_energy_successor hk0, F.source_energy_successor hk1]
    norm_num
  exact hmin1 B0 hmem0 hlt

/-- Any constructible strict branching holonomy family is necessarily
single-shell: the current global-minimality field forbids two distinct
successor energies. -/
theorem targetBound_lt_two
    (F :
      SU7NativeStrictBranchingHolonomySuccessorFamily
        n sourceBound targetBound) :
    targetBound < 2 := by
  by_contra hnot
  have hbound : 2 ≤ targetBound := by omega
  exact not_nonempty_of_two_le_targetBound hbound ⟨F⟩

/-- Endpoint-code pair read from the generated no-prime branching cell. -/
def witnessPair
    (F :
      SU7NativeStrictBranchingHolonomySuccessorFamily
        n sourceBound targetBound)
    (k : Nat) (hk : k < targetBound) : Nat × Nat :=
  su7NoPrimeBranchingPair (F.branchingCell k hk)

/-- Strict generated branching holonomy projects to the generated raw-code
holonomy cell used by the positive extraction socket. -/
theorem holonomyCell
    (F :
      SU7NativeStrictBranchingHolonomySuccessorFamily
        n sourceBound targetBound)
    (k : Nat) (hk : k < targetBound) :
    SU7GeneratedHolonomyCell n sourceBound (F.witnessPair k hk) := by
  dsimp [witnessPair, SU7GeneratedHolonomyCell, su7NoPrimeBranchingPair]
  simpa [SaturationMonoid.StandardModelConstraint.generatedNoPrimeAllowedPredicate]
    using
      SaturationMonoid.StandardModelConstraint.filteredRawCodePairHolonomy_of_noPrimeStrictHolonomy
        (SaturationMonoid.StandardModelConstraint.generatedNoPrimeBranchingCellsWithinBound
          n sourceBound)
        (F.strictHolonomy k hk)

/-- The endpoint-code pair read from the strict branching cell has the
successor source energy required by the generated holonomy family. -/
theorem holonomy_energy_successor
    (F :
      SU7NativeStrictBranchingHolonomySuccessorFamily
        n sourceBound targetBound)
    {k : Nat} (hk : k < targetBound) :
    su7RawCodePairResidualEnergy n
        (F.witnessPair k hk).1 (F.witnessPair k hk).2 =
      k + 2 := by
  rw [witnessPair, su7NoPrimeBranchingPair_raw_energy_eq,
    F.source_energy_successor hk]

/-- Strict generated branching holonomy cells project to the generated
holonomy family adapter.

For `targetBound >= 2`, this is vacuous by
`not_nonempty_of_two_le_targetBound`; the adapter is retained for single-shell
terminal-tension diagnostics. -/
def toGeneratedHolonomySuccessorFamily
    (F :
      SU7NativeStrictBranchingHolonomySuccessorFamily
        n sourceBound targetBound) :
    SU7NativeGeneratedHolonomySuccessorFamily
      n sourceBound targetBound where
  fallbackLabel := F.fallbackLabel
  witnessPair := F.witnessPair
  holonomyCell := F.holonomyCell
  holonomy_energy_successor := by
    intro k hk
    exact F.holonomy_energy_successor hk

/-- Strict generated branching holonomy cells adapt to the active-cell
selector in the active sigma interval.

For bounded successor use this is intentionally not a positive route:
`targetBound >= 2` makes the source family uninhabited. -/
noncomputable def toActiveCellSuccessorSelector
    {K : Type u} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    {σ : K} (hσ0 : 0 < σ) (hσ1 : σ < 1)
    (F :
      SU7NativeStrictBranchingHolonomySuccessorFamily
        n sourceBound targetBound) :
    SU7GeneratedActiveCellSuccessorSelector
      σ (ne_of_lt hσ1) n sourceBound targetBound :=
  (F.toGeneratedHolonomySuccessorFamily).toActiveCellSuccessorSelector hσ0 hσ1

/-- Theorem form of the strict branching selector adapter.

This is single-shell/diagnostic only; it is vacuous for `targetBound >= 2`. -/
theorem nonempty_active_cell_successor_selector
    {K : Type u} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    {σ : K} (hσ0 : 0 < σ) (hσ1 : σ < 1)
    (F :
      SU7NativeStrictBranchingHolonomySuccessorFamily
        n sourceBound targetBound) :
    Nonempty
      (SU7GeneratedActiveCellSuccessorSelector
        σ (ne_of_lt hσ1) n sourceBound targetBound) :=
  ⟨F.toActiveCellSuccessorSelector hσ0 hσ1⟩

end SU7NativeStrictBranchingHolonomySuccessorFamily

namespace SU7GeneratedActiveCellSuccessorSelector

variable {K : Type u} [Field K]
variable {σ : K} {hσ : σ ≠ 1}
variable {n sourceBound targetBound : Nat}

/-- Source label selected from the SU7 active source cell at shell `k`;
outside the bounded interval it returns a harmless fallback label. -/
def sourceLabel
    (S :
      SU7GeneratedActiveCellSuccessorSelector
        σ hσ n sourceBound targetBound)
    (k : Nat) : SU7Label :=
  if hk : k < targetBound then
    (SaturationMonoid.StandardModelConstraint.su7A6ConcreteEndpointSourceReadout
      (S.activeCell k hk)).source_label
  else
    S.fallbackLabel

/-- Target label generated by the SU7 projection-core law from the selected
active source cell at shell `k`; outside the bounded interval it returns the
same fallback label. -/
def targetLabel
    (L : SU7GeneratedProjectionCoreLaw σ hσ n sourceBound)
    (S :
      SU7GeneratedActiveCellSuccessorSelector
        σ hσ n sourceBound targetBound)
    (k : Nat) : SU7Label :=
  if hk : k < targetBound then
    let A := S.activeCell k hk
    let hpos := S.activeCellPos hk
    let R0 :=
      SaturationMonoid.StandardModelConstraint.su7A6ConcreteEndpointSourceReadout
        A
    let hheight := R0.source_signedHeight_pos hpos
    L.targetLabel R0.source_label hheight
  else
    S.fallbackLabel

/-- A generated SU7 projection-core law plus a bounded active-cell selector
supplies the bounded projection family required by the positive extraction
socket.

The `target_raw_energy` field is not hand-filled: it is derived from the SU7
unit center-cover raw-unit readout and the selector's source-energy
calibration `A.energy = k + 2`. -/
def boundedProjectionFamilyOfGeneratedCoreLaw
    (L : SU7GeneratedProjectionCoreLaw σ hσ n sourceBound)
    (S :
      SU7GeneratedActiveCellSuccessorSelector
        σ hσ n sourceBound targetBound) :
    SU7GeneratedBoundedProjectionFamily n targetBound where
  sourceLabel := S.sourceLabel
  targetLabel := S.targetLabel L
  source_target_core := by
    intro k hk
    let A := S.activeCell k hk
    let hpos := S.activeCellPos hk
    let R0 :=
      SaturationMonoid.StandardModelConstraint.su7A6ConcreteEndpointSourceReadout
        A
    let hheight := R0.source_signedHeight_pos hpos
    have Hcore :
        SU7SourceProjectionCore n R0.source_label
          (L.targetLabel R0.source_label hheight) := by
      simpa [SU7SourceProjectionCore, R0, hheight] using
        L.source_target_core A hpos
    simpa [sourceLabel, targetLabel, hk, A, hpos, R0, hheight] using
      Hcore
  target_raw_energy := by
    intro k hk
    let A := S.activeCell k hk
    let hpos := S.activeCellPos hk
    let R0 :=
      SaturationMonoid.StandardModelConstraint.su7A6ConcreteEndpointSourceReadout
        A
    let hheight := R0.source_signedHeight_pos hpos
    let target := L.targetLabel R0.source_label hheight
    let raw :=
      su7RawCodePairResidualEnergy n
        (su7LeftCode target) (su7RightCode target)
    have Hcore :
        SU7SourceProjectionCore n R0.source_label target := by
      simpa [SU7SourceProjectionCore, target, R0, hheight] using
        L.source_target_core A hpos
    have Hunit :
        ((raw + 1 : Nat) : Int) = ((k + 2 : Nat) : Int) := by
      calc
        ((raw + 1 : Nat) : Int) =
            SaturationMonoid.StandardModelConstraint.su7A6SignedHeight
              R0.source_label := by
          simpa [raw, su7RawCodePairResidualEnergy, su7LeftCode,
            su7RightCode, target, SU7SourceProjectionCore] using
            Hcore.raw_unit_reads_sourceSignedHeight
        _ = (A.energy : Int) := R0.source_height_reads_energy
        _ = ((k + 2 : Nat) : Int) := by
          rw [S.source_energy_successor hk]
    have Hnat : raw + 1 = k + 2 := by
      exact_mod_cast Hunit
    have Hraw : raw = k + 1 := by
      omega
    simpa [targetLabel, hk, A, hpos, R0, hheight, target, raw] using Hraw

/-- Generated-core-law readout as bounded positive successor steps. -/
theorem bounded_successor_steps_of_generated_core_law
    (L : SU7GeneratedProjectionCoreLaw σ hσ n sourceBound)
    (S :
      SU7GeneratedActiveCellSuccessorSelector
        σ hσ n sourceBound targetBound) :
    BoundedAtomPairRealizationSuccessorSteps
      NatMultiplicativelyAtomic n targetBound :=
  (boundedProjectionFamilyOfGeneratedCoreLaw L S).bounded_successor_steps

/-- Generated-core-law positive extraction: terminal zero plus a bounded
selector of SU7 active source cells extracts the target-shell atom-pair
witness. -/
theorem atom_pair_realization_of_generated_core_law_selector
    (L : SU7GeneratedProjectionCoreLaw σ hσ n sourceBound)
    (S :
      SU7GeneratedActiveCellSuccessorSelector
        σ hσ n sourceBound targetBound)
    (hzero :
      ∃ p : ArithmeticAtomPair NatMultiplicativelyAtomic n,
        ArithmeticAtomPair.energy p = 0) :
    ∃ p : ArithmeticAtomPair NatMultiplicativelyAtomic n,
      ArithmeticAtomPair.energy p = targetBound :=
  atom_pair_realization_at_bound_of_zero_and_successor_steps
    hzero targetBound
    (bounded_successor_steps_of_generated_core_law L S)

/-- Factorized extraction from the generated-core-law selector adapter. -/
theorem factorized_atom_pair_realization_of_generated_core_law_selector
    (L : SU7GeneratedProjectionCoreLaw σ hσ n sourceBound)
    (S :
      SU7GeneratedActiveCellSuccessorSelector
        σ hσ n sourceBound targetBound)
    (hzero :
      ∃ p : ArithmeticAtomPair NatMultiplicativelyAtomic n,
        ArithmeticAtomPair.energy p = 0) :
    FactorizedAtomPairRealization
      NatMultiplicativelyAtomic natMultiplicativeAtomFactorizationCategory
      n targetBound := by
  rcases atom_pair_realization_of_generated_core_law_selector L S hzero with
    ⟨p, hp⟩
  exact
    factorizedAtomPairRealizationOfPair
      natMultiplicativeAtomFactorizationCategory p hp

end SU7GeneratedActiveCellSuccessorSelector

/-- Direct generated projection family from native active-cell dynamics.

This is the selector-free API for the positive source-dynamics route: the
native dynamics supplies active cells with affine residual readout, and the
SU7 generated projection-core law supplies the faithful endpoint projection. -/
def SU7NativeActiveCellSuccessorDynamics.boundedProjectionFamilyOfGeneratedCoreLaw
    {K : Type u} [Field K]
    {σ : K} {hσ : σ ≠ 1}
    {n sourceBound targetBound : Nat}
    (L : SU7GeneratedProjectionCoreLaw σ hσ n sourceBound)
    (D :
      SU7NativeActiveCellSuccessorDynamics
        σ hσ n sourceBound targetBound) :
    SU7GeneratedBoundedProjectionFamily n targetBound :=
  SU7GeneratedActiveCellSuccessorSelector.boundedProjectionFamilyOfGeneratedCoreLaw
    L D.toActiveCellSuccessorSelector

/-- Native active-cell dynamics plus a generated projection-core law supplies
the bounded positive successor steps required by target-shell extraction. -/
theorem SU7NativeActiveCellSuccessorDynamics.bounded_successor_steps_of_generated_core_law
    {K : Type u} [Field K]
    {σ : K} {hσ : σ ≠ 1}
    {n sourceBound targetBound : Nat}
    (L : SU7GeneratedProjectionCoreLaw σ hσ n sourceBound)
    (D :
      SU7NativeActiveCellSuccessorDynamics
        σ hσ n sourceBound targetBound) :
    BoundedAtomPairRealizationSuccessorSteps
      NatMultiplicativelyAtomic n targetBound :=
  (D.boundedProjectionFamilyOfGeneratedCoreLaw L).bounded_successor_steps

/-- Native active-cell dynamics plus a generated projection-core law directly
materializes the selected successor shell `k + 1`.

This is the source-to-arithmetic single-step bridge: no terminal zero witness,
no predecessor realization, and no endpoint table are used. -/
theorem SU7NativeActiveCellSuccessorDynamics.atom_pair_realization_at_successor_of_generated_core_law
    {K : Type u} [Field K]
    {σ : K} {hσ : σ ≠ 1}
    {n sourceBound targetBound : Nat}
    (L : SU7GeneratedProjectionCoreLaw σ hσ n sourceBound)
    (D :
      SU7NativeActiveCellSuccessorDynamics
        σ hσ n sourceBound targetBound)
    {k : Nat} (hk : k < targetBound) :
    ∃ p : ArithmeticAtomPair NatMultiplicativelyAtomic n,
      ArithmeticAtomPair.energy p = k + 1 :=
  (D.boundedProjectionFamilyOfGeneratedCoreLaw L).atom_pair_realization_at_successor
    hk

/-- Factorized single-step readout from native active-cell dynamics and a
generated projection-core law. -/
theorem SU7NativeActiveCellSuccessorDynamics.factorized_atom_pair_realization_at_successor_of_generated_core_law
    {K : Type u} [Field K]
    {σ : K} {hσ : σ ≠ 1}
    {n sourceBound targetBound : Nat}
    (L : SU7GeneratedProjectionCoreLaw σ hσ n sourceBound)
    (D :
      SU7NativeActiveCellSuccessorDynamics
        σ hσ n sourceBound targetBound)
    {k : Nat} (hk : k < targetBound) :
    FactorizedAtomPairRealization
      NatMultiplicativelyAtomic natMultiplicativeAtomFactorizationCategory
      n (k + 1) :=
  (D.boundedProjectionFamilyOfGeneratedCoreLaw L).factorized_atom_pair_realization_at_successor
    hk

/-- Generated-core-law positive extraction directly from native active-cell
dynamics. -/
theorem atom_pair_realization_of_native_active_cell_dynamics
    {K : Type u} [Field K]
    {σ : K} {hσ : σ ≠ 1}
    {n sourceBound targetBound : Nat}
    (L : SU7GeneratedProjectionCoreLaw σ hσ n sourceBound)
    (D :
      SU7NativeActiveCellSuccessorDynamics
        σ hσ n sourceBound targetBound)
    (hzero :
      ∃ p : ArithmeticAtomPair NatMultiplicativelyAtomic n,
        ArithmeticAtomPair.energy p = 0) :
    ∃ p : ArithmeticAtomPair NatMultiplicativelyAtomic n,
      ArithmeticAtomPair.energy p = targetBound :=
  atom_pair_realization_at_bound_of_zero_and_successor_steps
    hzero targetBound
    (D.bounded_successor_steps_of_generated_core_law L)

/-- Factorized generated-core-law extraction directly from native active-cell
dynamics. -/
theorem factorized_atom_pair_realization_of_native_active_cell_dynamics
    {K : Type u} [Field K]
    {σ : K} {hσ : σ ≠ 1}
    {n sourceBound targetBound : Nat}
    (L : SU7GeneratedProjectionCoreLaw σ hσ n sourceBound)
    (D :
      SU7NativeActiveCellSuccessorDynamics
        σ hσ n sourceBound targetBound)
    (hzero :
      ∃ p : ArithmeticAtomPair NatMultiplicativelyAtomic n,
        ArithmeticAtomPair.energy p = 0) :
    FactorizedAtomPairRealization
      NatMultiplicativelyAtomic natMultiplicativeAtomFactorizationCategory
      n targetBound := by
  rcases
    atom_pair_realization_of_native_active_cell_dynamics L D hzero with
    ⟨p, hp⟩
  exact
    factorizedAtomPairRealizationOfPair
      natMultiplicativeAtomFactorizationCategory p hp

/-- Direct generated projection family from a thin source constructor family.

This is the preferred positive extraction socket after the holonomy
calibration: source feasible data produce active cells with affine `k + 2`
energy, then the generated projection-core law supplies the arithmetic
endpoint readout. -/
def SU7NativeThinSourceSuccessorFamily.boundedProjectionFamilyOfGeneratedCoreLaw
    {K : Type u} [Field K]
    {σ : K} {hσ : σ ≠ 1}
    {n sourceBound targetBound : Nat}
    (L : SU7GeneratedProjectionCoreLaw σ hσ n sourceBound)
    (F :
      SU7NativeThinSourceSuccessorFamily
        σ hσ n sourceBound targetBound) :
    SU7GeneratedBoundedProjectionFamily n targetBound :=
  F.toNativeActiveCellSuccessorDynamics.boundedProjectionFamilyOfGeneratedCoreLaw
    L

/-- Thin source constructors plus generated projection-core law supply the
bounded positive successor steps. -/
theorem SU7NativeThinSourceSuccessorFamily.bounded_successor_steps_of_generated_core_law
    {K : Type u} [Field K]
    {σ : K} {hσ : σ ≠ 1}
    {n sourceBound targetBound : Nat}
    (L : SU7GeneratedProjectionCoreLaw σ hσ n sourceBound)
    (F :
      SU7NativeThinSourceSuccessorFamily
        σ hσ n sourceBound targetBound) :
    BoundedAtomPairRealizationSuccessorSteps
      NatMultiplicativelyAtomic n targetBound :=
  (F.boundedProjectionFamilyOfGeneratedCoreLaw L).bounded_successor_steps

/-- Thin source constructors directly materialize the selected successor shell
after the generated projection-core law is supplied. -/
theorem SU7NativeThinSourceSuccessorFamily.atom_pair_realization_at_successor_of_generated_core_law
    {K : Type u} [Field K]
    {σ : K} {hσ : σ ≠ 1}
    {n sourceBound targetBound : Nat}
    (L : SU7GeneratedProjectionCoreLaw σ hσ n sourceBound)
    (F :
      SU7NativeThinSourceSuccessorFamily
        σ hσ n sourceBound targetBound)
    {k : Nat} (hk : k < targetBound) :
    ∃ p : ArithmeticAtomPair NatMultiplicativelyAtomic n,
      ArithmeticAtomPair.energy p = k + 1 :=
  (F.boundedProjectionFamilyOfGeneratedCoreLaw L).atom_pair_realization_at_successor
    hk

/-- Factorized selected-shell readout from thin source constructors and the
generated projection-core law. -/
theorem SU7NativeThinSourceSuccessorFamily.factorized_atom_pair_realization_at_successor_of_generated_core_law
    {K : Type u} [Field K]
    {σ : K} {hσ : σ ≠ 1}
    {n sourceBound targetBound : Nat}
    (L : SU7GeneratedProjectionCoreLaw σ hσ n sourceBound)
    (F :
      SU7NativeThinSourceSuccessorFamily
        σ hσ n sourceBound targetBound)
    {k : Nat} (hk : k < targetBound) :
    FactorizedAtomPairRealization
      NatMultiplicativelyAtomic natMultiplicativeAtomFactorizationCategory
      n (k + 1) :=
  (F.boundedProjectionFamilyOfGeneratedCoreLaw L)
    |>.factorized_atom_pair_realization_at_successor hk

/-- Windowed strict branching plus the relative projection law materializes a
selected successor shell through the old generated-holonomy adapter.

This remains a diagnostic/repair target, not the preferred positive producer
route: it still routes through permanent-holonomy language, so new source
constructors should feed `SU7NativeThinSourceSuccessorFamily` or
`SU7NativeActiveCellSuccessorDynamics` instead. -/
theorem SU7NativeWindowedStrictBranchingHolonomySuccessorFamily.atom_pair_realization_at_successor_of_generated_core_law
    {K : Type u} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    {σ : K} (hσ0 : 0 < σ) (hσ1 : σ < 1)
    {n sourceBound targetBound : Nat}
    (P :
      SU7WindowedStrictBranchingHolonomyProjectionLaw
        n sourceBound targetBound)
    (L : SU7GeneratedProjectionCoreLaw
      σ (ne_of_lt hσ1) n sourceBound)
    (F :
      SU7NativeWindowedStrictBranchingHolonomySuccessorFamily
        n sourceBound targetBound)
    {k : Nat} (hk : k < targetBound) :
    ∃ p : ArithmeticAtomPair NatMultiplicativelyAtomic n,
      ArithmeticAtomPair.energy p = k + 1 :=
  ((F.toGeneratedHolonomySuccessorFamily P)
    |>.toNativeActiveCellSuccessorDynamics hσ0 hσ1)
    |>.atom_pair_realization_at_successor_of_generated_core_law L hk

/-- Factorized single-step extraction from windowed strict branching plus the
relative projection law. -/
theorem SU7NativeWindowedStrictBranchingHolonomySuccessorFamily.factorized_atom_pair_realization_at_successor_of_generated_core_law
    {K : Type u} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    {σ : K} (hσ0 : 0 < σ) (hσ1 : σ < 1)
    {n sourceBound targetBound : Nat}
    (P :
      SU7WindowedStrictBranchingHolonomyProjectionLaw
        n sourceBound targetBound)
    (L : SU7GeneratedProjectionCoreLaw
      σ (ne_of_lt hσ1) n sourceBound)
    (F :
      SU7NativeWindowedStrictBranchingHolonomySuccessorFamily
        n sourceBound targetBound)
    {k : Nat} (hk : k < targetBound) :
    FactorizedAtomPairRealization
      NatMultiplicativelyAtomic natMultiplicativeAtomFactorizationCategory
      n (k + 1) :=
  ((F.toGeneratedHolonomySuccessorFamily P)
    |>.toNativeActiveCellSuccessorDynamics hσ0 hσ1)
    |>.factorized_atom_pair_realization_at_successor_of_generated_core_law L hk

/-- Native canonical-rich source dynamics plus the SU7 generated projection
core law gives the bounded positive extraction.

This is the extraction socket with the selector discharged by native source
witnesses rather than endpoint-shell coverage. -/
theorem atom_pair_realization_of_native_canonical_rich_witness_family
    {K : Type u} [Field K]
    {σ : K} {hσ : σ ≠ 1}
    {n sourceBound targetBound : Nat}
    (L : SU7GeneratedProjectionCoreLaw σ hσ n sourceBound)
    (F :
      SU7NativeCanonicalRichWitnessSuccessorFamily
        σ hσ n sourceBound targetBound)
    (hzero :
      ∃ p : ArithmeticAtomPair NatMultiplicativelyAtomic n,
        ArithmeticAtomPair.energy p = 0) :
    ∃ p : ArithmeticAtomPair NatMultiplicativelyAtomic n,
      ArithmeticAtomPair.energy p = targetBound :=
  atom_pair_realization_of_native_active_cell_dynamics
    L F.toNativeActiveCellSuccessorDynamics hzero

/-- Factorized extraction when the selector is supplied by native
canonical-rich source witnesses. -/
theorem factorized_atom_pair_realization_of_native_canonical_rich_witness_family
    {K : Type u} [Field K]
    {σ : K} {hσ : σ ≠ 1}
    {n sourceBound targetBound : Nat}
    (L : SU7GeneratedProjectionCoreLaw σ hσ n sourceBound)
    (F :
      SU7NativeCanonicalRichWitnessSuccessorFamily
        σ hσ n sourceBound targetBound)
    (hzero :
      ∃ p : ArithmeticAtomPair NatMultiplicativelyAtomic n,
        ArithmeticAtomPair.energy p = 0) :
    FactorizedAtomPairRealization
      NatMultiplicativelyAtomic natMultiplicativeAtomFactorizationCategory
      n targetBound :=
  factorized_atom_pair_realization_of_native_active_cell_dynamics
    L F.toNativeActiveCellSuccessorDynamics hzero

/-- Generated holonomy source cells in the active sigma interval are enough to
discharge the selector and feed the SU7 generated projection extraction.

This uses the SU7 canonical-rich lift for generated P950 holonomy cells; it
does not use checked-shell coverage or endpoint enumeration. -/
theorem atom_pair_realization_of_native_generated_holonomy_successor_family
    {K : Type u} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    {σ : K} (hσ0 : 0 < σ) (hσ1 : σ < 1)
    {n sourceBound targetBound : Nat}
    (L : SU7GeneratedProjectionCoreLaw
      σ (ne_of_lt hσ1) n sourceBound)
    (F :
      SU7NativeGeneratedHolonomySuccessorFamily
        n sourceBound targetBound)
    (hzero :
      ∃ p : ArithmeticAtomPair NatMultiplicativelyAtomic n,
        ArithmeticAtomPair.energy p = 0) :
    ∃ p : ArithmeticAtomPair NatMultiplicativelyAtomic n,
      ArithmeticAtomPair.energy p = targetBound :=
  atom_pair_realization_of_native_canonical_rich_witness_family
    L (F.toCanonicalRichWitnessSuccessorFamily hσ0 hσ1) hzero

/-- Factorized extraction from generated holonomy source cells in the active
sigma interval. -/
theorem factorized_atom_pair_realization_of_native_generated_holonomy_successor_family
    {K : Type u} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    {σ : K} (hσ0 : 0 < σ) (hσ1 : σ < 1)
    {n sourceBound targetBound : Nat}
    (L : SU7GeneratedProjectionCoreLaw
      σ (ne_of_lt hσ1) n sourceBound)
    (F :
      SU7NativeGeneratedHolonomySuccessorFamily
        n sourceBound targetBound)
    (hzero :
      ∃ p : ArithmeticAtomPair NatMultiplicativelyAtomic n,
        ArithmeticAtomPair.energy p = 0) :
    FactorizedAtomPairRealization
      NatMultiplicativelyAtomic natMultiplicativeAtomFactorizationCategory
      n targetBound :=
  factorized_atom_pair_realization_of_native_canonical_rich_witness_family
    L (F.toCanonicalRichWitnessSuccessorFamily hσ0 hσ1) hzero

/-- Strict generated branching holonomy cells feed the SU7 generated
projection extraction after projection to raw-code holonomy cells.

This is retained only as a single-shell terminal-tension adapter.  For
`targetBound >= 2`, the premise family is uninhabited because strict
permanent holonomy is global-minimal in one fixed generated list. -/
theorem atom_pair_realization_of_native_strict_branching_holonomy_successor_family
    {K : Type u} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    {σ : K} (hσ0 : 0 < σ) (hσ1 : σ < 1)
    {n sourceBound targetBound : Nat}
    (L : SU7GeneratedProjectionCoreLaw
      σ (ne_of_lt hσ1) n sourceBound)
    (F :
      SU7NativeStrictBranchingHolonomySuccessorFamily
        n sourceBound targetBound)
    (hzero :
      ∃ p : ArithmeticAtomPair NatMultiplicativelyAtomic n,
        ArithmeticAtomPair.energy p = 0) :
    ∃ p : ArithmeticAtomPair NatMultiplicativelyAtomic n,
      ArithmeticAtomPair.energy p = targetBound :=
  atom_pair_realization_of_native_generated_holonomy_successor_family
    hσ0 hσ1 L F.toGeneratedHolonomySuccessorFamily hzero

/-- Factorized single-shell/diagnostic extraction from strict generated
branching holonomy cells.  Vacuous for `targetBound >= 2`. -/
theorem factorized_atom_pair_realization_of_native_strict_branching_holonomy_successor_family
    {K : Type u} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    {σ : K} (hσ0 : 0 < σ) (hσ1 : σ < 1)
    {n sourceBound targetBound : Nat}
    (L : SU7GeneratedProjectionCoreLaw
      σ (ne_of_lt hσ1) n sourceBound)
    (F :
      SU7NativeStrictBranchingHolonomySuccessorFamily
        n sourceBound targetBound)
    (hzero :
      ∃ p : ArithmeticAtomPair NatMultiplicativelyAtomic n,
        ArithmeticAtomPair.energy p = 0) :
    FactorizedAtomPairRealization
      NatMultiplicativelyAtomic natMultiplicativeAtomFactorizationCategory
      n targetBound :=
  factorized_atom_pair_realization_of_native_generated_holonomy_successor_family
    hσ0 hσ1 L F.toGeneratedHolonomySuccessorFamily hzero

/-- A complete SU7 positive extraction package for the current socket.

The terminal witness is still separated from the bounded generated projection
family.  This avoids pretending that one `E-1` source label gives all lower
shells automatically. -/
structure SU7GeneratedPositiveExtractionDomain (n bound : Nat) where
  terminal_zero_realization :
    ∃ p : ArithmeticAtomPair NatMultiplicativelyAtomic n,
      ArithmeticAtomPair.energy p = 0
  generated_projection_family :
    SU7GeneratedBoundedProjectionFamily n bound

/-- SU7 generated projection data fills the generic positive extraction
theorem and extracts a target-shell atom-pair witness. -/
theorem atom_pair_realization_of_su7_generated_positive_extraction
    {n bound : Nat}
    (D : SU7GeneratedPositiveExtractionDomain n bound) :
    ∃ p : ArithmeticAtomPair NatMultiplicativelyAtomic n,
      ArithmeticAtomPair.energy p = bound :=
  atom_pair_realization_at_bound_of_zero_and_successor_steps
    D.terminal_zero_realization
    bound
    D.generated_projection_family.bounded_successor_steps

/-- Factorized readout for the SU7 generated positive extraction theorem. -/
theorem factorized_atom_pair_realization_of_su7_generated_positive_extraction
    {n bound : Nat}
    (D : SU7GeneratedPositiveExtractionDomain n bound) :
    FactorizedAtomPairRealization
      NatMultiplicativelyAtomic natMultiplicativeAtomFactorizationCategory
      n bound := by
  rcases atom_pair_realization_of_su7_generated_positive_extraction D with
    ⟨p, hp⟩
  exact
    factorizedAtomPairRealizationOfPair
      natMultiplicativeAtomFactorizationCategory p hp

/-!
## Concrete P948 pointwise positive sample
-/

/-- The existing SU7 P948 center-cover completion core materializes a local
Nat-atom endpoint pair at residual shell `5`.

This is a pointwise positive sample, not a bounded-family theorem. -/
theorem p948_completed_source_projection_core_atom_pair_realization :
    ∃ p : ArithmeticAtomPair NatMultiplicativelyAtomic 6,
      ArithmeticAtomPair.energy p = 5 := by
  rcases
    atom_pair_realization_of_su7_source_projection_core
      SaturationMonoid.StandardModelConstraint.su7A6P948CompletedRepairLabel_unitCenterCoverProjectionCore with
    ⟨p, hp⟩
  refine ⟨p, ?_⟩
  simpa [
    su7LeftCode,
    su7RightCode,
    su7RawCodePairResidualEnergy,
    SaturationMonoid.StandardModelConstraint.su7A6P948CompletedRepairLabel,
    SaturationMonoid.StandardModelConstraint.su7A6P948CompletedRepairLabel_unitCenterCoverProjectionCore,
    SaturationMonoid.StandardModelConstraint.su7A6ConcreteEndpointSourceGrammar,
    SaturationMonoid.StandardModelConstraint.su7A6EndpointSourceLabel_leftCode,
    SaturationMonoid.StandardModelConstraint.su7A6EndpointSourceLabel_rightCode,
    SaturationMonoid.StandardModelConstraint.rawCodePairResidualEnergy_six_two_five
  ] using hp


end SU7GeneratedProjectionPositiveExtraction

end RepresentationArithmeticAtomProjectionDefect
