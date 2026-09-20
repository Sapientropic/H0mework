import Mathlib.Data.Nat.Prime.Nth
import H0mework.Arithmetic.AtomicCodes.P878

/-!
# Proposition 879: prime-coded SU(7) atom readout

P878 proved that the current raw-code projection

```lean
atomCode a := a.weight.code
```

cannot satisfy the prime projection law while irreducibility is still the
placeholder predicate `True`.  This file supplies the next non-storing producer
route: keep `SU7Atom` unchanged, but read a physical atom through the canonical
prime enumeration:

```lean
su7PrimeCodedAtomCode a := Nat.nth Nat.Prime a.weight.code
```

Primality is then a theorem of the readout, not a field of the atom.  The
color-loop residual transport can be run against this prime-coded readout and
no longer needs an external `SU7AtomCodePrimeProjectionLaw` assumption.
-/

namespace SaturationMonoid
namespace StandardModelConstraint

noncomputable section

open SaturationMonoid.AffineRelaxation

set_option linter.defProp false

/-! ## Canonical prime-coded atom readout -/

/-- Canonical prime-code readout of a SU(7) weight.  The raw weight code is an
index into the increasing enumeration of prime numbers. -/
def su7PrimeCodeOfWeight (w : SU7WeightLattice) : ℕ :=
  Nat.nth Nat.Prime w.code

/-- Canonical prime-code readout of a physical SU(7) atom. -/
def su7PrimeCodedAtomCode (a : SU7Atom) : ℕ :=
  su7PrimeCodeOfWeight a.weight

/-- THEOREM 1: every SU(7) weight has a prime-coded readout. -/
theorem su7PrimeCodeOfWeight_prime (w : SU7WeightLattice) :
    Nat.Prime (su7PrimeCodeOfWeight w) := by
  unfold su7PrimeCodeOfWeight
  exact Nat.nth_mem_of_infinite Nat.infinite_setOf_prime w.code

/-- THEOREM 2: every physical atom has a prime-coded readout. -/
theorem su7PrimeCodedAtomCode_prime (a : SU7Atom) :
    Nat.Prime (su7PrimeCodedAtomCode a) := by
  unfold su7PrimeCodedAtomCode
  exact su7PrimeCodeOfWeight_prime a.weight

/-- THEOREM 3: the weight index `0` reads as the first prime, `2`. -/
theorem su7PrimeCodeOfWeight_zero_eq_two :
    su7PrimeCodeOfWeight { code := 0 } = 2 := by
  unfold su7PrimeCodeOfWeight
  exact Nat.nth_prime_zero_eq_two

/-- THEOREM 4: the composite raw-code atom from P878 reads as the fifth prime,
not as the composite raw code `4`.  This is the point of the derived readout:
the atom stores no prime proof, but the projection is prime-valued. -/
theorem su7PrimeCodedAtomCode_compositeCodeFourAtom_eq_eleven :
    su7PrimeCodedAtomCode compositeCodeFourAtom = 11 := by
  unfold su7PrimeCodedAtomCode su7PrimeCodeOfWeight compositeCodeFourAtom
    compositeCodeFourWeight
  exact Nat.nth_prime_four_eq_eleven

/-! ## Prime-coded physical residual -/

/-- Prime-coded residual of a physical branch cell.  This is the same color-loop
residual shape as P873, but read through `su7PrimeCodedAtomCode` instead of the
raw code. -/
def primeCodedPhysicalResidual
    {n : ℕ} (cell : SU7PhysicalBranchCell n) : ℤ :=
  ((su7PrimeCodedAtomCode cell.leftAtom +
      su7PrimeCodedAtomCode cell.rightAtom : ℕ) : ℤ) -
    ((2 * n : ℕ) : ℤ)

/-- Prime-coded residual energy. -/
def primeCodedPhysicalResidualEnergy
    {n : ℕ} (cell : SU7PhysicalBranchCell n) : ℕ :=
  Int.natAbs (primeCodedPhysicalResidual cell)

/-- THEOREM 5: zero prime-coded residual is exactly even-fiber balance under
the prime-coded atom readout. -/
theorem primeCodedPhysicalResidual_zero_to_sum
    {n : ℕ} (cell : SU7PhysicalBranchCell n)
    (hzero : primeCodedPhysicalResidual cell = 0) :
    su7PrimeCodedAtomCode cell.leftAtom +
      su7PrimeCodedAtomCode cell.rightAtom = 2 * n := by
  unfold primeCodedPhysicalResidual at hzero
  omega

/-- THEOREM 6: zero prime-coded residual energy is zero prime-coded residual. -/
theorem primeCodedPhysicalResidualEnergy_eq_zero_iff
    {n : ℕ} (cell : SU7PhysicalBranchCell n) :
    primeCodedPhysicalResidualEnergy cell = 0 ↔
      primeCodedPhysicalResidual cell = 0 := by
  unfold primeCodedPhysicalResidualEnergy
  rw [Int.natAbs_eq_zero]

/-! ## Well-founded prime-coded residual transport -/

/-- A physical orbit whose residual descent is measured in the prime-coded
readout.  It stores a starting physical cell and a strict successor law for any
nonzero prime-coded residual. -/
structure SU7PrimeCodedWellFoundedPhysicalOrbit (n : ℕ) where
  startCell : SU7PhysicalBranchCell n
  lyapunov_descends_nonzero :
    ∀ cell : SU7PhysicalBranchCell n,
      primeCodedPhysicalResidual cell ≠ 0 ->
        ∃ next : SU7PhysicalBranchCell n,
          primeCodedPhysicalResidualEnergy next <
            primeCodedPhysicalResidualEnergy cell

/-- THEOREM 7: well-founded prime-coded residual descent produces a zero
prime-coded residual cell. -/
theorem exists_zeroCell_of_primeCodedWellFoundedLyapunovOrbit
    {n : ℕ} (O : SU7PrimeCodedWellFoundedPhysicalOrbit n) :
    ∃ cell : SU7PhysicalBranchCell n,
      primeCodedPhysicalResidual cell = 0 := by
  let motive : ℕ -> Prop := fun e =>
    ∀ cell : SU7PhysicalBranchCell n,
      primeCodedPhysicalResidualEnergy cell = e ->
        ∃ zeroCell : SU7PhysicalBranchCell n,
          primeCodedPhysicalResidual zeroCell = 0
  have hstep : ∀ e : ℕ, (∀ e' < e, motive e') -> motive e := by
    intro e ih cell henergy
    by_cases hzero : primeCodedPhysicalResidual cell = 0
    · exact ⟨cell, hzero⟩
    · obtain ⟨next, hnext_lt⟩ :=
        O.lyapunov_descends_nonzero cell hzero
      exact ih (primeCodedPhysicalResidualEnergy next)
        (by simpa [henergy] using hnext_lt)
        next rfl
  have hstart : motive (primeCodedPhysicalResidualEnergy O.startCell) :=
    Nat.strong_induction_on
      (primeCodedPhysicalResidualEnergy O.startCell) hstep
  exact hstart O.startCell rfl

/-- A confinement dynamics object for prime-coded residual transport.  It keeps
the physical law names from P873/P876, but the zero-readout is generated by
well-founded descent in the prime-coded residual. -/
structure SU7PrimeCodedWellFoundedConfinementDynamics where
  compact_gauge_orbit : SU7CompactGaugeOrbit
  lyapunov_residual_dissipation : SU7LyapunovResidualDissipation
  quantized_spectrum_no_escaping_boundary :
    SU7QuantizedSpectrumNoEscapingBoundary
  orbit : ∀ n : ℕ, 2 ≤ n -> SU7PrimeCodedWellFoundedPhysicalOrbit n

/-- The generated zero cell in each even fiber. -/
def primeCodedPhysicalZeroCell_of_wellFounded
    (D : SU7PrimeCodedWellFoundedConfinementDynamics)
    (n : ℕ) (hn : 2 ≤ n) :
    SU7PhysicalBranchCell n :=
  Classical.choose
    (exists_zeroCell_of_primeCodedWellFoundedLyapunovOrbit
      (D.orbit n hn))

/-- THEOREM 8: the generated zero cell has zero prime-coded residual. -/
theorem primeCodedPhysicalZeroCell_of_wellFounded_residual_zero
    (D : SU7PrimeCodedWellFoundedConfinementDynamics)
    (n : ℕ) (hn : 2 ≤ n) :
    primeCodedPhysicalResidual
      (primeCodedPhysicalZeroCell_of_wellFounded D n hn) = 0 :=
  Classical.choose_spec
    (exists_zeroCell_of_primeCodedWellFoundedLyapunovOrbit
      (D.orbit n hn))

/-- THEOREM 9: prime-coded confinement dynamics gives an ordinary Goldbach
readout, without an external atom-code projection law. -/
theorem evenGoldbach_of_primeCodedWellFoundedConfinement
    (D : SU7PrimeCodedWellFoundedConfinementDynamics) :
    EvenGoldbachStatement := by
  intro n hn
  let cell := primeCodedPhysicalZeroCell_of_wellFounded D n hn
  refine
    ⟨⟨su7PrimeCodedAtomCode cell.leftAtom,
        su7PrimeCodedAtomCode_prime cell.leftAtom⟩,
      ⟨su7PrimeCodedAtomCode cell.rightAtom,
        su7PrimeCodedAtomCode_prime cell.rightAtom⟩,
      ?_⟩
  exact (primeCodedPhysicalResidual_zero_to_sum cell
    (primeCodedPhysicalZeroCell_of_wellFounded_residual_zero D n hn)).symm

/-! ## Certificate -/

/-- P879 certificate: prime-coded SU(7) atom readout removes the external
`SU7AtomCodePrimeProjectionLaw` assumption from the color-loop readout. -/
structure SU7PrimeCodedAtomReadoutCertificate : Prop where
  weight_code_prime :
    ∀ w : SU7WeightLattice, Nat.Prime (su7PrimeCodeOfWeight w)
  atom_code_prime :
    ∀ a : SU7Atom, Nat.Prime (su7PrimeCodedAtomCode a)
  composite_atom_prime_readout :
    su7PrimeCodedAtomCode compositeCodeFourAtom = 11
  residual_zero_to_balance :
    ∀ {n : ℕ} (cell : SU7PhysicalBranchCell n),
      primeCodedPhysicalResidual cell = 0 ->
        su7PrimeCodedAtomCode cell.leftAtom +
          su7PrimeCodedAtomCode cell.rightAtom = 2 * n
  well_founded_zero_cell :
    ∀ {n : ℕ}, SU7PrimeCodedWellFoundedPhysicalOrbit n ->
      ∃ cell : SU7PhysicalBranchCell n,
        primeCodedPhysicalResidual cell = 0
  goldbach_readout :
    SU7PrimeCodedWellFoundedConfinementDynamics ->
      EvenGoldbachStatement

/-- THEOREM 10: canonical P879 prime-coded atom readout certificate. -/
def su7PrimeCodedAtomReadoutCertificate :
    SU7PrimeCodedAtomReadoutCertificate where
  weight_code_prime := su7PrimeCodeOfWeight_prime
  atom_code_prime := su7PrimeCodedAtomCode_prime
  composite_atom_prime_readout :=
    su7PrimeCodedAtomCode_compositeCodeFourAtom_eq_eleven
  residual_zero_to_balance := primeCodedPhysicalResidual_zero_to_sum
  well_founded_zero_cell :=
    exists_zeroCell_of_primeCodedWellFoundedLyapunovOrbit
  goldbach_readout := evenGoldbach_of_primeCodedWellFoundedConfinement


end
end StandardModelConstraint
end SaturationMonoid
