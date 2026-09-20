import H0mework.Arithmetic.ProjectionDefect.AtomProjectionDefectCore

/-!
# Bounded transport hardness

This file records rejection tests for bounded pair-level successor transport.

Bounded transport is the safer interface for target-shell defect exclusion, but
it is still arithmetic content: with a shell-zero realization, transport below
`bound` realizes every shell up to `bound`.
-/

namespace RepresentationArithmeticAtomProjectionDefect

/-- Shell-zero realization plus bounded pair transport realizes every shell up
to the bound. -/
theorem atom_pair_realization_up_to_bound_of_zero_and_bounded_pair_transport
    {Atomic : Nat -> Prop} {n bound : Nat}
    (hZero :
      ∃ p : ArithmeticAtomPair Atomic n,
        ArithmeticAtomPair.energy p = 0)
    (T : BoundedAtomPairEnergySuccessorTransport Atomic n bound) :
    ∀ k : Nat,
      k ≤ bound ->
        ∃ p : ArithmeticAtomPair Atomic n,
          ArithmeticAtomPair.energy p = k := by
  intro k
  induction k with
  | zero =>
      intro _hk
      exact hZero
  | succ k ih =>
      intro hkSucc
      have hkBelow : k < bound := Nat.lt_of_succ_le hkSucc
      have hRealizedK :
          ∃ p : ArithmeticAtomPair Atomic n,
            ArithmeticAtomPair.energy p = k :=
        ih (Nat.le_of_lt hkBelow)
      simpa [Nat.succ_eq_add_one] using
        bounded_realization_transport_lift_of_pair_transport
          T hkBelow hRealizedK

/-- Contra hard-gate: if shell zero is realized but some shell below the bound
is missing, bounded successor transport up to that bound cannot exist. -/
theorem no_bounded_pair_transport_of_zero_and_missing_shell
    {Atomic : Nat -> Prop} {n bound k : Nat}
    (hZero :
      ∃ p : ArithmeticAtomPair Atomic n,
        ArithmeticAtomPair.energy p = 0)
    (hMissing :
      ¬ ∃ p : ArithmeticAtomPair Atomic n,
        ArithmeticAtomPair.energy p = k)
    (hk : k ≤ bound) :
    BoundedAtomPairEnergySuccessorTransport Atomic n bound -> False := by
  intro T
  exact hMissing
    (atom_pair_realization_up_to_bound_of_zero_and_bounded_pair_transport
      hZero T k hk)

/-- A bounded successor transport is impossible if the realized atom-pair
spectrum already has a maximum energy strictly below the target bound. -/
theorem no_bounded_pair_energy_successor_transport_of_max_energy_below_bound
    {Atomic : Nat -> Prop} {n bound : Nat}
    (M : AtomPairMaxEnergyCertificate Atomic n)
    (hBelow :
      ArithmeticAtomPair.energy M.maxPair < bound) :
    BoundedAtomPairEnergySuccessorTransport Atomic n bound -> False := by
  intro T
  have hle :
      ArithmeticAtomPair.energy (T.liftPair M.maxPair hBelow) ≤
        ArithmeticAtomPair.energy M.maxPair :=
    M.maxEnergy (T.liftPair M.maxPair hBelow)
  rw [T.energy_lift M.maxPair hBelow] at hle
  exact Nat.not_succ_le_self
    (ArithmeticAtomPair.energy M.maxPair)
    (by
      simpa [Nat.succ_eq_add_one] using hle)


end RepresentationArithmeticAtomProjectionDefect
