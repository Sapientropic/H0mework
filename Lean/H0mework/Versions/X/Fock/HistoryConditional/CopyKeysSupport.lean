import H0mework.Fock.HistoryConditional.CopyKeysNative
import H0mework.Versions.X.Fock.PrimeField.RecoveryCoefficient

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceCopyNativeKeys

open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime

theorem key_mem (state : Nat) (prime : Nat.Primes) :
    prime ∈ key state ↔ prime.val ≤ 2 * (state + 2) := by
  induction state with
  | zero =>
      change prime ∈ seed ↔ prime.val ≤ 4
      constructor
      · intro present
        have alternatives : prime = (⟨2, Nat.prime_two⟩ : Nat.Primes) ∨ prime = (⟨3, by decide⟩ : Nat.Primes) :=
          (Finset.mem_insert.mp present).imp_right Finset.mem_singleton.mp
        rcases alternatives with two | three
        · have value := congrArg (fun p : Nat.Primes => p.val) two
          change prime.val = 2 at value
          omega
        · have value := congrArg (fun p : Nat.Primes => p.val) three
          change prime.val = 3 at value
          omega
      · intro bound
        rcases prime.property.eq_two_or_odd with two | odd
        · exact Finset.mem_insert.mpr (Or.inl ((Nat.Primes.coe_nat_inj prime ⟨2, Nat.prime_two⟩).mp two))
        · have lower := prime.property.two_le
          have value : prime.val = 3 := by omega
          exact Finset.mem_insert.mpr (Or.inr (Finset.mem_singleton.mpr
            ((Nat.Primes.coe_nat_inj prime ⟨3, by decide⟩).mp value)))
  | succ state previous =>
      rw [key_next]
      by_cases fresh : Nat.Prime (2 * state + 5)
      · have update : advance state (key state) = insert (⟨2 * state + 5, fresh⟩ : Nat.Primes) (key state) := dif_pos fresh
        rw [update]
        constructor
        · intro present
          rcases Finset.mem_insert.mp present with added | old
          · have value := congrArg (fun p : Nat.Primes => p.val) added
            change prime.val = 2 * state + 5 at value
            omega
          · have bound := previous.mp old
            omega
        · intro bound
          by_cases old : prime.val ≤ 2 * (state + 2)
          · exact Finset.mem_insert.mpr (Or.inr (previous.mpr old))
          · have parity := prime.property.eq_two_or_odd
            have value : prime.val = 2 * state + 5 := by omega
            exact Finset.mem_insert.mpr (Or.inl ((Nat.Primes.coe_nat_inj prime ⟨2 * state + 5, fresh⟩).mp value))
      · rw [advance, dif_neg fresh, previous]
        constructor
        · intro old
          omega
        · intro bound
          by_contra old
          have parity := prime.property.eq_two_or_odd
          have value : prime.val = 2 * state + 5 := by omega
          exact fresh (value ▸ prime.property)

theorem key_source_support (state : Nat) :
    key state = (SourceFactorizationAction.primeCounts
      (SourceFactorizationAction.Fock.history (runtimeAt state).current.visit.current)).support := by
  apply Finset.ext
  intro prime
  have size := SourceFactorizationAction.Fock.history_size (runtimeAt state).current.visit.current
  rw [runtimeAt_scanIndex] at size
  exact (key_mem state prime).trans ((SourceFactorizationAction.Fock.primeCounts_support _ prime).trans
    (by rw [size])).symm

noncomputable section

theorem field_read (state : Nat) :
    SourcePrimeHistoryRecovery.rawField state = (key state).sum SourceFactorizationAction.atom := by
  have source := SourceFactorizationAction.Fock.field_read (runtimeAt state).current.visit.current
  change SourcePrimeHistoryRecovery.rawField state =
    (SourceFactorizationAction.primeCounts
      (SourceFactorizationAction.Fock.history (runtimeAt state).current.visit.current)).support.sum SourceFactorizationAction.atom at source
  rw [← key_source_support] at source
  exact source

theorem key_fibre (left right : Nat) :
    key left = key right ↔ SourcePrimeHistoryRecovery.rawField left = SourcePrimeHistoryRecovery.rawField right := by
  constructor
  · intro same
    rw [field_read, field_read, same]
  · intro same
    apply Finset.ext
    intro prime
    rw [key_mem, key_mem]
    have read := congrArg (SourcePrimeHistoryRecovery.primeRead prime) same
    simp only [SourcePrimeHistoryRecovery.primeRead_source] at read
    by_cases earlier : prime.val ≤ 2 * (left + 2)
    <;> by_cases later : prime.val ≤ 2 * (right + 2)
    <;> simp_all only [if_pos, if_neg, not_false_eq_true, iff_self]
    all_goals norm_num at read

end
end SourceCopyNativeKeys
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
