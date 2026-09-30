import H0mework.Probability.Information.InventoryGrowth
import H0mework.Fock.PrimeField.RecoveryCoefficient
import H0mework.Fock.PrimeField.Consumer

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceGeneratedConditionalInventory

open SourceConditionalInventory SourceUniformFibreVariance SourcePrimeHistoryRecovery
open NoIslandNoMagic.CanonicalArithmeticState ParticleWaveFock ParticleWaveFockRuntime
open scoped Classical
noncomputable section

local instance sourceInventoryMeasurable : MeasurableSpace IntegralOneParticle := ⊤

def snapshotCost (bound : Nat) : ℝ := cost bound (fun index => rawField index.val)

theorem source_step (bound : Nat) :
    rawField (bound + 1) = rawField bound +
      SourceFactorizationAction.Fock.birth (runtimeAt bound).current.visit.current :=
  (SourceFactorizationAction.Fock.runtime_source_factorization bound).2.1

theorem fresh_snapshot (bound : Nat) (prime : Nat.Prime (2 * bound + 5)) :
    rawField (bound + 1) ∉ outputs bound (fun index => rawField index.val) := by
  rintro present
  obtain ⟨index, _, same⟩ := Finset.mem_image.mp present
  let candidate : Nat.Primes := ⟨2 * bound + 5, prime⟩
  have old : primeRead candidate (rawField index.val) = 0 :=
    (primeRead_source candidate index.val).trans (if_neg (by change ¬ 2 * bound + 5 ≤ 2 * (index.val + 2); omega))
  have fresh : primeRead candidate (rawField (bound + 1)) = 1 :=
    (primeRead_source candidate (bound + 1)).trans (if_pos (by change 2 * bound + 5 ≤ 2 * (bound + 1 + 2); omega))
  exact (by norm_num : (0 : ℤ) ≠ 1) (old.symm.trans ((congrArg (primeRead candidate) same).trans fresh))

theorem unchanged_snapshot (bound : Nat) (composite : ¬ Nat.Prime (2 * bound + 5)) :
    rawField (bound + 1) = rawField bound := by
  have born : SourceFactorizationAction.Fock.birth (runtimeAt bound).current.visit.current = 0 := by
    apply SourceFactorizationAction.Fock.birth_of_composite
    simpa only [runtimeAt_scanIndex, Nat.mul_add, Nat.mul_one, Nat.add_assoc] using composite
  rw [source_step, born, add_zero]

theorem actual_cost_step (bound : Nat) :
    snapshotCost (bound + 1) = snapshotCost bound + if Nat.Prime (2 * bound + 5) then 0 else 1 := by
  unfold snapshotCost
  rw [cost_append]
  by_cases prime : Nat.Prime (2 * bound + 5)
  · rw [if_pos prime, if_neg (fresh_snapshot bound prime)]
  · have present : rawField (bound + 1) ∈ outputs bound (fun index => rawField index.val) :=
      Finset.mem_image.mpr ⟨Fin.last bound, Finset.mem_univ _, (unchanged_snapshot bound prime).symm⟩
    rw [if_neg prime, if_pos present]

theorem multiplicity_moves (bound : Nat) :
    0 < SourceFactorizationAction.Fock.wholeIncrement (runtimeAt bound).current.visit.current ⟨2, Nat.prime_two⟩ := by
  let current : CanonicalUnitArithmeticRoot.Current := (runtimeAt bound).current.visit.current
  have generated := SourceFactorizationAction.Fock.whole_increment_apply current ⟨2, Nat.prime_two⟩
  have positive : 0 < (2 * scanIndex current + 4).factorization 2 :=
    Nat.prime_two.factorization_pos_of_dvd (by omega)
      (dvd_add (dvd_mul_right 2 _) (by decide : 2 ∣ 4))
  have total : 0 < (2 * scanIndex current + 3).factorization 2 +
      (2 * scanIndex current + 4).factorization 2 := by omega
  exact total.trans_eq generated.symm

end
end SourceGeneratedConditionalInventory
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
