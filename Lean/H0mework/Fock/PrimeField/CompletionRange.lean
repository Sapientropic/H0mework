import H0mework.Fock.PrimeField.CompletionUnit

/-! Every complete stage keeps the original prime inventory; its prime coordinates separate that same stage. -/

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourcePrimeCompletion

open NoIslandNoMagic.CanonicalArithmeticState
open ParticleWaveFock ParticleWaveFockRuntime
open NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual
open SourceGeneratedActionObservationHistory SourcePrimeHistoryRecovery

noncomputable section

def primeLift : (Nat.Primes →₀ ℤ) →ₗ[ℤ] IntegralOneParticle :=
  Finsupp.linearCombination ℤ SourceFactorizationAction.atom

theorem primeRead_lift (prime : Nat.Primes) (counts : Nat.Primes →₀ ℤ) :
    primeRead prime (primeLift counts) = counts prime := by
  have coefficients : (primeRead prime).comp primeLift = Finsupp.lapply (R := ℤ) (M := ℤ) prime := by
    apply Finsupp.lhom_ext'
    intro other
    apply LinearMap.ext_ring
    change primeRead prime (primeLift (Finsupp.single other 1)) = (Finsupp.single other 1) prime
    simp only [primeLift, Finsupp.linearCombination_single, one_smul, primeRead_atom, Finsupp.single_apply]
  exact LinearMap.congr_fun coefficients counts

theorem rawField_in_range (state : Nat) : rawField state ∈ primeLift.range := by
  let current : CanonicalUnitArithmeticRoot.Current := (runtimeAt state).current.visit.current
  have actual : rawField state = SourceFactorizationAction.supportProjection
      (SourceFactorizationAction.primeCounts (SourceFactorizationAction.Fock.history current)) :=
    SourceFactorizationAction.Fock.field_read current
  rw [actual]
  change (SourceFactorizationAction.primeCounts (SourceFactorizationAction.Fock.history current)).support.sum
    SourceFactorizationAction.atom ∈ primeLift.range
  apply primeLift.range.sum_mem
  intro prime _
  exact ⟨Finsupp.single prime 1, by simp only [primeLift, Finsupp.linearCombination_single, one_smul]⟩

theorem word_read_in_range (word : SourceOperationNative.Carrier process) (stage : Nat) :
    observation ((nativeAction ^ stage) word) ∈ primeLift.range := by
  induction word using Finsupp.induction with
  | zero => simpa only [map_zero] using primeLift.range.zero_mem
  | @single_add state scalar word _ _ previous =>
      rw [map_add, map_add]
      apply primeLift.range.add_mem _ previous
      have point : Finsupp.single state scalar = scalar • SourceOperationNative.statePoint process state := by
        simp only [SourceOperationNative.statePoint, Finsupp.smul_single, smul_eq_mul, mul_one]
      rw [point, map_smul, map_smul, source_iterate, SourceOperationNative.observer_statePoint]
      exact primeLift.range.smul_mem scalar (rawField_in_range (state + stage))

theorem complete_read_in_range (value : Field) (stage : Nat) : read stage value ∈ primeLift.range := by
  obtain ⟨word, agrees⟩ := finite_source_reads value stage
  rw [← agrees stage le_rfl, read_source]
  exact word_read_in_range word stage

theorem read_zero_of_prime_reads_zero (value : Field) (stage : Nat)
    (invisible : ∀ prime, primeRead prime (read stage value) = 0) : read stage value = 0 := by
  obtain ⟨counts, source⟩ := complete_read_in_range value stage
  have empty : counts = 0 := by
    ext prime
    rw [← primeRead_lift prime counts, source]
    exact invisible prime
  rw [empty, map_zero] at source
  exact source.symm

end
end SourcePrimeCompletion
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
