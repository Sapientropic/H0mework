import H0mework.Versions.X.Fock.PrimeField.CompletionRow

/-! Prime reads retain the old unit mass and extend each coordinate of the existing successor primitive. -/

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourcePrimeCompletion

open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFock
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime
open SourceGeneratedActionObservationHistory SourcePrimeHistoryRecovery

noncomputable section

private def two : Nat.Primes := ⟨2, Nat.prime_two⟩

def mass : Field →ₗ[ℤ] ℤ := (primeRead two).comp (read 0)

def primitive (owner : GlobalParentOwner) (index : Nat) : Field →ₗ[ℤ] ℤ :=
  (primeRead (selectedPrime owner index)).comp (read (delay owner index))

theorem selected_cut (owner : GlobalParentOwner) (index : Nat) :
    cut (selectedPrime owner index) = index + delay owner index + 1 := by
  have position := selected_position owner index
  unfold cut
  omega

theorem mass_source (word : SourceOperationNative.Carrier process) :
    mass (sourceMap nativeAction observation word) = SourceSuccessorBoundary.mass ℤ word := by
  change primeRead two (read 0 (sourceMap nativeAction observation word)) = _
  rw [read_source]
  exact (LinearMap.congr_fun (source_row_is_prime_read two 0) word).symm

theorem primitive_source (owner : GlobalParentOwner) (index : Nat) (word : SourceOperationNative.Carrier process) :
    primitive owner index (sourceMap nativeAction observation word) = SourceSuccessorBoundary.certificate ℤ word index := by
  change primeRead (selectedPrime owner index)
    (read (delay owner index) (sourceMap nativeAction observation word)) = _
  rw [read_source]
  calc
    _ = sourceRow (selectedPrime owner index) (delay owner index) word :=
      (LinearMap.congr_fun (source_row_is_prime_read (selectedPrime owner index) (delay owner index)) word).symm
    _ = _ := by
      have position := selected_cut owner index
      unfold sourceRow
      rw [if_neg (by omega)]
      change SourceSuccessorBoundary.certificate ℤ word (cut (selectedPrime owner index) - delay owner index - 1) = _
      congr 1
      omega

end
end SourcePrimeCompletion
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
