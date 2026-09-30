import H0mework.Versions.X.Fock.PrimeField.CompletionPrimitive

/-! The existing boundary certificate retains the unit coordinate while recovering every source coefficient. -/

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourcePrimeCompletion

open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime
open SourceGeneratedActionObservationHistory SourcePrimeHistoryRecovery

noncomputable section

theorem source_zero (word : SourceOperationNative.Carrier process) :
    word 0 = SourceSuccessorBoundary.mass ℤ word - SourceSuccessorBoundary.certificate ℤ word 0 := by
  have original := congrArg (fun value : Nat →₀ ℤ => value 0) (SourceSuccessorBoundary.boundary_certificate ℤ word)
  change (Finsupp.mapDomain Nat.succ (SourceSuccessorBoundary.certificate ℤ word)) 0 -
    SourceSuccessorBoundary.certificate ℤ word 0 =
      word 0 - (SourceSuccessorBoundary.mass ℤ word • Finsupp.single 0 1) 0 at original
  rw [Finsupp.smul_apply, Finsupp.single_eq_same, smul_eq_mul, mul_one,
    Finsupp.mapDomain_of_notMem_range _ 0 (by rintro ⟨index, impossible⟩; omega)] at original
  omega

theorem source_successor (word : SourceOperationNative.Carrier process) (index : Nat) :
    word (index + 1) = SourceSuccessorBoundary.certificate ℤ word index -
      SourceSuccessorBoundary.certificate ℤ word (index + 1) := by
  have original := congrArg (fun value : Nat →₀ ℤ => value (index + 1))
    (SourceSuccessorBoundary.boundary_certificate ℤ word)
  change (Finsupp.mapDomain Nat.succ (SourceSuccessorBoundary.certificate ℤ word)) (Nat.succ index) -
    SourceSuccessorBoundary.certificate ℤ word (index + 1) =
      word (index + 1) - (SourceSuccessorBoundary.mass ℤ word • Finsupp.single 0 1) (index + 1) at original
  rw [Finsupp.mapDomain_apply Nat.succ_injective] at original
  simp only [Finsupp.smul_apply, Finsupp.single_eq_of_ne (by omega : index + 1 ≠ 0), smul_zero, sub_zero] at original
  exact original.symm

end
end SourcePrimeCompletion
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
