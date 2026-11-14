import H0mework.Realization.Perfectification.Cofinal.Topology.LivingLawRootGeneratedCofinalAllPrimeTopologyKernel
import H0mework.Versions.Reec031c4.ReleaseMaterials.SaturationMonoid.GenericFoundation.Integral.Completion.LivingLawRootGeneratedPrimePowerCompletionIntegerRegression

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace CofinalAllPrimeTopologyRegression

open CofinalAllPrimeTopology
open SourceGeneratedPrimePowerCompletion

noncomputable section

/-- The observation is nontrivial on an integral source coordinate. -/
theorem integer_one_observable :
    allPrimeMap (L := ℤ) 1 ≠ 0 := by
  intro invisible
  let prime : Nat.Primes := ⟨2, Nat.prime_two⟩
  have atPrime : canonicalLinearMap (L := ℤ) prime 1 = 0 := by
    exact congrFun invisible prime
  exact PrimePowerCompletionIntegerRegression.completedOne_ne_zero prime atPrime

/-- A divisible carrier has an actual nonzero invisible coordinate. -/
theorem rational_one_invisible :
    (1 : ℚ) ∈ AllPrimeKernel (L := ℚ) := by
  apply (allPrimeKernel_iff (L := ℚ) 1).2
  intro prime stage
  have nonzero : (prime.1 : ℚ) ≠ 0 := by
    exact_mod_cast prime.property.ne_zero
  refine ⟨((prime.1 : ℚ) ^ (stage + 1))⁻¹, ?_⟩
  rw [← Int.cast_smul_eq_zsmul (R := ℚ), smul_eq_mul,
    Int.cast_pow, Int.cast_natCast]
  exact mul_inv_cancel₀ (pow_ne_zero (stage + 1) nonzero)

theorem rational_nonzero_invisible :
    ∃ value : ℚ, value ≠ 0 ∧ value ∈ AllPrimeKernel (L := ℚ) :=
  ⟨1, one_ne_zero, rational_one_invisible⟩

#print axioms integer_one_observable
#print axioms rational_nonzero_invisible
#print axioms CofinalAllPrimeTopology.allPrime_restriction
#print axioms CofinalAllPrimeTopology.allPrimeKernel_iff
#print axioms CofinalAllPrimeTopology.allPrimeCoimageMap_injective
#print axioms CofinalAllPrimeTopology.source_inseparable_zero_iff_kernel
#print axioms CofinalAllPrimeTopology.TopologicalAt.inseparable_zero_iff_kernel

end
end CofinalAllPrimeTopologyRegression
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
