import H0mework.Versions.R58dfec4d.ReleaseMaterials.SaturationMonoid.GenericFoundation.Cofinal.Topology.FiniteModulus.Factorial.Integral.Bounded

set_option autoImplicit false
set_option Elab.async false

noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace CofinalAllPrimeTopology

open SourceGeneratedPrimePowerCompletion

variable {L : Type u} [AddCommGroup L]

/-- One prime retains the actual integral unit and every other prime reads zero. -/
def isolatedPrimeUnit (coordinate : L ≃ₗ[ℤ] ℤ) (focus : Nat.Primes) : AllPrimeCompletion L :=
  fun prime => if prime = focus then canonicalLinearMap prime (coordinate.symm 1) else 0

theorem factorial_isolated_prime_unit_outside (coordinate : L ≃ₗ[ℤ] ℤ)
    {focus other : Nat.Primes} (separated : other ≠ focus) :
    ¬ ∃ source : L, factorialCanonicalMap source = factorialFromPrimes (isolatedPrimeUnit coordinate focus) := by
  rintro ⟨source, wrote⟩
  have original := (factorialCompletionEquiv (L := L)).injective ((factorial_from_primes_canonical source).trans wrote)
  have atOther : canonicalLinearMap other source = 0 :=
    (congrFun original other).trans (if_neg separated)
  have atFocus : canonicalLinearMap focus source = canonicalLinearMap focus (coordinate.symm 1) :=
    (congrFun original focus).trans (if_pos rfl)
  have sourceZero := integral_prime_canonical_injective coordinate other
    (atOther.trans (map_zero (canonicalLinearMap other)).symm)
  have sourceUnit := integral_prime_canonical_injective coordinate focus atFocus
  have impossible := congrArg coordinate (sourceUnit.symm.trans sourceZero)
  rw [coordinate.apply_symm_apply, map_zero] at impossible
  exact one_ne_zero impossible

/-- A class outside the integral image gives an actual rejecting stage for any bounded inventory. -/
theorem factorial_integral_residual (coordinate : L ≃ₗ[ℤ] ℤ) (value : FactorialCompletion (L := L))
    (outside : ¬ ∃ source, factorialCanonicalMap source = value) (bound base : Nat) :
    ∃ stage ≥ base, ∀ source : L, (coordinate source).natAbs ≤ bound →
      modulusProjection (factorialModulus stage) source ≠ (factorialRestriction (L := L) stage).hom value := by
  by_contra! each
  obtain ⟨source, wrote, _⟩ := (factorial_integral_source_iff coordinate value).2 ⟨bound, base, each⟩
  exact outside ⟨source, wrote⟩

end CofinalAllPrimeTopology
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
