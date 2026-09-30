import H0mework.Fock.PrimeField.Birth
import H0mework.Realization.Operations.FieldInputs

/-! Original prime coordinates read the physical field's exact source threshold. -/

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourcePrimeHistoryRecovery

open NoIslandNoMagic.CanonicalArithmeticState
open ParticleWaveFock ParticleWaveFockRuntime
open NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual
open NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.ThetaJRoleRepresentation
open SourceGeneratedIntegralCharacterGroupRing

noncomputable section

def primeRead (prime : Nat.Primes) : IntegralOneParticle →ₗ[ℤ] ℤ :=
  (Finsupp.lapply (R := ℤ) (M := ℤ) (primePowerUnit prime 1)).comp canonicalBasis.repr.toLinearMap

private theorem unit_injective : Function.Injective (fun prime : Nat.Primes => primePowerUnit prime 1) := by
  intro left right same
  apply Subtype.ext
  have values := congrArg scaleValue same
  rw [primePowerUnit_value, primePowerUnit_value] at values
  simpa only [thetaDistributionPrimePower, pow_one, Nat.cast_inj] using values

theorem primeRead_atom (prime other : Nat.Primes) :
    primeRead prime (SourceFactorizationAction.atom other) = if other = prime then 1 else 0 := by
  change (canonicalBasis.repr (delta (primePowerUnit other 1))) (primePowerUnit prime 1) = _
  rw [← canonicalBasis_apply, canonicalBasis.repr_self, Finsupp.single_apply]
  simp only [unit_injective.eq_iff]

theorem primeRead_projection (prime : Nat.Primes) (counts : Nat.Primes →₀ Nat) :
    primeRead prime (SourceFactorizationAction.supportProjection counts) =
      if prime ∈ counts.support then 1 else 0 := by
  classical
  change primeRead prime (counts.support.sum SourceFactorizationAction.atom) = _
  rw [map_sum]
  simp only [primeRead_atom]
  exact Finset.sum_ite_eq' _ _ _

def rawField (state : Nat) : IntegralOneParticle := sourceFieldAt (runtimeAt state).current.visit.current

theorem primeRead_source (prime : Nat.Primes) (state : Nat) :
    primeRead prime (rawField state) = if prime.val ≤ 2 * (state + 2) then 1 else 0 := by
  let current : CanonicalUnitArithmeticRoot.Current := (runtimeAt state).current.visit.current
  calc
    _ = primeRead prime (SourceFactorizationAction.supportProjection
        (SourceFactorizationAction.primeCounts (SourceFactorizationAction.Fock.history current))) :=
      congrArg (primeRead prime) (SourceFactorizationAction.Fock.field_read current)
    _ = _ := by
      have index : scanIndex current = state + 1 := runtimeAt_scanIndex state
      simp only [primeRead_projection, SourceFactorizationAction.Fock.primeCounts_support,
        SourceFactorizationAction.Fock.history_size, index]

end
end SourcePrimeHistoryRecovery
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
