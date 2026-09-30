import H0mework.Versions.X.Arithmetic.Factorization.Action
import H0mework.Realization.Operations.SupportAction
import H0mework.Versions.X.Arithmetic.FockDynamics.RootRuntime

/-! The original exact-owner prime field is a dependent support projection of its full factorial multiplicities. -/

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceFactorizationAction

open ArithmeticGeneration CanonicalUnitArithmeticFactorizationOccurrence
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFock
open NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual
open NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.ThetaJRoleRepresentation
open SourceGeneratedIntegralCharacterGroupRing

noncomputable section

def primeCounts (history : UnitHistory) : Nat.Primes →₀ Nat :=
  (factorization history).subtypeDomain Nat.Prime

def primeIncrement (history : UnitHistory) : Nat.Primes →₀ Nat :=
  (increment history).subtypeDomain Nat.Prime

theorem prime_step (history : UnitHistory) :
    primeCounts history.next = primeCounts history + primeIncrement history := by
  change (factorization history.next).subtypeDomain Nat.Prime = _
  rw [source_step, Finsupp.subtypeDomain_add]
  rfl

def atom (prime : Nat.Primes) : IntegralOneParticle := delta (primePowerUnit prime 1)

def supportProjection (counts : Nat.Primes →₀ Nat) : IntegralOneParticle := SourceSupportAction.read atom counts

def primeIndexEquiv (history : UnitHistory) :
    PrimeIndex history ≃ {prime : Nat.Primes // prime ∈ (primeCounts history).support} where
  toFun index := ⟨prime history index, by
    apply Finsupp.mem_support_iff.mpr
    change factorization history index.val ≠ 0
    exact Finsupp.mem_support_iff.mp index.property⟩
  invFun index := ⟨index.val.val, by
    apply Finsupp.mem_support_iff.mpr
    have nonzero := Finsupp.mem_support_iff.mp index.property
    change factorization history index.val.val ≠ 0 at nonzero
    exact nonzero⟩
  left_inv index := by apply Subtype.ext; rfl
  right_inv index := by apply Subtype.ext; apply Subtype.ext; rfl

theorem owner_field_is_projection (owner : GlobalParentOwner) (index : Nat) :
    ownerPrimeField owner index = supportProjection (primeCounts (ownerEvenTargetHistory owner index)) := by
  let history := ownerEvenTargetHistory owner index
  calc
    _ = ∑ primeIndex : PrimeIndex history, atom (prime history primeIndex) := rfl
    _ = ∑ primeIndex : {p : Nat.Primes // p ∈ (primeCounts history).support}, atom primeIndex.val :=
      Equiv.sum_comp (primeIndexEquiv history) (fun primeIndex => atom primeIndex.val)
    _ = _ := Finset.sum_attach (primeCounts history).support atom

theorem support_step (history : UnitHistory) :
    supportProjection (primeCounts history.next) = supportProjection (primeCounts history) +
      SourceSupportAction.born atom (primeCounts history) (primeIncrement history) := by
  rw [prime_step]
  exact SourceSupportAction.read_update atom (primeCounts history) (primeIncrement history)

end
end SourceFactorizationAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
