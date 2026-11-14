import H0mework.Versions.R58dfec4d.ReleaseMaterials.SaturationMonoid.GenericFoundation.Cofinal.Topology.FiniteModulus.Factorial.Integral.Inventory
import Mathlib.Data.Int.Interval

set_option autoImplicit false
set_option Elab.async false

noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace CofinalAllPrimeTopology

open CategoryTheory CategoryTheory.Limits SourceGeneratedPrimePowerCompletion

variable {L : Type u} [AddCommGroup L]

/-- An actual integral coordinate is separated by each whole prime-power tower. -/
theorem integral_prime_canonical_injective (coordinate : L ≃ₗ[ℤ] ℤ) (prime : Nat.Primes) :
    Function.Injective (canonicalLinearMap (L := L) prime) := by
  intro left right equal
  apply coordinate.injective
  by_contra different
  let delta := coordinate left - coordinate right
  let stage := delta.natAbs
  let period : ℤ := (prime.val : ℤ)^(stage+1)
  have hidden : canonicalLinearMap prime (left-right) = 0 :=
    (map_sub (canonicalLinearMap prime) left right).trans (sub_eq_zero.mpr equal)
  obtain ⟨divided, written⟩ := (canonicalMap_eq_zero_iff prime (left-right)).1 hidden stage
  have coordinateWritten := congrArg coordinate written
  rw [map_smul, map_sub] at coordinateWritten
  have divides : period ∣ delta := ⟨coordinate divided, coordinateWritten.symm⟩
  have nonzero : delta ≠ 0 := sub_ne_zero.mpr different
  have bound : prime.val^(stage+1) ≤ stage := by
    simpa only [period, Int.natAbs_pow, Int.natAbs_natCast] using Int.natAbs_le_of_dvd_ne_zero divides nonzero
  have grows : stage < prime.val^(stage+1) :=
    (Nat.lt_succ_self stage).trans (Nat.lt_pow_self prime.property.one_lt)
  exact (not_le_of_gt grows) bound

/-- The same integral coordinate separates the original diagonal in the whole factorial limit. -/
theorem factorial_canonical_injective (coordinate : L ≃ₗ[ℤ] ℤ) :
    Function.Injective (factorialCanonicalMap (L := L)) := by
  intro left right equal
  have original := (factorialCompletionEquiv (L := L)).injective
    ((factorial_from_primes_canonical left).trans (equal.trans (factorial_from_primes_canonical right).symm))
  let prime : Nat.Primes := ⟨2, Nat.prime_two⟩
  exact integral_prime_canonical_injective coordinate prime (congrFun original prime)

/-- An eventual bound on actual stage representatives gives the unique original integral read. -/
theorem factorial_integral_source_iff (coordinate : L ≃ₗ[ℤ] ℤ) (value : FactorialCompletion (L := L)) :
    (∃! source, factorialCanonicalMap source = value) ↔
      ∃ bound base : Nat, ∀ stage ≥ base, ∃ source : L, (coordinate source).natAbs ≤ bound ∧
        modulusProjection (factorialModulus stage) source = (factorialRestriction (L := L) stage).hom value := by
  constructor
  · rintro ⟨source, written, _⟩
    exact ⟨(coordinate source).natAbs, 0, fun stage _ =>
      ⟨source, le_rfl, (factorial_canonical_restriction stage source).symm.trans
        (congrArg (factorialRestriction (L := L) stage).hom written)⟩⟩
  · rintro ⟨bound, base, each⟩
    let inventory := (Finset.Icc (-(bound : ℤ)) (bound : ℤ)).map coordinate.symm.toEquiv.toEmbedding
    have hits : ∃ beginAt : Nat, ∀ stage ≥ beginAt, ∃ source ∈ inventory,
        modulusProjection (factorialModulus stage) source = (factorialRestriction (L := L) stage).hom value := by
      refine ⟨base, fun stage later => ?_⟩
      obtain ⟨source, bounded, reads⟩ := each stage later
      have absBound : ((coordinate source).natAbs : ℤ) ≤ bound := by exact_mod_cast bounded
      have upper := (Int.le_natAbs (a := coordinate source)).trans absBound
      have lower : -(coordinate source) ≤ bound := by
        have absNeg : -(coordinate source) ≤ ((coordinate source).natAbs : ℤ) := by
          simpa only [Int.natAbs_neg] using (Int.le_natAbs (a := -(coordinate source)))
        exact absNeg.trans absBound
      have atSource : coordinate source ∈ Finset.Icc (-(bound : ℤ)) (bound : ℤ) :=
        Finset.mem_Icc.mpr ⟨by omega, upper⟩
      exact ⟨source, Finset.mem_map.mpr ⟨coordinate source, atSource, coordinate.symm_apply_apply source⟩, reads⟩
    obtain ⟨source, _, writes⟩ := (factorial_integral_inventory_iff inventory value).2 hits
    exact ⟨source, writes, fun other same => factorial_canonical_injective coordinate (same.trans writes.symm)⟩

end CofinalAllPrimeTopology
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
