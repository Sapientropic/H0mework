import SaturationMonoid.GenericFoundation.Cofinal.Topology.FiniteModulus.Completion
import Mathlib.Data.Nat.Factorization.Basic

set_option autoImplicit false
set_option Elab.async false

noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace CofinalAllPrimeTopology

open SourceGeneratedPrimePowerCompletion
open scoped BigOperators Pointwise

private def primeOfFactor (modulus : Nat) : modulus.primeFactors ↪ Nat.Primes where
  toFun p := ⟨p.val, Nat.prime_of_mem_primeFactors p.property⟩
  inj' := fun _ _ equal => Subtype.ext (congrArg (fun p : Nat.Primes => p.val) equal)

/-- The finite prime inventory comes from the actual modulus. -/
def modulusPrimes (modulus : Nat) : Finset Nat.Primes :=
  modulus.primeFactors.attach.map (primeOfFactor modulus)

theorem modulus_prime_mem {modulus : Nat} {prime : Nat.Primes} :
    prime ∈ modulusPrimes modulus ↔ prime.val ∈ modulus.primeFactors := by
  constructor
  · intro member
    obtain ⟨p, _, equal⟩ := Finset.mem_map.mp member
    exact congrArg Subtype.val equal ▸ p.property
  · intro member
    exact Finset.mem_map.mpr ⟨⟨prime.val, member⟩, Finset.mem_attach _ _, Subtype.ext rfl⟩

def modulusDepth (modulus : Nat) (p : modulusPrimes modulus) : Nat := modulus.factorization p.val.val - 1

theorem modulus_depth_succ (modulus : Nat) (p : modulusPrimes modulus) :
    modulusDepth modulus p + 1 = modulus.factorization p.val.val := by
  have member : p.val.val ∈ modulus.factorization.support := modulus_prime_mem.1 p.property
  exact Nat.sub_add_cancel (Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp member))

theorem composite_modulus_factorization {modulus : Nat} (nonzero : modulus ≠ 0) :
    compositeModulus (modulusPrimes modulus) (modulusDepth modulus) = (modulus : ℤ) := by
  change (∏ p : modulusPrimes modulus, (p.val.val : ℤ)^(modulusDepth modulus p + 1)) = _
  simp only [modulus_depth_succ]
  let factor : Nat.Primes → ℤ := fun p => (p.val : ℤ)^(modulus.factorization p.val)
  change (∏ p : modulusPrimes modulus, factor p.val) = _
  have natural : (∏ p ∈ modulus.primeFactors, p^(modulus.factorization p)) = modulus :=
    Nat.prod_factorization_pow_eq_self nonzero
  calc
    _ = ∏ p ∈ modulusPrimes modulus, factor p := Finset.prod_coe_sort _ _
    _ = ∏ p ∈ modulus.primeFactors.attach, factor (primeOfFactor modulus p) := Finset.prod_map _ _ _
    _ = ∏ p ∈ modulus.primeFactors, (p : ℤ)^(modulus.factorization p) := Finset.prod_attach _ _
    _ = _ := by simpa only [Nat.cast_prod, Nat.cast_pow] using congrArg (fun n : Nat => (n : ℤ)) natural

variable {L : Type u} [AddCommGroup L]

abbrev modulusRange (modulus : Nat) : Submodule ℤ L :=
  Ideal.span {(modulus : ℤ)} • (⊤ : Submodule ℤ L)

abbrev ModulusResidual (modulus : Nat) := L ⧸ modulusRange (L := L) modulus

def modulusProjection (modulus : Nat) : L →ₗ[ℤ] ModulusResidual (L := L) modulus :=
  (modulusRange modulus).mkQ

private theorem modulus_range_le {lower upper : Nat} (written : lower ∣ upper) :
    modulusRange (L := L) upper ≤ modulusRange (L := L) lower :=
  Submodule.smul_mono_left ((Ideal.span_singleton_le_iff_mem (Ideal.span {(lower : ℤ)})).2
    (Ideal.mem_span_singleton.2 (Int.natCast_dvd_natCast.2 written)))

def modulusMap {lower upper : Nat} (written : lower ∣ upper) :
    ModulusResidual (L := L) upper →ₗ[ℤ] ModulusResidual (L := L) lower :=
  (modulusRange upper).mapQ (modulusRange lower) LinearMap.id (modulus_range_le written)

theorem modulus_map_projection {lower upper : Nat} (written : lower ∣ upper) (value : L) :
    modulusMap written (modulusProjection upper value) = modulusProjection lower value := rfl

/-- Apply the original finite-prime equivalence at the whole actual modulus. -/
def modulusEquiv (modulus : Nat) (nonzero : modulus ≠ 0) :
    ModulusResidual (L := L) modulus ≃ₗ[ℤ]
      ((p : modulusPrimes modulus) → StageResidual (L := L) p.val (modulusDepth modulus p)) :=
  (Submodule.quotEquivOfEq _ _ (congrArg (fun m : ℤ => Ideal.span {m} • (⊤ : Submodule ℤ L))
    (composite_modulus_factorization nonzero).symm)).trans
      (finitePrimeEquiv (modulusPrimes modulus) (modulusDepth modulus))

theorem modulus_equiv_projection (modulus : Nat) (nonzero : modulus ≠ 0) (value : L) :
    modulusEquiv modulus nonzero (modulusProjection modulus value) =
      finitePrimeProjection (modulusPrimes modulus) (modulusDepth modulus) value :=
  finite_prime_equiv_projection (modulusPrimes modulus) (modulusDepth modulus) value

/-- The complete prime-power family writes the canonical residue for any positive modulus. -/
def modulusRead (modulus : Nat) (nonzero : modulus ≠ 0) : AllPrimeCompletion L →ₗ[ℤ] ModulusResidual (L := L) modulus :=
  let primes := modulusPrimes modulus
  let depth := modulusDepth modulus
  (modulusEquiv modulus nonzero).symm.toLinearMap.comp
    { toFun := finitePrimeRestriction primes depth
      map_add' := by
        intro left right
        funext p
        exact map_add (restriction (L := L) p.val (depth p)).hom (left p.val) (right p.val)
      map_smul' := by
        intro scalar value
        funext p
        exact map_zsmul (restriction (L := L) p.val (depth p)).hom scalar (value p.val) }

theorem modulus_projection_eq_iff (modulus : Nat) (nonzero : modulus ≠ 0)
    (source : L) (family : AllPrimeCompletion L) :
    modulusProjection modulus source = modulusRead modulus nonzero family ↔
      finitePrimeProjection (modulusPrimes modulus) (modulusDepth modulus) source =
        finitePrimeRestriction (modulusPrimes modulus) (modulusDepth modulus) family := by
  let read := modulusEquiv (L := L) modulus nonzero
  let coordinates := finitePrimeRestriction (modulusPrimes modulus) (modulusDepth modulus) family
  have integral := modulus_equiv_projection modulus nonzero source
  have resolved : read (modulusRead modulus nonzero family) = coordinates := read.apply_symm_apply coordinates
  constructor
  · intro selected
    exact integral.symm.trans ((congrArg read selected).trans resolved)
  · intro selected
    exact read.injective (integral.trans (selected.trans resolved.symm))

/-- Divisibility transports the residue written by the same complete family. -/
theorem modulus_read_naturality {lower upper : Nat} (lower_ne : lower ≠ 0) (upper_ne : upper ≠ 0)
    (written : lower ∣ upper) (family : AllPrimeCompletion L) :
    modulusMap written (modulusRead upper upper_ne family) = modulusRead lower lower_ne family := by
  let high := modulusPrimes upper
  let highDepth := modulusDepth upper
  let source := finitePrimeLift high highDepth family
  have highRead := (modulus_projection_eq_iff upper upper_ne source family).2
    (finite_prime_lift_projection high highDepth family)
  have orders := (Nat.factorization_le_iff_dvd lower_ne upper_ne).2 written
  have lowRead : modulusProjection lower source = modulusRead lower lower_ne family := by
    apply (modulus_projection_eq_iff lower lower_ne source family).2
    funext p
    have support : p.val.val ∈ lower.factorization.support := modulus_prime_mem.1 p.property
    let lifted : high := ⟨p.val, modulus_prime_mem.2 (Finsupp.support_mono orders support)⟩
    have depth_le : modulusDepth lower p ≤ highDepth lifted := Nat.sub_le_sub_right (orders p.val.val) 1
    exact finite_prime_lift_lower high highDepth family lifted (modulusDepth lower p) depth_le
  exact (congrArg (modulusMap written) highRead.symm).trans
    ((modulus_map_projection written source).trans lowRead)

end CofinalAllPrimeTopology
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
