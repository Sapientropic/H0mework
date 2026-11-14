import H0mework.Versions.R1f4eaffd.ReleaseMaterials.SaturationMonoid.GenericFoundation.Cofinal.Topology.FiniteModulus.Factorial.Equivalence

set_option autoImplicit false
set_option Elab.async false

noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace CofinalAllPrimeTopology

open CategoryTheory CategoryTheory.Limits SourceGeneratedPrimePowerCompletion
open scoped Pointwise
open private principal_smul_top from H0mework.Versions.R1f4eaffd.ReleaseMaterials.SaturationMonoid.GenericFoundation.Cofinal.Topology.FiniteModulus

variable {L M : Type u} [AddCommGroup L] [AddCommGroup M]

def factorialCanonicalMap : L →ₗ[ℤ] FactorialCompletion (L := L) :=
  (limit.lift _ (Cone.mk (ModuleCat.of ℤ L) (factorialSourceState (L := L)))).hom

theorem factorial_canonical_restriction (stage : Nat) (source : L) :
    (factorialRestriction (L := L) stage).hom (factorialCanonicalMap source) =
      modulusProjection (factorialModulus stage) source :=
  ConcreteCategory.congr_hom
    (limit.lift_π (Cone.mk (ModuleCat.of ℤ L) (factorialSourceState (L := L))) (Opposite.op stage)) source

theorem factorial_from_primes_canonical (source : L) :
    factorialFromPrimes (allPrimeMap source) = factorialCanonicalMap source := by
  apply Concrete.limit_ext (factorialTower (L := L))
  rintro ⟨stage⟩
  let modulus := factorialModulus stage
  let nonzero := factorial_modulus_ne_zero stage
  have read := (modulus_projection_eq_iff modulus nonzero source (allPrimeMap source)).2
    (funext fun p => (allPrime_restriction p.val (modulusDepth modulus p) source).symm)
  exact (factorial_from_primes_restriction stage (allPrimeMap source)).trans
    (read.symm.trans (factorial_canonical_restriction stage source).symm)

private def modulusAction (action : L →ₗ[ℤ] M) (modulus : Nat) :
    ModulusResidual (L := L) modulus →ₗ[ℤ] ModulusResidual (L := M) modulus :=
  (modulusRange modulus).mapQ (modulusRange modulus) action (by
    intro value paid
    change action value ∈ modulusRange (L := M) modulus
    rw [modulusRange, principal_smul_top] at paid ⊢
    obtain ⟨source, rfl⟩ := paid
    exact ⟨action source, (map_zsmul action (modulus : ℤ) source).symm⟩)

private theorem modulus_action_projection (action : L →ₗ[ℤ] M) (modulus : Nat) (source : L) :
    modulusAction action modulus (modulusProjection modulus source) = modulusProjection modulus (action source) := rfl

private theorem modulus_read_action (action : L →ₗ[ℤ] M) (modulus : Nat) (nonzero : modulus ≠ 0)
    (family : AllPrimeCompletion L) :
    modulusAction action modulus (modulusRead modulus nonzero family) =
      modulusRead modulus nonzero (allPrimeSuccessor action family) := by
  let primes := modulusPrimes modulus
  let depth := modulusDepth modulus
  let source := finitePrimeLift primes depth family
  have prior := finite_prime_lift_projection primes depth family
  have fromSource := (modulus_projection_eq_iff modulus nonzero source family).2 prior
  have arrived := (modulus_projection_eq_iff modulus nonzero (action source) (allPrimeSuccessor action family)).2
    (finite_prime_successor primes depth action family source prior)
  exact (congrArg (modulusAction action modulus) fromSource.symm).trans
    ((modulus_action_projection action modulus source).trans arrived)

private def factorialTowerMap (action : L →ₗ[ℤ] M) : factorialTower (L := L) ⟶ factorialTower (L := M) :=
  NatTrans.ofOpSequence (fun stage => ModuleCat.ofHom (modulusAction action (factorialModulus stage))) (by
    intro stage
    let step := Nat.le_add_right stage 1
    let fromSource := (factorialTower (L := L)).map (homOfLE step).op
    let atTarget := (factorialTower (L := M)).map (homOfLE step).op
    change fromSource ≫ ModuleCat.ofHom (modulusAction action (factorialModulus stage)) =
      ModuleCat.ofHom (modulusAction action (factorialModulus (stage+1))) ≫ atTarget
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro residue
    obtain ⟨source, rfl⟩ := (modulusRange (L := L) (factorialModulus (stage+1))).mkQ_surjective residue
    exact (congrArg (modulusAction action (factorialModulus stage)) (factorial_edge_projection step source)).trans
      ((modulus_action_projection action (factorialModulus stage) source).trans
        (factorial_edge_projection step (action source)).symm))

/-- The actual source action induces the action on the single full factorial limit. -/
def factorialCompletionAction (action : L →ₗ[ℤ] M) :
    FactorialCompletion (L := L) →ₗ[ℤ] FactorialCompletion (L := M) :=
  (limMap (factorialTowerMap action)).hom

theorem factorial_action_restriction (action : L →ₗ[ℤ] M) (stage : Nat) (value : FactorialCompletion (L := L)) :
    (factorialRestriction (L := M) stage).hom (factorialCompletionAction action value) =
      modulusAction action (factorialModulus stage) ((factorialRestriction (L := L) stage).hom value) :=
  ConcreteCategory.congr_hom (limMap_π (factorialTowerMap action) (Opposite.op stage)) value

theorem factorial_from_primes_action (action : L →ₗ[ℤ] M) (family : AllPrimeCompletion L) :
    factorialCompletionAction action (factorialFromPrimes family) =
      factorialFromPrimes (allPrimeSuccessor action family) := by
  apply Concrete.limit_ext (factorialTower (L := M))
  rintro ⟨stage⟩
  let modulus := factorialModulus stage
  let nonzero := factorial_modulus_ne_zero stage
  exact (factorial_action_restriction action stage (factorialFromPrimes family)).trans
    ((congrArg (modulusAction action modulus) (factorial_from_primes_restriction stage family)).trans
      ((modulus_read_action action modulus nonzero family).trans
        (factorial_from_primes_restriction stage (allPrimeSuccessor action family)).symm))

theorem factorial_action_readback (action : L →ₗ[ℤ] M) (family : AllPrimeCompletion L) :
    factorialToPrimes (factorialCompletionAction action (factorialFromPrimes family)) =
      allPrimeSuccessor action family :=
  (congrArg factorialToPrimes (factorial_from_primes_action action family)).trans
    (factorial_to_primes_from_primes (allPrimeSuccessor action family))

end CofinalAllPrimeTopology
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
