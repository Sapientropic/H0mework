import H0mework.Versions.R58dfec4d.ReleaseMaterials.SaturationMonoid.GenericFoundation.Cofinal.Topology.FiniteModulus.Factorial.Observation.Stage

set_option autoImplicit false
set_option Elab.async false

noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace CofinalAllPrimeTopology

open CategoryTheory CategoryTheory.Limits SourceGeneratedPrimePowerCompletion
open private completion_map_add from H0mework.Versions.R18f91d79.ReleaseMaterials.SaturationMonoid.GenericFoundation.Cofinal.Topology.Functor
open private factorial_step factorial_modulus_dvd from H0mework.Versions.R1f4eaffd.ReleaseMaterials.SaturationMonoid.GenericFoundation.Cofinal.Topology.FiniteModulus.Factorial

variable {L M N : Type u} [AddCommGroup L] [AddCommGroup M] [AddCommGroup N]

private theorem factorial_action_id : factorialCompletionAction (LinearMap.id : L →ₗ[ℤ] L) = LinearMap.id := by
  apply LinearMap.ext
  intro value
  obtain ⟨family, rfl⟩ := (factorialCompletionEquiv (L := L)).surjective value
  have read : allPrimeSuccessor LinearMap.id family = family := by
    funext prime
    exact ConcreteCategory.congr_hom (inducedCompletionMap_id (L := L) prime) (family prime)
  exact (factorial_from_primes_action LinearMap.id family).trans (congrArg factorialFromPrimes read)

private theorem factorial_action_comp (f : L →ₗ[ℤ] M) (g : M →ₗ[ℤ] N) :
    factorialCompletionAction (g.comp f) = (factorialCompletionAction g).comp (factorialCompletionAction f) := by
  apply LinearMap.ext
  intro value
  obtain ⟨family, rfl⟩ := (factorialCompletionEquiv (L := L)).surjective value
  have read : allPrimeSuccessor (g.comp f) family = allPrimeSuccessor g (allPrimeSuccessor f family) := by
    funext prime
    exact ConcreteCategory.congr_hom (inducedCompletionMap_comp prime g f) (family prime)
  have moved := (congrArg (factorialCompletionAction g) (factorial_from_primes_action f family)).trans
    (factorial_from_primes_action g (allPrimeSuccessor f family))
  exact (factorial_from_primes_action (g.comp f) family).trans ((congrArg factorialFromPrimes read).trans moved.symm)

private theorem factorial_action_add (f g : L →ₗ[ℤ] M) :
    factorialCompletionAction (f+g) = factorialCompletionAction f + factorialCompletionAction g := by
  apply LinearMap.ext
  intro value
  obtain ⟨family, rfl⟩ := (factorialCompletionEquiv (L := L)).surjective value
  have read : allPrimeSuccessor (f+g) family = allPrimeSuccessor f family + allPrimeSuccessor g family := by
    funext prime
    exact ConcreteCategory.congr_hom (completion_map_add prime f g) (family prime)
  have moved := congrArg₂ (fun left right => left + right)
    (factorial_from_primes_action f family) (factorial_from_primes_action g family)
  exact (factorial_from_primes_action (f+g) family).trans
    ((congrArg factorialFromPrimes read).trans
      ((map_add factorialFromPrimes (allPrimeSuccessor f family) (allPrimeSuccessor g family)).trans moved.symm))

/-- The original factorial inverse limit is an additive observation of the source action. -/
def factorialCompletionFunctor : AddCommGrpCat.{u} ⥤ ModuleCat.{u} ℤ where
  obj A := FactorialCompletion (L := A)
  map f := ModuleCat.ofHom (factorialCompletionAction f.hom.toIntLinearMap)
  map_id A := ModuleCat.hom_ext (factorial_action_id (L := A))
  map_comp f g := ModuleCat.hom_ext (factorial_action_comp f.hom.toIntLinearMap g.hom.toIntLinearMap)

instance : (factorialCompletionFunctor.{u}).Additive where
  map_add := by
    intro A B f g
    exact ModuleCat.hom_ext (factorial_action_add f.hom.toIntLinearMap g.hom.toIntLinearMap)

def factorialFunctorRestriction (stage : Nat) : factorialCompletionFunctor.{u} ⟶ factorialStageFunctor stage where
  app A := factorialRestriction (L := A) stage
  naturality _ _ f := ModuleCat.hom_ext
    (LinearMap.ext (factorial_action_restriction f.hom.toIntLinearMap stage))

theorem factorial_functor_restriction_step (stage : Nat) :
    factorialFunctorRestriction.{u} (stage+1) ≫ factorialStageTransition stage = factorialFunctorRestriction stage := by
  apply NatTrans.ext
  funext A
  let edge := (homOfLE (Nat.le_add_right stage 1)).op
  let upper := factorialRestriction (L := A) (stage+1)
  have compatible := limit.w (factorialTower (L := A)) edge
  exact (congrArg (fun step => upper ≫ step) (factorial_step (L := A) stage).symm).trans compatible

end CofinalAllPrimeTopology
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
