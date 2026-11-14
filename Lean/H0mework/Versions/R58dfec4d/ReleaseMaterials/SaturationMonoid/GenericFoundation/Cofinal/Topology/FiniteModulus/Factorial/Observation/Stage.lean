import H0mework.Versions.R1f4eaffd.ReleaseMaterials.SaturationMonoid.GenericFoundation.Cofinal.Topology.FiniteModulus.Factorial.Action
import H0mework.Versions.R18f91d79.ReleaseMaterials.SaturationMonoid.GenericFoundation.Cofinal.Topology.Functor

set_option autoImplicit false
set_option Elab.async false

noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace CofinalAllPrimeTopology

open CategoryTheory CategoryTheory.Limits
open private modulusAction from H0mework.Versions.R1f4eaffd.ReleaseMaterials.SaturationMonoid.GenericFoundation.Cofinal.Topology.FiniteModulus.Factorial.Action
open private factorial_modulus_dvd from H0mework.Versions.R1f4eaffd.ReleaseMaterials.SaturationMonoid.GenericFoundation.Cofinal.Topology.FiniteModulus.Factorial

variable {L M N : Type u} [AddCommGroup L] [AddCommGroup M] [AddCommGroup N]

private theorem modulus_action_id (n : Nat) :
    modulusAction (LinearMap.id : L →ₗ[ℤ] L) n = LinearMap.id := by
  apply Submodule.linearMap_qext
  exact LinearMap.ext fun _ => rfl

private theorem modulus_action_comp (n : Nat) (f : L →ₗ[ℤ] M) (g : M →ₗ[ℤ] N) :
    modulusAction (g.comp f) n = (modulusAction g n).comp (modulusAction f n) := by
  apply Submodule.linearMap_qext
  exact LinearMap.ext fun _ => rfl

private theorem modulus_action_add (n : Nat) (f g : L →ₗ[ℤ] M) :
    modulusAction (f + g) n = modulusAction f n + modulusAction g n := by
  apply Submodule.linearMap_qext
  exact LinearMap.ext fun source => map_add (modulusProjection n) (f source) (g source)

private theorem modulus_action_restrict (f : L →ₗ[ℤ] M) {lower upper : Nat} (written : lower ∣ upper) :
    (modulusMap written).comp (modulusAction f upper) = (modulusAction f lower).comp (modulusMap written) := by
  apply Submodule.linearMap_qext
  exact LinearMap.ext fun _ => rfl

/-- The original factorial quotients observe the action additively. -/
def factorialStageFunctor (stage : Nat) : AddCommGrpCat.{u} ⥤ ModuleCat.{u} ℤ where
  obj A := ModuleCat.of ℤ (ModulusResidual (L := A) (factorialModulus stage))
  map f := ModuleCat.ofHom (modulusAction f.hom.toIntLinearMap (factorialModulus stage))
  map_id A := ModuleCat.hom_ext (modulus_action_id (L := A) (factorialModulus stage))
  map_comp f g := ModuleCat.hom_ext (modulus_action_comp (factorialModulus stage) f.hom.toIntLinearMap g.hom.toIntLinearMap)

instance (stage : Nat) : (factorialStageFunctor.{u} stage).Additive where
  map_add := by
    intro A B f g
    exact ModuleCat.hom_ext (modulus_action_add (factorialModulus stage) f.hom.toIntLinearMap g.hom.toIntLinearMap)

def factorialStageTransition (stage : Nat) : factorialStageFunctor.{u} (stage+1) ⟶ factorialStageFunctor stage where
  app A := ModuleCat.ofHom (modulusMap (L := A) (factorial_modulus_dvd (Nat.le_succ stage)))
  naturality _ _ f := ModuleCat.hom_ext (modulus_action_restrict f.hom.toIntLinearMap (factorial_modulus_dvd (Nat.le_succ stage)))

theorem factorial_stage_transition_surjective (A : AddCommGrpCat.{u}) (stage : Nat) :
    Function.Surjective ((factorialStageTransition stage).app A) := by
  intro value
  obtain ⟨source, represented⟩ := (modulusRange (L := A) (factorialModulus stage)).mkQ_surjective value
  exact ⟨modulusProjection (factorialModulus (stage+1)) source, represented⟩

end CofinalAllPrimeTopology
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
