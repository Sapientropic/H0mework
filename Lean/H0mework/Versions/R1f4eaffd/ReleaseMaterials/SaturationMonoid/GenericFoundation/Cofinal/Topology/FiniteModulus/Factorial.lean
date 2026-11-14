import H0mework.Versions.R1f4eaffd.ReleaseMaterials.SaturationMonoid.GenericFoundation.Cofinal.Topology.FiniteModulus.Factorization
import Mathlib.Data.Nat.Factorial.Basic

set_option autoImplicit false
set_option Elab.async false

noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace CofinalAllPrimeTopology

open CategoryTheory CategoryTheory.Limits SourceGeneratedPrimePowerCompletion

variable {L : Type u} [AddCommGroup L]

def factorialModulus (stage : Nat) : Nat := (stage+1).factorial

theorem factorial_modulus_ne_zero (stage : Nat) : factorialModulus stage ≠ 0 := (Nat.factorial_pos _).ne'

private theorem factorial_modulus_dvd {lower upper : Nat} (read : lower ≤ upper) :
    factorialModulus lower ∣ factorialModulus upper :=
  Nat.factorial_dvd_factorial (Nat.succ_le_succ read)

/-- The actual factorial quotient tower uses only the divisibility restrictions. -/
def factorialTower : ℕᵒᵖ ⥤ ModuleCat.{u} ℤ :=
  Functor.ofOpSequence (X := fun stage => ModuleCat.of ℤ (ModulusResidual (L := L) (factorialModulus stage)))
    (fun stage => ModuleCat.ofHom (modulusMap (L := L) (factorial_modulus_dvd (Nat.le_succ stage))))

abbrev FactorialCompletion := limit (factorialTower (L := L))

def factorialRestriction (stage : Nat) : FactorialCompletion (L := L) ⟶
    (factorialTower (L := L)).obj (Opposite.op stage) :=
  limit.π (factorialTower (L := L)) (Opposite.op stage)

private theorem factorial_step (stage : Nat) :
    (factorialTower (L := L)).map (homOfLE (Nat.le_add_right stage 1)).op =
      ModuleCat.ofHom (modulusMap (L := L) (factorial_modulus_dvd (Nat.le_succ stage))) :=
  Functor.ofOpSequence_map_homOfLE_succ _ stage

/-- The original integral source projects to every factorial stage. -/
def factorialSourceState : (Functor.const ℕᵒᵖ).obj (ModuleCat.of ℤ L) ⟶ factorialTower (L := L) :=
  NatTrans.ofOpSequence (fun stage => ModuleCat.ofHom (modulusProjection (L := L) (factorialModulus stage)))
    (by
      intro stage
      let first := ModuleCat.ofHom (modulusProjection (L := L) (factorialModulus stage))
      let next := ModuleCat.ofHom (modulusProjection (L := L) (factorialModulus (stage+1)))
      change 𝟙 (ModuleCat.of ℤ L) ≫ first = next ≫ (factorialTower (L := L)).map _
      exact (Category.id_comp first).trans (Eq.trans rfl (congrArg (fun edge => next ≫ edge) (factorial_step (L := L) stage).symm)))

theorem factorial_edge_projection {lower upper : Nat} (written : lower ≤ upper) (value : L) :
    ((factorialTower (L := L)).map (homOfLE written).op).hom (modulusProjection (factorialModulus upper) value) =
      modulusProjection (factorialModulus lower) value :=
  (ConcreteCategory.congr_hom ((factorialSourceState (L := L)).naturality (homOfLE written).op) value).symm

private def factorialPrimeCone : Cone (factorialTower (L := L)) :=
  Cone.mk (ModuleCat.of ℤ (AllPrimeCompletion L))
    (NatTrans.ofOpSequence (fun stage => ModuleCat.ofHom
      (modulusRead (L := L) (factorialModulus stage) (factorial_modulus_ne_zero stage))) (by
        intro stage
        let lower := ModuleCat.ofHom (modulusRead (L := L) (factorialModulus stage) (factorial_modulus_ne_zero stage))
        let upper := ModuleCat.ofHom (modulusRead (L := L) (factorialModulus (stage+1)) (factorial_modulus_ne_zero (stage+1)))
        let written := factorial_modulus_dvd (Nat.le_succ stage)
        have paid : lower = upper ≫ ModuleCat.ofHom (modulusMap (L := L) written) :=
          ModuleCat.hom_ext (LinearMap.ext fun value => (modulus_read_naturality
            (factorial_modulus_ne_zero stage) (factorial_modulus_ne_zero (stage+1)) written value).symm)
        change 𝟙 (ModuleCat.of ℤ (AllPrimeCompletion L)) ≫ lower = upper ≫ (factorialTower (L := L)).map _
        exact (Category.id_comp lower).trans (paid.trans (congrArg (fun edge => upper ≫ edge) (factorial_step (L := L) stage).symm))))

/-- The inverse limit lift of the composite residues keeps all prime towers jointly. -/
def factorialFromPrimes : AllPrimeCompletion L →ₗ[ℤ] FactorialCompletion (L := L) :=
  (limit.lift _ (factorialPrimeCone (L := L))).hom

theorem factorial_from_primes_restriction (stage : Nat) (value : AllPrimeCompletion L) :
    (factorialRestriction (L := L) stage).hom (factorialFromPrimes value) =
      modulusRead (factorialModulus stage) (factorial_modulus_ne_zero stage) value :=
  ConcreteCategory.congr_hom (limit.lift_π (factorialPrimeCone (L := L)) (Opposite.op stage)) value

end CofinalAllPrimeTopology
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
