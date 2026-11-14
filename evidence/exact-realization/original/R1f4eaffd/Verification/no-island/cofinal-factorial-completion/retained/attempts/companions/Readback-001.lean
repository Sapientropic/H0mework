import SaturationMonoid.GenericFoundation.Cofinal.Topology.FiniteModulus.Factorial

set_option autoImplicit false
set_option Elab.async false

noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace CofinalAllPrimeTopology

open CategoryTheory CategoryTheory.Limits SourceGeneratedPrimePowerCompletion
open scoped Pointwise
open private principal_smul_top from SaturationMonoid.GenericFoundation.Cofinal.Topology.FiniteModulus
open private factorial_modulus_dvd from SaturationMonoid.GenericFoundation.Cofinal.Topology.FiniteModulus.Factorial

variable {L : Type u} [AddCommGroup L]

def primePowerAddress (p : Nat.Primes) (stage : Nat) : Nat := p.val^(stage+1)-1

theorem prime_power_address_dvd (p : Nat.Primes) (stage : Nat) :
    p.val^(stage+1) ∣ factorialModulus (primePowerAddress p stage) := by
  have positive : 0 < p.val^(stage+1) := pow_pos p.property.pos _
  apply Nat.dvd_factorial positive
  change p.val^(stage+1) ≤ (p.val^(stage+1)-1)+1
  rw [Nat.sub_add_cancel positive]

private theorem modulus_range_power (p : Nat.Primes) (stage : Nat) :
    modulusRange (L := L) (p.val^(stage+1)) = powerRange (L := L) p stage := by
  unfold modulusRange
  rw [Nat.cast_pow, principal_smul_top]
  exact congrArg LinearMap.range (LinearMap.ext fun _ => rfl)

/-- The actual factorial residue restricts to the original prime-power quotient. -/
def factorialStageToPrime (p : Nat.Primes) (stage address : Nat)
    (written : p.val^(stage+1) ∣ factorialModulus address) :
    ModulusResidual (L := L) (factorialModulus address) →ₗ[ℤ] StageResidual (L := L) p stage :=
  (Submodule.quotEquivOfEq _ _ (modulus_range_power (L := L) p stage)).toLinearMap.comp (modulusMap written)

theorem factorial_stage_to_prime_projection (p : Nat.Primes) (stage address : Nat)
    (written : p.val^(stage+1) ∣ factorialModulus address) (source : L) :
    factorialStageToPrime p stage address written (modulusProjection (factorialModulus address) source) =
      stageProjection p stage source := rfl

private theorem factorial_stage_to_prime_edge (p : Nat.Primes) (stage : Nat) {lower upper : Nat}
    (edge : lower ≤ upper) (lowerDvd : p.val^(stage+1) ∣ factorialModulus lower)
    (upperDvd : p.val^(stage+1) ∣ factorialModulus upper)
    (value : ModulusResidual (L := L) (factorialModulus upper)) :
    factorialStageToPrime p stage lower lowerDvd
        (((factorialTower (L := L)).map (homOfLE edge).op).hom value) =
      factorialStageToPrime p stage upper upperDvd value := by
  obtain ⟨source, rfl⟩ := (modulusRange (L := L) (factorialModulus upper)).mkQ_surjective value
  exact (congrArg (factorialStageToPrime p stage lower lowerDvd) (factorial_edge_projection edge source)).trans
    ((factorial_stage_to_prime_projection p stage lower lowerDvd source).trans
      (factorial_stage_to_prime_projection p stage upper upperDvd source).symm)

private def factorialPrimeRead (p : Nat.Primes) (stage : Nat) :
    FactorialCompletion (L := L) →ₗ[ℤ] StageResidual (L := L) p stage :=
  (factorialStageToPrime p stage (primePowerAddress p stage) (prime_power_address_dvd p stage)).comp
    (factorialRestriction (L := L) (primePowerAddress p stage)).hom

private theorem factorial_prime_read_at (p : Nat.Primes) (stage address : Nat)
    (written : p.val^(stage+1) ∣ factorialModulus address) (value : FactorialCompletion (L := L)) :
    factorialPrimeRead p stage value =
      factorialStageToPrime p stage address written ((factorialRestriction (L := L) address).hom value) := by
  let chosen := primePowerAddress p stage
  let upper := max chosen address
  let atChosen : chosen ≤ upper := le_max_left _ _
  let atAddress : address ≤ upper := le_max_right _ _
  let upperDvd := (prime_power_address_dvd p stage).trans (factorial_modulus_dvd atChosen)
  let high := (factorialRestriction (L := L) upper).hom value
  have chosenEq := ConcreteCategory.congr_hom (limit.w (factorialTower (L := L)) (homOfLE atChosen).op) value
  have addressEq := ConcreteCategory.congr_hom (limit.w (factorialTower (L := L)) (homOfLE atAddress).op) value
  let readChosen := factorialStageToPrime (L := L) p stage chosen (prime_power_address_dvd p stage)
  let readAddress := factorialStageToPrime (L := L) p stage address written
  exact (congrArg readChosen chosenEq.symm).trans
    ((factorial_stage_to_prime_edge p stage atChosen (prime_power_address_dvd p stage) upperDvd high).trans
      ((factorial_stage_to_prime_edge p stage atAddress written upperDvd high).symm.trans
        (congrArg readAddress addressEq)))

private theorem factorial_stage_to_prime_transition (p : Nat.Primes) (stage address : Nat)
    (lowerDvd : p.val^(stage+1) ∣ factorialModulus address)
    (upperDvd : p.val^(stage+1+1) ∣ factorialModulus address)
    (value : ModulusResidual (L := L) (factorialModulus address)) :
    transition p stage (factorialStageToPrime p (stage+1) address upperDvd value) =
      factorialStageToPrime p stage address lowerDvd value := by
  obtain ⟨source, rfl⟩ := (modulusRange (L := L) (factorialModulus address)).mkQ_surjective value
  exact LinearMap.congr_fun (transition_projection p stage) source

private def factorialCofinalCone (p : Nat.Primes) : Cone (tower (L := L) p) :=
  Cone.mk (FactorialCompletion (L := L))
    (NatTrans.ofOpSequence (fun stage => ModuleCat.ofHom (factorialPrimeRead (L := L) p stage)) (by
      intro stage
      let lower := ModuleCat.ofHom (factorialPrimeRead (L := L) p stage)
      let upper := ModuleCat.ofHom (factorialPrimeRead (L := L) p (stage+1))
      let address := primePowerAddress p (stage+1)
      let upperDvd := prime_power_address_dvd p (stage+1)
      let lowerDvd := (pow_dvd_pow p.val (Nat.le_succ (stage+1))).trans upperDvd
      have paid : lower = upper ≫ ModuleCat.ofHom (transition (L := L) p stage) :=
        ModuleCat.hom_ext (LinearMap.ext fun value =>
          (factorial_prime_read_at p stage address lowerDvd value).trans
            (factorial_stage_to_prime_transition p stage address lowerDvd upperDvd
              ((factorialRestriction (L := L) address).hom value)).symm)
      have edge : (tower (L := L) p).map (homOfLE (Nat.le_add_right stage 1)).op =
          ModuleCat.ofHom (transition (L := L) p stage) := Functor.ofOpSequence_map_homOfLE_succ _ stage
      change 𝟙 (FactorialCompletion (L := L)) ≫ lower = upper ≫ (tower (L := L) p).map _
      exact (Category.id_comp lower).trans (paid.trans (congrArg (fun written => upper ≫ written) edge.symm))))

private def factorialToPrime (p : Nat.Primes) : FactorialCompletion (L := L) →ₗ[ℤ] Completion (L := L) p :=
  (limit.lift _ (factorialCofinalCone (L := L) p)).hom

/-- Every original prime tower is read from the same factorial limit. -/
def factorialToPrimes : FactorialCompletion (L := L) →ₗ[ℤ] AllPrimeCompletion L where
  toFun := fun value p => factorialToPrime p value
  map_add' left right := funext fun p => map_add (factorialToPrime p) left right
  map_smul' scalar value := funext fun p => map_zsmul (factorialToPrime p) scalar value

theorem factorial_to_primes_restriction (p : Nat.Primes) (stage address : Nat)
    (written : p.val^(stage+1) ∣ factorialModulus address) (value : FactorialCompletion (L := L)) :
    (restriction (L := L) p stage).hom (factorialToPrimes value p) =
      factorialStageToPrime p stage address written ((factorialRestriction (L := L) address).hom value) :=
  (ConcreteCategory.congr_hom (limit.lift_π (factorialCofinalCone (L := L) p) (Opposite.op stage)) value).trans
    (factorial_prime_read_at p stage address written value)

end CofinalAllPrimeTopology
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
