import H0mework.Versions.R1f4eaffd.ReleaseMaterials.SaturationMonoid.GenericFoundation.Cofinal.Topology.CokernelTorsion.ConnectingExact

set_option autoImplicit false
set_option Elab.async false

noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceGeneratedPrimePowerCompletion

open CategoryTheory CategoryTheory.Limits

variable {L M : Type u} [AddCommGroup L] [AddCommGroup M]

def primePowerTorsionRestriction (p : Nat.Primes) (j : Nat) :
    PrimePowerTorsionSubmodule M p (j+1) →ₗ[ℤ] PrimePowerTorsionSubmodule M p j :=
  LinearMap.codRestrict _ ((p.1 : ℤ) • (PrimePowerTorsionSubmodule M p (j+1)).subtype) (by
    intro value
    change (p.1 : ℤ)^(j+1) • ((p.1 : ℤ) • value.val) = 0
    rw [smul_smul, ← pow_succ]
    exact value.property)

theorem prime_power_torsion_map_restriction (move : L →ₗ[ℤ] M) (p : Nat.Primes) (j : Nat)
    (value : PrimePowerTorsionSubmodule L p (j+1)) :
    primePowerTorsionRestriction p j (primePowerTorsionMap move p (j+1) value) =
      primePowerTorsionMap move p j (primePowerTorsionRestriction p j value) :=
  Subtype.ext (map_smul move (p.1 : ℤ) value.val).symm

theorem cokernel_connecting_restriction (evaluate : L →ₗ[ℤ] M)
    (injective : Function.Injective evaluate) (p : Nat.Primes) (j : Nat)
    (value : CokernelTorsion evaluate p (j+1)) :
    stageCokernelConnecting evaluate injective p j (primePowerTorsionRestriction p j value) =
      transition p j (stageCokernelConnecting evaluate injective p (j+1) value) := by
  obtain ⟨word, divided, paid, rfl⟩ := cokernel_torsion_has_division evaluate p (j+1) value
  let high := cokernelTorsionClassOfDivision evaluate p (j+1) word divided paid
  have lower : powerMultiplication p j ((p.1 : ℤ) • divided) = evaluate word := by
    change (p.1 : ℤ)^(j+1) • ((p.1 : ℤ) • divided) = evaluate word
    rw [smul_smul, ← pow_succ]
    exact paid
  let low := cokernelTorsionClassOfDivision evaluate p j word ((p.1 : ℤ) • divided) lower
  have same : primePowerTorsionRestriction p j high = low := by
    apply Subtype.ext
    change (p.1 : ℤ) • (LinearMap.range evaluate).mkQ divided =
      (LinearMap.range evaluate).mkQ ((p.1 : ℤ) • divided)
    exact (map_smul (LinearMap.range evaluate).mkQ _ _).symm
  calc
    _ = stageCokernelConnecting evaluate injective p j low :=
      congrArg (stageCokernelConnecting evaluate injective p j) same
    _ = stageProjection p j word :=
      stage_cokernel_connecting_of_paid evaluate injective p j word _ lower
    _ = transition p j (stageProjection p (j+1) word) :=
      (LinearMap.congr_fun (transition_projection (L := L) p j) word).symm
    _ = _ := congrArg (transition p j)
      (stage_cokernel_connecting_of_paid evaluate injective p (j+1) word divided paid).symm

/-- The torsion tower uses the actual prime multiplication at each successor. -/
def primePowerTorsionTower (A : Type u) [AddCommGroup A] (p : Nat.Primes) :
    ℕᵒᵖ ⥤ ModuleCat.{u} ℤ :=
  Functor.ofOpSequence (X := fun j => ModuleCat.of ℤ (PrimePowerTorsionSubmodule A p j))
    (fun j => ModuleCat.ofHom (primePowerTorsionRestriction p j))

abbrev PrimePowerTorsionCompletion (A : Type u) [AddCommGroup A] (p : Nat.Primes) :=
  limit (primePowerTorsionTower A p)

def torsionCompletionRestriction (A : Type u) [AddCommGroup A] (p : Nat.Primes) (j : Nat) :
    PrimePowerTorsionCompletion A p ⟶ ModuleCat.of ℤ (PrimePowerTorsionSubmodule A p j) :=
  limit.π (primePowerTorsionTower A p) (Opposite.op j)

def cokernelConnectingTowerMap (evaluate : L →ₗ[ℤ] M)
    (injective : Function.Injective evaluate) (p : Nat.Primes) :
    primePowerTorsionTower (M ⧸ LinearMap.range evaluate) p ⟶ tower (L := L) p :=
  NatTrans.ofOpSequence (fun j => ModuleCat.ofHom (stageCokernelConnecting evaluate injective p j))
    (fun j => by
      simp only [primePowerTorsionTower, tower, Functor.ofOpSequence_map_homOfLE_succ]
      apply ModuleCat.hom_ext
      exact LinearMap.ext (cokernel_connecting_restriction evaluate injective p j))

def cokernelConnectingAtLimit (evaluate : L →ₗ[ℤ] M)
    (injective : Function.Injective evaluate) (p : Nat.Primes) :
    PrimePowerTorsionCompletion (M ⧸ LinearMap.range evaluate) p →ₗ[ℤ] Completion (L := L) p :=
  (limMap (cokernelConnectingTowerMap evaluate injective p)).hom

theorem cokernel_connecting_limit_restriction (evaluate : L →ₗ[ℤ] M)
    (injective : Function.Injective evaluate) (p : Nat.Primes) (j : Nat)
    (value : PrimePowerTorsionCompletion (M ⧸ LinearMap.range evaluate) p) :
    (restriction (L := L) p j).hom (cokernelConnectingAtLimit evaluate injective p value) =
      stageCokernelConnecting evaluate injective p j
        ((torsionCompletionRestriction (M ⧸ LinearMap.range evaluate) p j).hom value) :=
  ConcreteCategory.congr_hom (limMap_π (cokernelConnectingTowerMap evaluate injective p) (Opposite.op j)) value

end SourceGeneratedPrimePowerCompletion
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
