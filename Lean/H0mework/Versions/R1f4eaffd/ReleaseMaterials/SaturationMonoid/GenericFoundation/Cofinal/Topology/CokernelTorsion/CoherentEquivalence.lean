import H0mework.Versions.R1f4eaffd.ReleaseMaterials.SaturationMonoid.GenericFoundation.Cofinal.Topology.CokernelTorsion.Tower

set_option autoImplicit false
set_option Elab.async false

noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceGeneratedPrimePowerCompletion

open CategoryTheory CategoryTheory.Limits

variable {L M : Type u} [AddCommGroup L] [AddCommGroup M]
variable (evaluate : L →ₗ[ℤ] M) (injective : Function.Injective evaluate) (p : Nat.Primes)
variable (divides : ∀ j, Function.Bijective (powerMultiplication (L := M) p j))

private def sourceCokernelTowerMap :
    tower (L := L) p ⟶ primePowerTorsionTower (M ⧸ LinearMap.range evaluate) p :=
  NatTrans.ofOpSequence
    (fun j => ModuleCat.ofHom (stageCokernelEquiv evaluate injective p j (divides j)).toLinearMap)
    (fun j => by
      simp only [tower, primePowerTorsionTower, Functor.ofOpSequence_map_homOfLE_succ]
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro value
      apply Subtype.ext
      exact stage_cokernel_transition evaluate injective p j (divides j) (divides (j+1)) value)

private def sourceCokernelAtLimit :
    Completion (L := L) p →ₗ[ℤ] PrimePowerTorsionCompletion (M ⧸ LinearMap.range evaluate) p :=
  (limMap (sourceCokernelTowerMap evaluate injective p divides)).hom

private theorem source_cokernel_limit_restriction (j : Nat) (value : Completion (L := L) p) :
    (torsionCompletionRestriction (M ⧸ LinearMap.range evaluate) p j).hom
        (sourceCokernelAtLimit evaluate injective p divides value) =
      stageCokernelEquiv evaluate injective p j (divides j) ((restriction p j).hom value) :=
  ConcreteCategory.congr_hom (limMap_π (sourceCokernelTowerMap evaluate injective p divides) (Opposite.op j)) value

/-- The original stage inverses assemble on the entire coherent source, with the actual connecting inverse. -/
def cokernelCompletionEquiv :
    Completion (L := L) p ≃ₗ[ℤ] PrimePowerTorsionCompletion (M ⧸ LinearMap.range evaluate) p :=
  LinearEquiv.ofLinearMap (sourceCokernelAtLimit evaluate injective p divides)
    (cokernelConnectingAtLimit evaluate injective p)
    (by
      apply LinearMap.ext
      intro value
      apply Concrete.limit_ext (primePowerTorsionTower (M ⧸ LinearMap.range evaluate) p)
      rintro ⟨j⟩
      change (torsionCompletionRestriction (M ⧸ LinearMap.range evaluate) p j).hom
        (sourceCokernelAtLimit evaluate injective p divides (cokernelConnectingAtLimit evaluate injective p value)) = _
      rw [source_cokernel_limit_restriction, cokernel_connecting_limit_restriction]
      exact (stage_cokernel_connecting_inverse evaluate injective p j (divides j)).rightInverse_of_surjective
        (stageCokernelEquiv evaluate injective p j (divides j)).surjective
        ((torsionCompletionRestriction (M ⧸ LinearMap.range evaluate) p j).hom value))
    (by
      apply LinearMap.ext
      intro value
      apply Concrete.limit_ext (tower (L := L) p)
      rintro ⟨j⟩
      change (restriction (L := L) p j).hom
        (cokernelConnectingAtLimit evaluate injective p (sourceCokernelAtLimit evaluate injective p divides value)) = _
      rw [cokernel_connecting_limit_restriction, source_cokernel_limit_restriction]
      exact stage_cokernel_connecting_inverse evaluate injective p j (divides j) ((restriction p j).hom value))

theorem cokernel_completion_restriction (j : Nat) (value : Completion (L := L) p) :
    (torsionCompletionRestriction (M ⧸ LinearMap.range evaluate) p j).hom
        (cokernelCompletionEquiv evaluate injective p divides value) =
      stageCokernelEquiv evaluate injective p j (divides j) ((restriction p j).hom value) :=
  source_cokernel_limit_restriction evaluate injective p divides j value

theorem cokernel_completion_inverse (value : PrimePowerTorsionCompletion (M ⧸ LinearMap.range evaluate) p) :
    (cokernelCompletionEquiv evaluate injective p divides).symm value =
      cokernelConnectingAtLimit evaluate injective p value := rfl

end SourceGeneratedPrimePowerCompletion
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
