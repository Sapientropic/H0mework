import SaturationMonoid.GenericFoundation.Cofinal.Topology.CokernelTorsion.CoherentFibre
import Mathlib.CategoryTheory.Limits.Types.Images

set_option autoImplicit false
set_option Elab.async false

noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceGeneratedPrimePowerCompletion

open CategoryTheory CategoryTheory.Limits

variable {L M : Type u} [AddCommGroup L] [AddCommGroup M]

private theorem completion_stage_compatible (p : Nat.Primes) (j : Nat) (value : Completion (L := L) p) :
    transition p j ((restriction p (j+1)).hom value) = (restriction p j).hom value := by
  let arrow := (homOfLE (Nat.le_add_right j 1)).op
  have arrowEq : (tower (L := L) p).map arrow = ModuleCat.ofHom (transition (L := L) p j) := by
    exact Functor.ofOpSequence_map_homOfLE_succ _ j
  have commutes := limit.w (tower (L := L) p) arrow
  rw [arrowEq] at commutes
  exact ConcreteCategory.congr_hom commutes value

private abbrev StageFibre (evaluate : L →ₗ[ℤ] M) (injective : Function.Injective evaluate)
    (p : Nat.Primes) (value : Completion (L := L) p) (j : Nat) :=
  {torsion : CokernelTorsion evaluate p j //
    stageCokernelConnecting evaluate injective p j torsion = (restriction p j).hom value}

private def fibreRestriction (evaluate : L →ₗ[ℤ] M) (injective : Function.Injective evaluate)
    (p : Nat.Primes) (value : Completion (L := L) p) (j : Nat) :
    StageFibre evaluate injective p value (j+1) → StageFibre evaluate injective p value j :=
  fun upper => ⟨primePowerTorsionRestriction p j upper.val,
    (cokernel_connecting_restriction evaluate injective p j upper.val).trans
      ((congrArg (transition p j) upper.property).trans (completion_stage_compatible p j value))⟩

private def fibreTower (evaluate : L →ₗ[ℤ] M) (injective : Function.Injective evaluate)
    (p : Nat.Primes) (value : Completion (L := L) p) : ℕᵒᵖ ⥤ Type u :=
  Functor.ofOpSequence (X := fun j => StageFibre evaluate injective p value j)
    (fun j => ↾(fibreRestriction evaluate injective p value j))

private theorem fibre_restriction_surjective (evaluate : L →ₗ[ℤ] M)
    (injective : Function.Injective evaluate) (p : Nat.Primes)
    (ambient : Function.Surjective (fun value : M => (p.1 : ℤ) • value))
    (value : Completion (L := L) p) (j : Nat) :
    Function.Surjective (fibreRestriction evaluate injective p value j) := by
  intro lower
  obtain ⟨lifted, drops, reads⟩ := cokernel_connecting_lift_step evaluate injective p ambient j lower.val
    ((restriction p (j+1)).hom value)
    (lower.property.trans (completion_stage_compatible p j value).symm)
  exact ⟨⟨lifted, reads⟩, Subtype.ext drops⟩

private theorem fibre_sections (evaluate : L →ₗ[ℤ] M)
    (injective : Function.Injective evaluate) (p : Nat.Primes)
    (ambient : Function.Surjective (fun value : M => (p.1 : ℤ) • value))
    (value : Completion (L := L) p) :
    Nonempty (fibreTower evaluate injective p value).sections := by
  let fibres := fibreTower evaluate injective p value
  have lifts (j : Nat) : Function.Surjective (fibres.map (homOfLE (Nat.le_succ j)).op) := by
    change Function.Surjective ((fibreTower evaluate injective p value).map (homOfLE (Nat.le_succ j)).op)
    rw [fibreTower, Functor.ofOpSequence_map_homOfLE_succ]
    exact fibre_restriction_surjective evaluate injective p ambient value j
  obtain ⟨initial, reads⟩ := cokernel_connecting_stage_surjective evaluate injective p ambient 0
    ((restriction p 0).hom value)
  have onto := Types.surjective_π_app_zero_of_surjective_map (Types.limitConeIsLimit fibres) lifts
  obtain ⟨liftedSection, _⟩ := onto (⟨initial, reads⟩ : StageFibre evaluate injective p value 0)
  exact ⟨liftedSection⟩

private def fibreCone (evaluate : L →ₗ[ℤ] M) (injective : Function.Injective evaluate)
    (p : Nat.Primes) (value : Completion (L := L) p)
    (liftedSection : (fibreTower evaluate injective p value).sections) :
    Cone (primePowerTorsionTower (M ⧸ LinearMap.range evaluate) p) :=
  Cone.mk (ModuleCat.of ℤ ℤ)
    (NatTrans.ofOpSequence
      (fun j => ModuleCat.ofHom (LinearMap.toSpanSingleton ℤ _ (liftedSection.val (Opposite.op j)).val))
      (fun j => by
        have square := liftedSection.property (homOfLE (Nat.le_add_right j 1)).op
        rw [fibreTower, Functor.ofOpSequence_map_homOfLE_succ] at square
        have drops := congrArg Subtype.val square
        simp only [Functor.const_obj_map, Category.id_comp, primePowerTorsionTower,
          Functor.ofOpSequence_map_homOfLE_succ]
        apply ModuleCat.hom_ext
        apply LinearMap.ext
        intro coefficient
        change coefficient • (liftedSection.val (Opposite.op j)).val =
          primePowerTorsionRestriction p j (coefficient • (liftedSection.val (Opposite.op (j+1))).val)
        rw [map_smul, drops]))

/-- Every coherent source stage lifts along the original torsion tower when the ambient prime divides. -/
theorem cokernel_connecting_limit_surjective (evaluate : L →ₗ[ℤ] M)
    (injective : Function.Injective evaluate) (p : Nat.Primes)
    (ambient : Function.Surjective (fun value : M => (p.1 : ℤ) • value)) :
    Function.Surjective (cokernelConnectingAtLimit evaluate injective p) := by
  intro value
  obtain ⟨liftedSection⟩ := fibre_sections evaluate injective p ambient value
  let cone := fibreCone evaluate injective p value liftedSection
  let lifted := (limit.lift (primePowerTorsionTower (M ⧸ LinearMap.range evaluate) p) cone).hom (1 : ℤ)
  refine ⟨lifted, ?_⟩
  apply Concrete.limit_ext (tower (L := L) p)
  rintro ⟨j⟩
  have evaluated := ConcreteCategory.congr_hom
    (limit.lift_π cone (Opposite.op j)) (1 : ℤ)
  change (torsionCompletionRestriction (M ⧸ LinearMap.range evaluate) p j).hom lifted =
    LinearMap.toSpanSingleton ℤ _ (liftedSection.val (Opposite.op j)).val 1 at evaluated
  have same := evaluated.trans (LinearMap.toSpanSingleton_apply_one ℤ _ _)
  calc
    _ = stageCokernelConnecting evaluate injective p j
        ((torsionCompletionRestriction (M ⧸ LinearMap.range evaluate) p j).hom lifted) :=
      cokernel_connecting_limit_restriction evaluate injective p j lifted
    _ = stageCokernelConnecting evaluate injective p j (liftedSection.val (Opposite.op j)).val :=
      congrArg (stageCokernelConnecting evaluate injective p j) same
    _ = _ := (liftedSection.val (Opposite.op j)).property

end SourceGeneratedPrimePowerCompletion
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
