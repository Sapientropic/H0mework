import H0mework.Realization.HomotopyLimits.Sequential
import H0mework.Versions.R18f91d79.Realization.HomotopyLimits.Endomorphism
import H0mework.Versions.R7e4da746.Realization.MappingCone.Functoriality

/-! # Sequential homotopy-limit transport along actual natural transformations -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SequentialHomotopyLimitNaturality

open CategoryTheory CategoryTheory.Limits
open CochainMappingCoconeFunctoriality
open SequentialHomotopyLimit
open SequentialHomotopyLimitEndomorphism

noncomputable section

universe u v w

variable {R : Type u} {S : Type v} {T : Type w}
    {sourceOccurrence : RootedAccountedUnfolding
      (R × (ℕᵒᵖ ⥤ IntegralCochainComplex))}
    {targetOccurrence : RootedAccountedUnfolding
      (S × (ℕᵒᵖ ⥤ IntegralCochainComplex))}
    {thirdOccurrence : RootedAccountedUnfolding
      (T × (ℕᵒᵖ ⥤ IntegralCochainComplex))}
    (source : RootGeneratedSequentialHomotopyLimitAt sourceOccurrence)
    (target : RootGeneratedSequentialHomotopyLimitAt targetOccurrence)
    (third : RootGeneratedSequentialHomotopyLimitAt thirdOccurrence)

def productMap (comparison : source.actualTower ⟶ target.actualTower) :
    source.productComplex ⟶ target.productComplex :=
  Pi.lift fun stage => source.productProjection stage ≫ comparison.app (Opposite.op stage)

@[reassoc (attr := simp)] theorem productMap_projection
    (comparison : source.actualTower ⟶ target.actualTower) (stage : Nat) :
    productMap source target comparison ≫ target.productProjection stage =
      source.productProjection stage ≫ comparison.app (Opposite.op stage) :=
  Pi.lift_π _ stage

theorem differenceSquare (comparison : source.actualTower ⟶ target.actualTower) :
    productMap source target comparison ≫ target.difference =
      source.difference ≫ productMap source target comparison := by
  unfold productMap RootGeneratedSequentialHomotopyLimitAt.difference
    RootGeneratedSequentialHomotopyLimitAt.shift
    RootGeneratedSequentialHomotopyLimitAt.shiftComponent
    RootGeneratedSequentialHomotopyLimitAt.productProjection
  apply Pi.hom_ext
  intro stage
  simp only [Preadditive.comp_sub, Preadditive.sub_comp,
    Category.comp_id, Category.id_comp, Category.assoc, Pi.lift_π, Pi.lift_π_assoc]
  exact congrArg
    (fun arrow => source.productProjection stage ≫ comparison.app (Opposite.op stage) -
      source.productProjection (stage + 1) ≫ arrow)
    (comparison.naturality (homOfLE (Nat.le_add_right stage 1)).op).symm

def homotopyLimitMap (comparison : source.actualTower ⟶ target.actualTower) :
    source.homotopyLimit ⟶ target.homotopyLimit :=
  mappingCoconeMap source.difference target.difference
    (productMap source target comparison) (productMap source target comparison)
    (differenceSquare source target comparison)

@[reassoc] theorem homotopyLimitMap_restriction
    (comparison : source.actualTower ⟶ target.actualTower) (stage : Nat) :
    homotopyLimitMap source target comparison ≫ target.restriction stage =
      source.restriction stage ≫ comparison.app (Opposite.op stage) := by
  unfold homotopyLimitMap RootGeneratedSequentialHomotopyLimitAt.restriction
  rw [← Category.assoc, mappingCoconeMap_fst, Category.assoc, productMap_projection,
    ← Category.assoc]

theorem productMap_comp
    (first : source.actualTower ⟶ target.actualTower)
    (second : target.actualTower ⟶ third.actualTower) :
    productMap source third (first ≫ second) =
      productMap source target first ≫ productMap target third second := by
  unfold productMap RootGeneratedSequentialHomotopyLimitAt.productProjection
  apply Pi.hom_ext
  intro stage
  simp only [Category.assoc, Pi.lift_π, Pi.lift_π_assoc, NatTrans.comp_app]

theorem homotopyLimitMap_comp
    (first : source.actualTower ⟶ target.actualTower)
    (second : target.actualTower ⟶ third.actualTower) :
    homotopyLimitMap source third (first ≫ second) =
      homotopyLimitMap source target first ≫ homotopyLimitMap target third second := by
  unfold homotopyLimitMap
  have square :
      (productMap source target first ≫ productMap target third second) ≫ third.difference =
        source.difference ≫ (productMap source target first ≫ productMap target third second) := by
    rw [Category.assoc, differenceSquare, ← Category.assoc, differenceSquare, Category.assoc]
  exact (mappingCoconeMap_congr source.difference third.difference
      (differenceSquare source third (first ≫ second)) square
      (productMap_comp source target third first second)
      (productMap_comp source target third first second)).trans
    (mappingCoconeMap_comp _ _ _ _ _ _ _ _ _)

theorem productMap_identity :
    productMap source source (𝟙 source.actualTower) = 𝟙 source.productComplex := by
  unfold productMap RootGeneratedSequentialHomotopyLimitAt.productProjection
  apply Pi.hom_ext
  intro stage
  simp only [Pi.lift_π, NatTrans.id_app, Category.comp_id, Category.id_comp]

theorem homotopyLimitMap_identity :
    homotopyLimitMap source source (𝟙 source.actualTower) = 𝟙 source.homotopyLimit := by
  unfold homotopyLimitMap
  exact (mappingCoconeMap_congr source.difference source.difference
      (differenceSquare source source (𝟙 source.actualTower)) (by simp)
      (productMap_identity source) (productMap_identity source)).trans
    (mappingCoconeMap_id _)

theorem homotopyLimitMap_equivariant
    (sourceAction : source.actualTower ⟶ source.actualTower)
    (targetAction : target.actualTower ⟶ target.actualTower)
    (comparison : source.actualTower ⟶ target.actualTower)
    (commutes : sourceAction ≫ comparison = comparison ≫ targetAction) :
    homotopyLimitMap source source sourceAction ≫ homotopyLimitMap source target comparison =
      homotopyLimitMap source target comparison ≫ homotopyLimitMap target target targetAction :=
  (homotopyLimitMap_comp source source target sourceAction comparison).symm.trans
    ((congrArg (homotopyLimitMap source target) commutes).trans
      (homotopyLimitMap_comp source target target comparison targetAction))

theorem endomorphismAction_eq_homotopyLimitMap
    {dependentEndomorphism : RootedAccountedUnfolding
      (R × (source.actualTower ⟶ source.actualTower))}
    {projects : dependentEndomorphism.map Prod.fst = source.root}
    (endomorphism : RootGeneratedSequentialHomotopyLimitEndomorphismAt
      source dependentEndomorphism projects) :
    endomorphism.homotopyLimitAction =
      homotopyLimitMap source source endomorphism.actualEndomorphism := by
  rfl

end
end SequentialHomotopyLimitNaturality
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
