import H0mework.Versions.R2.Arithmetic.PrimeShadow.LivingLawCanonicalUnitArithmeticCofinalRelationHomotopyLimit
import H0mework.Realization.HomotopyLimits.Endomorphism

/-!
# Cofinal reversal action on the arithmetic relation limit

The stage reversal commutes with the actual `id - ι` boundary and with every
source-generated restriction.  Mapping-cocone functoriality therefore makes
it an endomorphism of each full two-term relation complex, then a natural
endomorphism of the inverse tower.  The frozen sequential-homotopy action
kernel finally installs it on the same rooted homotopy-limit occurrence.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ResponsibilityLifecycle
namespace LivingLawEvolution
namespace ConstructiveRoot
namespace CanonicalUnitArithmeticCofinalRelationAction

open CanonicalUnitArithmeticCofinalEulerLimit
open CanonicalUnitArithmeticCofinalRelationHomotopyLimit
open CanonicalUnitArithmeticCofinalReversalRelation
open CategoryTheory
open CategoryTheory.Limits
open CochainMappingCoconeFunctoriality
open SequentialHomotopyLimit
open SequentialHomotopyLimitEndomorphism
open SequentialHomotopyLimitEndomorphism.RootGeneratedSequentialHomotopyLimitEndomorphismAt

noncomputable section

noncomputable def stageReversalMap (stage : Nat) :
    stageLatticeComplex stage ⟶ stageLatticeComplex stage :=
  (CochainComplex.singleFunctor (ModuleCat ℤ) 0).map
    (ModuleCat.ofHom (stageReversal stage))

theorem stageReversal_boundary_commutes (stage : Nat) :
    (stageBoundary stage).comp (stageReversal stage) =
      (stageReversal stage).comp (stageBoundary stage) := by
  unfold stageBoundary
  rw [weightedStageReversal_eq_reversal]
  ext value index
  simp [stageReversal]

theorem stageReversal_complex_boundary_square (stage : Nat) :
    stageReversalMap stage ≫ stageBoundaryMap stage =
      stageBoundaryMap stage ≫ stageReversalMap stage := by
  unfold stageReversalMap stageBoundaryMap
  rw [← Functor.map_comp, ← Functor.map_comp]
  apply congrArg
  apply ModuleCat.hom_ext
  exact stageReversal_boundary_commutes stage

theorem stageReversal_comp_self (stage : Nat) :
    (stageReversal stage).comp (stageReversal stage) = LinearMap.id := by
  ext value index
  simp [stageReversal]

theorem stageReversalMap_comp_self (stage : Nat) :
    stageReversalMap stage ≫ stageReversalMap stage =
      𝟙 (stageLatticeComplex stage) := by
  let F := CochainComplex.singleFunctor (ModuleCat ℤ) 0
  have moduleEq :
      ModuleCat.ofHom (stageReversal stage) ≫
          ModuleCat.ofHom (stageReversal stage) =
        𝟙 (StageLatticeModule stage) := by
    apply ModuleCat.hom_ext
    exact stageReversal_comp_self stage
  calc
    stageReversalMap stage ≫ stageReversalMap stage =
        F.map (ModuleCat.ofHom (stageReversal stage) ≫
          ModuleCat.ofHom (stageReversal stage)) := by
      exact (F.map_comp _ _).symm
    _ = F.map (𝟙 (StageLatticeModule stage)) :=
      congrArg F.map moduleEq
    _ = 𝟙 (stageLatticeComplex stage) := F.map_id _

/-- Reversal on the full two-term relation complex, before cokernel. -/
noncomputable def stageRelationReversal (stage : Nat) :
    stageComplex stage ⟶ stageComplex stage :=
  mappingCoconeMap
    (stageBoundaryMap stage) (stageBoundaryMap stage)
    (stageReversalMap stage) (stageReversalMap stage)
    (stageReversal_complex_boundary_square stage)

theorem stageRelationReversal_comp_self (stage : Nat) :
    stageRelationReversal stage ≫ stageRelationReversal stage =
      𝟙 (stageComplex stage) := by
  unfold stageRelationReversal
  rw [← mappingCoconeMap_comp]
  calc
    _ = mappingCoconeMap
        (stageBoundaryMap stage) (stageBoundaryMap stage)
        (𝟙 _) (𝟙 _) (by simp) := by
      apply mappingCoconeMap_congr
      · exact stageReversalMap_comp_self stage
      · exact stageReversalMap_comp_self stage
    _ = 𝟙 _ := mappingCoconeMap_id _

theorem stageReversalMap_transition (stage : Nat) :
    stageReversalMap (stage + 1) ≫ stageLatticeRestriction stage =
      stageLatticeRestriction stage ≫ stageReversalMap stage := by
  unfold stageReversalMap stageLatticeRestriction
  rw [← Functor.map_comp, ← Functor.map_comp]
  apply congrArg
  apply ModuleCat.hom_ext
  exact relationRestriction_reversal_square stage

theorem stageRelationReversal_transition (stage : Nat) :
    stageRelationReversal (stage + 1) ≫ stageTransition stage =
      stageTransition stage ≫ stageRelationReversal stage := by
  unfold stageRelationReversal stageTransition
  rw [← mappingCoconeMap_comp, ← mappingCoconeMap_comp]
  apply mappingCoconeMap_congr
  · exact stageReversalMap_transition stage
  · exact stageReversalMap_transition stage

/-- One actual reversal natural transformation of the generated inverse
relation tower. -/
noncomputable def relationReversalNatTrans :
    relationTower ⟶ relationTower :=
  NatTrans.ofOpSequence
    stageRelationReversal
    (fun stage => by
      rw [show relationTower.map
          (homOfLE (Nat.le_add_right stage 1)).op = stageTransition stage from
        Functor.ofOpSequence_map_homOfLE_succ stageTransition stage]
      exact (stageRelationReversal_transition stage).symm)

def dependentReversalOccurrence : RootedAccountedUnfolding
    (TowerRoot ×
      (homotopyLimitFace.actualTower ⟶ homotopyLimitFace.actualTower)) :=
  cofinalLimitOccurrence.map fun root => (root, relationReversalNatTrans)

theorem dependentReversalOccurrence_projects :
    dependentReversalOccurrence.map Prod.fst = homotopyLimitFace.root := by
  rw [dependentReversalOccurrence, RootedAccountedUnfolding.map_map,
    homotopyLimitFace_projects_to_cofinalEulerRoot]
  change cofinalLimitOccurrence.map id = cofinalLimitOccurrence
  exact RootedAccountedUnfolding.map_id _

/-- Frozen installation of the actual reversal on the derived relation
limit. -/
def reversalActionFace :
    RootGeneratedSequentialHomotopyLimitEndomorphismAt
      homotopyLimitFace dependentReversalOccurrence
        dependentReversalOccurrence_projects :=
  RootGeneratedSequentialHomotopyLimitEndomorphismAt.generate

@[simp] theorem reversalAction_componentAt (stage : Nat) :
    reversalActionFace.componentAt stage = stageRelationReversal stage :=
  rfl

theorem reversalAction_componentAt_comp_self (stage : Nat) :
    reversalActionFace.componentAt stage ≫
        reversalActionFace.componentAt stage =
      𝟙 (homotopyLimitFace.towerObject stage) := by
  change stageRelationReversal stage ≫ stageRelationReversal stage =
    𝟙 (stageComplex stage)
  exact stageRelationReversal_comp_self stage

theorem reversalAction_productMap_comp_self :
    reversalActionFace.productMap ≫ reversalActionFace.productMap =
      𝟙 homotopyLimitFace.productComplex := by
  apply Pi.hom_ext
  intro stage
  change
    (reversalActionFace.productMap ≫ reversalActionFace.productMap) ≫
        homotopyLimitFace.productProjection stage =
      (𝟙 homotopyLimitFace.productComplex) ≫
        homotopyLimitFace.productProjection stage
  rw [Category.assoc, reversalActionFace.productMap_projection]
  rw [← Category.assoc, reversalActionFace.productMap_projection]
  rw [Category.assoc, reversalAction_componentAt_comp_self,
    Category.comp_id]
  simp

noncomputable def derivedRelationReversal :
    derivedRelationLimit ⟶ derivedRelationLimit :=
  reversalActionFace.homotopyLimitAction

theorem derivedRelationReversal_comp_self :
    derivedRelationReversal ≫ derivedRelationReversal =
      𝟙 derivedRelationLimit := by
  unfold derivedRelationReversal
  unfold RootGeneratedSequentialHomotopyLimitEndomorphismAt.homotopyLimitAction
  rw [← mappingCoconeMap_comp]
  calc
    _ = mappingCoconeMap
        homotopyLimitFace.difference homotopyLimitFace.difference
        (𝟙 _) (𝟙 _) (by simp) := by
      apply mappingCoconeMap_congr
      · exact reversalAction_productMap_comp_self
      · exact reversalAction_productMap_comp_self
    _ = 𝟙 _ := mappingCoconeMap_id _

theorem derivedRelationReversal_restricts_to_stage (stage : Nat) :
    derivedRelationReversal ≫ homotopyLimitFace.restriction stage =
      homotopyLimitFace.restriction stage ≫
        stageRelationReversal stage := by
  exact reversalActionFace.homotopyLimitAction_restriction stage

theorem reversalAction_preserves_common_root :
    dependentReversalOccurrence.map Prod.fst = homotopyLimitFace.root ∧
      reversalActionFace.actualEndomorphism =
        dependentReversalOccurrence.root.2 :=
  ⟨dependentReversalOccurrence_projects, rfl⟩

end
end CanonicalUnitArithmeticCofinalRelationAction
end ConstructiveRoot
end LivingLawEvolution
end ResponsibilityLifecycle
end SaturationMonoid
