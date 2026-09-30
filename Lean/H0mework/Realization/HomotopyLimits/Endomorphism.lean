import H0mework.Realization.MappingCone.Functoriality
import H0mework.Realization.HomotopyLimits.Sequential

/-!
# Root-generated endomorphisms of sequential homotopy limits

An actual natural endomorphism of one inverse tower acts componentwise on the
canonical product.  Naturality makes that product action commute with
`1 - shift`, so mapping-cocone functoriality generates an endomorphism of the
framework homotopy-limit model.  No component inverse, homotopy equivalence,
strict limit, compatible state, candidate action or determinant is accepted.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ResponsibilityLifecycle
namespace LivingLawEvolution
namespace ConstructiveRoot
namespace SequentialHomotopyLimitEndomorphism

open CategoryTheory
open CategoryTheory.Limits
open CochainMappingCoconeFunctoriality
open SequentialHomotopyLimit

noncomputable section

universe w

variable {Root : Type w}
variable {dependentOccurrence : RootedAccountedUnfolding
  (Root × (ℕᵒᵖ ⥤ IntegralCochainComplex))}
variable {towerFace : RootGeneratedSequentialHomotopyLimitAt
  dependentOccurrence}
variable {dependentEndomorphismOccurrence : RootedAccountedUnfolding
  (Root × (towerFace.actualTower ⟶ towerFace.actualTower))}
variable {projects : dependentEndomorphismOccurrence.map Prod.fst =
  towerFace.root}

/-- One exact tower endomorphism on the same root as its homotopy-limit
carrier. -/
structure RootGeneratedSequentialHomotopyLimitEndomorphismAt
    (towerFace : RootGeneratedSequentialHomotopyLimitAt dependentOccurrence)
    (dependentEndomorphismOccurrence : RootedAccountedUnfolding
      (Root × (towerFace.actualTower ⟶ towerFace.actualTower)))
    (_projects : dependentEndomorphismOccurrence.map Prod.fst =
      towerFace.root) : Type w where
  private mk ::

namespace RootGeneratedSequentialHomotopyLimitEndomorphismAt

def generate : RootGeneratedSequentialHomotopyLimitEndomorphismAt
    towerFace dependentEndomorphismOccurrence projects :=
  ⟨⟩

def actualEndomorphism
    (_face : RootGeneratedSequentialHomotopyLimitEndomorphismAt
      towerFace dependentEndomorphismOccurrence projects) :
    towerFace.actualTower ⟶ towerFace.actualTower :=
  dependentEndomorphismOccurrence.root.2

def componentAt
    (face : RootGeneratedSequentialHomotopyLimitEndomorphismAt
      towerFace dependentEndomorphismOccurrence projects)
    (stage : Nat) : towerFace.towerObject stage ⟶
      towerFace.towerObject stage :=
  face.actualEndomorphism.app (Opposite.op stage)

/-- Product action generated from all actual components. -/
noncomputable def productMap
    (face : RootGeneratedSequentialHomotopyLimitEndomorphismAt
      towerFace dependentEndomorphismOccurrence projects) :
    towerFace.productComplex ⟶ towerFace.productComplex :=
  Pi.lift fun stage => towerFace.productProjection stage ≫
    face.componentAt stage

@[reassoc (attr := simp)] theorem productMap_projection
    (face : RootGeneratedSequentialHomotopyLimitEndomorphismAt
      towerFace dependentEndomorphismOccurrence projects)
    (stage : Nat) :
    face.productMap ≫ towerFace.productProjection stage =
      towerFace.productProjection stage ≫ face.componentAt stage :=
  Pi.lift_π _ stage

/-- Tower naturality generates the exact square with `1 - shift`. -/
theorem differenceSquare
    (face : RootGeneratedSequentialHomotopyLimitEndomorphismAt
      towerFace dependentEndomorphismOccurrence projects) :
    face.productMap ≫ towerFace.difference =
      towerFace.difference ≫ face.productMap := by
  unfold RootGeneratedSequentialHomotopyLimitAt.difference
    RootGeneratedSequentialHomotopyLimitAt.shift
    RootGeneratedSequentialHomotopyLimitAt.shiftComponent
    RootGeneratedSequentialHomotopyLimitAt.productProjection
    RootGeneratedSequentialHomotopyLimitEndomorphismAt.productMap
  apply Pi.hom_ext
  intro stage
  simp only [Preadditive.comp_sub, Preadditive.sub_comp,
    Category.comp_id, Category.id_comp, Category.assoc, Pi.lift_π]
  rw [← Category.assoc, Pi.lift_π]
  unfold RootGeneratedSequentialHomotopyLimitAt.productProjection
  have shiftProjection :
      (Pi.lift fun current =>
          Pi.π (fun index : Nat => towerFace.towerObject index)
              (current + 1) ≫ towerFace.transitionAt current) ≫
        Pi.π (fun index : Nat => towerFace.towerObject index) stage =
      Pi.π (fun index : Nat => towerFace.towerObject index) (stage + 1) ≫
        towerFace.transitionAt stage :=
    Pi.lift_π _ stage
  rw [sub_right_inj]
  rw [← Category.assoc, shiftProjection]
  unfold RootGeneratedSequentialHomotopyLimitAt.transitionAt componentAt
  rw [Category.assoc]
  rw [← face.actualEndomorphism.naturality
    (homOfLE (Nat.le_add_right stage 1)).op]
  rfl

/-- Endomorphism generated on the framework homotopy-limit carrier. -/
noncomputable def homotopyLimitAction
    (face : RootGeneratedSequentialHomotopyLimitEndomorphismAt
      towerFace dependentEndomorphismOccurrence projects) :
    towerFace.homotopyLimit ⟶ towerFace.homotopyLimit :=
  mappingCoconeMap towerFace.difference towerFace.difference
    face.productMap face.productMap face.differenceSquare

@[reassoc (attr := simp)] theorem homotopyLimitAction_fst
    (face : RootGeneratedSequentialHomotopyLimitEndomorphismAt
      towerFace dependentEndomorphismOccurrence projects) :
    face.homotopyLimitAction ≫
        CochainComplex.mappingCocone.fst towerFace.difference =
      CochainComplex.mappingCocone.fst towerFace.difference ≫
        face.productMap :=
  mappingCoconeMap_fst _ _ _ _ _

/-- Every finite stage is a restriction of the generated cofinal action. -/
@[reassoc (attr := simp)] theorem homotopyLimitAction_restriction
    (face : RootGeneratedSequentialHomotopyLimitEndomorphismAt
      towerFace dependentEndomorphismOccurrence projects)
    (stage : Nat) :
    face.homotopyLimitAction ≫ towerFace.restriction stage =
      towerFace.restriction stage ≫ face.componentAt stage := by
  unfold RootGeneratedSequentialHomotopyLimitAt.restriction
  calc
    face.homotopyLimitAction ≫
        (CochainComplex.mappingCocone.fst towerFace.difference ≫
          towerFace.productProjection stage) =
      (face.homotopyLimitAction ≫
        CochainComplex.mappingCocone.fst towerFace.difference) ≫
          towerFace.productProjection stage :=
        (Category.assoc _ _ _).symm
    _ = (CochainComplex.mappingCocone.fst towerFace.difference ≫
          face.productMap) ≫ towerFace.productProjection stage := by
      rw [face.homotopyLimitAction_fst]
    _ = CochainComplex.mappingCocone.fst towerFace.difference ≫
        (face.productMap ≫ towerFace.productProjection stage) :=
      Category.assoc _ _ _
    _ = (CochainComplex.mappingCocone.fst towerFace.difference ≫
          towerFace.productProjection stage) ≫ face.componentAt stage := by
      rw [face.productMap_projection]
      exact (Category.assoc _ _ _).symm

theorem preserves_same_root_and_actual_tower_action
    (face : RootGeneratedSequentialHomotopyLimitEndomorphismAt
      towerFace dependentEndomorphismOccurrence projects) :
    dependentEndomorphismOccurrence.map Prod.fst = towerFace.root ∧
      face.actualEndomorphism = dependentEndomorphismOccurrence.root.2 ∧
      (∀ stage, face.componentAt stage =
        dependentEndomorphismOccurrence.root.2.app (Opposite.op stage)) :=
  ⟨projects, rfl, fun _ => rfl⟩

end RootGeneratedSequentialHomotopyLimitEndomorphismAt

end

end SequentialHomotopyLimitEndomorphism
end ConstructiveRoot
end LivingLawEvolution
end ResponsibilityLifecycle
end SaturationMonoid
