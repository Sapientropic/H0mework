import H0mework.Versions.Y.Arithmetic.EulerLog.ExponentOperator
import H0mework.Realization.HomotopyLimits.Endomorphism

/-!
# Runtime-generated cofinal Euler/reversal action

The genuine prime/exponent Euler convolution coupled to reversal commutes
with its own `id - action` relation boundary and with the simultaneous
prime/exponent restriction.  It therefore acts on every full two-term stage,
forms a natural endomorphism of the runtime diagonal tower, and is lifted by
the frozen homotopy-limit endomorphism kernel.

The natural transformation is calculated from `root.2.limit` at the exact
runtime cofinal occurrence; no constant action is attached afterward.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ResponsibilityLifecycle
namespace LivingLawEvolution
namespace ConstructiveRoot
namespace CanonicalUnitArithmeticPrimeExponentEulerCofinalAction

open CanonicalUnitArithmeticCofinalEulerLimit
open CanonicalUnitArithmeticPrimeExponentEulerOperator
open CanonicalUnitArithmeticRuntimeCofinalEuler
open CategoryTheory
open CochainMappingCoconeFunctoriality
open SequentialHomotopyLimit
open SequentialHomotopyLimitEndomorphism
open SequentialHomotopyLimitEndomorphism.RootGeneratedSequentialHomotopyLimitEndomorphismAt

noncomputable section

noncomputable def stageEulerActionMap
    (generated : GeneratedCofinalEulerLimit) (stage : Nat) :
    stageLatticeComplex stage stage ⟶ stageLatticeComplex stage stage :=
  (CochainComplex.singleFunctor (ModuleCat ℤ) 0).map
    (ModuleCat.ofHom (eulerReversalAction generated stage stage))

theorem stageEulerAction_boundary_commutes
    (generated : GeneratedCofinalEulerLimit) (stage : Nat) :
    (stageBoundary generated stage stage).comp
        (eulerReversalAction generated stage stage) =
      (eulerReversalAction generated stage stage).comp
        (stageBoundary generated stage stage) := by
  unfold stageBoundary
  rw [LinearMap.sub_comp, LinearMap.comp_sub,
    LinearMap.id_comp, LinearMap.comp_id]

theorem stageEulerAction_complex_boundary_square
    (generated : GeneratedCofinalEulerLimit) (stage : Nat) :
    stageEulerActionMap generated stage ≫
        stageBoundaryMap generated stage stage =
      stageBoundaryMap generated stage stage ≫
        stageEulerActionMap generated stage := by
  unfold stageEulerActionMap stageBoundaryMap
  rw [← Functor.map_comp, ← Functor.map_comp]
  apply congrArg
  apply ModuleCat.hom_ext
  exact stageEulerAction_boundary_commutes generated stage

noncomputable def stageComplexEulerAction
    (generated : GeneratedCofinalEulerLimit) (stage : Nat) :
    stageComplex generated stage stage ⟶
      stageComplex generated stage stage :=
  mappingCoconeMap
    (stageBoundaryMap generated stage stage)
    (stageBoundaryMap generated stage stage)
    (stageEulerActionMap generated stage)
    (stageEulerActionMap generated stage)
    (stageEulerAction_complex_boundary_square generated stage)

theorem stageEulerActionMap_transition
    (generated : GeneratedCofinalEulerLimit) (stage : Nat) :
    stageEulerActionMap generated (stage + 1) ≫
        diagonalLatticeRestrictionMap stage =
      diagonalLatticeRestrictionMap stage ≫
        stageEulerActionMap generated stage := by
  unfold stageEulerActionMap diagonalLatticeRestrictionMap
  rw [← Functor.map_comp, ← Functor.map_comp]
  apply congrArg
  apply ModuleCat.hom_ext
  exact diagonalRestriction_action_square generated stage

theorem stageComplexEulerAction_transition
    (generated : GeneratedCofinalEulerLimit) (stage : Nat) :
    stageComplexEulerAction generated (stage + 1) ≫
        diagonalStageTransition generated stage =
      diagonalStageTransition generated stage ≫
        stageComplexEulerAction generated stage := by
  unfold stageComplexEulerAction diagonalStageTransition
  rw [← mappingCoconeMap_comp, ← mappingCoconeMap_comp]
  apply mappingCoconeMap_congr
  · exact stageEulerActionMap_transition generated stage
  · exact stageEulerActionMap_transition generated stage

noncomputable def diagonalEulerActionNatTrans
    (generated : GeneratedCofinalEulerLimit) :
    diagonalRelationTowerAt generated ⟶
      diagonalRelationTowerAt generated :=
  NatTrans.ofOpSequence
    (stageComplexEulerAction generated)
    (fun stage => by
      simp only [diagonalRelationTowerAt,
        Functor.ofOpSequence_map_homOfLE_succ]
      exact (stageComplexEulerAction_transition generated stage).symm)

noncomputable def actualEulerActionNatTrans :
    diagonalHomotopyLimitFace.actualTower ⟶
      diagonalHomotopyLimitFace.actualTower := by
  change diagonalRelationTowerAt
      runtimeCofinalLimitOccurrence.root.2 ⟶
    diagonalRelationTowerAt runtimeCofinalLimitOccurrence.root.2
  exact diagonalEulerActionNatTrans
    runtimeCofinalLimitOccurrence.root.2

def dependentEulerActionOccurrence : RootedAccountedUnfolding
    (EulerTowerRoot ×
      (diagonalHomotopyLimitFace.actualTower ⟶
        diagonalHomotopyLimitFace.actualTower)) :=
  diagonalDependentOccurrence.map fun payload =>
    (payload.1, actualEulerActionNatTrans)

theorem dependentEulerActionOccurrence_projects :
    dependentEulerActionOccurrence.map Prod.fst =
      diagonalHomotopyLimitFace.root := by
  rw [dependentEulerActionOccurrence, RootedAccountedUnfolding.map_map,
    RootGeneratedSequentialHomotopyLimitAt.root]
  change diagonalDependentOccurrence.map Prod.fst =
    diagonalDependentOccurrence.map Prod.fst
  rfl

def eulerActionFace :
    RootGeneratedSequentialHomotopyLimitEndomorphismAt
      diagonalHomotopyLimitFace dependentEulerActionOccurrence
        dependentEulerActionOccurrence_projects :=
  RootGeneratedSequentialHomotopyLimitEndomorphismAt.generate

abbrev EulerRelationLimit : IntegralCochainComplex :=
  diagonalHomotopyLimitFace.homotopyLimit

noncomputable def globalEulerReversalAction :
    EulerRelationLimit ⟶ EulerRelationLimit :=
  eulerActionFace.homotopyLimitAction

theorem globalEulerReversalAction_restriction (stage : Nat) :
    globalEulerReversalAction ≫
        diagonalHomotopyLimitFace.restriction stage =
      diagonalHomotopyLimitFace.restriction stage ≫
        eulerActionFace.componentAt stage := by
  exact eulerActionFace.homotopyLimitAction_restriction stage

theorem globalEulerAction_preserves_runtime_root :
    dependentEulerActionOccurrence.map Prod.fst =
      runtimeCofinalLimitOccurrence := by
  rw [dependentEulerActionOccurrence_projects,
    diagonalHomotopyLimitFace_projects_to_runtimeOccurrence]

end
end CanonicalUnitArithmeticPrimeExponentEulerCofinalAction
end ConstructiveRoot
end LivingLawEvolution
end ResponsibilityLifecycle
end SaturationMonoid
