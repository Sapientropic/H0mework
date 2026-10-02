import H0mework.Versions.R2.Arithmetic.EulerGlobal.DerivedDeterminant
import H0mework.Realization.GlobalSections.DerivedState

/-!
# Global action and reversal of the integral full-Euler carrier

The same finite carrier/action occurrences used by the determinant section
form a source-generated inverse diagram under the actual support-expanding
restriction.  The frozen dependent-global-state engine generates its global
carrier.  Local prime actions and reversals are natural transformations, so
the limit universal property generates the global action, reversal, their
restriction laws, commutation, and reversal involution.

No determinant zero fibre, dual coordinate, selected element, landing, or
fixedness is supplied here.
-/

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false

namespace SaturationMonoid
namespace ResponsibilityLifecycle
namespace LivingLawEvolution
namespace ConstructiveRoot
namespace CanonicalUnitArithmeticFactorizationFullEulerGlobalAction

open CanonicalUnitArithmeticFactorizationEulerDependentDiagram
open CanonicalUnitArithmeticFactorizationFullEulerSolutionAction
open CanonicalUnitArithmeticFactorizationFullEulerDerivedDeterminantSection
open DependentDerivedGlobalState
open DependentDerivedGlobalState.RootGeneratedDependentDerivedGlobalStateAt
open CategoryTheory
open CategoryTheory.Limits
open DerivedAdicCofiber

noncomputable section

def actualRestriction (seed : FactorizationPayload) (stage : Nat) :
    ActualComplex seed (stage + 1) ⟶ ActualComplex seed stage where
  f degree := by
    by_cases degreeZero : degree = 0
    · subst degree
      exact ModuleCat.ofHom (carrierRestriction seed stage)
    · exact 0
  comm' _source _target _relation := by
    change _ ≫ (0 : _ ⟶ _) = (0 : _ ⟶ _) ≫ _
    rw [CategoryTheory.Limits.comp_zero, CategoryTheory.Limits.zero_comp]

theorem actualEulerAction_transition
    (seed : FactorizationPayload) (stage : Nat) :
    actualEulerAction seed (stage + 1) ≫ actualRestriction seed stage =
      actualRestriction seed stage ≫ actualEulerAction seed stage := by
  ext degree
  by_cases degreeZero : degree = 0
  · subst degree
    exact LinearMap.congr_fun
      (carrierRestriction_euler_square seed stage) _
  · simp [actualEulerAction, actualRestriction, degreeZero]

theorem actualReversalAction_transition
    (seed : FactorizationPayload) (stage : Nat) :
    actualReversalAction seed (stage + 1) ≫ actualRestriction seed stage =
      actualRestriction seed stage ≫ actualReversalAction seed stage := by
  ext degree
  by_cases degreeZero : degree = 0
  · subst degree
    exact LinearMap.congr_fun
      (carrierRestriction_reversal_square seed stage) _
  · simp [actualReversalAction, actualRestriction, degreeZero]

def localActionDiagram (seed : FactorizationPayload) :
    CategoryTheory.Functor ℕᵒᵖ (IntegralCochainComplex ℤ) :=
  Functor.ofOpSequence
    (X := fun stage => ActualComplex seed stage)
    (actualRestriction seed)

def dependentOccurrence : RootedAccountedUnfolding
    (FactorizationPayload ×
      CategoryTheory.Functor ℕᵒᵖ (IntegralCochainComplex ℤ)) :=
  seedOccurrence.map fun seed => (seed, localActionDiagram seed)

def globalFace : RootGeneratedDependentDerivedGlobalStateAt
    dependentOccurrence :=
  RootGeneratedDependentDerivedGlobalStateAt.generate

abbrev GlobalState : IntegralCochainComplex ℤ :=
  globalFace.globalState

noncomputable def globalRestriction (stage : ℕᵒᵖ) :
    GlobalState ⟶ globalFace.actualDiagram.obj stage :=
  globalFace.restriction stage

noncomputable def eulerActionNatTrans (seed : FactorizationPayload) :
    localActionDiagram seed ⟶ localActionDiagram seed :=
  NatTrans.ofOpSequence
    (actualEulerAction seed)
    (fun stage => by
      simp only [localActionDiagram, Functor.ofOpSequence_map_homOfLE_succ]
      exact (actualEulerAction_transition seed stage).symm)

noncomputable def reversalNatTrans (seed : FactorizationPayload) :
    localActionDiagram seed ⟶ localActionDiagram seed :=
  NatTrans.ofOpSequence
    (actualReversalAction seed)
    (fun stage => by
      simp only [localActionDiagram, Functor.ofOpSequence_map_homOfLE_succ]
      exact (actualReversalAction_transition seed stage).symm)

noncomputable def globalEulerAction : GlobalState ⟶ GlobalState := by
  change limit (localActionDiagram seedOccurrence.root) ⟶
    limit (localActionDiagram seedOccurrence.root)
  exact limMap (eulerActionNatTrans seedOccurrence.root)

noncomputable def globalReversal : GlobalState ⟶ GlobalState := by
  change limit (localActionDiagram seedOccurrence.root) ⟶
    limit (localActionDiagram seedOccurrence.root)
  exact limMap (reversalNatTrans seedOccurrence.root)

theorem globalEulerAction_restriction (stage : ℕᵒᵖ) :
    globalEulerAction ≫ globalRestriction stage =
      globalRestriction stage ≫
        (eulerActionNatTrans seedOccurrence.root).app stage :=
  limMap_π (eulerActionNatTrans seedOccurrence.root) stage

theorem globalReversal_restriction (stage : ℕᵒᵖ) :
    globalReversal ≫ globalRestriction stage =
      globalRestriction stage ≫
        (reversalNatTrans seedOccurrence.root).app stage :=
  limMap_π (reversalNatTrans seedOccurrence.root) stage

theorem actualReversalAction_involutive
    (seed : FactorizationPayload) (stage : Nat) :
    actualReversalAction seed stage ≫ actualReversalAction seed stage =
      𝟙 (ActualComplex seed stage) := by
  ext degree value
  by_cases degreeZero : degree = 0
  · subst degree
    exact carrierReversal_involutive seed stage value
  · let targetSubsingleton : Subsingleton
        ((ActualComplex seed stage).X degree) := by
      dsimp [ActualComplex]
      rw [if_neg degreeZero]
      infer_instance
    exact @Subsingleton.elim _ targetSubsingleton _ _

theorem globalReversal_involutive :
    globalReversal ≫ globalReversal = 𝟙 GlobalState := by
  change limMap (reversalNatTrans seedOccurrence.root) ≫
      limMap (reversalNatTrans seedOccurrence.root) =
    𝟙 (limit (localActionDiagram seedOccurrence.root))
  apply limit.hom_ext
  intro stage
  have componentInvolutive :
      (reversalNatTrans seedOccurrence.root).app stage ≫
          (reversalNatTrans seedOccurrence.root).app stage =
        𝟙 ((localActionDiagram seedOccurrence.root).obj stage) := by
    exact actualReversalAction_involutive
      seedOccurrence.root stage.unop
  calc
    (limMap (reversalNatTrans seedOccurrence.root) ≫
        limMap (reversalNatTrans seedOccurrence.root)) ≫
          limit.π (localActionDiagram seedOccurrence.root) stage =
        limit.π (localActionDiagram seedOccurrence.root) stage ≫
          ((reversalNatTrans seedOccurrence.root).app stage ≫
            (reversalNatTrans seedOccurrence.root).app stage) := by
      rw [Category.assoc, limMap_π, ← Category.assoc,
        limMap_π, Category.assoc]
    _ = limit.π (localActionDiagram seedOccurrence.root) stage := by
      rw [componentInvolutive, Category.comp_id]
    _ = 𝟙 (limit (localActionDiagram seedOccurrence.root)) ≫
        limit.π (localActionDiagram seedOccurrence.root) stage := by
      rw [Category.id_comp]

theorem globalEuler_reversal_commutes :
    globalEulerAction ≫ globalReversal =
      globalReversal ≫ globalEulerAction := by
  change limMap (eulerActionNatTrans seedOccurrence.root) ≫
      limMap (reversalNatTrans seedOccurrence.root) =
    limMap (reversalNatTrans seedOccurrence.root) ≫
      limMap (eulerActionNatTrans seedOccurrence.root)
  apply limit.hom_ext
  intro stage
  have componentCommutes :
      (eulerActionNatTrans seedOccurrence.root).app stage ≫
          (reversalNatTrans seedOccurrence.root).app stage =
        (reversalNatTrans seedOccurrence.root).app stage ≫
          (eulerActionNatTrans seedOccurrence.root).app stage :=
    actualEuler_reversal_commutes seedOccurrence.root stage.unop
  calc
    (limMap (eulerActionNatTrans seedOccurrence.root) ≫
        limMap (reversalNatTrans seedOccurrence.root)) ≫
          limit.π (localActionDiagram seedOccurrence.root) stage =
        limit.π (localActionDiagram seedOccurrence.root) stage ≫
          ((eulerActionNatTrans seedOccurrence.root).app stage ≫
            (reversalNatTrans seedOccurrence.root).app stage) := by
      rw [Category.assoc, limMap_π, ← Category.assoc,
        limMap_π, Category.assoc]
    _ = limit.π (localActionDiagram seedOccurrence.root) stage ≫
          ((reversalNatTrans seedOccurrence.root).app stage ≫
            (eulerActionNatTrans seedOccurrence.root).app stage) := by
      rw [componentCommutes]
    _ = (limMap (reversalNatTrans seedOccurrence.root) ≫
        limMap (eulerActionNatTrans seedOccurrence.root)) ≫
          limit.π (localActionDiagram seedOccurrence.root) stage := by
      symm
      rw [Category.assoc, limMap_π, ← Category.assoc,
        limMap_π, Category.assoc]

theorem preserves_exact_root_local_action_diagram_and_global_action :
    globalFace.root = seedOccurrence ∧
      globalFace.actualDiagram = localActionDiagram seedOccurrence.root ∧
      globalEulerAction = limMap (eulerActionNatTrans seedOccurrence.root) ∧
      globalReversal = limMap (reversalNatTrans seedOccurrence.root) := by
  exact ⟨rfl, rfl, rfl, rfl⟩

end
end CanonicalUnitArithmeticFactorizationFullEulerGlobalAction
end ConstructiveRoot
end LivingLawEvolution
end ResponsibilityLifecycle
end SaturationMonoid
