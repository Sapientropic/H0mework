import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
import H0mework.Arithmetic.EulerDualBlock.WholeRelationDeterminant
import H0mework.Realization.GlobalSections.DerivedState

/-!
# Global whole action of the prime-dual block complex

The complete, uncancelled block whole/relation complex is first restricted
from its common coordinate ring to its underlying integral module.  The
actual source successor then forms one dependent inverse diagram, and the
frozen dependent-global-state engine generates the unique global carrier.
Euler action and reversal are induced by natural transformations on that
same diagram.
-/

set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency false

namespace SaturationMonoid
namespace ResponsibilityLifecycle
namespace LivingLawEvolution
namespace ConstructiveRoot
namespace CanonicalUnitArithmeticFactorizationFullEulerWholePrimeDualBlockGlobalAction

open CanonicalUnitArithmeticFactorizationEulerDependentDiagram
open CanonicalUnitArithmeticFactorizationFullEulerWholePrimeDualBlockFrame
open CanonicalUnitArithmeticFactorizationFullEulerWholePrimeDualBlockWholeRelationDeterminant
open DependentDerivedGlobalState
open DependentDerivedGlobalState.RootGeneratedDependentDerivedGlobalStateAt
open CategoryTheory
open CategoryTheory.Limits
open DerivedAdicCofiber

noncomputable section

abbrev BlockIntegralDirectObject
    (seed : FactorizationPayload) (stage : Nat) (degree : ℤ) :
    ModuleCat ℤ :=
  if degree = 0 then ModuleCat.of ℤ (BlockWholeVertex seed stage)
  else if degree = 1 then ModuleCat.of ℤ (BlockWholeRelation seed stage)
  else ModuleCat.of ℤ (Fin 0 → BlockCoordinateRing)

def blockIntegralDifferential
    (seed : FactorizationPayload) (stage : Nat) (degree : ℤ) :
    BlockIntegralDirectObject seed stage degree ⟶
      BlockIntegralDirectObject seed stage (degree + 1) := by
  by_cases degreeZero : degree = 0
  · subst degree
    exact ModuleCat.ofHom
      ((blockFactorizationDifferential seed stage).restrictScalars ℤ)
  · exact 0

theorem blockIntegralDifferential_sq
    (seed : FactorizationPayload) (stage : Nat) (degree : ℤ) :
    blockIntegralDifferential seed stage degree ≫
        blockIntegralDifferential seed stage (degree + 1) = 0 := by
  by_cases degreeZero : degree = 0
  · subst degree
    simp [blockIntegralDifferential]
  · simp [blockIntegralDifferential, degreeZero]

noncomputable abbrev UnderlyingBlockDirectComplex
    (seed : FactorizationPayload) (stage : Nat) : IntegralCochainComplex ℤ :=
  CochainComplex.of (BlockIntegralDirectObject seed stage)
    (blockIntegralDifferential seed stage)
    (blockIntegralDifferential_sq seed stage)

noncomputable def underlyingBlockDirectEulerAction
    (seed : FactorizationPayload) (stage : Nat) :
    UnderlyingBlockDirectComplex seed stage ⟶
      UnderlyingBlockDirectComplex seed stage where
  f degree := by
    by_cases degreeZero : degree = 0
    · subst degree
      exact ModuleCat.ofHom
        ((blockWholeVertexAction seed stage).restrictScalars ℤ)
    · by_cases degreeOne : degree = 1
      · subst degree
        exact ModuleCat.ofHom
          ((blockWholeRelationAction seed stage).restrictScalars ℤ)
      · exact 0
  comm' source target related := by
    change source + 1 = target at related
    subst target
    by_cases sourceZero : source = 0
    · subst source
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro value
      exact LinearMap.congr_fun
        (blockFactorizationDifferential_action_square seed stage) value
    · simp [UnderlyingBlockDirectComplex, blockIntegralDifferential,
        sourceZero]

noncomputable def underlyingBlockDirectReversal
    (seed : FactorizationPayload) (stage : Nat) :
    UnderlyingBlockDirectComplex seed stage ⟶
      UnderlyingBlockDirectComplex seed stage where
  f degree := by
    by_cases degreeZero : degree = 0
    · subst degree
      exact ModuleCat.ofHom
        ((blockWholeVertexReversal seed stage).restrictScalars ℤ)
    · by_cases degreeOne : degree = 1
      · subst degree
        exact ModuleCat.ofHom
          ((blockWholeRelationReversal seed stage).restrictScalars ℤ)
      · exact 0
  comm' source target related := by
    change source + 1 = target at related
    subst target
    by_cases sourceZero : source = 0
    · subst source
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro value
      exact LinearMap.congr_fun
        (blockFactorizationDifferential_reversal_square seed stage) value
    · simp [UnderlyingBlockDirectComplex, blockIntegralDifferential,
        sourceZero]

noncomputable def underlyingBlockDirectRestriction
    (seed : FactorizationPayload) (stage : Nat) :
    UnderlyingBlockDirectComplex seed (stage + 1) ⟶
      UnderlyingBlockDirectComplex seed stage where
  f degree := by
    by_cases degreeZero : degree = 0
    · subst degree
      exact ModuleCat.ofHom
        ((blockWholeVertexRestriction seed stage).restrictScalars ℤ)
    · by_cases degreeOne : degree = 1
      · subst degree
        exact ModuleCat.ofHom
          ((blockWholeRelationRestriction seed stage).restrictScalars ℤ)
      · exact 0
  comm' source target related := by
    change source + 1 = target at related
    subst target
    by_cases sourceZero : source = 0
    · subst source
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro value
      exact LinearMap.congr_fun
        (blockFactorizationDifferential_restriction_square seed stage) value
    · simp [UnderlyingBlockDirectComplex, blockIntegralDifferential,
        sourceZero]

theorem underlyingBlockRestriction_action_square
    (seed : FactorizationPayload) (stage : Nat) :
  underlyingBlockDirectEulerAction seed (stage + 1) ≫
        underlyingBlockDirectRestriction seed stage =
      underlyingBlockDirectRestriction seed stage ≫
        underlyingBlockDirectEulerAction seed stage := by
  ext degree
  by_cases degreeZero : degree = 0
  · subst degree
    exact LinearMap.congr_fun
      (blockWholeVertexRestriction_action_square seed stage) _
  · by_cases degreeOne : degree = 1
    · subst degree
      exact LinearMap.congr_fun
        (blockWholeRelationRestriction_action_square seed stage) _
    · simp [underlyingBlockDirectEulerAction,
        underlyingBlockDirectRestriction, degreeZero, degreeOne]

theorem underlyingBlockRestriction_reversal_square
    (seed : FactorizationPayload) (stage : Nat) :
    underlyingBlockDirectReversal seed (stage + 1) ≫
        underlyingBlockDirectRestriction seed stage =
      underlyingBlockDirectRestriction seed stage ≫
        underlyingBlockDirectReversal seed stage := by
  ext degree
  by_cases degreeZero : degree = 0
  · subst degree
    exact LinearMap.congr_fun
      (blockWholeVertexRestriction_reversal_square seed stage) _
  · by_cases degreeOne : degree = 1
    · subst degree
      exact LinearMap.congr_fun
        (blockWholeRelationRestriction_reversal_square seed stage) _
    · simp [underlyingBlockDirectReversal,
        underlyingBlockDirectRestriction, degreeZero, degreeOne]

theorem underlyingBlockEuler_reversal_commutes
    (seed : FactorizationPayload) (stage : Nat) :
    underlyingBlockDirectEulerAction seed stage ≫
        underlyingBlockDirectReversal seed stage =
      underlyingBlockDirectReversal seed stage ≫
        underlyingBlockDirectEulerAction seed stage := by
  ext degree
  by_cases degreeZero : degree = 0
  · subst degree
    change blockWholeVertexReversal seed stage
        (blockWholeVertexAction seed stage _) =
      blockWholeVertexAction seed stage
        (blockWholeVertexReversal seed stage _)
    exact LinearMap.congr_fun
      (blockWholeVertexAction_reversal_square seed stage).symm _
  · by_cases degreeOne : degree = 1
    · subst degree
      change blockWholeRelationReversal seed stage
          (blockWholeRelationAction seed stage _) =
        blockWholeRelationAction seed stage
          (blockWholeRelationReversal seed stage _)
      exact LinearMap.congr_fun
        (blockWholeRelationAction_reversal_square seed stage).symm _
    · simp [underlyingBlockDirectEulerAction,
        underlyingBlockDirectReversal, degreeZero, degreeOne]

theorem underlyingBlockReversal_involutive
    (seed : FactorizationPayload) (stage : Nat) :
    underlyingBlockDirectReversal seed stage ≫
        underlyingBlockDirectReversal seed stage =
      𝟙 (UnderlyingBlockDirectComplex seed stage) := by
  ext degree value
  by_cases degreeZero : degree = 0
  · subst degree
    change blockWholeVertexReversal seed stage
        (blockWholeVertexReversal seed stage value) = value
    funext role
    cases role with
    | none => exact blockInnerReversal_involutive seed stage (value none)
    | some row => simp [blockWholeVertexReversal]
  · by_cases degreeOne : degree = 1
    · subst degree
      change blockWholeRelationReversal seed stage
          (blockWholeRelationReversal seed stage value) = value
      funext row
      simp [blockWholeRelationReversal]
    · let targetSubsingleton : Subsingleton
          ((UnderlyingBlockDirectComplex seed stage).X degree) := by
        change Subsingleton (BlockIntegralDirectObject seed stage degree)
        simp [BlockIntegralDirectObject, degreeZero, degreeOne]
        exact ⟨fun left right => funext fun index => Fin.elim0 index⟩
      exact @Subsingleton.elim _ targetSubsingleton _ _

noncomputable def localBlockRelationDiagram (seed : FactorizationPayload) :
    ℕᵒᵖ ⥤ IntegralCochainComplex ℤ :=
  Functor.ofOpSequence
    (X := fun stage => UnderlyingBlockDirectComplex seed stage)
    (underlyingBlockDirectRestriction seed)

def dependentBlockComplexOccurrence : RootedAccountedUnfolding
    (FactorizationPayload × (ℕᵒᵖ ⥤ IntegralCochainComplex ℤ)) :=
  seedOccurrence.map fun seed => (seed, localBlockRelationDiagram seed)

theorem dependentBlockComplexOccurrence_projects :
    dependentBlockComplexOccurrence.map Prod.fst = seedOccurrence := by
  unfold dependentBlockComplexOccurrence
  rw [RootedAccountedUnfolding.map_map]
  change seedOccurrence.map id = seedOccurrence
  exact RootedAccountedUnfolding.map_id _

def globalBlockComplexFace :
    RootGeneratedDependentDerivedGlobalStateAt dependentBlockComplexOccurrence :=
  RootGeneratedDependentDerivedGlobalStateAt.generate

abbrev GlobalBlockWholeState : IntegralCochainComplex ℤ :=
  globalBlockComplexFace.globalState

noncomputable def globalBlockRestriction (stage : ℕᵒᵖ) :
    GlobalBlockWholeState ⟶ globalBlockComplexFace.actualDiagram.obj stage :=
  globalBlockComplexFace.restriction stage

noncomputable def blockEulerActionNatTrans (seed : FactorizationPayload) :
    localBlockRelationDiagram seed ⟶ localBlockRelationDiagram seed :=
  NatTrans.ofOpSequence
    (underlyingBlockDirectEulerAction seed)
    (fun stage => by
      simp only [localBlockRelationDiagram,
        Functor.ofOpSequence_map_homOfLE_succ]
      exact (underlyingBlockRestriction_action_square seed stage).symm)

noncomputable def blockReversalNatTrans (seed : FactorizationPayload) :
    localBlockRelationDiagram seed ⟶ localBlockRelationDiagram seed :=
  NatTrans.ofOpSequence
    (underlyingBlockDirectReversal seed)
    (fun stage => by
      simp only [localBlockRelationDiagram,
        Functor.ofOpSequence_map_homOfLE_succ]
      exact (underlyingBlockRestriction_reversal_square seed stage).symm)

noncomputable def globalBlockEulerAction :
    GlobalBlockWholeState ⟶ GlobalBlockWholeState := by
  change limit (localBlockRelationDiagram seedOccurrence.root) ⟶
    limit (localBlockRelationDiagram seedOccurrence.root)
  exact limMap (blockEulerActionNatTrans seedOccurrence.root)

noncomputable def globalBlockReversal :
    GlobalBlockWholeState ⟶ GlobalBlockWholeState := by
  change limit (localBlockRelationDiagram seedOccurrence.root) ⟶
    limit (localBlockRelationDiagram seedOccurrence.root)
  exact limMap (blockReversalNatTrans seedOccurrence.root)

theorem globalBlockEulerAction_restriction (stage : ℕᵒᵖ) :
    globalBlockEulerAction ≫ globalBlockRestriction stage =
      globalBlockRestriction stage ≫
        (blockEulerActionNatTrans seedOccurrence.root).app stage :=
  limMap_π (blockEulerActionNatTrans seedOccurrence.root) stage

theorem globalBlockReversal_restriction (stage : ℕᵒᵖ) :
    globalBlockReversal ≫ globalBlockRestriction stage =
      globalBlockRestriction stage ≫
        (blockReversalNatTrans seedOccurrence.root).app stage :=
  limMap_π (blockReversalNatTrans seedOccurrence.root) stage

theorem globalBlockReversal_involutive :
    globalBlockReversal ≫ globalBlockReversal =
      𝟙 GlobalBlockWholeState := by
  change limMap (blockReversalNatTrans seedOccurrence.root) ≫
      limMap (blockReversalNatTrans seedOccurrence.root) =
    𝟙 (limit (localBlockRelationDiagram seedOccurrence.root))
  apply limit.hom_ext
  intro stage
  have componentInvolutive :
      (blockReversalNatTrans seedOccurrence.root).app stage ≫
          (blockReversalNatTrans seedOccurrence.root).app stage =
        𝟙 ((localBlockRelationDiagram seedOccurrence.root).obj stage) :=
    underlyingBlockReversal_involutive seedOccurrence.root stage.unop
  calc
    (limMap (blockReversalNatTrans seedOccurrence.root) ≫
        limMap (blockReversalNatTrans seedOccurrence.root)) ≫
          limit.π (localBlockRelationDiagram seedOccurrence.root) stage =
        limit.π (localBlockRelationDiagram seedOccurrence.root) stage ≫
          ((blockReversalNatTrans seedOccurrence.root).app stage ≫
            (blockReversalNatTrans seedOccurrence.root).app stage) := by
      rw [Category.assoc, limMap_π, ← Category.assoc,
        limMap_π, Category.assoc]
    _ = limit.π (localBlockRelationDiagram seedOccurrence.root) stage := by
      rw [componentInvolutive, Category.comp_id]
    _ = 𝟙 (limit (localBlockRelationDiagram seedOccurrence.root)) ≫
        limit.π (localBlockRelationDiagram seedOccurrence.root) stage := by
      rw [Category.id_comp]

theorem globalBlockEuler_reversal_commutes :
    globalBlockEulerAction ≫ globalBlockReversal =
      globalBlockReversal ≫ globalBlockEulerAction := by
  change limMap (blockEulerActionNatTrans seedOccurrence.root) ≫
      limMap (blockReversalNatTrans seedOccurrence.root) =
    limMap (blockReversalNatTrans seedOccurrence.root) ≫
      limMap (blockEulerActionNatTrans seedOccurrence.root)
  apply limit.hom_ext
  intro stage
  have componentCommutes :
      (blockEulerActionNatTrans seedOccurrence.root).app stage ≫
          (blockReversalNatTrans seedOccurrence.root).app stage =
        (blockReversalNatTrans seedOccurrence.root).app stage ≫
          (blockEulerActionNatTrans seedOccurrence.root).app stage :=
    underlyingBlockEuler_reversal_commutes seedOccurrence.root stage.unop
  calc
    (limMap (blockEulerActionNatTrans seedOccurrence.root) ≫
        limMap (blockReversalNatTrans seedOccurrence.root)) ≫
          limit.π (localBlockRelationDiagram seedOccurrence.root) stage =
      limit.π (localBlockRelationDiagram seedOccurrence.root) stage ≫
        ((blockEulerActionNatTrans seedOccurrence.root).app stage ≫
          (blockReversalNatTrans seedOccurrence.root).app stage) := by
        rw [Category.assoc, limMap_π,
          ← Category.assoc, limMap_π, Category.assoc]
    _ = limit.π (localBlockRelationDiagram seedOccurrence.root) stage ≫
        ((blockReversalNatTrans seedOccurrence.root).app stage ≫
          (blockEulerActionNatTrans seedOccurrence.root).app stage) := by
        rw [componentCommutes]
    _ = (limMap (blockReversalNatTrans seedOccurrence.root) ≫
        limMap (blockEulerActionNatTrans seedOccurrence.root)) ≫
          limit.π (localBlockRelationDiagram seedOccurrence.root) stage := by
      symm
      rw [Category.assoc, limMap_π,
        ← Category.assoc, limMap_π, Category.assoc]

theorem preserves_exact_root_uncancelled_global_block_state :
    globalBlockComplexFace.root = seedOccurrence ∧
      globalBlockComplexFace.actualDiagram =
        localBlockRelationDiagram seedOccurrence.root ∧
      (∀ stage : ℕᵒᵖ,
        globalBlockEulerAction ≫ globalBlockRestriction stage =
          globalBlockRestriction stage ≫
            (blockEulerActionNatTrans seedOccurrence.root).app stage) ∧
      (∀ stage : ℕᵒᵖ,
        globalBlockReversal ≫ globalBlockRestriction stage =
          globalBlockRestriction stage ≫
            (blockReversalNatTrans seedOccurrence.root).app stage) := by
  refine ⟨?_, rfl, globalBlockEulerAction_restriction,
    globalBlockReversal_restriction⟩
  unfold RootGeneratedDependentDerivedGlobalStateAt.root
    dependentBlockComplexOccurrence
  rw [RootedAccountedUnfolding.map_map]
  change seedOccurrence.map id = seedOccurrence
  exact RootedAccountedUnfolding.map_id _

end
end CanonicalUnitArithmeticFactorizationFullEulerWholePrimeDualBlockGlobalAction
end ConstructiveRoot
end LivingLawEvolution
end ResponsibilityLifecycle
end SaturationMonoid
