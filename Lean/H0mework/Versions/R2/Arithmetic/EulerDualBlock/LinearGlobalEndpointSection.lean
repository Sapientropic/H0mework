import H0mework.Versions.R2.Arithmetic.EulerDualBlock.LinearGlobalAction

/-!
# Endpoints of the block-linear global whole complex

The actual `none` role supplies a two-dimensional endpoint family over the
common coordinate ring.  Runtime restriction preserves it strictly, so the
limit universal property generates the global endpoints on the unique
block-linear carrier.  Their differential is retained as the global
relation boundary; no cocycle or fixedness law is assumed.
-/

set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency false

namespace SaturationMonoid
namespace ResponsibilityLifecycle
namespace LivingLawEvolution
namespace ConstructiveRoot
namespace CanonicalUnitArithmeticFactorizationFullEulerWholePrimeDualBlockLinearGlobalEndpointSection

open CanonicalUnitArithmeticFactorizationEulerDependentDiagram
open CanonicalUnitArithmeticFactorizationFullEulerWholePrimeDualBlockFrame
open CanonicalUnitArithmeticFactorizationFullEulerWholePrimeDualBlockLinearGlobalAction
open CanonicalUnitArithmeticFactorizationFullEulerWholePrimeDualBlockWholeRelationDeterminant
open CategoryTheory
open CategoryTheory.Limits

noncomputable section

abbrev BlockDualBase := Fin 2 → BlockCoordinateRing

def blockDualBaseReversal : BlockDualBase →ₗ[BlockCoordinateRing]
    BlockDualBase where
  toFun base dualIndex := base dualIndex.rev
  map_add' _left _right := rfl
  map_smul' _scalar _base := rfl

def localBlockEndpointVertexMap (stage : Nat) :
    BlockDualBase →ₗ[BlockCoordinateRing]
      BlockWholeVertex seedOccurrence.root stage where
  toFun base role index :=
    match role with
    | none => base index.2
    | some _row => 0
  map_add' left right := by
    funext role index
    cases role <;> rfl
  map_smul' scalar base := by
    funext role index
    cases role <;> simp

theorem localBlockEndpointVertexMap_successor (stage : Nat) :
    (blockWholeVertexRestriction seedOccurrence.root stage).comp
        (localBlockEndpointVertexMap (stage + 1)) =
      localBlockEndpointVertexMap stage := by
  apply LinearMap.ext
  intro base
  funext role index
  cases role <;> rfl

theorem localBlockEndpointVertexMap_reversal (stage : Nat) :
    (blockWholeVertexReversal seedOccurrence.root stage).comp
        (localBlockEndpointVertexMap stage) =
      (localBlockEndpointVertexMap stage).comp blockDualBaseReversal := by
  apply LinearMap.ext
  intro base
  funext role index
  cases role with
  | none => rfl
  | some row => simp [blockWholeVertexReversal, localBlockEndpointVertexMap]

abbrev BlockDualBaseObject : ModuleCat BlockCoordinateRing :=
  ModuleCat.of BlockCoordinateRing BlockDualBase

abbrev blockDegreeZeroEvaluation :
    CochainComplex (ModuleCat BlockCoordinateRing) ℤ ⥤
      ModuleCat BlockCoordinateRing :=
  HomologicalComplex.eval (ModuleCat BlockCoordinateRing)
    (ComplexShape.up ℤ) 0

abbrev blockEndpointDegreeZeroDiagram :
    ℕᵒᵖ ⥤ ModuleCat BlockCoordinateRing :=
  localBlockLinearDiagram seedOccurrence.root ⋙ blockDegreeZeroEvaluation

noncomputable def blockEndpointDegreeZeroCone :
    Cone blockEndpointDegreeZeroDiagram where
  pt := BlockDualBaseObject
  π := NatTrans.ofOpSequence
    (fun stage => ModuleCat.ofHom (localBlockEndpointVertexMap stage))
    (fun stage => by
      simp only [Functor.const_obj_map, blockEndpointDegreeZeroDiagram,
        Functor.comp_map, HomologicalComplex.eval_map,
        localBlockLinearDiagram, Functor.ofOpSequence_map_homOfLE_succ]
      apply ModuleCat.hom_ext
      exact (localBlockEndpointVertexMap_successor stage).symm)

noncomputable def blockEndpointDegreeZeroLift :
    BlockDualBaseObject ⟶ limit blockEndpointDegreeZeroDiagram :=
  limit.lift blockEndpointDegreeZeroDiagram blockEndpointDegreeZeroCone

noncomputable def blockDegreeZeroLimitIso :
    BlockLinearGlobalState.X 0 ≅ limit blockEndpointDegreeZeroDiagram :=
  preservesLimitIso blockDegreeZeroEvaluation
    (localBlockLinearDiagram seedOccurrence.root)

theorem blockDegreeZeroLimitIso_inv_restriction (stage : Nat) :
    blockDegreeZeroLimitIso.inv ≫
        (blockLinearGlobalRestriction (Opposite.op stage)).f 0 =
      limit.π blockEndpointDegreeZeroDiagram (Opposite.op stage) := by
  exact preservesLimitIso_inv_π blockDegreeZeroEvaluation
    (localBlockLinearDiagram seedOccurrence.root) (Opposite.op stage)

theorem blockDegreeZeroLimitIso_hom_projection (stage : ℕᵒᵖ) :
    blockDegreeZeroLimitIso.hom ≫
        limit.π blockEndpointDegreeZeroDiagram stage =
      (blockLinearGlobalRestriction stage).f 0 := by
  exact preservesLimitIso_hom_π blockDegreeZeroEvaluation
    (localBlockLinearDiagram seedOccurrence.root) stage

noncomputable def globalBlockEndpointVertexMapHom :
    BlockDualBaseObject ⟶ BlockLinearGlobalState.X 0 :=
  blockEndpointDegreeZeroLift ≫ blockDegreeZeroLimitIso.inv

def globalBlockEndpointVertexMap :
    BlockDualBase →ₗ[BlockCoordinateRing] (BlockLinearGlobalState.X 0 : Type) :=
  globalBlockEndpointVertexMapHom.hom

theorem globalBlockEndpointVertexMapHom_restriction (stage : Nat) :
    globalBlockEndpointVertexMapHom ≫
        (blockLinearGlobalRestriction (Opposite.op stage)).f 0 =
      ModuleCat.ofHom (localBlockEndpointVertexMap stage) := by
  rw [globalBlockEndpointVertexMapHom, Category.assoc,
    blockDegreeZeroLimitIso_inv_restriction]
  exact limit.lift_π blockEndpointDegreeZeroCone (Opposite.op stage)

theorem globalBlockEndpointVertexMap_restriction (stage : Nat) :
    ((blockLinearGlobalRestriction (Opposite.op stage)).f 0).hom.comp
        globalBlockEndpointVertexMap =
      localBlockEndpointVertexMap stage :=
  congrArg ModuleCat.Hom.hom
    (globalBlockEndpointVertexMapHom_restriction stage)

def blockLeftEndpointBase : BlockDualBase
  | 0 => 1
  | 1 => 0

def blockRightEndpointBase : BlockDualBase
  | 0 => 0
  | 1 => 1

@[simp] theorem blockDualBaseReversal_leftEndpointBase :
    blockDualBaseReversal blockLeftEndpointBase = blockRightEndpointBase := by
  funext index
  fin_cases index <;> rfl

@[simp] theorem blockDualBaseReversal_rightEndpointBase :
    blockDualBaseReversal blockRightEndpointBase = blockLeftEndpointBase := by
  funext index
  fin_cases index <;> rfl

def globalBlockLeftEndpoint : (BlockLinearGlobalState.X 0 : Type) :=
  globalBlockEndpointVertexMap blockLeftEndpointBase

def globalBlockRightEndpoint : (BlockLinearGlobalState.X 0 : Type) :=
  globalBlockEndpointVertexMap blockRightEndpointBase

theorem globalBlockEndpointVertexMap_reversal :
    (blockLinearGlobalReversal.f 0).hom.comp globalBlockEndpointVertexMap =
      globalBlockEndpointVertexMap.comp blockDualBaseReversal := by
  have homEquality :
      globalBlockEndpointVertexMapHom ≫ blockLinearGlobalReversal.f 0 =
        ModuleCat.ofHom blockDualBaseReversal ≫
          globalBlockEndpointVertexMapHom := by
    apply (cancel_mono blockDegreeZeroLimitIso.hom).1
    apply limit.hom_ext
    intro stage
    have reversalRestrictionZero :
        blockLinearGlobalReversal.f 0 ≫
            (blockLinearGlobalRestriction stage).f 0 =
          (blockLinearGlobalRestriction stage).f 0 ≫
            ((blockLinearReversalNatTrans
              seedOccurrence.root).app stage).f 0 := by
      exact congrArg (fun arrow => arrow.f 0)
        (blockLinearGlobalReversal_restriction stage)
    calc
      ((globalBlockEndpointVertexMapHom ≫
          blockLinearGlobalReversal.f 0) ≫
            blockDegreeZeroLimitIso.hom) ≫
              limit.π blockEndpointDegreeZeroDiagram stage =
          globalBlockEndpointVertexMapHom ≫
            (blockLinearGlobalReversal.f 0 ≫
              (blockDegreeZeroLimitIso.hom ≫
                limit.π blockEndpointDegreeZeroDiagram stage)) := by
              simp only [Category.assoc]
      _ = globalBlockEndpointVertexMapHom ≫
            (blockLinearGlobalReversal.f 0 ≫
              (blockLinearGlobalRestriction stage).f 0) := by
            rw [blockDegreeZeroLimitIso_hom_projection]
      _ = globalBlockEndpointVertexMapHom ≫
            ((blockLinearGlobalRestriction stage).f 0 ≫
              ((blockLinearReversalNatTrans
                seedOccurrence.root).app stage).f 0) := by
            rw [reversalRestrictionZero]
      _ = (globalBlockEndpointVertexMapHom ≫
              (blockLinearGlobalRestriction stage).f 0) ≫
            ((blockLinearReversalNatTrans
              seedOccurrence.root).app stage).f 0 := by
            simp only [Category.assoc]
      _ = ModuleCat.ofHom
              (localBlockEndpointVertexMap stage.unop) ≫
            ((blockLinearReversalNatTrans
              seedOccurrence.root).app stage).f 0 := by
            rw [globalBlockEndpointVertexMapHom_restriction]
      _ = ModuleCat.ofHom blockDualBaseReversal ≫
            ModuleCat.ofHom
              (localBlockEndpointVertexMap stage.unop) := by
            apply ModuleCat.hom_ext
            exact localBlockEndpointVertexMap_reversal stage.unop
      _ = ModuleCat.ofHom blockDualBaseReversal ≫
            (globalBlockEndpointVertexMapHom ≫
              (blockLinearGlobalRestriction stage).f 0) := by
            rw [globalBlockEndpointVertexMapHom_restriction]
      _ = ModuleCat.ofHom blockDualBaseReversal ≫
            (globalBlockEndpointVertexMapHom ≫
              (blockDegreeZeroLimitIso.hom ≫
                limit.π blockEndpointDegreeZeroDiagram stage)) := by
            rw [blockDegreeZeroLimitIso_hom_projection]
      _ = ((ModuleCat.ofHom blockDualBaseReversal ≫
              globalBlockEndpointVertexMapHom) ≫
            blockDegreeZeroLimitIso.hom) ≫
          limit.π blockEndpointDegreeZeroDiagram stage := by
            simp only [Category.assoc]
  exact congrArg ModuleCat.Hom.hom homEquality

@[simp] theorem globalBlockReversal_leftEndpoint :
    (blockLinearGlobalReversal.f 0).hom globalBlockLeftEndpoint =
      globalBlockRightEndpoint := by
  change (blockLinearGlobalReversal.f 0).hom
      (globalBlockEndpointVertexMap blockLeftEndpointBase) = _
  rw [← LinearMap.comp_apply, globalBlockEndpointVertexMap_reversal,
    LinearMap.comp_apply, blockDualBaseReversal_leftEndpointBase]
  rfl

@[simp] theorem globalBlockReversal_rightEndpoint :
    (blockLinearGlobalReversal.f 0).hom globalBlockRightEndpoint =
      globalBlockLeftEndpoint := by
  change (blockLinearGlobalReversal.f 0).hom
      (globalBlockEndpointVertexMap blockRightEndpointBase) = _
  rw [← LinearMap.comp_apply, globalBlockEndpointVertexMap_reversal,
    LinearMap.comp_apply, blockDualBaseReversal_rightEndpointBase]
  rfl

def globalBlockDifferential :
    (BlockLinearGlobalState.X 0 : Type) →ₗ[BlockCoordinateRing]
      (BlockLinearGlobalState.X 1 : Type) :=
  (BlockLinearGlobalState.d 0 1).hom

def globalBlockLeftBoundary : (BlockLinearGlobalState.X 1 : Type) :=
  globalBlockDifferential globalBlockLeftEndpoint

def globalBlockRightBoundary : (BlockLinearGlobalState.X 1 : Type) :=
  globalBlockDifferential globalBlockRightEndpoint

theorem globalBlockLeftBoundary_is_actual :
    globalBlockDifferential globalBlockLeftEndpoint =
      globalBlockLeftBoundary :=
  rfl

theorem globalBlockRightBoundary_is_actual :
    globalBlockDifferential globalBlockRightEndpoint =
      globalBlockRightBoundary :=
  rfl

def blockLinearEndpointOccurrence : RootedAccountedUnfolding
    (FactorizationPayload ×
      ((BlockLinearGlobalState.X 0 : Type) ×
        (BlockLinearGlobalState.X 0 : Type))) :=
  seedOccurrence.map fun owner =>
    (owner, (globalBlockLeftEndpoint, globalBlockRightEndpoint))

theorem blockLinearEndpointOccurrence_projects :
    blockLinearEndpointOccurrence.map Prod.fst = seedOccurrence := by
  unfold blockLinearEndpointOccurrence
  rw [RootedAccountedUnfolding.map_map]
  change seedOccurrence.map id = seedOccurrence
  exact RootedAccountedUnfolding.map_id _

theorem preserves_actual_endpoint_cone_and_global_boundary (stage : Nat) :
    blockLinearEndpointOccurrence.map Prod.fst = seedOccurrence ∧
      ((blockLinearGlobalRestriction (Opposite.op stage)).f 0).hom.comp
          globalBlockEndpointVertexMap =
        localBlockEndpointVertexMap stage ∧
      globalBlockDifferential globalBlockLeftEndpoint =
        globalBlockLeftBoundary ∧
      globalBlockDifferential globalBlockRightEndpoint =
        globalBlockRightBoundary := by
  exact ⟨blockLinearEndpointOccurrence_projects,
    globalBlockEndpointVertexMap_restriction stage, rfl, rfl⟩

end
end CanonicalUnitArithmeticFactorizationFullEulerWholePrimeDualBlockLinearGlobalEndpointSection
end ConstructiveRoot
end LivingLawEvolution
end ResponsibilityLifecycle
end SaturationMonoid
