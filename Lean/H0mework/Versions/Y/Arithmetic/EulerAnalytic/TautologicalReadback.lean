import H0mework.Versions.Y.Arithmetic.EulerAnalytic.EndpointCofiberElement

/-!
# Same-component tautological anti-invariant readback

The actual global endpoint section enters the generated pair-action cofiber
through its tautological inclusion.  Reading that literal element through the
canonical shifted source projection, the generated global-to-local
restriction, and the actual local anti-invariant map returns exactly

`(u_left - u_right) ⊗ localEndpointAntiInvariant`.

No cycle, source zero, cofiber-class zero, fixedness, or endpoint equality is
accepted.
-/

set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false

namespace SaturationMonoid
namespace ResponsibilityLifecycle
namespace LivingLawEvolution
namespace ConstructiveRoot
namespace CanonicalUnitArithmeticFactorizationFullEulerWholePrimeDualBlockAnalyticTautologicalReadback

open CanonicalUnitArithmeticFactorizationEulerDependentDiagram
open CanonicalUnitArithmeticFactorizationFullEulerWholePrimeDualBlockFrame
open CanonicalUnitArithmeticFactorizationFullEulerWholePrimeDualBlockWholeRelationDeterminant
open CanonicalUnitArithmeticFactorizationFullEulerWholePrimeDualBlockLinearGlobalAction
open CanonicalUnitArithmeticFactorizationFullEulerWholePrimeDualBlockLinearGlobalEndpointSection
open CanonicalUnitArithmeticFactorizationFullEulerWholePrimeDualBlockAnalyticGlobalActionCofiber
open CanonicalUnitArithmeticFactorizationFullEulerWholePrimeDualBlockAnalyticEndpointCofiberElement
open CanonicalUnitArithmeticFactorizationWholePrimeDualBlockDeterminantLineCoordinate
open CategoryTheory
open DerivedAdicCofiber
open scoped ChangeOfRings

noncomputable section

abbrev PairBlockLocalState (stage : Nat) :
    IntegralCochainComplex PairCoefficientRing :=
  PairBlockExtensionFunctor.obj
    (blockDirectComplex seedOccurrence.root stage)

noncomputable def pairBlockGlobalRestriction (stage : Nat) :
    PairBlockGlobalState ⟶ PairBlockLocalState stage :=
  PairBlockExtensionFunctor.map
    (blockLinearGlobalRestriction (Opposite.op stage))

abbrev BlockInnerObject (stage : Nat) : ModuleCat BlockCoordinateRing :=
  ModuleCat.of BlockCoordinateRing
    (BlockInner seedOccurrence.root stage)

noncomputable abbrev blockInnerSingle (stage : Nat) :
    IntegralCochainComplex BlockCoordinateRing :=
  (CochainComplex.singleFunctor (ModuleCat BlockCoordinateRing) 0).obj
    (BlockInnerObject stage)

def blockWholeAntiInvariantProjection (stage : Nat) :
    BlockWholeVertex seedOccurrence.root stage →ₗ[BlockCoordinateRing]
      BlockInner seedOccurrence.root stage :=
  (blockInnerAntiInvariant seedOccurrence.root stage).comp
    (LinearMap.proj none)

noncomputable def blockWholeAntiInvariantMap (stage : Nat) :
    blockDirectComplex seedOccurrence.root stage ⟶
      blockInnerSingle stage where
  f degree := by
    by_cases degreeZero : degree = 0
    · subst degree
      exact ModuleCat.ofHom (blockWholeAntiInvariantProjection stage)
    · exact 0
  comm' source target related := by
    change source + 1 = target at related
    subst target
    by_cases sourceZero : source = 0
    · subst source
      simp [blockInnerSingle]
    · simp [blockInnerSingle, blockDirectDifferential, sourceZero]

noncomputable abbrev PairBlockLocalInnerSingle (stage : Nat) :
    IntegralCochainComplex PairCoefficientRing :=
  PairBlockExtensionFunctor.obj (blockInnerSingle stage)

noncomputable def pairBlockWholeAntiInvariantMap (stage : Nat) :
    PairBlockLocalState stage ⟶ PairBlockLocalInnerSingle stage :=
  PairBlockExtensionFunctor.map (blockWholeAntiInvariantMap stage)

def pairBlockLocalEndpointSection (stage : Nat) :
    (PairBlockLocalState stage).X 0 :=
  universalLeftCoordinate installedOwner
      ⊗ₜ[BlockCoordinateRing, blockCoordinateToPairZeroFiber]
        localBlockEndpointVertexMap stage blockLeftEndpointBase +
    universalRightCoordinate installedOwner
      ⊗ₜ[BlockCoordinateRing, blockCoordinateToPairZeroFiber]
        localBlockEndpointVertexMap stage blockRightEndpointBase

theorem pairBlockGlobalRestriction_endpointSection (stage : Nat) :
    ((pairBlockGlobalRestriction stage).f 0).hom
        pairBlockGlobalEndpointSection =
      pairBlockLocalEndpointSection stage := by
  have leftRestriction := LinearMap.congr_fun
    (globalBlockEndpointVertexMap_restriction stage) blockLeftEndpointBase
  have rightRestriction := LinearMap.congr_fun
    (globalBlockEndpointVertexMap_restriction stage) blockRightEndpointBase
  change
    (ModuleCat.extendScalars blockCoordinateToPairZeroFiber).map
          ((blockLinearGlobalRestriction (Opposite.op stage)).f 0)
          (universalLeftCoordinate installedOwner
            ⊗ₜ[BlockCoordinateRing, blockCoordinateToPairZeroFiber]
              globalBlockLeftEndpoint +
            universalRightCoordinate installedOwner
            ⊗ₜ[BlockCoordinateRing, blockCoordinateToPairZeroFiber]
              globalBlockRightEndpoint) = _
  rw [map_add, ModuleCat.ExtendScalars.map_tmul,
    ModuleCat.ExtendScalars.map_tmul]
  change
    universalLeftCoordinate installedOwner
          ⊗ₜ[BlockCoordinateRing, blockCoordinateToPairZeroFiber]
            ((blockLinearGlobalRestriction (Opposite.op stage)).f 0).hom
              globalBlockLeftEndpoint +
        universalRightCoordinate installedOwner
          ⊗ₜ[BlockCoordinateRing, blockCoordinateToPairZeroFiber]
            ((blockLinearGlobalRestriction (Opposite.op stage)).f 0).hom
              globalBlockRightEndpoint = _
  rw [show ((blockLinearGlobalRestriction (Opposite.op stage)).f 0).hom
      globalBlockLeftEndpoint =
        localBlockEndpointVertexMap stage blockLeftEndpointBase by
      exact leftRestriction,
    show ((blockLinearGlobalRestriction (Opposite.op stage)).f 0).hom
      globalBlockRightEndpoint =
        localBlockEndpointVertexMap stage blockRightEndpointBase by
      exact rightRestriction]
  rfl

def localBlockEndpointAntiInvariant (stage : Nat) :
    BlockInner seedOccurrence.root stage :=
  blockWholeAntiInvariantProjection stage
    (localBlockEndpointVertexMap stage blockLeftEndpointBase)

theorem localBlockRightEndpointAntiInvariant (stage : Nat) :
    blockWholeAntiInvariantProjection stage
        (localBlockEndpointVertexMap stage blockRightEndpointBase) =
      -localBlockEndpointAntiInvariant stage := by
  funext index
  rcases index with ⟨primeIndex, dualIndex⟩
  fin_cases dualIndex <;>
    simp [blockWholeAntiInvariantProjection,
      blockInnerAntiInvariant, blockInnerReversal,
      localBlockEndpointVertexMap, blockLeftEndpointBase,
      blockRightEndpointBase, localBlockEndpointAntiInvariant]

def localPairBlockActualEndpointDifference (stage : Nat) :
    (PairBlockLocalInnerSingle stage).X 0 :=
  (universalLeftCoordinate installedOwner -
      universalRightCoordinate installedOwner)
    ⊗ₜ[BlockCoordinateRing, blockCoordinateToPairZeroFiber]
      localBlockEndpointAntiInvariant stage

theorem pairBlockLocalEndpointSection_antiInvariant (stage : Nat) :
    ((pairBlockWholeAntiInvariantMap stage).f 0).hom
        (pairBlockLocalEndpointSection stage) =
      localPairBlockActualEndpointDifference stage := by
  letI : Module BlockCoordinateRing PairCoefficientRing :=
    Module.compHom PairCoefficientRing blockCoordinateToPairZeroFiber
  change
    (ModuleCat.extendScalars blockCoordinateToPairZeroFiber).map
          (ModuleCat.ofHom (blockWholeAntiInvariantProjection stage))
          (universalLeftCoordinate installedOwner
              ⊗ₜ[BlockCoordinateRing, blockCoordinateToPairZeroFiber]
                localBlockEndpointVertexMap stage blockLeftEndpointBase +
            universalRightCoordinate installedOwner
              ⊗ₜ[BlockCoordinateRing, blockCoordinateToPairZeroFiber]
                localBlockEndpointVertexMap stage blockRightEndpointBase) = _
  rw [map_add, ModuleCat.ExtendScalars.map_tmul,
    ModuleCat.ExtendScalars.map_tmul]
  change
    universalLeftCoordinate installedOwner
          ⊗ₜ[BlockCoordinateRing, blockCoordinateToPairZeroFiber]
            localBlockEndpointAntiInvariant stage +
        universalRightCoordinate installedOwner
          ⊗ₜ[BlockCoordinateRing, blockCoordinateToPairZeroFiber]
            blockWholeAntiInvariantProjection stage
              (localBlockEndpointVertexMap stage blockRightEndpointBase) = _
  unfold localPairBlockActualEndpointDifference
  rw [localBlockRightEndpointAntiInvariant,
    TensorProduct.tmul_neg, ← TensorProduct.neg_tmul,
    ← TensorProduct.add_tmul]
  rfl

/-! ## Literal cofiber element and readback -/

def pairBlockEndpointSourceReadback : PairBlockGlobalState.X 0 :=
  ((CochainComplex.mappingCocone.snd
      pairBlockGlobalEulerOperator).v 1 0 (by omega)).hom
    pairBlockEndpointCofiberElement

theorem pairBlockTautologicalInclusion_source_readback :
    pairBlockTautologicalInclusion.1.comp
        (CochainComplex.mappingCocone.snd
          pairBlockGlobalEulerOperator) (add_neg_cancel (1 : ℤ)) =
      CochainComplex.HomComplex.Cochain.ofHom
        (𝟙 PairBlockGlobalState) := by
  ext sourceDegree : 1
  simp [pairBlockTautologicalInclusion,
    CochainComplex.HomComplex.Cochain.comp_v]

@[reassoc] theorem pairBlockTautologicalInclusion_source_readback_v :
    pairBlockTautologicalInclusion.1.v 0 1 (by omega) ≫
        (CochainComplex.mappingCocone.snd
          pairBlockGlobalEulerOperator).v 1 0 (by omega) =
      𝟙 _ := by
  have equality := pairBlockTautologicalInclusion_source_readback
  exact CochainComplex.HomComplex.Cochain.congr_v equality 0 0 (by omega)

theorem pairBlockEndpointSourceReadback_eq_section :
    pairBlockEndpointSourceReadback = pairBlockGlobalEndpointSection := by
  exact ConcreteCategory.congr_hom
    pairBlockTautologicalInclusion_source_readback_v
    pairBlockGlobalEndpointSection

def localPairBlockTautologicalAntiInvariantReadback (stage : Nat) :
    (PairBlockLocalInnerSingle stage).X 0 :=
  ((pairBlockWholeAntiInvariantMap stage).f 0).hom
    (((pairBlockGlobalRestriction stage).f 0).hom
      pairBlockEndpointSourceReadback)

def localPairBlockEndpointAntiInvariantComponent (stage : Nat) :
    (PairBlockLocalInnerSingle stage).X 0 :=
  ((pairBlockWholeAntiInvariantMap stage).f 0).hom
    (((pairBlockGlobalRestriction stage).f 0).hom
      pairBlockGlobalEndpointSection)

theorem localPairBlockTautologicalAntiInvariantReadback_eq_component
    (stage : Nat) :
    localPairBlockTautologicalAntiInvariantReadback stage =
      localPairBlockEndpointAntiInvariantComponent stage := by
  unfold localPairBlockTautologicalAntiInvariantReadback
    localPairBlockEndpointAntiInvariantComponent
  rw [pairBlockEndpointSourceReadback_eq_section]

theorem localPairBlockTautologicalAntiInvariantReadback_eq_actual_difference
    (stage : Nat) :
    localPairBlockTautologicalAntiInvariantReadback stage =
      localPairBlockActualEndpointDifference stage := by
  rw [localPairBlockTautologicalAntiInvariantReadback_eq_component]
  unfold localPairBlockEndpointAntiInvariantComponent
  rw [pairBlockGlobalRestriction_endpointSection,
    pairBlockLocalEndpointSection_antiInvariant]

def pairBlockTautologicalReadbackOccurrence (stage : Nat) :
    RootedAccountedUnfolding
      (FactorizationPayload × (PairBlockLocalInnerSingle stage).X 0) :=
  seedOccurrence.map fun owner =>
    (owner, localPairBlockTautologicalAntiInvariantReadback stage)

theorem pairBlockTautologicalReadbackOccurrence_projects (stage : Nat) :
    (pairBlockTautologicalReadbackOccurrence stage).map Prod.fst =
      seedOccurrence := by
  unfold pairBlockTautologicalReadbackOccurrence
  rw [RootedAccountedUnfolding.map_map]
  change seedOccurrence.map id = seedOccurrence
  exact RootedAccountedUnfolding.map_id _

theorem preserves_same_cofiber_endpoint_local_component_and_actual_difference
    (stage : Nat) :
    pairBlockGlobalActionCofiberFace.root = seedOccurrence ∧
      (pairBlockTautologicalReadbackOccurrence stage).map Prod.fst =
        seedOccurrence ∧
      localPairBlockTautologicalAntiInvariantReadback stage =
        localPairBlockEndpointAntiInvariantComponent stage ∧
      localPairBlockTautologicalAntiInvariantReadback stage =
        localPairBlockActualEndpointDifference stage := by
  exact ⟨pairBlockGlobalActionCofiberFace.preserves_actual_transition.1,
    pairBlockTautologicalReadbackOccurrence_projects stage,
    localPairBlockTautologicalAntiInvariantReadback_eq_component stage,
    localPairBlockTautologicalAntiInvariantReadback_eq_actual_difference stage⟩

end
end CanonicalUnitArithmeticFactorizationFullEulerWholePrimeDualBlockAnalyticTautologicalReadback
end ConstructiveRoot
end LivingLawEvolution
end ResponsibilityLifecycle
end SaturationMonoid
