import H0mework.Versions.R2.Arithmetic.EulerDerived.AdjugateEndpointAtom
import H0mework.Realization.Completion.ProcessDiagram
import H0mework.Realization.GlobalSections.DerivedState

/-!
# Framework-generated cofinal derived solution of the whole block endpoint

The domain supplies the existing corrected endpoint fibre at one state and
its actual source successor.  The generic cofinal-process kernel generates
the complete diagram and the dependent-global-state kernel generates one
global derived solution.  The two endpoint atoms are then obtained by the
limit universal property.

No completed `Nat`-indexed diagram, determinant point, endpoint equality or
fixedness premise enters this producer.  The full whole/relation roles and
the mapped endpoint boundary remain present until downstream settlement.
-/

set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency false

namespace SaturationMonoid
namespace ResponsibilityLifecycle
namespace LivingLawEvolution
namespace ConstructiveRoot
namespace CanonicalUnitArithmeticFactorizationFullEulerWholePrimeDualBlockDerivedSolutionCofinal

open CategoryTheory
open CategoryTheory.Limits
open CofinalProcessDiagram
open CofinalProcessDiagram.RootGeneratedCofinalProcessDiagramAt
open DependentDerivedGlobalState
open DependentDerivedGlobalState.RootGeneratedDependentDerivedGlobalStateAt
open DerivedAdicCofiber
open CanonicalUnitArithmeticFactorizationEulerDependentDiagram
open CanonicalUnitArithmeticFactorizationFullEulerWholePrimeDualBlockFrame
open CanonicalUnitArithmeticFactorizationFullEulerWholePrimeDualBlockLinearGlobalEndpointSection
open CanonicalUnitArithmeticFactorizationFullEulerWholePrimeDualBlockWholeRelationDeterminant
open CanonicalUnitArithmeticFactorizationFullEulerWholePrimeDualBlockWholeComplexAdjugateTotalFiber
open CanonicalUnitArithmeticFactorizationFullEulerWholePrimeDualBlockWholeComplexAdjugateTotalFiberEndpointAtom
open CochainMappingCoconeDegreewiseKernel
open scoped ChangeOfRings

noncomputable section

abbrev LocalDerivedSolution (stage : Nat) :=
  CochainComplex.mappingCocone (localTotalInclusion stage)

abbrev BlockToIntegral :=
  ModuleCat.restrictScalars (Int.castRingHom BlockCoordinateRing)

abbrev BlockComplexToIntegral :=
  BlockToIntegral.mapHomologicalComplex (ComplexShape.up ℤ)

noncomputable abbrev UnderlyingLocalDerivedSolution (stage : Nat) :
    IntegralCochainComplex ℤ :=
  BlockComplexToIntegral.obj (LocalDerivedSolution stage)

noncomputable def underlyingDerivedSolutionRestriction (stage : Nat) :
    UnderlyingLocalDerivedSolution (stage + 1) ⟶
      UnderlyingLocalDerivedSolution stage :=
  BlockComplexToIntegral.map (localCorrectedEndpointRestriction stage)

def derivedSolutionProcess :
    CofinalDiagramSuccessorProcessAt
      (IntegralCochainComplex ℤ) where
  State := Nat
  seed := 0
  next := Nat.succ
  object := UnderlyingLocalDerivedSolution
  transition := underlyingDerivedSolutionRestriction

@[simp] theorem derivedSolutionProcess_stateAt (stage : Nat) :
    derivedSolutionProcess.stateAt stage = stage := by
  induction stage with
  | zero => rfl
  | succ stage inductionHypothesis =>
      change Nat.succ (derivedSolutionProcess.stateAt stage) = stage + 1
      rw [inductionHypothesis]

def derivedSolutionProcessOccurrence : RootedAccountedUnfolding
    (FactorizationPayload ×
      CofinalDiagramSuccessorProcessAt
        (IntegralCochainComplex ℤ)) :=
  seedOccurrence.map fun owner => (owner, derivedSolutionProcess)

theorem derivedSolutionProcessOccurrence_projects :
    derivedSolutionProcessOccurrence.map Prod.fst = seedOccurrence := by
  unfold derivedSolutionProcessOccurrence
  rw [RootedAccountedUnfolding.map_map]
  change seedOccurrence.map id = seedOccurrence
  exact RootedAccountedUnfolding.map_id _

@[simp] theorem derivedSolutionProcessOccurrence_process :
    derivedSolutionProcessOccurrence.root.2 = derivedSolutionProcess :=
  rfl

@[simp] theorem derivedSolutionProcess_stateAt_succ (stage : Nat) :
    derivedSolutionProcess.stateAt (stage + 1) =
      Nat.succ (derivedSolutionProcess.stateAt stage) :=
  rfl

@[simp] theorem derivedSolutionProcess_transitionAt (stage : Nat) :
    derivedSolutionProcess.transitionAt stage =
      underlyingDerivedSolutionRestriction
        (derivedSolutionProcess.stateAt stage) :=
  rfl

def derivedSolutionDiagramFace :
    RootGeneratedCofinalProcessDiagramAt seedOccurrence
      derivedSolutionProcessOccurrence
      derivedSolutionProcessOccurrence_projects :=
  RootGeneratedCofinalProcessDiagramAt.generate

theorem derivedSolutionDiagramFace_object (stage : Nat) :
    derivedSolutionDiagramFace.actualDiagram.obj (Opposite.op stage) =
      UnderlyingLocalDerivedSolution stage := by
  change UnderlyingLocalDerivedSolution
      (derivedSolutionProcess.stateAt stage) =
        UnderlyingLocalDerivedSolution stage
  rw [derivedSolutionProcess_stateAt]

theorem derivedSolutionDiagramFace_successor (stage : Nat) :
    derivedSolutionDiagramFace.actualDiagram.map
        ((homOfLE (Nat.le_succ stage)).op) =
      derivedSolutionDiagramFace.actualProcess.transitionAt stage :=
  derivedSolutionDiagramFace.actualDiagram_succ stage

def derivedSolutionDiagramOccurrence :=
  derivedSolutionDiagramFace.dependentDiagramOccurrence

theorem derivedSolutionDiagramOccurrence_projects :
    derivedSolutionDiagramOccurrence.map Prod.fst = seedOccurrence :=
  derivedSolutionDiagramFace.dependentDiagramOccurrence_projects

def globalDerivedSolutionFace :
    RootGeneratedDependentDerivedGlobalStateAt
      derivedSolutionDiagramOccurrence :=
  RootGeneratedDependentDerivedGlobalStateAt.generate

theorem globalDerivedSolution_actualDiagram :
    globalDerivedSolutionFace.actualDiagram =
      derivedSolutionDiagramFace.actualDiagram :=
  rfl

abbrev GlobalDerivedSolution := globalDerivedSolutionFace.globalState

noncomputable def globalDerivedSolutionRestriction (stage : Nat) :
    GlobalDerivedSolution ⟶ UnderlyingLocalDerivedSolution stage := by
  change limit derivedSolutionDiagramFace.actualDiagram ⟶
    UnderlyingLocalDerivedSolution stage
  exact limit.π derivedSolutionDiagramFace.actualDiagram
      (Opposite.op stage) ≫
    eqToHom (derivedSolutionDiagramFace_object stage)

theorem globalDerivedSolutionFace_projects :
    globalDerivedSolutionFace.root = seedOccurrence := by
  unfold RootGeneratedDependentDerivedGlobalStateAt.root
  exact derivedSolutionDiagramOccurrence_projects

/-! The existing endpoint atom is strictly natural as a map, not merely in
its two displayed coordinates. -/

theorem localCorrectedEndpointPoint_successor
    (stage : Nat)
    (endpoint : (LocalWholeComplex (stage + 1)).X 0) :
    localCorrectedEndpointPoint (stage + 1) endpoint ≫
        localCorrectedEndpointRestriction stage =
      localCorrectedEndpointPoint stage
        (((blockDirectRestriction seedOccurrence.root stage).f 0).hom
          endpoint) := by
  apply HomologicalComplex.from_single_hom_ext
  apply degree_hom_ext (localTotalInclusion stage) 1
  · exact congrArg (fun arrow => arrow.f 1)
      (localCorrectedEndpointPoint_successor_fst stage endpoint)
  · exact localCorrectedEndpointPoint_successor_snd stage endpoint

def localLeftEndpoint (stage : Nat) : (LocalWholeComplex stage).X 0 :=
  localBlockEndpointVertexMap stage blockLeftEndpointBase

def localRightEndpoint (stage : Nat) : (LocalWholeComplex stage).X 0 :=
  localBlockEndpointVertexMap stage blockRightEndpointBase

theorem localLeftEndpoint_successor (stage : Nat) :
    ((blockDirectRestriction seedOccurrence.root stage).f 0).hom
        (localLeftEndpoint (stage + 1)) = localLeftEndpoint stage := by
  exact LinearMap.congr_fun
    (localBlockEndpointVertexMap_successor stage) blockLeftEndpointBase

theorem localRightEndpoint_successor (stage : Nat) :
    ((blockDirectRestriction seedOccurrence.root stage).f 0).hom
        (localRightEndpoint (stage + 1)) = localRightEndpoint stage := by
  exact LinearMap.congr_fun
    (localBlockEndpointVertexMap_successor stage) blockRightEndpointBase

noncomputable def localLeftDerivedPoint (stage : Nat) :
    CochainMappingCoconeMappedBoundaryAtomOver.ScalarSingleOne
        (R := BlockCoordinateRing) ⟶ LocalDerivedSolution stage :=
  localCorrectedEndpointPoint stage (localLeftEndpoint stage)

noncomputable def localRightDerivedPoint (stage : Nat) :
    CochainMappingCoconeMappedBoundaryAtomOver.ScalarSingleOne
        (R := BlockCoordinateRing) ⟶ LocalDerivedSolution stage :=
  localCorrectedEndpointPoint stage (localRightEndpoint stage)

theorem localLeftDerivedPoint_successor (stage : Nat) :
    localLeftDerivedPoint (stage + 1) ≫
        localCorrectedEndpointRestriction stage =
      localLeftDerivedPoint stage := by
  rw [localLeftDerivedPoint, localLeftDerivedPoint,
    localCorrectedEndpointPoint_successor,
    localLeftEndpoint_successor]

theorem localRightDerivedPoint_successor (stage : Nat) :
    localRightDerivedPoint (stage + 1) ≫
        localCorrectedEndpointRestriction stage =
      localRightDerivedPoint stage := by
  rw [localRightDerivedPoint, localRightDerivedPoint,
    localCorrectedEndpointPoint_successor,
    localRightEndpoint_successor]

noncomputable abbrev UnderlyingScalarSingleOne : IntegralCochainComplex ℤ :=
  BlockComplexToIntegral.obj
    (CochainMappingCoconeMappedBoundaryAtomOver.ScalarSingleOne
      (R := BlockCoordinateRing))

noncomputable def underlyingLocalLeftDerivedPoint (stage : Nat) :
    UnderlyingScalarSingleOne ⟶ UnderlyingLocalDerivedSolution stage :=
  BlockComplexToIntegral.map (localLeftDerivedPoint stage)

noncomputable def underlyingLocalRightDerivedPoint (stage : Nat) :
    UnderlyingScalarSingleOne ⟶ UnderlyingLocalDerivedSolution stage :=
  BlockComplexToIntegral.map (localRightDerivedPoint stage)

theorem underlyingLocalLeftDerivedPoint_successor (stage : Nat) :
    underlyingLocalLeftDerivedPoint (stage + 1) ≫
        underlyingDerivedSolutionRestriction stage =
      underlyingLocalLeftDerivedPoint stage := by
  unfold underlyingLocalLeftDerivedPoint
    underlyingDerivedSolutionRestriction
  rw [← Functor.map_comp, localLeftDerivedPoint_successor]

theorem underlyingLocalRightDerivedPoint_successor (stage : Nat) :
    underlyingLocalRightDerivedPoint (stage + 1) ≫
        underlyingDerivedSolutionRestriction stage =
      underlyingLocalRightDerivedPoint stage := by
  unfold underlyingLocalRightDerivedPoint
    underlyingDerivedSolutionRestriction
  rw [← Functor.map_comp, localRightDerivedPoint_successor]

noncomputable def generatedLocalLeftDerivedPoint (stage : Nat) :
    UnderlyingScalarSingleOne ⟶
      derivedSolutionDiagramFace.actualDiagram.obj (Opposite.op stage) :=
  underlyingLocalLeftDerivedPoint
      (derivedSolutionProcess.stateAt stage) ≫
    eqToHom (derivedSolutionDiagramFace.actualDiagram_obj stage).symm

noncomputable def generatedLocalRightDerivedPoint (stage : Nat) :
    UnderlyingScalarSingleOne ⟶
      derivedSolutionDiagramFace.actualDiagram.obj (Opposite.op stage) :=
  underlyingLocalRightDerivedPoint
      (derivedSolutionProcess.stateAt stage) ≫
    eqToHom (derivedSolutionDiagramFace.actualDiagram_obj stage).symm

theorem generatedLocalLeftDerivedPoint_successor (stage : Nat) :
    generatedLocalLeftDerivedPoint stage =
      generatedLocalLeftDerivedPoint (stage + 1) ≫
        derivedSolutionDiagramFace.actualDiagram.map
          ((homOfLE (Nat.le_succ stage)).op) := by
  rw [derivedSolutionDiagramFace_successor]
  unfold generatedLocalLeftDerivedPoint
  simp only [RootGeneratedCofinalProcessDiagramAt.actualDiagram_obj,
    eqToHom_refl, Category.comp_id,
    RootGeneratedCofinalProcessDiagramAt.actualProcess,
    derivedSolutionDiagramFace,
    derivedSolutionProcessOccurrence_process,
    derivedSolutionProcess_stateAt_succ]
  change underlyingLocalLeftDerivedPoint
      (derivedSolutionProcess.stateAt stage) =
    underlyingLocalLeftDerivedPoint
        (Nat.succ (derivedSolutionProcess.stateAt stage)) ≫
      underlyingDerivedSolutionRestriction
        (derivedSolutionProcess.stateAt stage)
  simpa only [Nat.succ_eq_add_one] using
    (underlyingLocalLeftDerivedPoint_successor
      (derivedSolutionProcess.stateAt stage)).symm

theorem generatedLocalRightDerivedPoint_successor (stage : Nat) :
    generatedLocalRightDerivedPoint stage =
      generatedLocalRightDerivedPoint (stage + 1) ≫
        derivedSolutionDiagramFace.actualDiagram.map
          ((homOfLE (Nat.le_succ stage)).op) := by
  rw [derivedSolutionDiagramFace_successor]
  unfold generatedLocalRightDerivedPoint
  simp only [RootGeneratedCofinalProcessDiagramAt.actualDiagram_obj,
    eqToHom_refl, Category.comp_id,
    RootGeneratedCofinalProcessDiagramAt.actualProcess,
    derivedSolutionDiagramFace,
    derivedSolutionProcessOccurrence_process,
    derivedSolutionProcess_stateAt_succ]
  change underlyingLocalRightDerivedPoint
      (derivedSolutionProcess.stateAt stage) =
    underlyingLocalRightDerivedPoint
        (Nat.succ (derivedSolutionProcess.stateAt stage)) ≫
      underlyingDerivedSolutionRestriction
        (derivedSolutionProcess.stateAt stage)
  simpa only [Nat.succ_eq_add_one] using
    (underlyingLocalRightDerivedPoint_successor
      (derivedSolutionProcess.stateAt stage)).symm

noncomputable def globalLeftDerivedPointCone :
    Cone derivedSolutionDiagramFace.actualDiagram where
  pt := UnderlyingScalarSingleOne
  π := NatTrans.ofOpSequence generatedLocalLeftDerivedPoint
    (fun stage => by
      simpa only [Functor.const_obj_map] using
        (Category.id_comp (generatedLocalLeftDerivedPoint stage)).trans
          (generatedLocalLeftDerivedPoint_successor stage))

noncomputable def globalRightDerivedPointCone :
    Cone derivedSolutionDiagramFace.actualDiagram where
  pt := UnderlyingScalarSingleOne
  π := NatTrans.ofOpSequence generatedLocalRightDerivedPoint
    (fun stage => by
      simpa only [Functor.const_obj_map] using
        (Category.id_comp (generatedLocalRightDerivedPoint stage)).trans
          (generatedLocalRightDerivedPoint_successor stage))

noncomputable def globalLeftDerivedPoint :
    UnderlyingScalarSingleOne ⟶ GlobalDerivedSolution := by
  change UnderlyingScalarSingleOne ⟶
    limit derivedSolutionDiagramFace.actualDiagram
  exact limit.lift derivedSolutionDiagramFace.actualDiagram
    globalLeftDerivedPointCone

noncomputable def globalRightDerivedPoint :
    UnderlyingScalarSingleOne ⟶ GlobalDerivedSolution := by
  change UnderlyingScalarSingleOne ⟶
    limit derivedSolutionDiagramFace.actualDiagram
  exact limit.lift derivedSolutionDiagramFace.actualDiagram
    globalRightDerivedPointCone

noncomputable def globalDerivedAntiInvariantPoint :
    UnderlyingScalarSingleOne ⟶ GlobalDerivedSolution :=
  globalLeftDerivedPoint - globalRightDerivedPoint

theorem globalLeftDerivedPoint_restriction_raw (stage : Nat) :
    globalLeftDerivedPoint ≫
        limit.π derivedSolutionDiagramFace.actualDiagram
          (Opposite.op stage) =
      underlyingLocalLeftDerivedPoint
        (derivedSolutionProcess.stateAt stage) := by
  exact limit.lift_π globalLeftDerivedPointCone (Opposite.op stage)

theorem globalRightDerivedPoint_restriction_raw (stage : Nat) :
    globalRightDerivedPoint ≫
        limit.π derivedSolutionDiagramFace.actualDiagram
          (Opposite.op stage) =
      underlyingLocalRightDerivedPoint
        (derivedSolutionProcess.stateAt stage) := by
  exact limit.lift_π globalRightDerivedPointCone (Opposite.op stage)

theorem globalDerivedAntiInvariantPoint_restriction_raw (stage : Nat) :
    globalDerivedAntiInvariantPoint ≫
        limit.π derivedSolutionDiagramFace.actualDiagram
          (Opposite.op stage) =
      underlyingLocalLeftDerivedPoint
          (derivedSolutionProcess.stateAt stage) -
        underlyingLocalRightDerivedPoint
          (derivedSolutionProcess.stateAt stage) := by
  unfold globalDerivedAntiInvariantPoint
  rw [Preadditive.sub_comp,
    globalLeftDerivedPoint_restriction_raw,
    globalRightDerivedPoint_restriction_raw]

theorem preserves_exact_root_generated_derived_solution_and_endpoints :
    globalDerivedSolutionFace.root = seedOccurrence ∧
      (∀ stage,
        globalLeftDerivedPoint ≫
            limit.π derivedSolutionDiagramFace.actualDiagram
              (Opposite.op stage) =
          underlyingLocalLeftDerivedPoint
            (derivedSolutionProcess.stateAt stage)) ∧
      (∀ stage,
        globalRightDerivedPoint ≫
            limit.π derivedSolutionDiagramFace.actualDiagram
              (Opposite.op stage) =
          underlyingLocalRightDerivedPoint
            (derivedSolutionProcess.stateAt stage)) :=
  ⟨globalDerivedSolutionFace_projects,
    globalLeftDerivedPoint_restriction_raw,
    globalRightDerivedPoint_restriction_raw⟩

end
end CanonicalUnitArithmeticFactorizationFullEulerWholePrimeDualBlockDerivedSolutionCofinal
end ConstructiveRoot
end LivingLawEvolution
end ResponsibilityLifecycle
end SaturationMonoid
