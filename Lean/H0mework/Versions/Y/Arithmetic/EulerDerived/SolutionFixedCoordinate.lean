import H0mework.Versions.Y.Arithmetic.EulerDerived.SolutionSpecialization
import H0mework.Versions.Y.Arithmetic.EulerDualBlock.EndpointFixedCoordinateReadback

set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false

namespace SaturationMonoid
namespace ResponsibilityLifecycle
namespace LivingLawEvolution
namespace ConstructiveRoot
namespace CanonicalUnitArithmeticFactorizationFullEulerWholePrimeDualBlockDerivedSolutionFixedCoordinateReadback

open CategoryTheory
open CategoryTheory.Limits
open CanonicalUnitArithmeticCoordinateProjectionObstruction
open CanonicalUnitArithmeticFactorizationEulerDependentDiagram
open CanonicalUnitArithmeticDualReadouts
open CanonicalUnitArithmeticFactorizationWholeHistorySolutionCarrier
open CanonicalUnitArithmeticFactorizationFullEulerWholePrimeDualBlockFrame
open CanonicalUnitArithmeticFactorizationFullEulerWholePrimeDualBlockAnalyticGlobalActionCofiber
open CanonicalUnitArithmeticFactorizationFullEulerWholePrimeDualBlockDerivedSolutionCofinal
open CanonicalUnitArithmeticFactorizationFullEulerWholePrimeDualBlockDerivedSolutionPointSpecialization
open CanonicalUnitArithmeticFactorizationFullEulerWholePrimeDualBlockWholeComplexAdjugateTotalFiber
open CanonicalUnitArithmeticFactorizationFullEulerWholePrimeDualBlockWholeComplexAdjugateTotalFiberEndpointAtom
open CanonicalUnitArithmeticFactorizationFullEulerWholePrimeDualBlockWholeComplexAdjugate
open CanonicalUnitArithmeticFactorizationWholePrimeDualBlockGlobalComplexDeterminantLine
open CanonicalUnitArithmeticFactorizationWholePrimeDualBlockGlobalComplexDeterminantLineDerivedSpecialization
open CanonicalUnitArithmeticFactorizationWholePrimeDualBlockEndpointFixedCoordinateReadback
open CanonicalUnitArithmeticFactorizationWholePrimeDualBlockDeterminantLineCoordinate
open CochainMappingCoconeDeterminantAdjugateTotalFiber
open CochainMappingCoconeMappedBoundaryAtomOver
open scoped ChangeOfRings TensorProduct

noncomputable section

local instance pairCoefficientModule :
    Module BlockCoordinateRing PairCoefficientRing :=
  Module.compHom PairCoefficientRing blockCoordinateToPairZeroFiber

def blockScalarSingleOneGenerator :
    (ScalarSingleOne (R := BlockCoordinateRing)).X 1 := by
  exact (HomologicalComplex.singleObjXSelf
    (ComplexShape.up ℤ) 1
      (ScalarUnit (R := BlockCoordinateRing))).inv.hom 1

theorem blockScalarSingleOneGenerator_eq_one :
    blockScalarSingleOneGenerator = (1 : BlockCoordinateRing) :=
  rfl

noncomputable def totalEndpointProjection (stage : Nat) :
    LocalTotalFiber stage ⟶ LocalWholeComplex stage :=
  CochainComplex.mappingCocone.fst
      (totalRow (blockDirectEulerOperator stage)
        (blockDirectDeterminantMultiplication stage)) ≫
    biprod.snd

def blockWholeEndpointCoordinate (stage : Nat)
    (row : FactorRow seedOccurrence.root stage) :
    (LocalWholeComplex stage).X 0 →ₗ[BlockCoordinateRing]
      BlockCoordinateRing where
  toFun value := value none (row.1, 0)
  map_add' _left _right := rfl
  map_smul' _scalar _value := rfl

def localDerivedEndpointReadback (stage : Nat)
    (row : FactorRow seedOccurrence.root stage) :
    (LocalDerivedSolution stage).X 1 →ₗ[BlockCoordinateRing]
      BlockCoordinateRing :=
  -((blockWholeEndpointCoordinate stage row).comp
    (((totalEndpointProjection stage).f 0).hom.comp
      ((CochainComplex.mappingCocone.snd
        (localTotalInclusion stage)).v 1 0 (by omega)).hom))

@[simp] theorem blockWholeEndpointCoordinate_left (stage : Nat)
    (row : FactorRow seedOccurrence.root stage) :
    blockWholeEndpointCoordinate stage row (localLeftEndpoint stage) = 1 := by
  rfl

@[simp] theorem blockWholeEndpointCoordinate_right (stage : Nat)
    (row : FactorRow seedOccurrence.root stage) :
    blockWholeEndpointCoordinate stage row (localRightEndpoint stage) = 0 := by
  rfl

theorem localDerivedEndpointReadback_left (stage : Nat)
    (row : FactorRow seedOccurrence.root stage) :
    localDerivedEndpointReadback stage row
        ((localLeftDerivedPoint stage).f 1 blockScalarSingleOneGenerator) = 1 := by
  have sndOne := localCorrectedEndpointPoint_snd_one stage
    (localLeftEndpoint stage)
  change (((localLeftDerivedPoint stage).f 1 ≫
      (CochainComplex.mappingCocone.snd
        (localTotalInclusion stage)).v 1 0 (by omega)).hom
        blockScalarSingleOneGenerator) =
      -localTotalEndpointElement stage (localLeftEndpoint stage) at sndOne
  have sndApplied :
      ((CochainComplex.mappingCocone.snd
          (localTotalInclusion stage)).v 1 0 (by omega)).hom
        ((localLeftDerivedPoint stage).f 1 blockScalarSingleOneGenerator) =
      -localTotalEndpointElement stage (localLeftEndpoint stage) := by
    simpa only [ConcreteCategory.comp_apply] using sndOne
  unfold localDerivedEndpointReadback
  change -blockWholeEndpointCoordinate stage row
      (((totalEndpointProjection stage).f 0).hom
        (((CochainComplex.mappingCocone.snd
          (localTotalInclusion stage)).v 1 0 (by omega)).hom
          ((localLeftDerivedPoint stage).f 1 blockScalarSingleOneGenerator))) = 1
  rw [sndApplied]
  rw [map_neg, map_neg]
  rw [neg_neg]
  change blockWholeEndpointCoordinate stage row
      (localTotalEndpointReadback stage (localLeftEndpoint stage)) = 1
  rw [localTotalEndpointReadback_eq,
    blockWholeEndpointCoordinate_left]

theorem localDerivedEndpointReadback_right (stage : Nat)
    (row : FactorRow seedOccurrence.root stage) :
    localDerivedEndpointReadback stage row
        ((localRightDerivedPoint stage).f 1 blockScalarSingleOneGenerator) = 0 := by
  have sndOne := localCorrectedEndpointPoint_snd_one stage
    (localRightEndpoint stage)
  change (((localRightDerivedPoint stage).f 1 ≫
      (CochainComplex.mappingCocone.snd
        (localTotalInclusion stage)).v 1 0 (by omega)).hom
        blockScalarSingleOneGenerator) =
      -localTotalEndpointElement stage (localRightEndpoint stage) at sndOne
  have sndApplied :
      ((CochainComplex.mappingCocone.snd
          (localTotalInclusion stage)).v 1 0 (by omega)).hom
        ((localRightDerivedPoint stage).f 1 blockScalarSingleOneGenerator) =
      -localTotalEndpointElement stage (localRightEndpoint stage) := by
    simpa only [ConcreteCategory.comp_apply] using sndOne
  unfold localDerivedEndpointReadback
  change -blockWholeEndpointCoordinate stage row
      (((totalEndpointProjection stage).f 0).hom
        (((CochainComplex.mappingCocone.snd
          (localTotalInclusion stage)).v 1 0 (by omega)).hom
          ((localRightDerivedPoint stage).f 1 blockScalarSingleOneGenerator))) = 0
  rw [sndApplied]
  rw [map_neg, map_neg]
  rw [neg_neg]
  change blockWholeEndpointCoordinate stage row
      (localTotalEndpointReadback stage (localRightEndpoint stage)) = 0
  rw [localTotalEndpointReadback_eq,
    blockWholeEndpointCoordinate_right]

noncomputable def blockGlobalToLocalDerivedSolution (stage : Nat) :
    BlockGlobalDerivedSolution ⟶ LocalDerivedSolution stage :=
  limit.π blockDerivedSolutionDiagramFace.actualDiagram
      (Opposite.op stage) ≫
    eqToHom (blockDerivedSolutionDiagramFace_object stage)

theorem localLeftDerivedPoint_cast {source target : Nat}
    (equality : source = target) :
    localLeftDerivedPoint source ≫
        eqToHom (congrArg LocalDerivedSolution equality) =
      localLeftDerivedPoint target := by
  subst target
  simp

theorem localRightDerivedPoint_cast {source target : Nat}
    (equality : source = target) :
    localRightDerivedPoint source ≫
        eqToHom (congrArg LocalDerivedSolution equality) =
      localRightDerivedPoint target := by
  subst target
  simp

def blockGlobalDerivedEndpointReadback (stage : Nat)
    (row : FactorRow seedOccurrence.root stage) :
    (BlockGlobalDerivedSolution.X 1 : Type) →ₗ[BlockCoordinateRing]
      BlockCoordinateRing :=
  (localDerivedEndpointReadback stage row).comp
    ((blockGlobalToLocalDerivedSolution stage).f 1).hom

theorem blockGlobalLeftDerivedPoint_restriction_local (stage : Nat) :
    blockGlobalLeftDerivedPoint ≫
        blockGlobalToLocalDerivedSolution stage =
      localLeftDerivedPoint stage := by
  unfold blockGlobalToLocalDerivedSolution
  calc
    blockGlobalLeftDerivedPoint ≫
        (limit.π blockDerivedSolutionDiagramFace.actualDiagram
          (Opposite.op stage) ≫
            eqToHom (blockDerivedSolutionDiagramFace_object stage)) =
      (blockGlobalLeftDerivedPoint ≫
          limit.π blockDerivedSolutionDiagramFace.actualDiagram
            (Opposite.op stage)) ≫
        eqToHom (blockDerivedSolutionDiagramFace_object stage) :=
      (Category.assoc _ _ _).symm
    _ = generatedBlockLocalLeftDerivedPoint stage ≫
        eqToHom (blockDerivedSolutionDiagramFace_object stage) := by
      rw [blockGlobalLeftDerivedPoint_restriction]
    _ = localLeftDerivedPoint stage := by
      unfold generatedBlockLocalLeftDerivedPoint
      rw [Category.assoc, eqToHom_trans]
      let equality := blockDerivedSolutionProcess_stateAt stage
      have proofEquality :
          (blockDerivedSolutionDiagramFace.actualDiagram_obj stage).symm.trans
              (blockDerivedSolutionDiagramFace_object stage) =
            congrArg LocalDerivedSolution equality :=
        Subsingleton.elim _ _
      rw [proofEquality]
      exact localLeftDerivedPoint_cast equality

theorem blockGlobalRightDerivedPoint_restriction_local (stage : Nat) :
    blockGlobalRightDerivedPoint ≫
        blockGlobalToLocalDerivedSolution stage =
      localRightDerivedPoint stage := by
  unfold blockGlobalToLocalDerivedSolution
  calc
    blockGlobalRightDerivedPoint ≫
        (limit.π blockDerivedSolutionDiagramFace.actualDiagram
          (Opposite.op stage) ≫
            eqToHom (blockDerivedSolutionDiagramFace_object stage)) =
      (blockGlobalRightDerivedPoint ≫
          limit.π blockDerivedSolutionDiagramFace.actualDiagram
            (Opposite.op stage)) ≫
        eqToHom (blockDerivedSolutionDiagramFace_object stage) :=
      (Category.assoc _ _ _).symm
    _ = generatedBlockLocalRightDerivedPoint stage ≫
        eqToHom (blockDerivedSolutionDiagramFace_object stage) := by
      rw [blockGlobalRightDerivedPoint_restriction]
    _ = localRightDerivedPoint stage := by
      unfold generatedBlockLocalRightDerivedPoint
      rw [Category.assoc, eqToHom_trans]
      let equality := blockDerivedSolutionProcess_stateAt stage
      have proofEquality :
          (blockDerivedSolutionDiagramFace.actualDiagram_obj stage).symm.trans
              (blockDerivedSolutionDiagramFace_object stage) =
            congrArg LocalDerivedSolution equality :=
        Subsingleton.elim _ _
      rw [proofEquality]
      exact localRightDerivedPoint_cast equality

theorem blockGlobalDerivedEndpointReadback_left (stage : Nat)
    (row : FactorRow seedOccurrence.root stage) :
    blockGlobalDerivedEndpointReadback stage row
        ((blockGlobalLeftDerivedPoint.f 1).hom
          blockScalarSingleOneGenerator) = 1 := by
  have restriction := congrArg (fun arrow => arrow.f 1)
    (blockGlobalLeftDerivedPoint_restriction_local stage)
  have evaluated := ConcreteCategory.congr_hom restriction
    blockScalarSingleOneGenerator
  change (((blockGlobalToLocalDerivedSolution stage).f 1).hom
      ((blockGlobalLeftDerivedPoint.f 1).hom
        blockScalarSingleOneGenerator)) =
    ((localLeftDerivedPoint stage).f 1).hom
      blockScalarSingleOneGenerator at evaluated
  change localDerivedEndpointReadback stage row
      (((blockGlobalToLocalDerivedSolution stage).f 1).hom
        ((blockGlobalLeftDerivedPoint.f 1).hom
          blockScalarSingleOneGenerator)) = 1
  rw [evaluated]
  change localDerivedEndpointReadback stage row
      ((localLeftDerivedPoint stage).f 1 blockScalarSingleOneGenerator) = 1
  exact localDerivedEndpointReadback_left stage row

theorem blockGlobalDerivedEndpointReadback_right (stage : Nat)
    (row : FactorRow seedOccurrence.root stage) :
    blockGlobalDerivedEndpointReadback stage row
        ((blockGlobalRightDerivedPoint.f 1).hom
          blockScalarSingleOneGenerator) = 0 := by
  have restriction := congrArg (fun arrow => arrow.f 1)
    (blockGlobalRightDerivedPoint_restriction_local stage)
  have evaluated := ConcreteCategory.congr_hom restriction
    blockScalarSingleOneGenerator
  change (((blockGlobalToLocalDerivedSolution stage).f 1).hom
      ((blockGlobalRightDerivedPoint.f 1).hom
        blockScalarSingleOneGenerator)) =
    ((localRightDerivedPoint stage).f 1).hom
      blockScalarSingleOneGenerator at evaluated
  change localDerivedEndpointReadback stage row
      (((blockGlobalToLocalDerivedSolution stage).f 1).hom
        ((blockGlobalRightDerivedPoint.f 1).hom
          blockScalarSingleOneGenerator)) = 0
  rw [evaluated]
  change localDerivedEndpointReadback stage row
      ((localRightDerivedPoint stage).f 1 blockScalarSingleOneGenerator) = 0
  exact localDerivedEndpointReadback_right stage row

noncomputable def pairGlobalDerivedDegreeOneEquiv :
    (PairGlobalDerivedSolution.X 1 : Type) ≃ₗ[PairCoefficientRing]
      PairCoefficientRing ⊗[BlockCoordinateRing]
        (BlockGlobalDerivedSolution.X 1 : Type) :=
  LinearEquiv.refl PairCoefficientRing _

@[simp] theorem pairGlobalDerivedDegreeOneEquiv_tmul
    (coefficient : PairCoefficientRing)
    (value : BlockGlobalDerivedSolution.X 1) :
    pairGlobalDerivedDegreeOneEquiv
        (coefficient ⊗ₜ[BlockCoordinateRing] value) =
      coefficient ⊗ₜ[BlockCoordinateRing] value :=
  rfl

noncomputable def pairGlobalDerivedEndpointReadback (stage : Nat)
    (row : FactorRow seedOccurrence.root stage) :
    (PairGlobalDerivedSolution.X 1 : Type) →ₗ[PairCoefficientRing]
      PairCoefficientRing := by
  letI : Algebra BlockCoordinateRing PairCoefficientRing :=
    blockCoordinateToPairZeroFiber.toAlgebra
  exact (TensorProduct.AlgebraTensorModule.rid BlockCoordinateRing
      PairCoefficientRing PairCoefficientRing).toLinearMap.comp
    (((blockGlobalDerivedEndpointReadback stage row).baseChange
      PairCoefficientRing).comp pairGlobalDerivedDegreeOneEquiv.toLinearMap)

noncomputable def pairDerivedScalarSingleOneGenerator :
    (PairDerivedScalarSingleOne.X 1 : Type) := by
  change PairCoefficientRing ⊗[BlockCoordinateRing]
    (ScalarSingleOne (R := BlockCoordinateRing)).X 1
  exact (1 : PairCoefficientRing) ⊗ₜ[BlockCoordinateRing]
    blockScalarSingleOneGenerator

def pairDerivedPointEndpointReadback (stage : Nat)
    (row : FactorRow seedOccurrence.root stage)
    (point : PairDerivedScalarSingleOne ⟶ PairGlobalDerivedSolution) :
    PairCoefficientRing :=
  pairGlobalDerivedEndpointReadback stage row
    ((point.f 1).hom pairDerivedScalarSingleOneGenerator)

theorem pairGlobalLeftDerivedPoint_generator :
    (pairGlobalLeftDerivedPoint.f 1).hom
        pairDerivedScalarSingleOneGenerator =
      (1 : PairCoefficientRing) ⊗ₜ[BlockCoordinateRing]
        ((blockGlobalLeftDerivedPoint.f 1).hom
          blockScalarSingleOneGenerator) := by
  change
    (ModuleCat.extendScalars blockCoordinateToPairZeroFiber).map
        (blockGlobalLeftDerivedPoint.f 1)
        ((1 : PairCoefficientRing) ⊗ₜ[BlockCoordinateRing]
          blockScalarSingleOneGenerator) = _
  rw [ModuleCat.ExtendScalars.map_tmul]

theorem pairGlobalRightDerivedPoint_generator :
    (pairGlobalRightDerivedPoint.f 1).hom
        pairDerivedScalarSingleOneGenerator =
      (1 : PairCoefficientRing) ⊗ₜ[BlockCoordinateRing]
        ((blockGlobalRightDerivedPoint.f 1).hom
          blockScalarSingleOneGenerator) := by
  change
    (ModuleCat.extendScalars blockCoordinateToPairZeroFiber).map
        (blockGlobalRightDerivedPoint.f 1)
        ((1 : PairCoefficientRing) ⊗ₜ[BlockCoordinateRing]
          blockScalarSingleOneGenerator) = _
  rw [ModuleCat.ExtendScalars.map_tmul]

theorem pairGlobalDerivedDegreeOneEquiv_left_generator :
    pairGlobalDerivedDegreeOneEquiv
        ((pairGlobalLeftDerivedPoint.f 1).hom
          pairDerivedScalarSingleOneGenerator) =
      (1 : PairCoefficientRing) ⊗ₜ[BlockCoordinateRing]
        ((blockGlobalLeftDerivedPoint.f 1).hom
          blockScalarSingleOneGenerator) := by
  rw [pairGlobalLeftDerivedPoint_generator]
  exact pairGlobalDerivedDegreeOneEquiv_tmul _ _

theorem pairGlobalDerivedDegreeOneEquiv_right_generator :
    pairGlobalDerivedDegreeOneEquiv
        ((pairGlobalRightDerivedPoint.f 1).hom
          pairDerivedScalarSingleOneGenerator) =
      (1 : PairCoefficientRing) ⊗ₜ[BlockCoordinateRing]
        ((blockGlobalRightDerivedPoint.f 1).hom
          blockScalarSingleOneGenerator) := by
  rw [pairGlobalRightDerivedPoint_generator]
  exact pairGlobalDerivedDegreeOneEquiv_tmul _ _

theorem pairGlobalDerivedEndpointReadback_left (stage : Nat)
    (row : FactorRow seedOccurrence.root stage) :
    pairDerivedPointEndpointReadback stage row
        pairGlobalLeftDerivedPoint = 1 := by
  letI : Algebra BlockCoordinateRing PairCoefficientRing :=
    blockCoordinateToPairZeroFiber.toAlgebra
  unfold pairDerivedPointEndpointReadback
  unfold pairGlobalDerivedEndpointReadback
  simp only [LinearMap.comp_apply, LinearEquiv.coe_toLinearMap]
  rw [pairGlobalDerivedDegreeOneEquiv_left_generator]
  rw [LinearMap.baseChange_tmul,
    TensorProduct.AlgebraTensorModule.rid_tmul,
    blockGlobalDerivedEndpointReadback_left]
  simp

theorem pairGlobalDerivedEndpointReadback_right (stage : Nat)
    (row : FactorRow seedOccurrence.root stage) :
    pairDerivedPointEndpointReadback stage row
        pairGlobalRightDerivedPoint = 0 := by
  letI : Algebra BlockCoordinateRing PairCoefficientRing :=
    blockCoordinateToPairZeroFiber.toAlgebra
  unfold pairDerivedPointEndpointReadback
  unfold pairGlobalDerivedEndpointReadback
  simp only [LinearMap.comp_apply, LinearEquiv.coe_toLinearMap]
  rw [pairGlobalDerivedDegreeOneEquiv_right_generator]
  rw [LinearMap.baseChange_tmul,
    TensorProduct.AlgebraTensorModule.rid_tmul,
    blockGlobalDerivedEndpointReadback_right]
  simp

theorem pairUniversalDerivedPoint_readback (stage : Nat)
    (row : FactorRow seedOccurrence.root stage) :
    pairDerivedPointEndpointReadback stage row pairUniversalDerivedPoint =
      universalLeftCoordinate installedOwner := by
  unfold pairDerivedPointEndpointReadback pairUniversalDerivedPoint
  change pairGlobalDerivedEndpointReadback stage row
      (universalLeftCoordinate installedOwner •
          (pairGlobalLeftDerivedPoint.f 1).hom
            pairDerivedScalarSingleOneGenerator +
        universalRightCoordinate installedOwner •
          (pairGlobalRightDerivedPoint.f 1).hom
            pairDerivedScalarSingleOneGenerator) = _
  have left := pairGlobalDerivedEndpointReadback_left stage row
  have right := pairGlobalDerivedEndpointReadback_right stage row
  change pairGlobalDerivedEndpointReadback stage row
      ((pairGlobalLeftDerivedPoint.f 1).hom
        pairDerivedScalarSingleOneGenerator) = 1 at left
  change pairGlobalDerivedEndpointReadback stage row
      ((pairGlobalRightDerivedPoint.f 1).hom
        pairDerivedScalarSingleOneGenerator) = 0 at right
  rw [map_add, map_smul, map_smul, left, right,
    smul_eq_mul, mul_one, smul_zero, add_zero]

theorem pairReversedUniversalDerivedPoint_readback (stage : Nat)
    (row : FactorRow seedOccurrence.root stage) :
    pairDerivedPointEndpointReadback stage row
        pairReversedUniversalDerivedPoint =
      universalRightCoordinate installedOwner := by
  unfold pairDerivedPointEndpointReadback pairReversedUniversalDerivedPoint
  change pairGlobalDerivedEndpointReadback stage row
      (universalRightCoordinate installedOwner •
          (pairGlobalLeftDerivedPoint.f 1).hom
            pairDerivedScalarSingleOneGenerator +
        universalLeftCoordinate installedOwner •
          (pairGlobalRightDerivedPoint.f 1).hom
            pairDerivedScalarSingleOneGenerator) = _
  have left := pairGlobalDerivedEndpointReadback_left stage row
  have right := pairGlobalDerivedEndpointReadback_right stage row
  change pairGlobalDerivedEndpointReadback stage row
      ((pairGlobalLeftDerivedPoint.f 1).hom
        pairDerivedScalarSingleOneGenerator) = 1 at left
  change pairGlobalDerivedEndpointReadback stage row
      ((pairGlobalRightDerivedPoint.f 1).hom
        pairDerivedScalarSingleOneGenerator) = 0 at right
  rw [map_add, map_smul, map_smul, left, right,
    smul_eq_mul, mul_one, smul_zero, add_zero]

noncomputable def pointGlobalDerivedEndpointReadback
    (point : DeterminantLinePoint) (stage : Nat)
    (row : FactorRow seedOccurrence.root stage) :
    (PointGlobalDerivedSolution point).X 1 →ₗ[ℂ] ℂ := by
  letI : Algebra PairCoefficientRing ℂ :=
    (actionCoefficientSpecialization point).toAlgebra
  change ((ModuleCat.extendScalars
      (actionCoefficientSpecialization point)).obj
        (PairGlobalDerivedSolution.X 1) : Type) →ₗ[ℂ] ℂ
  exact (TensorProduct.AlgebraTensorModule.rid
      PairCoefficientRing ℂ ℂ).toLinearMap.comp
    ((pairGlobalDerivedEndpointReadback stage row).baseChange ℂ)

theorem pointGlobalDerivedEndpointReadback_tmul
    (point : DeterminantLinePoint) (stage : Nat)
    (row : FactorRow seedOccurrence.root stage)
    (coefficient : ℂ) (value : PairGlobalDerivedSolution.X 1) :
    pointGlobalDerivedEndpointReadback point stage row
        (coefficient ⊗ₜ[PairCoefficientRing,
          actionCoefficientSpecialization point] value) =
      coefficient * actionCoefficientSpecialization point
        (pairGlobalDerivedEndpointReadback stage row value) := by
  letI : Algebra PairCoefficientRing ℂ :=
    (actionCoefficientSpecialization point).toAlgebra
  unfold pointGlobalDerivedEndpointReadback
  change (TensorProduct.AlgebraTensorModule.rid
      PairCoefficientRing ℂ ℂ)
        (((pairGlobalDerivedEndpointReadback stage row).baseChange ℂ)
          (coefficient ⊗ₜ[PairCoefficientRing] value)) = _
  rw [LinearMap.baseChange_tmul,
    TensorProduct.AlgebraTensorModule.rid_tmul]
  change actionCoefficientSpecialization point
      (pairGlobalDerivedEndpointReadback stage row value) * coefficient = _
  exact mul_comm _ _

noncomputable def pointDerivedScalarSingleOneGenerator
    (point : DeterminantLinePoint) :
    (PointDerivedScalarSingleOne point).X 1 :=
  (1 : ℂ) ⊗ₜ[PairCoefficientRing, actionCoefficientSpecialization point]
    pairDerivedScalarSingleOneGenerator

def pointDerivedPointEndpointReadback
    (point : DeterminantLinePoint) (stage : Nat)
    (row : FactorRow seedOccurrence.root stage)
    (derivedPoint : PointDerivedScalarSingleOne point ⟶
      PointGlobalDerivedSolution point) : ℂ :=
  pointGlobalDerivedEndpointReadback point stage row
    ((derivedPoint.f 1).hom
      (pointDerivedScalarSingleOneGenerator point))

theorem determinantLineDerivedSolutionPoint_generator
    (point : DeterminantLinePoint) :
    ((determinantLineDerivedSolutionPoint point).f 1).hom
        (pointDerivedScalarSingleOneGenerator point) =
      (1 : ℂ) ⊗ₜ[PairCoefficientRing,
        actionCoefficientSpecialization point]
        ((pairUniversalDerivedPoint.f 1).hom
          pairDerivedScalarSingleOneGenerator) := by
  unfold determinantLineDerivedSolutionPoint
    pointDerivedScalarSingleOneGenerator
  change
    (ModuleCat.extendScalars
        (actionCoefficientSpecialization point)).map
          (pairUniversalDerivedPoint.f 1)
          ((1 : ℂ) ⊗ₜ[PairCoefficientRing,
            actionCoefficientSpecialization point]
              pairDerivedScalarSingleOneGenerator) = _
  rw [ModuleCat.ExtendScalars.map_tmul]

theorem determinantLineReversedDerivedSolutionPoint_generator
    (point : DeterminantLinePoint) :
    ((determinantLineReversedDerivedSolutionPoint point).f 1).hom
        (pointDerivedScalarSingleOneGenerator point) =
      (1 : ℂ) ⊗ₜ[PairCoefficientRing,
        actionCoefficientSpecialization point]
        ((pairReversedUniversalDerivedPoint.f 1).hom
          pairDerivedScalarSingleOneGenerator) := by
  unfold determinantLineReversedDerivedSolutionPoint
    pointDerivedScalarSingleOneGenerator
  change
    (ModuleCat.extendScalars
        (actionCoefficientSpecialization point)).map
          (pairReversedUniversalDerivedPoint.f 1)
          ((1 : ℂ) ⊗ₜ[PairCoefficientRing,
            actionCoefficientSpecialization point]
              pairDerivedScalarSingleOneGenerator) = _
  rw [ModuleCat.ExtendScalars.map_tmul]

theorem pointDerivedSolutionPoint_readback
    (point : DeterminantLinePoint) (stage : Nat)
    (row : FactorRow seedOccurrence.root stage) :
    pointDerivedPointEndpointReadback point stage row
        (determinantLineDerivedSolutionPoint point) = point.pair.1 := by
  unfold pointDerivedPointEndpointReadback
  rw [determinantLineDerivedSolutionPoint_generator,
    pointGlobalDerivedEndpointReadback_tmul]
  have readback := pairUniversalDerivedPoint_readback stage row
  change pairGlobalDerivedEndpointReadback stage row
      ((pairUniversalDerivedPoint.f 1).hom
        pairDerivedScalarSingleOneGenerator) = _ at readback
  rw [readback,
    actionCoefficientSpecialization_universalLeft,
    one_mul]

theorem pointReversedDerivedSolutionPoint_readback
    (point : DeterminantLinePoint) (stage : Nat)
    (row : FactorRow seedOccurrence.root stage) :
    pointDerivedPointEndpointReadback point stage row
        (determinantLineReversedDerivedSolutionPoint point) = point.pair.2 := by
  unfold pointDerivedPointEndpointReadback
  rw [determinantLineReversedDerivedSolutionPoint_generator,
    pointGlobalDerivedEndpointReadback_tmul]
  have readback := pairReversedUniversalDerivedPoint_readback stage row
  change pairGlobalDerivedEndpointReadback stage row
      ((pairReversedUniversalDerivedPoint.f 1).hom
        pairDerivedScalarSingleOneGenerator) = _ at readback
  rw [readback,
    actionCoefficientSpecialization_universalRight,
    one_mul]

theorem determinantLinePoint_pair_fixed_of_derivedPoint_fixed
    (point : DeterminantLinePoint)
    (fixed : determinantLineDerivedSolutionPoint point =
      determinantLineReversedDerivedSolutionPoint point) :
    point.pair.1 = point.pair.2 := by
  have readback := congrArg
    (pointDerivedPointEndpointReadback point terminalReadbackStage
      terminalReadbackRow) fixed
  rw [pointDerivedSolutionPoint_readback,
    pointReversedDerivedSolutionPoint_readback] at readback
  exact readback

theorem riemannHypothesis_of_mathlibDerivedPoint_fixed
    (fixed : ∀ coordinate (zetaZero : riemannZeta coordinate = 0),
      (¬∃ n : Nat, coordinate = -2 * (n + 1)) →
      coordinate ≠ 1 →
      determinantLineDerivedSolutionPoint
          (mathlibZeroPoint coordinate zetaZero) =
        determinantLineReversedDerivedSolutionPoint
          (mathlibZeroPoint coordinate zetaZero)) :
    RiemannHypothesis := by
  intro coordinate zetaZero nontrivial notPole
  have pointFixed := determinantLinePoint_pair_fixed_of_derivedPoint_fixed
    (mathlibZeroPoint coordinate zetaZero)
      (fixed coordinate zetaZero nontrivial notPole)
  exact real_eq_half_of_complement_fixed coordinate (by
    simpa [coordinateReversal,
      CanonicalUnitArithmeticFactorizationWholePrimeDualBlockGlobalComplexDeterminantLine.mathlibPair]
      using pointFixed)

theorem universalCoordinates_eq_of_derivedPoint_fixed
    (fixed : pairUniversalDerivedPoint =
      pairReversedUniversalDerivedPoint) :
    universalLeftCoordinate installedOwner =
      universalRightCoordinate installedOwner := by
  have readback := congrArg
    (pairDerivedPointEndpointReadback terminalReadbackStage
      terminalReadbackRow) fixed
  rw [pairUniversalDerivedPoint_readback,
    pairReversedUniversalDerivedPoint_readback] at readback
  exact readback

theorem determinantLinePoint_pair_fixed_of_universalDerivedPoint_fixed
    (point : DeterminantLinePoint)
    (fixed : pairUniversalDerivedPoint =
      pairReversedUniversalDerivedPoint) :
    point.pair.1 = point.pair.2 := by
  have coefficientFixed := universalCoordinates_eq_of_derivedPoint_fixed fixed
  have specialized := congrArg (actionCoefficientSpecialization point)
    coefficientFixed
  simpa using specialized

theorem riemannHypothesis_of_universalDerivedPoint_fixed
    (fixed : pairUniversalDerivedPoint =
      pairReversedUniversalDerivedPoint) :
    RiemannHypothesis := by
  intro coordinate zetaZero _nontrivial _notPole
  have pairFixed :=
    determinantLinePoint_pair_fixed_of_universalDerivedPoint_fixed
      (mathlibZeroPoint coordinate zetaZero) fixed
  exact real_eq_half_of_complement_fixed coordinate (by
    simpa [coordinateReversal,
      CanonicalUnitArithmeticFactorizationWholePrimeDualBlockGlobalComplexDeterminantLine.mathlibPair]
      using pairFixed)

end
end CanonicalUnitArithmeticFactorizationFullEulerWholePrimeDualBlockDerivedSolutionFixedCoordinateReadback
end ConstructiveRoot
end LivingLawEvolution
end ResponsibilityLifecycle
end SaturationMonoid
