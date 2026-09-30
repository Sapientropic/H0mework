import H0mework.Versions.Y.Arithmetic.EulerDerived.SolutionSpecialization
import H0mework.Versions.Y.Arithmetic.RiemannLineage.FullRowCReadback

/-!
# Universal pair-coefficient full-row separator

The two source-owned q-rich orientations are first base-changed to the
existing universal pair coefficient ring and only then weighted by its two
universal coordinates.  Point specialization is downstream.  No analytic
fibre partner enters the producer, and no separator-zero or fixedness premise
is accepted.
-/

set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency false

namespace SaturationMonoid
namespace ResponsibilityLifecycle
namespace LivingLawEvolution
namespace ConstructiveRoot
namespace NoIslandNoMagic
namespace CanonicalRiemann
namespace QRich

open CategoryTheory
open CanonicalUnitArithmeticFactorizationEulerDependentDiagram
open CanonicalUnitArithmeticFactorizationWholeHistorySolutionCarrier
open CanonicalUnitArithmeticFactorizationFullEulerWholePrimeDualBlockFrame
open CanonicalUnitArithmeticFactorizationFullEulerWholePrimeDualBlockLinearGlobalEndpointSection
open CanonicalUnitArithmeticFactorizationFullEulerWholePrimeDualBlockAnalyticGlobalActionCofiber
open CanonicalUnitArithmeticFactorizationFullEulerWholePrimeDualBlockDerivedSolutionPointSpecialization
open CanonicalUnitArithmeticFactorizationFullEulerWholePrimeDualBlockDerivedPointActualDatum
open CanonicalUnitArithmeticFactorizationWholePrimeDualBlockDeterminantLineCoordinate
open CanonicalUnitArithmeticFactorizationWholePrimeDualBlockGlobalComplexDeterminantLine
open CanonicalUnitArithmeticFactorizationWholePrimeDualBlockGlobalComplexDeterminantLineDerivedSpecialization
open CochainMappingCoconeMappedBoundaryAtomOver
open scoped ChangeOfRings TensorProduct

noncomputable section

local instance pairCoefficientModule :
    Module BlockCoordinateRing PairCoefficientRing :=
  Module.compHom PairCoefficientRing blockCoordinateToPairZeroFiber

noncomputable abbrev PairFullRowVerticalTotal (stage : Nat) :=
  PairDerivedExtensionFunctor.obj
    (fullRowDerivedSquare stage).verticalTotal

noncomputable def pairQRichFullRowTransposedPoint (stage : Nat)
    (base : BlockDualBase) :
    PairDerivedScalarSingleOne ⟶ PairFullRowVerticalTotal stage :=
  PairDerivedExtensionFunctor.map
    (qRichFullRowTransposedPoint stage base)

/-- The source producer contains only the two universal coefficient
coordinates and the two pre-existing source bases. -/
noncomputable def universalPairCoefficientCSeparator (stage : Nat) :
    PairDerivedScalarSingleOne ⟶ PairFullRowVerticalTotal stage :=
  universalLeftCoordinate installedOwner •
      pairQRichFullRowTransposedPoint stage blockLeftEndpointBase +
    universalRightCoordinate installedOwner •
      pairQRichFullRowTransposedPoint stage blockRightEndpointBase

noncomputable def pairFullRowSourceGenerator :
    (PairDerivedScalarSingleOne.X 1 : Type) := by
  change PairCoefficientRing ⊗[BlockCoordinateRing]
    (ScalarSingleOne (R := BlockCoordinateRing)).X 1
  exact (1 : PairCoefficientRing) ⊗ₜ[BlockCoordinateRing]
    scalarSingleOneGenerator

noncomputable def pairFullRowDegreeOneEquiv (stage : Nat) :
    ((ModuleCat.extendScalars blockCoordinateToPairZeroFiber).obj
        ((fullRowDerivedSquare stage).verticalTotal.X 1) : Type) ≃ₗ[
      PairCoefficientRing]
      PairCoefficientRing ⊗[BlockCoordinateRing]
        ((fullRowDerivedSquare stage).verticalTotal.X 1 : Type) :=
  LinearEquiv.refl PairCoefficientRing _

@[simp] theorem pairFullRowDegreeOneEquiv_tmul (stage : Nat)
    (coefficient : PairCoefficientRing)
    (value : (fullRowDerivedSquare stage).verticalTotal.X 1) :
    pairFullRowDegreeOneEquiv stage
        (coefficient ⊗ₜ[BlockCoordinateRing] value) =
      coefficient ⊗ₜ[BlockCoordinateRing] value :=
  rfl

noncomputable def pairFullRowCReadback (stage : Nat)
    (row : FactorRow seedOccurrence.root stage) :
    (PairFullRowVerticalTotal stage).X 1 →ₗ[PairCoefficientRing]
      PairCoefficientRing := by
  let _ : Algebra BlockCoordinateRing PairCoefficientRing :=
    blockCoordinateToPairZeroFiber.toAlgebra
  change ((ModuleCat.extendScalars
      blockCoordinateToPairZeroFiber).obj
        ((fullRowDerivedSquare stage).verticalTotal.X 1) : Type) →ₗ[
          PairCoefficientRing] PairCoefficientRing
  exact (TensorProduct.AlgebraTensorModule.rid BlockCoordinateRing
      PairCoefficientRing PairCoefficientRing).toLinearMap.comp
    (((fullRowCReadback stage row).baseChange PairCoefficientRing).comp
      (pairFullRowDegreeOneEquiv stage).toLinearMap)

def pairFullRowCPointValue (stage : Nat)
    (row : FactorRow seedOccurrence.root stage)
    (point : PairDerivedScalarSingleOne ⟶
      PairFullRowVerticalTotal stage) : PairCoefficientRing :=
  pairFullRowCReadback stage row
    ((point.f 1).hom pairFullRowSourceGenerator)

theorem pairQRichFullRowTransposedPoint_generator (stage : Nat)
    (base : BlockDualBase) :
    ((pairQRichFullRowTransposedPoint stage base).f 1).hom
        pairFullRowSourceGenerator =
      (1 : PairCoefficientRing) ⊗ₜ[BlockCoordinateRing]
        ((qRichFullRowTransposedPoint stage base).f 1).hom
          scalarSingleOneGenerator := by
  unfold pairQRichFullRowTransposedPoint pairFullRowSourceGenerator
  change
    (ModuleCat.extendScalars blockCoordinateToPairZeroFiber).map
        ((qRichFullRowTransposedPoint stage base).f 1)
        ((1 : PairCoefficientRing) ⊗ₜ[BlockCoordinateRing]
          scalarSingleOneGenerator) = _
  rw [ModuleCat.ExtendScalars.map_tmul]

theorem pairFullRowCReadback_tmul (stage : Nat)
    (row : FactorRow seedOccurrence.root stage)
    (coefficient : PairCoefficientRing)
    (value : (fullRowDerivedSquare stage).verticalTotal.X 1) :
    pairFullRowCReadback stage row
        (coefficient ⊗ₜ[BlockCoordinateRing] value) =
      coefficient * blockCoordinateToPairZeroFiber
        (fullRowCReadback stage row value) := by
  let _ : Algebra BlockCoordinateRing PairCoefficientRing :=
    blockCoordinateToPairZeroFiber.toAlgebra
  unfold pairFullRowCReadback
  change (TensorProduct.AlgebraTensorModule.rid BlockCoordinateRing
      PairCoefficientRing PairCoefficientRing)
        (((fullRowCReadback stage row).baseChange PairCoefficientRing)
          (pairFullRowDegreeOneEquiv stage
            (coefficient ⊗ₜ[BlockCoordinateRing] value))) = _
  rw [pairFullRowDegreeOneEquiv_tmul,
    LinearMap.baseChange_tmul,
    TensorProduct.AlgebraTensorModule.rid_tmul]
  exact mul_comm _ _

@[simp] theorem pairFullRowCPointValue_left (stage : Nat)
    (row : FactorRow seedOccurrence.root stage) :
    pairFullRowCPointValue stage row
        (pairQRichFullRowTransposedPoint stage blockLeftEndpointBase) =
      -(quotientCoefficient row : PairCoefficientRing) := by
  unfold pairFullRowCPointValue
  rw [pairQRichFullRowTransposedPoint_generator,
    pairFullRowCReadback_tmul]
  have source := fullRowCPointValue_left stage row
  change fullRowCReadback stage row
      (((qRichFullRowTransposedPoint stage
        blockLeftEndpointBase).f 1).hom scalarSingleOneGenerator) =
    -(quotientCoefficient row : BlockCoordinateRing) at source
  rw [source, map_neg]
  simp

@[simp] theorem pairFullRowCPointValue_right (stage : Nat)
    (row : FactorRow seedOccurrence.root stage) :
    pairFullRowCPointValue stage row
        (pairQRichFullRowTransposedPoint stage blockRightEndpointBase) =
      (quotientCoefficient row : PairCoefficientRing) := by
  unfold pairFullRowCPointValue
  rw [pairQRichFullRowTransposedPoint_generator,
    pairFullRowCReadback_tmul]
  have source := fullRowCPointValue_right stage row
  change fullRowCReadback stage row
      (((qRichFullRowTransposedPoint stage
        blockRightEndpointBase).f 1).hom scalarSingleOneGenerator) =
    (quotientCoefficient row : BlockCoordinateRing) at source
  rw [source]
  simp

theorem universalPairCoefficientCSeparator_readback (stage : Nat)
    (row : FactorRow seedOccurrence.root stage) :
    pairFullRowCPointValue stage row
        (universalPairCoefficientCSeparator stage) =
      -(quotientCoefficient row : PairCoefficientRing) *
        (universalLeftCoordinate installedOwner -
          universalRightCoordinate installedOwner) := by
  unfold pairFullRowCPointValue universalPairCoefficientCSeparator
  change pairFullRowCReadback stage row
      (universalLeftCoordinate installedOwner •
          ((pairQRichFullRowTransposedPoint stage
            blockLeftEndpointBase).f 1).hom pairFullRowSourceGenerator +
        universalRightCoordinate installedOwner •
          ((pairQRichFullRowTransposedPoint stage
            blockRightEndpointBase).f 1).hom pairFullRowSourceGenerator) = _
  have left := pairFullRowCPointValue_left stage row
  have right := pairFullRowCPointValue_right stage row
  change pairFullRowCReadback stage row
      (((pairQRichFullRowTransposedPoint stage
        blockLeftEndpointBase).f 1).hom pairFullRowSourceGenerator) =
      -(quotientCoefficient row : PairCoefficientRing) at left
  change pairFullRowCReadback stage row
      (((pairQRichFullRowTransposedPoint stage
        blockRightEndpointBase).f 1).hom pairFullRowSourceGenerator) =
      (quotientCoefficient row : PairCoefficientRing) at right
  rw [map_add, map_smul, map_smul, left, right]
  simp only [smul_eq_mul]
  ring

noncomputable abbrev PointFullRowVerticalTotal
    (point : DeterminantLinePoint) (stage : Nat) :=
  (PointExtensionFunctor point).obj (PairFullRowVerticalTotal stage)

noncomputable def pointFullRowCSeparator (point : DeterminantLinePoint)
    (stage : Nat) :
    (PointExtensionFunctor point).obj PairDerivedScalarSingleOne ⟶
      PointFullRowVerticalTotal point stage :=
  (PointExtensionFunctor point).map
    (universalPairCoefficientCSeparator stage)

def pointFullRowCSeparatorValue (point : DeterminantLinePoint)
    (stage : Nat) (row : FactorRow seedOccurrence.root stage) : ℂ :=
  actionCoefficientSpecialization point
    (pairFullRowCPointValue stage row
      (universalPairCoefficientCSeparator stage))

theorem pointFullRowCSeparatorValue_eq (point : DeterminantLinePoint)
    (stage : Nat) (row : FactorRow seedOccurrence.root stage) :
    pointFullRowCSeparatorValue point stage row =
      -(quotientCoefficient row : ℂ) *
        (point.pair.1 - point.pair.2) := by
  unfold pointFullRowCSeparatorValue
  rw [universalPairCoefficientCSeparator_readback,
    map_mul, map_neg, map_sub,
    actionCoefficientSpecialization_universalLeft,
    actionCoefficientSpecialization_universalRight]
  simp only [map_natCast]

end
end QRich
end CanonicalRiemann
end NoIslandNoMagic
end ConstructiveRoot
end LivingLawEvolution
end ResponsibilityLifecycle
end SaturationMonoid
