import H0mework.Arithmetic.RiemannLineage.FullRowSeparatorPoint

/-!
# Linear readback of the full-row C separator

The C coordinate exposed by total-fibre transposition is evaluated at one
actual factor row and its canonical dual-zero coordinate.  The two existing
source-owned bases read the opposite nonzero quotient coefficients.  This
module contains no analytic point or vanishing claim.
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
open CochainComplex.HomComplex
open CanonicalUnitArithmeticFactorizationEulerDependentDiagram
open CanonicalUnitArithmeticFactorizationWholeHistorySolutionCarrier
open CanonicalUnitArithmeticFactorizationFullEulerWholePrimeDualBlockFrame
open CanonicalUnitArithmeticFactorizationFullEulerWholePrimeDualBlockLinearGlobalEndpointSection
open CanonicalUnitArithmeticFactorizationFullEulerWholePrimeDualBlockAnalyticTautologicalReadback
open CanonicalUnitArithmeticFactorizationFullEulerWholePrimeDualBlockDerivedPointActualDatum
open CochainMappingCoconeMappedBoundaryAtomOver

noncomputable section

noncomputable abbrev fullRowVerticalMap (stage : Nat) :=
  CochainMappingCoconeTotalFiberSymmetry.verticalMap
    (fullRowDerivedSquare stage).horizontalSource
    (fullRowDerivedSquare stage).horizontalTarget
    (fullRowDerivedSquare stage).verticalLeft
    (fullRowDerivedSquare stage).verticalRight
    (fullRowDerivedSquare stage).square

def blockRowCoordinate (stage : Nat)
    (row : FactorRow seedOccurrence.root stage) :
    BlockRowFamily stage →ₗ[BlockCoordinateRing] BlockCoordinateRing where
  toFun value := value row (row.1, 0)
  map_add' _left _right := rfl
  map_smul' _scalar _value := rfl

def fullRowCReadback (stage : Nat)
    (row : FactorRow seedOccurrence.root stage) :
    ((fullRowDerivedSquare stage).verticalTotal.X 1 : Type) →ₗ[
      BlockCoordinateRing] BlockCoordinateRing :=
  (blockRowCoordinate stage row).comp
    (((CochainComplex.mappingCocone.snd
      (fullRowDerivedSquare stage).verticalLeft).v 1 0 (by omega)).hom.comp
        ((CochainComplex.mappingCocone.fst
          (fullRowVerticalMap stage)).f 1).hom)

def fullRowCPointValue (stage : Nat)
    (row : FactorRow seedOccurrence.root stage)
    (point : ScalarSingleOne (R := BlockCoordinateRing) ⟶
      (fullRowDerivedSquare stage).verticalTotal) : BlockCoordinateRing :=
  fullRowCReadback stage row
    ((point.f 1).hom scalarSingleOneGenerator)

theorem fullRowCPointValue_qRich (stage : Nat)
    (row : FactorRow seedOccurrence.root stage) (base : BlockDualBase) :
    fullRowCPointValue stage row
        (qRichFullRowTransposedPoint stage base) =
      -(quotientCoefficient row : BlockCoordinateRing) *
        (base 0 - base 1) := by
  have coordinate := qRichFullRowTransposedPoint_C
    stage base 1 0 (by omega)
  have evaluated := ConcreteCategory.congr_hom coordinate
    scalarSingleOneGenerator
  have readbackCoordinate :
      fullRowCPointValue stage row
          (qRichFullRowTransposedPoint stage base) =
        blockRowCoordinate stage row
          (((qRichFullRowQuotientCap stage base).v 1 0 (by omega)).hom
            scalarSingleOneGenerator) := by
    exact congrArg (blockRowCoordinate stage row) evaluated
  rw [readbackCoordinate]
  change
    blockQuotientFamilyProjection stage
      ((localDerivedEndpointCochain stage
        (localQRichDerivedPoint stage base)).v
          1 0 (by omega) scalarSingleOneGenerator) row (row.1, 0) = _
  rw [localQRichDerivedPoint,
    localCorrectedEndpoint_endpointCochain, map_neg]
  change -blockQuotientAntiInvariantProjection stage row
      (blockQRichEndpointVertexMap stage base) (row.1, 0) = _
  rw [blockQRichEndpoint_quotientAntiInvariant]
  simp

@[simp] theorem fullRowCPointValue_left (stage : Nat)
    (row : FactorRow seedOccurrence.root stage) :
    fullRowCPointValue stage row
        (qRichFullRowTransposedPoint stage blockLeftEndpointBase) =
      -(quotientCoefficient row : BlockCoordinateRing) := by
  rw [fullRowCPointValue_qRich]
  simp [blockLeftEndpointBase]

@[simp] theorem fullRowCPointValue_right (stage : Nat)
    (row : FactorRow seedOccurrence.root stage) :
    fullRowCPointValue stage row
        (qRichFullRowTransposedPoint stage blockRightEndpointBase) =
      (quotientCoefficient row : BlockCoordinateRing) := by
  rw [fullRowCPointValue_qRich]
  simp [blockRightEndpointBase]

theorem fullRowCPointValue_left_ne_zero (stage : Nat)
    (row : FactorRow seedOccurrence.root stage) :
    fullRowCPointValue stage row
        (qRichFullRowTransposedPoint stage blockLeftEndpointBase) ≠ 0 := by
  rw [fullRowCPointValue_left, neg_ne_zero]
  change MvPolynomial.C ((quotientCoefficient row : Nat) : ℤ) ≠ 0
  rw [MvPolynomial.C_ne_zero]
  exact_mod_cast blockQRichQuotientCoefficient_ne_zero stage row

end
end QRich
end CanonicalRiemann
end NoIslandNoMagic
end ConstructiveRoot
end LivingLawEvolution
end ResponsibilityLifecycle
end SaturationMonoid
