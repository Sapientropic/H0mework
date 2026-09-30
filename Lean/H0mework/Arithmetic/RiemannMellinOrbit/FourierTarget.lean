import H0mework.Arithmetic.RiemannMellinOrbit.ParityFourier

/-!
# Clozel two-point Fourier target

The two Fourier coefficients combine the existing point-specialised
left/right full-row sources.  Their actual C readback factors through the odd
mode and, on the Mathlib left component, is the existing branch separator.
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
open CanonicalUnitArithmeticFactorizationWholePrimeDualBlockGlobalComplexDeterminantLine
open CanonicalUnitArithmeticFactorizationWholePrimeDualBlockGlobalComplexDeterminantLineDerivedSpecialization
open InverseZeroFibre
open scoped ChangeOfRings TensorProduct ZMod

noncomputable section

noncomputable def pointLeftQRichFullRowTransposedPoint
    (point : DeterminantLinePoint) (stage : Nat) :
    (PointExtensionFunctor point).obj PairDerivedScalarSingleOne ⟶
      PointFullRowVerticalTotal point stage :=
  (PointExtensionFunctor point).map
    (pairQRichFullRowTransposedPoint stage blockLeftEndpointBase)

noncomputable def pointRightQRichFullRowTransposedPoint
    (point : DeterminantLinePoint) (stage : Nat) :
    (PointExtensionFunctor point).obj PairDerivedScalarSingleOne ⟶
      PointFullRowVerticalTotal point stage :=
  (PointExtensionFunctor point).map
    (pairQRichFullRowTransposedPoint stage blockRightEndpointBase)

/-- Two-point coefficients act on the actual specialised transposed points. -/
noncomputable def pointQRichZModTwoCombination
    (point : DeterminantLinePoint) (stage : Nat) :
    ZModTwoCarrier →ₗ[ℂ]
      ((PointExtensionFunctor point).obj PairDerivedScalarSingleOne ⟶
        PointFullRowVerticalTotal point stage) where
  toFun coefficient :=
    coefficient 0 • pointLeftQRichFullRowTransposedPoint point stage +
      coefficient 1 • pointRightQRichFullRowTransposedPoint point stage
  map_add' left right := by
    simp only [Pi.add_apply, add_smul]
    abel
  map_smul' scalar coefficient := by
    simp only [Pi.smul_apply, RingHom.id_apply, smul_eq_mul]
    rw [smul_add, smul_smul, smul_smul]

def pointFullRowSourceGenerator (point : DeterminantLinePoint) :
    (((PointExtensionFunctor point).obj PairDerivedScalarSingleOne).X 1 :
      Type) :=
  (1 : ℂ) ⊗ₜ[PairCoefficientRing,
      actionCoefficientSpecialization point]
    pairFullRowSourceGenerator

noncomputable def pointFullRowCReadback
    (point : DeterminantLinePoint) (stage : Nat)
    (row : FactorRow seedOccurrence.root stage) :
    ((PointFullRowVerticalTotal point stage).X 1 : Type) →ₗ[ℂ] ℂ := by
  let _ : Algebra PairCoefficientRing ℂ :=
    (actionCoefficientSpecialization point).toAlgebra
  change ((ModuleCat.extendScalars
      (actionCoefficientSpecialization point)).obj
        ((PairFullRowVerticalTotal stage).X 1) : Type) →ₗ[ℂ] ℂ
  exact (TensorProduct.AlgebraTensorModule.rid
      PairCoefficientRing ℂ ℂ).toLinearMap.comp
    ((pairFullRowCReadback stage row).baseChange ℂ)

/-- Evaluation on the specialised source generator, bundled linearly. -/
noncomputable def pointFullRowHomCReadback
    (point : DeterminantLinePoint) (stage : Nat)
    (row : FactorRow seedOccurrence.root stage) :
    ((PointExtensionFunctor point).obj PairDerivedScalarSingleOne ⟶
      PointFullRowVerticalTotal point stage) →ₗ[ℂ] ℂ where
  toFun source := pointFullRowCReadback point stage row
    ((source.f 1).hom (pointFullRowSourceGenerator point))
  map_add' left right := by simp
  map_smul' scalar source := by simp

/-- Point extension commutes with the existing pair-level C readback. -/
theorem pointFullRowHomCReadback_map
    (point : DeterminantLinePoint) (stage : Nat)
    (row : FactorRow seedOccurrence.root stage)
    (source : PairDerivedScalarSingleOne ⟶
      PairFullRowVerticalTotal stage) :
    pointFullRowHomCReadback point stage row
        ((PointExtensionFunctor point).map source) =
      actionCoefficientSpecialization point
        (pairFullRowCPointValue stage row source) := by
  let _ : Algebra PairCoefficientRing ℂ :=
    (actionCoefficientSpecialization point).toAlgebra
  unfold pointFullRowHomCReadback pointFullRowSourceGenerator
    pointFullRowCReadback pairFullRowCPointValue
  change (TensorProduct.AlgebraTensorModule.rid PairCoefficientRing ℂ ℂ)
    (((pairFullRowCReadback stage row).baseChange ℂ)
      ((ModuleCat.extendScalars
          (actionCoefficientSpecialization point)).map
        (source.f 1) ((1 : ℂ) ⊗ₜ[PairCoefficientRing]
          pairFullRowSourceGenerator))) = _
  rw [ModuleCat.ExtendScalars.map_tmul, LinearMap.baseChange_tmul,
    TensorProduct.AlgebraTensorModule.rid_tmul]
  change actionCoefficientSpecialization point
      (pairFullRowCReadback stage row
        ((source.f 1).hom pairFullRowSourceGenerator)) * 1 = _
  simp

@[simp] theorem pointLeftQRichFullRowTransposedPoint_readback
    (point : DeterminantLinePoint) (stage : Nat)
    (row : FactorRow seedOccurrence.root stage) :
    pointFullRowHomCReadback point stage row
        (pointLeftQRichFullRowTransposedPoint point stage) =
      -(quotientCoefficient row : ℂ) := by
  rw [pointLeftQRichFullRowTransposedPoint,
    pointFullRowHomCReadback_map, pairFullRowCPointValue_left, map_neg]
  simp

@[simp] theorem pointRightQRichFullRowTransposedPoint_readback
    (point : DeterminantLinePoint) (stage : Nat)
    (row : FactorRow seedOccurrence.root stage) :
    pointFullRowHomCReadback point stage row
        (pointRightQRichFullRowTransposedPoint point stage) =
      (quotientCoefficient row : ℂ) := by
  rw [pointRightQRichFullRowTransposedPoint,
    pointFullRowHomCReadback_map, pairFullRowCPointValue_right]
  simp

/-- The actual target readback is the q-rich coefficient times the odd mode. -/
theorem pointQRichZModTwoCombination_readback
    (point : DeterminantLinePoint) (stage : Nat)
    (row : FactorRow seedOccurrence.root stage)
    (coefficient : ZModTwoCarrier) :
    pointFullRowHomCReadback point stage row
        (pointQRichZModTwoCombination point stage coefficient) =
      -(quotientCoefficient row : ℂ) *
        (coefficient 0 - coefficient 1) := by
  change pointFullRowHomCReadback point stage row
      (coefficient 0 • pointLeftQRichFullRowTransposedPoint point stage +
        coefficient 1 • pointRightQRichFullRowTransposedPoint point stage) = _
  rw [map_add, map_smul, map_smul,
    pointLeftQRichFullRowTransposedPoint_readback,
    pointRightQRichFullRowTransposedPoint_readback]
  simp only [smul_eq_mul]
  ring

/-- The centered target reads Mathlib's odd DFT frequency literally. -/
theorem pointClozelCenteredCombination_readback_eq_dft_odd
    (point : DeterminantLinePoint) (s : ℂ) (stage : Nat)
    (row : FactorRow seedOccurrence.root stage) :
    pointFullRowHomCReadback point stage row
        (pointQRichZModTwoCombination point stage
          (clozelJPairToZModTwo (clozelCenteredParameter s,
            clozelReversedCenteredParameter s))) =
      -(quotientCoefficient row : ℂ) *
        ZMod.dft (clozelJPairToZModTwo (clozelCenteredParameter s,
          clozelReversedCenteredParameter s)) 1 := by
  rw [pointQRichZModTwoCombination_readback,
    clozelCenteredPair_dft_odd]
  rfl

/-- On the existing Mathlib left component this odd-mode readback is the
frozen branch-normalized separator. -/
theorem mathlibLeft_clozelFourierTarget_readback_eq_branchSeparator
    (observation : GeneratedRiemannZeroObservation)
    (stage : Nat) (row : FactorRow seedOccurrence.root stage) :
    pointFullRowHomCReadback
        (mathlibZeroPoint observation.coordinate observation.mathlibZero)
        stage row
        (pointQRichZModTwoCombination
          (mathlibZeroPoint observation.coordinate observation.mathlibZero)
          stage (clozelJPairToZModTwo
            (clozelCenteredParameter observation.coordinate,
              clozelReversedCenteredParameter observation.coordinate))) =
      branchNormalizedQRichSeparator
        (mathlibLeftRegressionComponent observation) stage row := by
  rw [pointQRichZModTwoCombination_readback,
    mathlibLeft_branchNormalizedSeparator_eq_clozelCross]
  rfl

end
end QRich
end CanonicalRiemann
end NoIslandNoMagic
end ConstructiveRoot
end LivingLawEvolution
end ResponsibilityLifecycle
end SaturationMonoid
