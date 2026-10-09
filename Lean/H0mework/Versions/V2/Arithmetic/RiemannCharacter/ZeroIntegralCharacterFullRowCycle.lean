import H0mework.Versions.V2.Arithmetic.RiemannCharacter.ZeroIntegralCharacterGroupRing
import H0mework.Versions.R2.Arithmetic.RiemannMellinOrbit.ProperMellinFullRowIncidence

/-!
# Integral character group ring in the q-rich full-row cycle

The selected and reversal evaluations of the same integral positive-scale
group ring supply the two coefficients of the existing q-rich point-full-row
cycle.  Its established C readback therefore sees the literal difference of
the two source-owned characters at every integral group-ring element.

For an actual factor row the distinguished group element is its prime, not
its prime power: the exponent already belongs to the row's quotient
coefficient, while the local Euler character acts once by that prime.
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
namespace Character
namespace IntegralCharacterGroupRing

open CanonicalUnitArithmeticFactorizationEulerDependentDiagram
open CanonicalUnitArithmeticFactorizationWholeHistorySolutionCarrier
open CanonicalUnitArithmeticCoordinateProjectionObstruction
open CanonicalUnitArithmeticFactorizationFullEulerWholePrimeDualBlockDeterminantSection
open CanonicalUnitArithmeticFactorizationFullEulerWholePrimeDualBlockDerivedSolutionPointSpecialization
open CanonicalUnitArithmeticFactorizationWholePrimeDualBlockGlobalComplexDeterminantLine
open CanonicalUnitArithmeticFactorizationWholePrimeDualBlockGlobalComplexDeterminantLineDerivedSpecialization
open InverseZeroFibre
open SourceGeneratedIntegralCharacterGroupRing
open SourceGeneratedPositiveRealCharacter

noncomputable section

/-- The two evaluations already carried by the zero-owned integral character
occurrence, bundled without changing coefficients. -/
def zeroIntegralCharacterPairEvaluation
    (observation : GeneratedRiemannZeroObservation) :
    PositiveScaleCarrier →ₗ[ℤ] QRich.ClozelJPair where
  toFun value :=
    ((zeroOwnedIntegralCharacterOccurrence observation).root.2.1 value,
      (zeroOwnedIntegralCharacterOccurrence observation).root.2.2 value)
  map_add' left right := by
    ext <;> simp
  map_smul' scalar value := by
    ext
    · exact map_smul
        (zeroOwnedIntegralCharacterOccurrence observation).root.2.1
        scalar value
    · exact map_smul
        (zeroOwnedIntegralCharacterOccurrence observation).root.2.2
        scalar value

/-- Reindex the selected/reversal evaluations by the existing `ZMod 2`
coefficient carrier. -/
noncomputable def zeroIntegralCharacterZModTwoEvaluation
    (observation : GeneratedRiemannZeroObservation) :
    PositiveScaleCarrier →ₗ[ℤ] QRich.ZModTwoCarrier :=
  (QRich.clozelJPairToZModTwo.toLinearMap.restrictScalars ℤ).comp
    (zeroIntegralCharacterPairEvaluation observation)

@[simp] theorem zeroIntegralCharacterZModTwoEvaluation_zero
    (observation : GeneratedRiemannZeroObservation)
    (value : PositiveScaleCarrier) :
    zeroIntegralCharacterZModTwoEvaluation observation value 0 =
      (zeroOwnedIntegralCharacterOccurrence observation).root.2.1 value := by
  simp [zeroIntegralCharacterZModTwoEvaluation,
    zeroIntegralCharacterPairEvaluation]

@[simp] theorem zeroIntegralCharacterZModTwoEvaluation_one
    (observation : GeneratedRiemannZeroObservation)
    (value : PositiveScaleCarrier) :
    zeroIntegralCharacterZModTwoEvaluation observation value 1 =
      (zeroOwnedIntegralCharacterOccurrence observation).root.2.2 value := by
  simp [zeroIntegralCharacterZModTwoEvaluation,
    zeroIntegralCharacterPairEvaluation]

/-- The existing two-point q-rich combination, now driven by the common
integral character carrier. -/
noncomputable def zeroIntegralCharacterPointFullRowHom
    (observation : GeneratedRiemannZeroObservation) (stage : Nat) :
    PositiveScaleCarrier →ₗ[ℤ]
      (((PointExtensionFunctor
          (mathlibZeroPoint observation.coordinate observation.mathlibZero)).obj
            PairDerivedScalarSingleOne) ⟶
        QRich.PointFullRowVerticalTotal
          (mathlibZeroPoint observation.coordinate observation.mathlibZero)
          stage) :=
  ((QRich.pointQRichZModTwoCombination
      (mathlibZeroPoint observation.coordinate observation.mathlibZero)
      stage).restrictScalars ℤ).comp
    (zeroIntegralCharacterZModTwoEvaluation observation)

/-- Evaluation on the existing source generator produces a genuine
degree-one cycle in the existing point-full-row total. -/
noncomputable def zeroIntegralCharacterPointFullRowCycle
    (observation : GeneratedRiemannZeroObservation) (stage : Nat) :
    PositiveScaleCarrier →ₗ[ℤ]
      QRich.PointFullRowDegreeOneCycles
        (mathlibZeroPoint observation.coordinate observation.mathlibZero)
        stage :=
  ((QRich.pointFullRowHomCycle
      (mathlibZeroPoint observation.coordinate observation.mathlibZero)
      stage).restrictScalars ℤ).comp
    (zeroIntegralCharacterPointFullRowHom observation stage)

/-- The full-row C readback is exactly the q-rich quotient coefficient times
the selected/reversal character difference. -/
theorem zeroIntegralCharacterPointFullRowCycle_readback
    (observation : GeneratedRiemannZeroObservation) (stage : Nat)
    (row : FactorRow seedOccurrence.root stage)
    (value : PositiveScaleCarrier) :
    QRich.pointFullRowCycleCReadback
        (mathlibZeroPoint observation.coordinate observation.mathlibZero)
        stage row
        (zeroIntegralCharacterPointFullRowCycle observation stage value) =
      -(quotientCoefficient row : ℂ) *
        ((zeroOwnedIntegralCharacterOccurrence observation).root.2.1 value -
          (zeroOwnedIntegralCharacterOccurrence observation).root.2.2 value) := by
  change QRich.pointFullRowCycleCReadback
      (mathlibZeroPoint observation.coordinate observation.mathlibZero)
      stage row
      (QRich.pointFullRowHomCycle
        (mathlibZeroPoint observation.coordinate observation.mathlibZero)
        stage
        (zeroIntegralCharacterPointFullRowHom observation stage value)) = _
  rw [QRich.pointFullRowCycleCReadback, LinearMap.comp_apply,
    QRich.pointFullRowHomCycle_inclusion]
  change QRich.pointFullRowHomCReadback
      (mathlibZeroPoint observation.coordinate observation.mathlibZero)
      stage row
      (QRich.pointQRichZModTwoCombination
        (mathlibZeroPoint observation.coordinate observation.mathlibZero)
        stage (zeroIntegralCharacterZModTwoEvaluation observation value)) = _
  rw [QRich.pointQRichZModTwoCombination_readback,
    zeroIntegralCharacterZModTwoEvaluation_zero,
    zeroIntegralCharacterZModTwoEvaluation_one]

/-- The local Euler unit attached to a factor row.  Its exponent belongs to
the row coefficient and is deliberately not folded into this unit. -/
def rowPrimeScaleUnit {stage : Nat}
    (row : FactorRow seedOccurrence.root stage) : Units NNReal :=
  positiveRealUnit (rowPrime row : ℝ) (by
    exact_mod_cast (rowPrime row).2.pos)

/-- On the row's prime basis vector the same full-row readback is the literal
difference of the selected and reversal complex-power characters. -/
theorem zeroIntegralCharacterPointFullRowCycle_delta_rowPrime_readback
    (observation : GeneratedRiemannZeroObservation) (stage : Nat)
    (row : FactorRow seedOccurrence.root stage) :
    QRich.pointFullRowCycleCReadback
        (mathlibZeroPoint observation.coordinate observation.mathlibZero)
        stage row
        (zeroIntegralCharacterPointFullRowCycle observation stage
          (delta (rowPrimeScaleUnit row))) =
      -(quotientCoefficient row : ℂ) *
        (complexPowerCharacter observation.coordinate (rowPrimeScaleUnit row) -
          complexPowerCharacter (coordinateReversal observation.coordinate)
            (rowPrimeScaleUnit row)) := by
  rw [zeroIntegralCharacterPointFullRowCycle_readback,
    zeroOwnedIntegralCharacterOccurrence_root_selected,
    zeroOwnedIntegralCharacterOccurrence_root_reversal]
  simp only [characterEvaluation_delta]
  rw [
    zeroOwnedMultiplicativeCharacterOccurrence_root_selected,
    zeroOwnedMultiplicativeCharacterOccurrence_root_reversal]

/-- The same basis readback in the already installed arithmetic prime
coordinates. -/
theorem zeroIntegralCharacterPointFullRowCycle_delta_rowPrime_installed
    (observation : GeneratedRiemannZeroObservation) (stage : Nat)
    (row : FactorRow seedOccurrence.root stage) :
    QRich.pointFullRowCycleCReadback
        (mathlibZeroPoint observation.coordinate observation.mathlibZero)
        stage row
        (zeroIntegralCharacterPointFullRowCycle observation stage
          (delta (rowPrimeScaleUnit row))) =
      -(quotientCoefficient row : ℂ) *
        (installedPrimeEigenvalue (rowPrime row) observation.coordinate -
          installedPrimeEigenvalue (rowPrime row)
            (coordinateReversal observation.coordinate)) := by
  rw [installedPrimeEigenvalue_eq_complexPowerCharacter,
    installedPrimeEigenvalue_eq_complexPowerCharacter]
  simpa [rowPrimeScaleUnit] using
    zeroIntegralCharacterPointFullRowCycle_delta_rowPrime_readback
      observation stage row

end

end IntegralCharacterGroupRing
end Character
end CanonicalRiemann
end NoIslandNoMagic
end ConstructiveRoot
end LivingLawEvolution
end ResponsibilityLifecycle
end SaturationMonoid
