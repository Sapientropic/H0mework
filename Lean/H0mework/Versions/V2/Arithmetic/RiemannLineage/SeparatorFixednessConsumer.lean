import H0mework.Versions.R2.Arithmetic.EulerDerived.SolutionFixedCoordinate
import H0mework.Versions.R2.Arithmetic.RiemannInverseFibre.QRichSeparator

/-!
# From the q-rich separator zero to the existing RH terminal

The complete inverse-fibre separator already turns its zero into equality of
the two coordinates of the incident determinant-line point.  This module
shows that such pair equality makes the two existing specialized derived
points literally equal, and then packages the Mathlib regression component
for the existing Riemann-hypothesis consumer.

No separator zero is generated here.  This is the direct downstream consumer
of the integral-global descent frontier.
-/

set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option linter.style.haveILetI false

namespace SaturationMonoid
namespace ResponsibilityLifecycle
namespace LivingLawEvolution
namespace ConstructiveRoot
namespace NoIslandNoMagic
namespace CanonicalRiemann
namespace QRich

open CategoryTheory
open CanonicalUnitArithmeticFactorizationEulerDependentDiagram
open CanonicalUnitArithmeticFactorizationFullEulerWholePrimeDualBlockAnalyticGlobalActionCofiber
open CanonicalUnitArithmeticFactorizationFullEulerWholePrimeDualBlockDerivedSolutionPointSpecialization
open CanonicalUnitArithmeticFactorizationFullEulerWholePrimeDualBlockDerivedSolutionFixedCoordinateReadback
open CanonicalUnitArithmeticFactorizationWholePrimeDualBlockDeterminantLineCoordinate
open CanonicalUnitArithmeticFactorizationWholePrimeDualBlockEndpointFixedCoordinateReadback
open CanonicalUnitArithmeticFactorizationWholePrimeDualBlockGlobalComplexDeterminantLine
open CanonicalUnitArithmeticFactorizationWholePrimeDualBlockGlobalComplexDeterminantLineDerivedSpecialization
open CanonicalUnitArithmeticFactorizationWholeHistorySolutionCarrier
open InverseZeroFibre
open scoped ChangeOfRings TensorProduct

noncomputable section

/-- Equality of the two specialized coefficients makes the existing universal
derived point and its reversal literally equal after point specialization. -/
theorem determinantLineDerivedSolutionPoint_eq_reversed_of_pair_fixed
    (point : DeterminantLinePoint)
    (fixed : point.pair.1 = point.pair.2) :
    determinantLineDerivedSolutionPoint point =
      determinantLineReversedDerivedSolutionPoint point := by
  letI : Algebra PairCoefficientRing ℂ :=
    (actionCoefficientSpecialization point).toAlgebra
  unfold determinantLineDerivedSolutionPoint
    determinantLineReversedDerivedSolutionPoint
  apply HomologicalComplex.Hom.ext
  funext degree
  apply ModuleCat.ExtendScalars.hom_ext
  intro value
  change
    (ModuleCat.extendScalars (actionCoefficientSpecialization point)).map
        (pairUniversalDerivedPoint.f degree)
        ((1 : ℂ) ⊗ₜ[PairCoefficientRing,
          actionCoefficientSpecialization point] value) =
      (ModuleCat.extendScalars (actionCoefficientSpecialization point)).map
        (pairReversedUniversalDerivedPoint.f degree)
        ((1 : ℂ) ⊗ₜ[PairCoefficientRing,
          actionCoefficientSpecialization point] value)
  rw [ModuleCat.ExtendScalars.map_tmul,
    ModuleCat.ExtendScalars.map_tmul]
  unfold pairUniversalDerivedPoint pairReversedUniversalDerivedPoint
  let leftValue := (pairGlobalLeftDerivedPoint.f degree).hom value
  let rightValue := (pairGlobalRightDerivedPoint.f degree).hom value
  change
    (1 : ℂ) ⊗ₜ[PairCoefficientRing]
        (universalLeftCoordinate installedOwner • leftValue +
          universalRightCoordinate installedOwner • rightValue) =
      (1 : ℂ) ⊗ₜ[PairCoefficientRing]
        (universalRightCoordinate installedOwner • leftValue +
          universalLeftCoordinate installedOwner • rightValue)
  have leftScalar :
      universalLeftCoordinate installedOwner • (1 : ℂ) =
        actionCoefficientSpecialization point
          (universalLeftCoordinate installedOwner) := by
    change actionCoefficientSpecialization point
        (universalLeftCoordinate installedOwner) * 1 = _
    simp
  have rightScalar :
      universalRightCoordinate installedOwner • (1 : ℂ) =
        actionCoefficientSpecialization point
          (universalRightCoordinate installedOwner) := by
    change actionCoefficientSpecialization point
        (universalRightCoordinate installedOwner) * 1 = _
    simp
  rw [TensorProduct.tmul_add, TensorProduct.tmul_add,
    TensorProduct.tmul_smul, TensorProduct.tmul_smul,
    TensorProduct.tmul_smul, TensorProduct.tmul_smul]
  change
    ((universalLeftCoordinate installedOwner • (1 : ℂ))
        ⊗ₜ[PairCoefficientRing] leftValue) +
      ((universalRightCoordinate installedOwner • (1 : ℂ))
        ⊗ₜ[PairCoefficientRing] rightValue) =
    ((universalRightCoordinate installedOwner • (1 : ℂ))
        ⊗ₜ[PairCoefficientRing] leftValue) +
      ((universalLeftCoordinate installedOwner • (1 : ℂ))
        ⊗ₜ[PairCoefficientRing] rightValue)
  rw [leftScalar, rightScalar,
    actionCoefficientSpecialization_universalLeft,
    actionCoefficientSpecialization_universalRight, fixed]

/-- Separator-zero on Mathlib's lawful left regression component now gives
the literal derived fixedness expected by the frozen terminal consumer. -/
theorem mathlibDerivedSolutionPoint_fixed_of_branchSeparator_zero
    (observation : GeneratedRiemannZeroObservation)
    (stage : Nat) (row : FactorRow seedOccurrence.root stage)
    (separatorZero :
      branchNormalizedQRichSeparator
        (mathlibLeftRegressionComponent observation) stage row = 0) :
    determinantLineDerivedSolutionPoint
        (mathlibZeroPoint observation.coordinate observation.mathlibZero) =
      determinantLineReversedDerivedSolutionPoint
        (mathlibZeroPoint observation.coordinate observation.mathlibZero) := by
  have pairFixed := incidentPoint_pair_fixed_of_separator_zero
    (mathlibLeftRegressionComponent observation) stage row separatorZero
  rw [mathlibLeftRegressionComponent_point] at pairFixed
  exact determinantLineDerivedSolutionPoint_eq_reversed_of_pair_fixed
    (mathlibZeroPoint observation.coordinate observation.mathlibZero)
      pairFixed

/-- Exact final consumer contract for the missing descent producer. -/
theorem riemannHypothesis_of_branchNormalizedQRichSeparator_zero
    (separatorZero : ∀ coordinate (zetaZero : riemannZeta coordinate = 0),
      (¬ ∃ n : Nat, coordinate = -2 * (n + 1)) →
      coordinate ≠ 1 →
      branchNormalizedQRichSeparator
        (mathlibLeftRegressionComponent
          (GeneratedRiemannZeroObservation.ofMathlibZero
            coordinate zetaZero))
        terminalReadbackStage terminalReadbackRow = 0) :
    RiemannHypothesis := by
  apply riemannHypothesis_of_mathlibDerivedPoint_fixed
  intro coordinate zetaZero nontrivial notPole
  let observation :=
    GeneratedRiemannZeroObservation.ofMathlibZero coordinate zetaZero
  have fixed := mathlibDerivedSolutionPoint_fixed_of_branchSeparator_zero
    observation terminalReadbackStage terminalReadbackRow
      (separatorZero coordinate zetaZero nontrivial notPole)
  simpa [observation] using fixed

end
end QRich
end CanonicalRiemann
end NoIslandNoMagic
end ConstructiveRoot
end LivingLawEvolution
end ResponsibilityLifecycle
end SaturationMonoid
