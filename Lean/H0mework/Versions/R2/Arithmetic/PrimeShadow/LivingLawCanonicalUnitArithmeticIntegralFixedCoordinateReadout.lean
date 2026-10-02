import H0mework.Versions.R2.Arithmetic.PrimeShadow.LivingLawCanonicalUnitArithmeticEulerDeterminantCoordinateRegression
import H0mework.Versions.R2.Arithmetic.EulerGlobal.HistoryZeroFiberState

/-!
# Coordinate readout of the settled integral-first fixed component

This adapter consumes the repaired anti-invariant-only settlement.  Frozen
rigidity identifies the two whole endpoints, while the source-generated
diagonal unit survives with value `1`.  A same-occurrence coordinate/reversal
readout therefore carries the generated equality to `s = 1 - conj s`, hence
to `Re(s)=1/2`.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ResponsibilityLifecycle
namespace LivingLawEvolution
namespace ConstructiveRoot
namespace CanonicalUnitArithmeticIntegralFixedCoordinateReadout

open CanonicalUnitArithmeticCoordinateProjectionObstruction
open CanonicalUnitArithmeticDerivedCoordinateRegression
open CanonicalUnitArithmeticEulerDeterminantCoordinateRegression
open CanonicalUnitArithmeticFactorizationFullEulerWholeRelationUniversalSolutionLocalLanding
open CanonicalUnitArithmeticFactorizationWholeHistoryIntegralZeroFiberState
open CanonicalUnitArithmeticUnitNormalizedCoordinateRegression
open CanonicalUnitArithmeticUnitNormalizedRelationHistory

noncomputable section

def settledWholeComponent (stage : Nat)
    (value : IntegralFirstUniversalKernel) : LocalScalarInner stage :=
  localWholeComponent stage
    (localTensorRestriction stage (universalInclusion value))

def settledReversedWholeComponent (stage : Nat)
    (value : IntegralFirstUniversalKernel) : LocalScalarInner stage :=
  localWholeComponent stage
    (localTensorRestriction stage
      (universalInclusion (kernelReversal value)))

/-- Frozen rigidity has generated equality of the actual whole component and
its actual reversal. -/
theorem settledWholeComponent_eq_reversal
    (stage : Nat) (value : IntegralFirstUniversalKernel) :
    settledWholeComponent stage value =
      settledReversedWholeComponent stage value := by
  have fixed := universalWholeAntiInvariant_eq_zero stage value
  change
    localWholeComponent stage
        (localTensorRestriction stage
          (universalInclusion (value - kernelReversal value))) = 0 at fixed
  rw [map_sub, map_sub, map_sub, sub_eq_zero] at fixed
  exact fixed

/-- A linear coordinate/reversal readout consumes the settled equality.  The
two endpoint equations are readout laws, not arithmetic producer premises. -/
theorem coordinate_fixed_of_settled_linear_readout
    (stage : Nat) (value : IntegralFirstUniversalKernel)
    (coordinate : ℂ)
    (evaluation : LocalScalarInner stage →ₗ[ℤ] UnitCoordinate)
    (original : evaluation (settledWholeComponent stage value) =
      unitCoordinateGenerator coordinate)
    (reversed : evaluation (settledReversedWholeComponent stage value) =
      unitCoordinateGenerator (coordinateReversal coordinate)) :
    coordinate = coordinateReversal coordinate := by
  have sameReadout := congrArg evaluation
    (settledWholeComponent_eq_reversal stage value)
  rw [original, reversed] at sameReadout
  exact congrArg Prod.snd sameReadout

theorem coordinateDifference_eq_zero_of_settled_linear_readout
    (stage : Nat) (value : IntegralFirstUniversalKernel)
    (coordinate : ℂ)
    (evaluation : LocalScalarInner stage →ₗ[ℤ] UnitCoordinate)
    (original : evaluation (settledWholeComponent stage value) =
      unitCoordinateGenerator coordinate)
    (reversed : evaluation (settledReversedWholeComponent stage value) =
      unitCoordinateGenerator (coordinateReversal coordinate)) :
    coordinateDifference coordinate = 0 := by
  exact (coordinateDifference_eq_zero_iff_fixed coordinate).2
    (coordinate_fixed_of_settled_linear_readout
      stage value coordinate evaluation original reversed)

theorem real_eq_half_of_settled_linear_readout
    (stage : Nat) (value : IntegralFirstUniversalKernel)
    (coordinate : ℂ)
    (evaluation : LocalScalarInner stage →ₗ[ℤ] UnitCoordinate)
    (original : evaluation (settledWholeComponent stage value) =
      unitCoordinateGenerator coordinate)
    (reversed : evaluation (settledReversedWholeComponent stage value) =
      unitCoordinateGenerator (coordinateReversal coordinate)) :
    coordinate.re = 1 / 2 := by
  have fixed := coordinate_fixed_of_settled_linear_readout
    stage value coordinate evaluation original reversed
  have realFixed := congrArg Complex.re fixed
  change coordinate.re = 1 - coordinate.re at realFixed
  linarith

/-- Existing completion-coordinate specializations can consume the settlement
through one same-occurrence linear readout. -/
theorem existing_specialization_reads_settled_component
    (stage : Nat) (value : IntegralFirstUniversalKernel)
    (coordinate : ℂ)
    (readout : LocalScalarInner stage →ₗ[ℤ] history.CompletionCarrier)
    (original : readout (settledWholeComponent stage value) = componentClass 0)
    (reversed : readout (settledReversedWholeComponent stage value) =
      componentClass 1)
    (specialization : CoordinateSpecializationAt coordinate) :
    coordinate.re = 1 / 2 := by
  exact real_eq_half_of_settled_linear_readout stage value coordinate
    (specialization.evaluation.comp readout)
    (by rw [LinearMap.comp_apply, original, specialization.original])
    (by rw [LinearMap.comp_apply, reversed, specialization.reversed])

end
end CanonicalUnitArithmeticIntegralFixedCoordinateReadout
end ConstructiveRoot
end LivingLawEvolution
end ResponsibilityLifecycle
end SaturationMonoid
