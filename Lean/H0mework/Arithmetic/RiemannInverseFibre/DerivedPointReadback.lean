import H0mework.Arithmetic.EulerDerived.SolutionFixedCoordinate
import H0mework.Arithmetic.RiemannInverseFibre.ReversalResidual

/-!
# Branch-aware derived-point consumer of the complete inverse fibre

The chart carrying the observed zero selects the matching existing derived
readback; the opposite chart reads the surviving partner residual.  This is
a fixedness-free consumer.  It neither identifies the two scalars nor
constructs a q-rich cycle.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ResponsibilityLifecycle
namespace LivingLawEvolution
namespace ConstructiveRoot
namespace NoIslandNoMagic
namespace CanonicalRiemann

open CanonicalUnitArithmeticFactorizationEulerDependentDiagram
open CanonicalUnitArithmeticFactorizationWholeHistorySolutionCarrier
open CanonicalUnitArithmeticCoordinateProjectionObstruction
open CanonicalUnitArithmeticFactorizationFullEulerWholePrimeDualBlockDerivedSolutionPointSpecialization
open CanonicalUnitArithmeticFactorizationFullEulerWholePrimeDualBlockDerivedSolutionFixedCoordinateReadback

noncomputable section

namespace InverseZeroFibre

def selectedDerivedReadback
    {observation : GeneratedRiemannZeroObservation}
    (fibre : InverseZeroFibre observation)
    (stage : Nat) (row : FactorRow seedOccurrence.root stage) : ℂ :=
  match fibre.1 with
  | .left point _ =>
      pointDerivedPointEndpointReadback point stage row
        (determinantLineDerivedSolutionPoint point)
  | .right point _ =>
      pointDerivedPointEndpointReadback point stage row
        (determinantLineReversedDerivedSolutionPoint point)

def partnerDerivedReadback
    {observation : GeneratedRiemannZeroObservation}
    (fibre : InverseZeroFibre observation)
    (stage : Nat) (row : FactorRow seedOccurrence.root stage) : ℂ :=
  match fibre.1 with
  | .left point _ =>
      pointDerivedPointEndpointReadback point stage row
        (determinantLineReversedDerivedSolutionPoint point)
  | .right point _ =>
      pointDerivedPointEndpointReadback point stage row
        (determinantLineDerivedSolutionPoint point)

theorem selectedDerivedReadback_eq_observation
    {observation : GeneratedRiemannZeroObservation}
    (fibre : InverseZeroFibre observation)
    (stage : Nat) (row : FactorRow seedOccurrence.root stage) :
    selectedDerivedReadback fibre stage row = observation.coordinate := by
  rcases fibre with ⟨incidence, readback⟩
  cases incidence with
  | left point zero =>
      change pointDerivedPointEndpointReadback point stage row
          (determinantLineDerivedSolutionPoint point) = _
      rw [pointDerivedSolutionPoint_readback]
      exact congrArg GeneratedRiemannZeroObservationAt.coordinate readback
  | right point zero =>
      change pointDerivedPointEndpointReadback point stage row
          (determinantLineReversedDerivedSolutionPoint point) = _
      rw [pointReversedDerivedSolutionPoint_readback]
      exact congrArg GeneratedRiemannZeroObservationAt.coordinate readback

theorem partnerDerivedReadback_eq_residual
    {observation : GeneratedRiemannZeroObservation}
    (fibre : InverseZeroFibre observation)
    (stage : Nat) (row : FactorRow seedOccurrence.root stage) :
    partnerDerivedReadback fibre stage row = partnerResidual fibre := by
  rcases fibre with ⟨incidence, readback⟩
  cases incidence with
  | left point zero =>
      exact pointReversedDerivedSolutionPoint_readback point stage row
  | right point zero =>
      exact pointDerivedSolutionPoint_readback point stage row

theorem mathlibLeftRegressionComponent_selectedReadback
    (observation : GeneratedRiemannZeroObservation)
    (stage : Nat) (row : FactorRow seedOccurrence.root stage) :
    selectedDerivedReadback (mathlibLeftRegressionComponent observation)
        stage row = observation.coordinate :=
  selectedDerivedReadback_eq_observation _ _ _

theorem mathlibLeftRegressionComponent_partnerReadback
    (observation : GeneratedRiemannZeroObservation)
    (stage : Nat) (row : FactorRow seedOccurrence.root stage) :
    partnerDerivedReadback (mathlibLeftRegressionComponent observation)
        stage row = coordinateReversal observation.coordinate := by
  rw [partnerDerivedReadback_eq_residual]
  rfl

end InverseZeroFibre

end
end CanonicalRiemann
end NoIslandNoMagic
end ConstructiveRoot
end LivingLawEvolution
end ResponsibilityLifecycle
end SaturationMonoid
