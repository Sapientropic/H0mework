import H0mework.Versions.Y.Arithmetic.RiemannGraph.History.Consumer.LivingLawCanonicalRiemannRuntimeMuntzPrimePowerConductorReindex
import H0mework.Versions.Y.Arithmetic.MellinConductor.Graph.Action.LivingLawCanonicalCoPoissonHalfPositionJointConductorAction

/-!
# Source shells and scalar conductor-term measurement

The selected and reversal unit shells are generated inside their actual
half-position domains.  Their normalized graph-action measurements expose
the integral character at the conductor index selected by a prime-power
receipt.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ResponsibilityLifecycle
namespace LivingLawEvolution
namespace ConstructiveRoot
namespace NoIslandNoMagic
namespace CanonicalRiemann
namespace AllPlace
namespace WeilQuadratic
namespace Runtime
namespace MuntzGraph
namespace Conductor
namespace History

open Character
open CanonicalUnitArithmeticCoordinateProjectionObstruction
open Character.GlobalCoPoissonCurrent
open Character.IntegralCharacterGroupRing
open ClozelGeneralizedDual
open ClozelGeneralizedDual.CenteredGram
open ClozelGeneralizedDual.MuntzConductor.GraphLogPositionCone
open ClozelGeneralizedDual.MuntzConductor.HalfPositionSource
open ClozelGeneralizedDual.MuntzConductor.HalfPositionSource.GraphAction
open ClozelGeneralizedDual.ThetaJRoleRepresentation
open PrimePower.Runtime
open SourceGeneratedFunctionalGraphPerfectification
open SourceGeneratedIntegralCharacterGroupRing
open SourceGeneratedPositiveRealCharacter

noncomputable section

/-- The selected unit shell with its generated half-position-domain witness. -/
def selectedPrimePowerConductorSeed
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1)) :
    quarterMellinHalfPositionSourceDomain
      (selectedCoPoissonMuntzParameter observation) :=
  ⟨selectedIntegralDilationTestOrbit observation nontrivial (delta 1),
    selectedIntegralDilationFeature_mem_domain
      observation nontrivial (delta 1)⟩

/-- Reversal sibling of the same source-generated shell. -/
def reversalPrimePowerConductorSeed
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1)) :
    quarterMellinHalfPositionSourceDomain
      (reversalCoPoissonMuntzParameter observation) :=
  ⟨reversalIntegralDilationTestOrbit observation nontrivial (delta 1),
    reversalIntegralDilationFeature_mem_domain
      observation nontrivial (delta 1)⟩

@[simp] theorem selectedPrimePowerConductorSeed_measurement
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1)) :
    halfPositionGraphFunctional
        (selectedCoPoissonMuntzParameter observation)
        (selectedPrimePowerConductorSeed observation nontrivial) = 1 := by
  change quarterMellinL2Functional
      (selectedCoPoissonMuntzParameter observation)
      (selectedIntegralDilationTestOrbit observation nontrivial (delta 1)) = 1
  rw [selectedIntegralDilationTestOrbit_delta]
  change (selectedGraphOrbitBasis observation nontrivial 1).snd = 1
  rw [selectedGraphOrbitBasis_snd]
  simp [quarterDilationCharacter, scaleSquare, scaleValue]

@[simp] theorem reversalPrimePowerConductorSeed_measurement
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1)) :
    halfPositionGraphFunctional
        (reversalCoPoissonMuntzParameter observation)
        (reversalPrimePowerConductorSeed observation nontrivial) = 1 := by
  change quarterMellinL2Functional
      (reversalCoPoissonMuntzParameter observation)
      (reversalIntegralDilationTestOrbit observation nontrivial (delta 1)) = 1
  rw [reversalIntegralDilationTestOrbit_delta]
  change (reversalGraphOrbitBasis observation nontrivial 1).snd = 1
  rw [reversalGraphOrbitBasis_snd]
  simp [quarterDilationCharacter, scaleSquare, scaleValue]

/-- The graph half-density is the inverse Quarter-Mellin weight at the
squared integer scale. -/
theorem graphHalfDensityWeight_eq_quarterWeight_inv (index : Nat) :
    (graphHalfDensityWeight index : ℂ) =
      (positiveMellinQuarterDilationWeight
        (graphIntegerDilationScale index))⁻¹ := by
  unfold graphHalfDensityWeight positiveMellinQuarterDilationWeight
  rw [graphIntegerDilationScale_log]
  unfold graphLogTranslationShift
  rw [← Complex.ofReal_inv]
  norm_cast
  rw [← Real.exp_neg]
  congr 1
  ring

theorem graphIntegerScaleUnit_primePower
    (prime : Nat.Primes) (exponent : Nat) (positive : 0 < exponent) :
    graphIntegerScaleUnit
        (primePowerConductorObservationIndex prime exponent) =
      primePowerUnit prime exponent := by
  apply Units.ext
  apply NNReal.eq
  rw [show
      (((graphIntegerScaleUnit
          (primePowerConductorObservationIndex prime exponent) :
            Units NNReal) : NNReal) : ℝ) =
        ((primePowerConductorObservationIndex prime exponent + 1 : Nat) : ℝ) by
      rfl]
  unfold primePowerUnit
  rw [positiveRealUnit_val]
  exact_mod_cast primePowerConductorObservationIndex_succ
    prime exponent positive

theorem graphIntegerDilationScale_eq_scaleSquare (index : Nat) :
    graphIntegerDilationScale index =
      scaleSquare (graphIntegerScaleUnit index) := by
  rfl

theorem selectedJointConductorTerm_measurement
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (coefficients : ArithmeticFunction ℝ) (index : Nat) :
    (graphNormalizedHalfPositionJointActionTerm
        (selectedCoPoissonMuntzParameter observation) coefficients index
        (graphFeature
          (halfPositionGraphFeature
            (selectedCoPoissonMuntzParameter observation))
          (halfPositionGraphFunctional
            (selectedCoPoissonMuntzParameter observation))
          (selectedPrimePowerConductorSeed observation nontrivial))).snd =
      (coefficients (index + 1) : ℂ) *
        selectedGraphCharacterBasisReadback observation nontrivial
          (graphIntegerScaleUnit index) := by
  rw [graphNormalizedHalfPositionJointActionTerm_snd,
    (graphFeature_apply
      (halfPositionGraphFeature
        (selectedCoPoissonMuntzParameter observation))
      (halfPositionGraphFunctional
        (selectedCoPoissonMuntzParameter observation))
      (selectedPrimePowerConductorSeed observation nontrivial)).2,
    selectedPrimePowerConductorSeed_measurement, mul_one,
    graphHalfDensityWeight_eq_quarterWeight_inv]
  unfold selectedGraphCharacterBasisReadback
  rw [selectedGraphOrbitBasis_snd,
    graphIntegerDilationScale_eq_scaleSquare]
  ring

theorem reversalJointConductorTerm_measurement
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (coefficients : ArithmeticFunction ℝ) (index : Nat) :
    (graphNormalizedHalfPositionJointActionTerm
        (reversalCoPoissonMuntzParameter observation) coefficients index
        (graphFeature
          (halfPositionGraphFeature
            (reversalCoPoissonMuntzParameter observation))
          (halfPositionGraphFunctional
            (reversalCoPoissonMuntzParameter observation))
          (reversalPrimePowerConductorSeed observation nontrivial))).snd =
      (coefficients (index + 1) : ℂ) *
        reversalGraphCharacterBasisReadback observation nontrivial
          (graphIntegerScaleUnit index) := by
  rw [graphNormalizedHalfPositionJointActionTerm_snd,
    (graphFeature_apply
      (halfPositionGraphFeature
        (reversalCoPoissonMuntzParameter observation))
      (halfPositionGraphFunctional
        (reversalCoPoissonMuntzParameter observation))
      (reversalPrimePowerConductorSeed observation nontrivial)).2,
    reversalPrimePowerConductorSeed_measurement, mul_one,
    graphHalfDensityWeight_eq_quarterWeight_inv]
  unfold reversalGraphCharacterBasisReadback
  rw [reversalGraphOrbitBasis_snd,
    graphIntegerDilationScale_eq_scaleSquare]
  ring

theorem selectedGraphCharacterBasisReadback_eq_complexPower
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (scale : Units NNReal) :
    selectedGraphCharacterBasisReadback observation nontrivial scale =
      complexPowerCharacter observation.coordinate scale := by
  rw [← selectedGraphCharacterEvaluation_delta,
    selectedGraphCharacterEvaluation_eq_integralOccurrence,
    zeroOwnedIntegralCharacterOccurrence_root_selected,
    characterEvaluation_delta,
    zeroOwnedMultiplicativeCharacterOccurrence_root_selected]

theorem reversalGraphCharacterBasisReadback_eq_complexPower
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (scale : Units NNReal) :
    reversalGraphCharacterBasisReadback observation nontrivial scale =
      complexPowerCharacter (coordinateReversal observation.coordinate) scale := by
  rw [← reversalGraphCharacterEvaluation_delta,
    reversalGraphCharacterEvaluation_eq_integralOccurrence,
    zeroOwnedIntegralCharacterOccurrence_root_reversal,
    characterEvaluation_delta,
    zeroOwnedMultiplicativeCharacterOccurrence_root_reversal]

end
end History
end Conductor
end MuntzGraph
end Runtime
end WeilQuadratic
end AllPlace
end CanonicalRiemann
end NoIslandNoMagic
end ConstructiveRoot
end LivingLawEvolution
end ResponsibilityLifecycle
end SaturationMonoid
