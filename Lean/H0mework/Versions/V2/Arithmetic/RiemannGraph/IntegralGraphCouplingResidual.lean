import H0mework.Versions.V2.Arithmetic.RiemannGraph.GraphTargetOwnerFreeDilation
import H0mework.Versions.V2.Arithmetic.RiemannGraph.IntegralGraphOrbit

/-!
# Owner-free coupling residual of the integral graph orbit

Integral left translation and owner-free coherent evolution commute exactly
on the energy coordinate.  Their entire mismatch lies in the measurement
coordinate and has normal form `(1 - χ(a²)) χ(b²)`.  This is the typed
detector-coupling residual; inserting the zero-dependent character into the
action would hide rather than settle it.
-/

set_option autoImplicit false
set_option maxHeartbeats 3000000

namespace SaturationMonoid
namespace ResponsibilityLifecycle
namespace LivingLawEvolution
namespace ConstructiveRoot
namespace NoIslandNoMagic
namespace CanonicalRiemann
namespace ClozelGeneralizedDual
namespace CenteredGram

open Character
open Character.GlobalCoPoissonCurrent
open ThetaJRoleRepresentation
open SourceGeneratedIntegralCharacterGroupRing

noncomputable section

/-- Owner-free coherent evolution at the squared scale used by the integral
graph orbit. -/
def ownerFreeGraphProductAction (scale : Units NNReal) :
    JointGraphTarget →L[ℂ] JointGraphTarget :=
  (positiveMellinQuarterGraphTargetIsometry
    (Real.log (scaleSquare scale))).toContinuousLinearEquiv.toContinuousLinearMap

@[simp] theorem ownerFreeGraphProductAction_fst
    (scale : Units NNReal) (value : JointGraphTarget) :
    (ownerFreeGraphProductAction scale value).fst =
      positiveMellinQuarterEnergyTranslation
        (Real.log (scaleSquare scale)) value.fst :=
  rfl

@[simp] theorem ownerFreeGraphProductAction_snd
    (scale : Units NNReal) (value : JointGraphTarget) :
    (ownerFreeGraphProductAction scale value).snd = value.snd :=
  rfl

/-- Exact selected mismatch between integral translation and owner-free
evolution. -/
def selectedOwnerFreeCouplingResidual
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (scale : Units NNReal) :
    IntegralScaleCarrier →ₗ[ℤ] JointGraphTarget :=
  ((ownerFreeGraphProductAction scale).toLinearMap.restrictScalars ℤ).comp
      (selectedIntegralGraphOrbit observation nontrivial) -
    (selectedIntegralGraphOrbit observation nontrivial).comp
      (leftTranslation scale).toLinearMap

def reversalOwnerFreeCouplingResidual
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (scale : Units NNReal) :
    IntegralScaleCarrier →ₗ[ℤ] JointGraphTarget :=
  ((ownerFreeGraphProductAction scale).toLinearMap.restrictScalars ℤ).comp
      (reversalIntegralGraphOrbit observation nontrivial) -
    (reversalIntegralGraphOrbit observation nontrivial).comp
      (leftTranslation scale).toLinearMap

theorem selectedOwnerFreeCouplingResidual_delta_fst
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (left right : Units NNReal) :
    (selectedOwnerFreeCouplingResidual
      observation nontrivial left (delta right)).fst = 0 := by
  have translated :
      (leftTranslation left).toLinearMap (delta right) =
        delta (left * right) :=
    leftTranslation_delta left right
  rw [selectedOwnerFreeCouplingResidual, LinearMap.sub_apply,
    LinearMap.comp_apply, LinearMap.comp_apply,
    selectedIntegralGraphOrbit_delta, translated,
    selectedIntegralGraphOrbit_delta]
  change
    (ownerFreeGraphProductAction left
        (selectedGraphOrbitBasis observation nontrivial right)).fst -
      (selectedGraphOrbitBasis observation nontrivial (left * right)).fst = 0
  rw [ownerFreeGraphProductAction_fst,
    selectedGraphOrbitBasis_fst, selectedGraphOrbitBasis_fst]
  have composition := LinearMap.congr_fun
    (positiveMellinQuarterEnergyTranslation_comp
      (Real.log (scaleSquare left)) (Real.log (scaleSquare right)))
    (quarterMellinL2Feature
      (selectedCoPoissonMuntzParameter observation)
      (normalizedCoPoissonMuntzQuarterShellTest
        (selectedCoPoissonMuntzParameter observation)
        (selectedCoPoissonMuntzParameter_re_pos observation nontrivial)))
  change positiveMellinQuarterEnergyTranslation
      (Real.log (scaleSquare left))
      (positiveMellinQuarterEnergyTranslation
        (Real.log (scaleSquare right))
        (quarterMellinL2Feature
          (selectedCoPoissonMuntzParameter observation)
          (normalizedCoPoissonMuntzQuarterShellTest
            (selectedCoPoissonMuntzParameter observation)
            (selectedCoPoissonMuntzParameter_re_pos
              observation nontrivial)))) =
    positiveMellinQuarterEnergyTranslation
      (Real.log (scaleSquare right) + Real.log (scaleSquare left))
      (quarterMellinL2Feature
        (selectedCoPoissonMuntzParameter observation)
        (normalizedCoPoissonMuntzQuarterShellTest
          (selectedCoPoissonMuntzParameter observation)
          (selectedCoPoissonMuntzParameter_re_pos
            observation nontrivial))) at composition
  rw [composition, log_scaleSquare_mul, add_comm]
  exact sub_self _

theorem selectedOwnerFreeCouplingResidual_delta_snd
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (left right : Units NNReal) :
    (selectedOwnerFreeCouplingResidual
      observation nontrivial left (delta right)).snd =
      quarterDilationCharacter
          (selectedCoPoissonMuntzParameter observation)
          (scaleSquare right) -
        quarterDilationCharacter
          (selectedCoPoissonMuntzParameter observation)
          (scaleSquare (left * right)) := by
  have translated :
      (leftTranslation left).toLinearMap (delta right) =
        delta (left * right) :=
    leftTranslation_delta left right
  rw [selectedOwnerFreeCouplingResidual, LinearMap.sub_apply,
    LinearMap.comp_apply, LinearMap.comp_apply,
    selectedIntegralGraphOrbit_delta, translated,
    selectedIntegralGraphOrbit_delta]
  change
    (ownerFreeGraphProductAction left
        (selectedGraphOrbitBasis observation nontrivial right)).snd -
      (selectedGraphOrbitBasis observation nontrivial (left * right)).snd = _
  rw [ownerFreeGraphProductAction_snd,
    selectedGraphOrbitBasis_snd, selectedGraphOrbitBasis_snd]

theorem reversalOwnerFreeCouplingResidual_delta_fst
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (left right : Units NNReal) :
    (reversalOwnerFreeCouplingResidual
      observation nontrivial left (delta right)).fst = 0 := by
  have translated :
      (leftTranslation left).toLinearMap (delta right) =
        delta (left * right) :=
    leftTranslation_delta left right
  rw [reversalOwnerFreeCouplingResidual, LinearMap.sub_apply,
    LinearMap.comp_apply, LinearMap.comp_apply,
    reversalIntegralGraphOrbit_delta, translated,
    reversalIntegralGraphOrbit_delta]
  change
    (ownerFreeGraphProductAction left
        (reversalGraphOrbitBasis observation nontrivial right)).fst -
      (reversalGraphOrbitBasis observation nontrivial (left * right)).fst = 0
  rw [ownerFreeGraphProductAction_fst,
    reversalGraphOrbitBasis_fst, reversalGraphOrbitBasis_fst]
  have composition := LinearMap.congr_fun
    (positiveMellinQuarterEnergyTranslation_comp
      (Real.log (scaleSquare left)) (Real.log (scaleSquare right)))
    (quarterMellinL2Feature
      (reversalCoPoissonMuntzParameter observation)
      (normalizedCoPoissonMuntzQuarterShellTest
        (reversalCoPoissonMuntzParameter observation)
        (reversalCoPoissonMuntzParameter_re_pos observation nontrivial)))
  change positiveMellinQuarterEnergyTranslation
      (Real.log (scaleSquare left))
      (positiveMellinQuarterEnergyTranslation
        (Real.log (scaleSquare right))
        (quarterMellinL2Feature
          (reversalCoPoissonMuntzParameter observation)
          (normalizedCoPoissonMuntzQuarterShellTest
            (reversalCoPoissonMuntzParameter observation)
            (reversalCoPoissonMuntzParameter_re_pos
              observation nontrivial)))) =
    positiveMellinQuarterEnergyTranslation
      (Real.log (scaleSquare right) + Real.log (scaleSquare left))
      (quarterMellinL2Feature
        (reversalCoPoissonMuntzParameter observation)
        (normalizedCoPoissonMuntzQuarterShellTest
          (reversalCoPoissonMuntzParameter observation)
          (reversalCoPoissonMuntzParameter_re_pos
            observation nontrivial))) at composition
  rw [composition, log_scaleSquare_mul, add_comm]
  exact sub_self _

theorem reversalOwnerFreeCouplingResidual_delta_snd
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (left right : Units NNReal) :
    (reversalOwnerFreeCouplingResidual
      observation nontrivial left (delta right)).snd =
      quarterDilationCharacter
          (reversalCoPoissonMuntzParameter observation)
          (scaleSquare right) -
        quarterDilationCharacter
          (reversalCoPoissonMuntzParameter observation)
          (scaleSquare (left * right)) := by
  have translated :
      (leftTranslation left).toLinearMap (delta right) =
        delta (left * right) :=
    leftTranslation_delta left right
  rw [reversalOwnerFreeCouplingResidual, LinearMap.sub_apply,
    LinearMap.comp_apply, LinearMap.comp_apply,
    reversalIntegralGraphOrbit_delta, translated,
    reversalIntegralGraphOrbit_delta]
  change
    (ownerFreeGraphProductAction left
        (reversalGraphOrbitBasis observation nontrivial right)).snd -
      (reversalGraphOrbitBasis observation nontrivial (left * right)).snd = _
  rw [ownerFreeGraphProductAction_snd,
    reversalGraphOrbitBasis_snd, reversalGraphOrbitBasis_snd]

theorem selectedOwnerFreeCouplingResidual_delta_normalForm
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (left right : Units NNReal) :
    (selectedOwnerFreeCouplingResidual
        observation nontrivial left (delta right)).snd =
      (1 - quarterDilationCharacter
          (selectedCoPoissonMuntzParameter observation)
          (scaleSquare left)) *
        quarterDilationCharacter
          (selectedCoPoissonMuntzParameter observation)
          (scaleSquare right) := by
  rw [selectedOwnerFreeCouplingResidual_delta_snd,
    quarterDilationCharacter_scaleSquare_mul]
  ring

theorem reversalOwnerFreeCouplingResidual_delta_normalForm
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (left right : Units NNReal) :
    (reversalOwnerFreeCouplingResidual
        observation nontrivial left (delta right)).snd =
      (1 - quarterDilationCharacter
          (reversalCoPoissonMuntzParameter observation)
          (scaleSquare left)) *
        quarterDilationCharacter
          (reversalCoPoissonMuntzParameter observation)
          (scaleSquare right) := by
  rw [reversalOwnerFreeCouplingResidual_delta_snd,
    quarterDilationCharacter_scaleSquare_mul]
  ring

theorem selectedOwnerFreeCouplingResidual_delta_snd_eq_zero_iff
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (left right : Units NNReal) :
    (selectedOwnerFreeCouplingResidual
          observation nontrivial left (delta right)).snd = 0 ↔
      quarterDilationCharacter
          (selectedCoPoissonMuntzParameter observation)
          (scaleSquare left) = 1 := by
  rw [selectedOwnerFreeCouplingResidual_delta_normalForm]
  constructor
  · intro productZero
    have leftZero := (mul_eq_zero.mp productZero).resolve_right
      (quarterDilationCharacter_ne_zero
        (selectedCoPoissonMuntzParameter observation)
        (scaleSquare right) (scaleSquare_pos right))
    exact (sub_eq_zero.mp leftZero).symm
  · intro characterOne
    rw [characterOne, sub_self, zero_mul]

theorem reversalOwnerFreeCouplingResidual_delta_snd_eq_zero_iff
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (left right : Units NNReal) :
    (reversalOwnerFreeCouplingResidual
          observation nontrivial left (delta right)).snd = 0 ↔
      quarterDilationCharacter
          (reversalCoPoissonMuntzParameter observation)
          (scaleSquare left) = 1 := by
  rw [reversalOwnerFreeCouplingResidual_delta_normalForm]
  constructor
  · intro productZero
    have leftZero := (mul_eq_zero.mp productZero).resolve_right
      (quarterDilationCharacter_ne_zero
        (reversalCoPoissonMuntzParameter observation)
        (scaleSquare right) (scaleSquare_pos right))
    exact (sub_eq_zero.mp leftZero).symm
  · intro characterOne
    rw [characterOne, sub_self, zero_mul]

end


end CenteredGram
end ClozelGeneralizedDual
end CanonicalRiemann
end NoIslandNoMagic
end ConstructiveRoot
end LivingLawEvolution
end ResponsibilityLifecycle
end SaturationMonoid
