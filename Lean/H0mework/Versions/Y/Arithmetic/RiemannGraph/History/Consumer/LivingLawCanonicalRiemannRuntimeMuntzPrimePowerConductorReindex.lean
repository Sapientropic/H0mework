import H0mework.Versions.Y.Arithmetic.RiemannGraph.History.Consumer.LivingLawCanonicalRiemannRuntimeMuntzConductorHistoryConsumer

/-!
# Prime-power receipt on the independent conductor clock

The q-rich runtime depth and conductor observation index encode different
coordinates of the same exact occurrence.  A prime-power receipt is emitted
at runtime depth `(p^k)^2 - 3`; inside that occurrence the independently
rooted conductor history observes the physical successor at `p^k - 1`.
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

open CanonicalUnitArithmeticRoot
open Material
open PrimePower.Runtime

noncomputable section

def primePowerConductorObservationIndex
    (prime : Nat.Primes) (exponent : Nat) : Nat :=
  (primePowerRuntimeScale prime exponent) - 1

theorem primePowerConductorObservationIndex_succ
    (prime : Nat.Primes) (exponent : Nat) (positive : 0 < exponent) :
    primePowerConductorObservationIndex prime exponent + 1 =
      primePowerRuntimeScale prime exponent := by
  unfold primePowerConductorObservationIndex
  exact Nat.sub_add_cancel
    (Nat.one_le_iff_ne_zero.mpr
      (Nat.ne_of_gt
        (lt_of_lt_of_le Nat.zero_lt_two
          (primePowerRuntimeScale_two_le prime exponent positive))))

/-- The physical conductor successor is observed inside the exact
prime-power runtime occurrence without identifying its index with the
q-rich runtime depth. -/
theorem primePowerRuntimeOccurrence_observes_conductorSuccessor
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (prime : Nat.Primes) (exponent : Nat) :
    conductorSuccessorPresentedEvent
        (primePowerConductorObservationIndex prime exponent) ∈
      (((runtimeConductorHistoryMaterialLaw observation nontrivial).historyAt
        (Consumer.primePowerRuntimeOccurrence
          observation nontrivial prime exponent)).observation
            (primePowerConductorObservationIndex prime exponent)).trace := by
  exact materialHistory_observes_successor observation nontrivial
    (Consumer.primePowerRuntimeOccurrence
      observation nontrivial prime exponent)
    (primePowerConductorObservationIndex prime exponent)

/-- One direct consumer keeps the arithmetic receipt, the q-rich runtime
depth, the independent conductor successor, and the actual increment
readback together. -/
theorem primePowerRuntimeReceipt_conductorClock_consumer
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (test : SchwartzMap ℝ ℂ) (scale : ℝ)
    (prime : Nat.Primes) (exponent : Nat) (positive : 0 < exponent) :
    let face := Consumer.primePowerRuntimeFace
      observation nontrivial prime exponent
    type_of% (primePowerRuntime_actualReceipt prime exponent positive) ∧
      face.stage = primePowerRuntimeStage prime exponent ∧
      conductorSuccessorPresentedEvent
          (primePowerConductorObservationIndex prime exponent) ∈
        (((runtimeConductorHistoryMaterialLaw observation nontrivial).historyAt
          face.exactOccurrence).observation
            (primePowerConductorObservationIndex prime exponent)).trace ∧
      conductorHistoryGeneratorValue face
          ((primePowerConductorObservationIndex prime exponent), .increment)
            test scale =
        (Real.log ((prime : Nat) : ℝ) : ℂ) *
          ClozelGeneralizedDual.coPoissonMuntzEvenSource test
            ((primePowerRuntimeScale prime exponent : ℝ) * scale) := by
  dsimp only
  refine ⟨primePowerRuntime_actualReceipt prime exponent positive,
    Consumer.primePowerRuntimeFace_stage
      observation nontrivial prime exponent, ?_, ?_⟩
  · rw [(Consumer.primePowerRuntimeFace observation nontrivial prime exponent
      ).exactOccurrence_eq]
    exact primePowerRuntimeOccurrence_observes_conductorSuccessor
      observation nontrivial prime exponent
  · unfold primePowerConductorObservationIndex primePowerRuntimeScale
    exact primePowerConductorHistoryIncrement_readback
      observation nontrivial test scale prime exponent positive

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
