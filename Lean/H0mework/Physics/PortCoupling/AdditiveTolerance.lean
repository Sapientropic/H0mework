import H0mework.Physics.LCDesign.Components

/-!
# Finite additive-disturbance tolerance kernel

An implementation may combine an inexact complex-linear endpoint operator
with an arbitrary input-dependent additive disturbance.  The disturbance is
not assumed linear, constant, source-independent or channel-diagonal.

A `1/80` linear-part margin and a uniform `1/8` disturbance bound preserve
the active, inactive, intervention and cross-channel threshold separations.
No observation verdict, coupling receipt, consciousness or body predicate is
stored in the tolerance certificate.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace NoIslandNoMagic
namespace Consciousness
namespace Immortality
namespace Embodied
namespace Canonical
namespace Coupling
namespace Physical
namespace Producer

open Physical.Interface

noncomputable section

abbrev EndpointDisturbance :=
  FiniteEmbodimentState → HilbertEmbodimentState

def disturbedImplementedState
    (linearPart : HilbertEmbodimentState →L[ℂ] HilbertEmbodimentState)
    (disturbance : EndpointDisturbance)
    (state : FiniteEmbodimentState) : FiniteEmbodimentState :=
  decodeHilbert (linearPart (encodeHilbert state) + disturbance state)

@[simp] theorem encodeHilbert_disturbedImplementedState
    (linearPart : HilbertEmbodimentState →L[ℂ] HilbertEmbodimentState)
    (disturbance : EndpointDisturbance)
    (state : FiniteEmbodimentState) :
    encodeHilbert (disturbedImplementedState linearPart disturbance state) =
      linearPart (encodeHilbert state) + disturbance state := by
  simp [disturbedImplementedState]

structure AdditiveDisturbanceToleranceAt
    (linearPart : HilbertEmbodimentState →L[ℂ] HilbertEmbodimentState)
    (disturbance : EndpointDisturbance) : Prop where
  linearPartTolerance :
    ‖linearPart - idealQuarterOperator‖ < (1 : ℝ) / 80
  disturbanceBound : ∀ state, ‖disturbance state‖ < (1 : ℝ) / 8

theorem disturbedImplementation_hilbertError_le
    (linearPart : HilbertEmbodimentState →L[ℂ] HilbertEmbodimentState)
    (disturbance : EndpointDisturbance)
    (state : FiniteEmbodimentState) :
    ‖encodeHilbert (disturbedImplementedState linearPart disturbance state) -
        idealQuarterOperator (encodeHilbert state)‖ ≤
      ‖linearPart - idealQuarterOperator‖ * ‖encodeHilbert state‖ +
        ‖disturbance state‖ := by
  rw [encodeHilbert_disturbedImplementedState]
  rw [show linearPart (encodeHilbert state) + disturbance state -
      idealQuarterOperator (encodeHilbert state) =
      (linearPart - idealQuarterOperator) (encodeHilbert state) +
        disturbance state by simp; abel]
  exact (norm_add_le _ _).trans
    (add_le_add
      (ContinuousLinearMap.le_opNorm
        (linearPart - idealQuarterOperator) (encodeHilbert state)) le_rfl)

theorem activeDisturbedImplementation_hilbertError_lt_quarter
    (linearPart : HilbertEmbodimentState →L[ℂ] HilbertEmbodimentState)
    (disturbance : EndpointDisturbance)
    (tolerant : AdditiveDisturbanceToleranceAt linearPart disturbance) :
    ‖encodeHilbert
          (disturbedImplementedState linearPart disturbance
            (preparedState true)) -
        encodeHilbert (evolutionAtOccurrence true)‖ < (1 : ℝ) / 4 := by
  rw [show encodeHilbert (evolutionAtOccurrence true) =
      idealQuarterOperator (encodeHilbert (preparedState true)) by
    rw [idealQuarterOperator_apply]
    exact congrArg encodeHilbert
      (harmonicFlow_pi_div_two_eq_evolve_on_prepared true).symm]
  have operatorContribution :
      ‖linearPart - idealQuarterOperator‖ *
          ‖encodeHilbert (preparedState true)‖ < (1 : ℝ) / 8 := by
    calc
      _ < ((1 : ℝ) / 80) * ‖encodeHilbert (preparedState true)‖ :=
        mul_lt_mul_of_pos_right tolerant.linearPartTolerance
          norm_encodeHilbert_preparedState_true_pos
      _ ≤ ((1 : ℝ) / 80) * 10 :=
        mul_le_mul_of_nonneg_left
          norm_encodeHilbert_preparedState_true_le_ten (by norm_num)
      _ = (1 : ℝ) / 8 := by norm_num
  exact lt_of_le_of_lt
    (disturbedImplementation_hilbertError_le linearPart disturbance
      (preparedState true))
    (by nlinarith [tolerant.disturbanceBound (preparedState true)])

theorem interventionDisturbedImplementation_hilbertError_lt_quarter
    (linearPart : HilbertEmbodimentState →L[ℂ] HilbertEmbodimentState)
    (disturbance : EndpointDisturbance)
    (tolerant : AdditiveDisturbanceToleranceAt linearPart disturbance)
    (channel : FiniteEmbodimentChannel) :
    ‖encodeHilbert
          (disturbedImplementedState linearPart disturbance
            (intervention channel 1)) -
        encodeHilbert (evolve (intervention channel 1))‖ < (1 : ℝ) / 4 := by
  rw [show encodeHilbert (evolve (intervention channel 1)) =
      idealQuarterOperator (encodeHilbert (intervention channel 1)) by
    rw [idealQuarterOperator_apply]
    exact congrArg encodeHilbert
      (harmonicFlow_pi_div_two_eq_evolve_on_intervention channel 1).symm]
  have errorBound := disturbedImplementation_hilbertError_le
    linearPart disturbance (intervention channel 1)
  rw [norm_encodeHilbert_intervention_one] at errorBound
  exact lt_of_le_of_lt errorBound
    (by nlinarith [tolerant.linearPartTolerance,
      tolerant.disturbanceBound (intervention channel 1)])

theorem activeDisturbedImplementation_allTargetsAboveHalf
    (linearPart : HilbertEmbodimentState →L[ℂ] HilbertEmbodimentState)
    (disturbance : EndpointDisturbance)
    (tolerant : AdditiveDisturbanceToleranceAt linearPart disturbance)
    (channel : FiniteEmbodimentChannel) :
    (1 : ℝ) / 2 < targetPort
      (disturbedImplementedState linearPart disturbance (preparedState true))
      channel := by
  have error := lt_of_le_of_lt
    (targetPort_error_le_hilbertError
      (disturbedImplementedState linearPart disturbance (preparedState true))
      (evolutionAtOccurrence true) channel)
    (activeDisturbedImplementation_hilbertError_lt_quarter
      linearPart disturbance tolerant)
  have exactTarget : targetPort (evolutionAtOccurrence true) channel = 1 := by
    simp [evolutionAtOccurrence, physicalNoSuspendedCausalMagic,
      preparedState, evolve, targetPort]
  rw [exactTarget] at error
  have lower := (abs_lt.mp error).1
  linarith

theorem interventionDisturbedImplementation_correspondingTargetAboveHalf
    (linearPart : HilbertEmbodimentState →L[ℂ] HilbertEmbodimentState)
    (disturbance : EndpointDisturbance)
    (tolerant : AdditiveDisturbanceToleranceAt linearPart disturbance)
    (channel : FiniteEmbodimentChannel) :
    (1 : ℝ) / 2 < targetPort
      (disturbedImplementedState linearPart disturbance
        (intervention channel 1)) channel := by
  have error := lt_of_le_of_lt
    (targetPort_error_le_hilbertError
      (disturbedImplementedState linearPart disturbance
        (intervention channel 1))
      (evolve (intervention channel 1)) channel)
    (interventionDisturbedImplementation_hilbertError_lt_quarter
      linearPart disturbance tolerant channel)
  rw [intervention_hits_corresponding_target] at error
  have lower := (abs_lt.mp error).1
  linarith

theorem interventionDisturbedImplementation_otherTargetBelowHalf
    (linearPart : HilbertEmbodimentState →L[ℂ] HilbertEmbodimentState)
    (disturbance : EndpointDisturbance)
    (tolerant : AdditiveDisturbanceToleranceAt linearPart disturbance)
    {sourceChannel targetChannel : FiniteEmbodimentChannel}
    (different : targetChannel ≠ sourceChannel) :
    targetPort
        (disturbedImplementedState linearPart disturbance
          (intervention sourceChannel 1)) targetChannel < (1 : ℝ) / 2 := by
  have error := lt_of_le_of_lt
    (targetPort_error_le_hilbertError
      (disturbedImplementedState linearPart disturbance
        (intervention sourceChannel 1))
      (evolve (intervention sourceChannel 1)) targetChannel)
    (interventionDisturbedImplementation_hilbertError_lt_quarter
      linearPart disturbance tolerant sourceChannel)
  rw [intervention_leaves_other_target_zero different] at error
  have upper := (abs_lt.mp error).2
  linarith

theorem targetPort_abs_le_encodeHilbertNorm
    (state : FiniteEmbodimentState) (channel : FiniteEmbodimentChannel) :
    |targetPort state channel| ≤ ‖encodeHilbert state‖ := by
  have bound := targetPort_error_le_hilbertError state 0 channel
  have encodedZero : encodeHilbert (0 : FiniteEmbodimentState) = 0 := by
    ext candidate
    simp [encodeHilbert, encodeComplex, encodePort]
  rw [encodedZero, sub_zero] at bound
  simpa [targetPort] using bound

theorem falseDisturbedImplementation_allTargetsBelowHalf
    (linearPart : HilbertEmbodimentState →L[ℂ] HilbertEmbodimentState)
    (disturbance : EndpointDisturbance)
    (tolerant : AdditiveDisturbanceToleranceAt linearPart disturbance)
    (channel : FiniteEmbodimentChannel) :
    targetPort
      (disturbedImplementedState linearPart disturbance (preparedState false))
      channel < (1 : ℝ) / 2 := by
  have coordinateBound := targetPort_abs_le_encodeHilbertNorm
    (disturbedImplementedState linearPart disturbance (preparedState false))
    channel
  have encodedFalse :
      encodeHilbert
          (disturbedImplementedState linearPart disturbance
            (preparedState false)) =
        disturbance (preparedState false) := by
    rw [encodeHilbert_disturbedImplementedState]
    have preparedZero : preparedState false = 0 := by
      funext candidate
      simp [preparedState]
    rw [preparedZero]
    have encodedZero : encodeHilbert (0 : FiniteEmbodimentState) = 0 := by
      ext candidate
      simp [encodeHilbert, encodeComplex, encodePort]
    rw [encodedZero, map_zero, zero_add]
  rw [encodedFalse] at coordinateBound
  calc
    targetPort
        (disturbedImplementedState linearPart disturbance
          (preparedState false)) channel ≤
      |targetPort
        (disturbedImplementedState linearPart disturbance
          (preparedState false)) channel| := le_abs_self _
    _ ≤ ‖disturbance (preparedState false)‖ := coordinateBound
    _ < (1 : ℝ) / 8 := tolerant.disturbanceBound _
    _ < (1 : ℝ) / 2 := by norm_num

theorem interventionDisturbedImplementation_sensitiveZeroToOne
    (linearPart : HilbertEmbodimentState →L[ℂ] HilbertEmbodimentState)
    (disturbance : EndpointDisturbance)
    (tolerant : AdditiveDisturbanceToleranceAt linearPart disturbance)
    (channel : FiniteEmbodimentChannel) :
    targetPort
        (disturbedImplementedState linearPart disturbance
          (intervention channel 0)) channel ≠
      targetPort
        (disturbedImplementedState linearPart disturbance
          (intervention channel 1)) channel := by
  have zeroInput : intervention channel 0 = preparedState false := by
    funext candidate
    by_cases same : candidate = channel <;>
      simp [intervention, preparedState, same]
  have below := falseDisturbedImplementation_allTargetsBelowHalf
    linearPart disturbance tolerant channel
  rw [← zeroInput] at below
  have above := interventionDisturbedImplementation_correspondingTargetAboveHalf
    linearPart disturbance tolerant channel
  intro same
  rw [same] at below
  linarith

end

end Producer
end Physical
end Coupling
end Canonical
end Embodied
end Immortality
end Consciousness
end NoIslandNoMagic
end SaturationMonoid

#print axioms SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Physical.Producer.activeDisturbedImplementation_allTargetsAboveHalf
#print axioms SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Physical.Producer.falseDisturbedImplementation_allTargetsBelowHalf
#print axioms SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Physical.Producer.interventionDisturbedImplementation_sensitiveZeroToOne
