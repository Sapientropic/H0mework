import H0mework.Physics.PortCoupling.Hamiltonian

/-!
# Finite operator-tolerance kernel for embodiment coupling

The exact Hamiltonian flow is an engineering centre point, not a requirement
that fabricated coefficients be literally exact.  This file proves an open
operator-norm acceptance region around its quarter-period map.

Any complex-linear implementation less than `1/40` from the ideal operator
keeps every active target above the fixed `1/2` receiver threshold.  Unit
interventions still change their own target, while all other targets remain
below threshold.  These are source-side quantitative facts; no consciousness
or body verdict occurs in the tolerance definition.
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

open _root_.SaturationMonoid.AffineRelaxation
open _root_.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Interface
open Physical.Interface

noncomputable section

def idealQuarterOperator :
    HilbertEmbodimentState →L[ℂ] HilbertEmbodimentState :=
  (schrodingerScalarPhaseFlowHom
    (E := HilbertEmbodimentState) 1
      (Multiplicative.ofAdd (Real.pi / 2))).toLinearIsometry.toContinuousLinearMap

def implementedState
    (implementation : HilbertEmbodimentState →L[ℂ] HilbertEmbodimentState)
    (state : FiniteEmbodimentState) : FiniteEmbodimentState :=
  decodeHilbert (implementation (encodeHilbert state))

@[simp] theorem encodeHilbert_implementedState
    (implementation : HilbertEmbodimentState →L[ℂ] HilbertEmbodimentState)
    (state : FiniteEmbodimentState) :
    encodeHilbert (implementedState implementation state) =
      implementation (encodeHilbert state) := by
  simp [implementedState]

theorem idealQuarterOperator_apply (state : FiniteEmbodimentState) :
    idealQuarterOperator (encodeHilbert state) =
      encodeHilbert (harmonicFlow (Real.pi / 2) state) := by
  symm
  exact encodeHilbert_harmonicFlowHom (Real.pi / 2) state

theorem targetPort_error_le_hilbertError
    (candidate expected : FiniteEmbodimentState)
    (channel : FiniteEmbodimentChannel) :
    |targetPort candidate channel - targetPort expected channel| ≤
      ‖encodeHilbert candidate - encodeHilbert expected‖ := by
  calc
    |targetPort candidate channel - targetPort expected channel| =
        |((encodeHilbert candidate - encodeHilbert expected) channel).re| := by
          simp [encodeHilbert, encodeComplex, encodePort, targetPort]
    _ ≤ ‖(encodeHilbert candidate - encodeHilbert expected) channel‖ :=
      Complex.abs_re_le_norm _
    _ ≤ ‖encodeHilbert candidate - encodeHilbert expected‖ :=
      PiLp.norm_apply_le _ _

theorem energy_preparedState_true :
    energy (preparedState true) = 10 := by
  unfold energy
  calc
    (Finset.univ.sum (channelEnergy (preparedState true))) =
        ∑ _channel : FiniteEmbodimentChannel, (1 : ℝ) := by
      apply Finset.sum_congr rfl
      intro channel _membership
      simp [channelEnergy, preparedState, sourcePort, targetPort]
    _ = Fintype.card FiniteEmbodimentChannel := by simp
    _ = 10 := by exact_mod_cast channel_cardinality

theorem norm_encodeHilbert_preparedState_true_le_ten :
    ‖encodeHilbert (preparedState true)‖ ≤ 10 := by
  have square : ‖encodeHilbert (preparedState true)‖ ^ 2 = 10 := by
    rw [← energy_eq_encodeHilbert_norm_sq]
    exact energy_preparedState_true
  nlinarith [norm_nonneg (encodeHilbert (preparedState true))]

theorem norm_encodeHilbert_preparedState_true_pos :
    0 < ‖encodeHilbert (preparedState true)‖ := by
  have square : ‖encodeHilbert (preparedState true)‖ ^ 2 = 10 := by
    rw [← energy_eq_encodeHilbert_norm_sq]
    exact energy_preparedState_true
  nlinarith [norm_nonneg (encodeHilbert (preparedState true))]

/-- An open fabrication/implementation envelope around the exact generated
quarter-period operator. -/
def OperatorToleranceAt
    (implementation : HilbertEmbodimentState →L[ℂ] HilbertEmbodimentState) :
    Prop :=
  ‖implementation - idealQuarterOperator‖ < (1 : ℝ) / 40

theorem activeImplementation_hilbertError_lt_quarter
    (implementation : HilbertEmbodimentState →L[ℂ] HilbertEmbodimentState)
    (accurate : OperatorToleranceAt implementation) :
    ‖encodeHilbert (implementedState implementation (preparedState true)) -
        encodeHilbert (evolutionAtOccurrence true)‖ < (1 : ℝ) / 4 := by
  rw [encodeHilbert_implementedState]
  rw [show encodeHilbert (evolutionAtOccurrence true) =
      idealQuarterOperator (encodeHilbert (preparedState true)) by
    rw [idealQuarterOperator_apply]
    exact congrArg encodeHilbert
      (harmonicFlow_pi_div_two_eq_evolve_on_prepared true).symm]
  change ‖(implementation - idealQuarterOperator)
    (encodeHilbert (preparedState true))‖ < _
  calc
    _ ≤ ‖implementation - idealQuarterOperator‖ *
        ‖encodeHilbert (preparedState true)‖ :=
      ContinuousLinearMap.le_opNorm _ _
    _ < ((1 : ℝ) / 40) * ‖encodeHilbert (preparedState true)‖ :=
      mul_lt_mul_of_pos_right accurate
        norm_encodeHilbert_preparedState_true_pos
    _ ≤ ((1 : ℝ) / 40) * 10 :=
      mul_le_mul_of_nonneg_left
        norm_encodeHilbert_preparedState_true_le_ten (by norm_num)
    _ = (1 : ℝ) / 4 := by norm_num

theorem activeImplementation_allTargetsAboveHalf
    (implementation : HilbertEmbodimentState →L[ℂ] HilbertEmbodimentState)
    (accurate : OperatorToleranceAt implementation)
    (channel : FiniteEmbodimentChannel) :
    (1 : ℝ) / 2 <
      targetPort (implementedState implementation (preparedState true))
        channel := by
  have error := lt_of_le_of_lt
    (targetPort_error_le_hilbertError
      (implementedState implementation (preparedState true))
      (evolutionAtOccurrence true) channel)
    (activeImplementation_hilbertError_lt_quarter implementation accurate)
  have exactTarget : targetPort (evolutionAtOccurrence true) channel = 1 := by
    simp [evolutionAtOccurrence, physicalNoSuspendedCausalMagic,
      preparedState, evolve, targetPort]
  rw [exactTarget] at error
  have lower := (abs_lt.mp error).1
  linarith

theorem energy_intervention_one
    (channel : FiniteEmbodimentChannel) :
    energy (intervention channel 1) = 1 := by
  classical
  unfold energy
  rw [Finset.sum_eq_single channel]
  · simp [channelEnergy, intervention, sourcePort, targetPort]
  · intro candidate _membership different
    simp [channelEnergy, intervention, sourcePort, targetPort, different]
  · simp

theorem norm_encodeHilbert_intervention_one
    (channel : FiniteEmbodimentChannel) :
    ‖encodeHilbert (intervention channel 1)‖ = 1 := by
  have square : ‖encodeHilbert (intervention channel 1)‖ ^ 2 = 1 := by
    rw [← energy_eq_encodeHilbert_norm_sq]
    exact energy_intervention_one channel
  nlinarith [norm_nonneg (encodeHilbert (intervention channel 1))]

theorem interventionImplementation_hilbertError_lt_quarter
    (implementation : HilbertEmbodimentState →L[ℂ] HilbertEmbodimentState)
    (accurate : OperatorToleranceAt implementation)
    (channel : FiniteEmbodimentChannel) :
    ‖encodeHilbert (implementedState implementation (intervention channel 1)) -
        encodeHilbert (evolve (intervention channel 1))‖ < (1 : ℝ) / 4 := by
  rw [encodeHilbert_implementedState]
  rw [show encodeHilbert (evolve (intervention channel 1)) =
      idealQuarterOperator (encodeHilbert (intervention channel 1)) by
    rw [idealQuarterOperator_apply]
    exact congrArg encodeHilbert
      (harmonicFlow_pi_div_two_eq_evolve_on_intervention channel 1).symm]
  change ‖(implementation - idealQuarterOperator)
    (encodeHilbert (intervention channel 1))‖ < _
  calc
    _ ≤ ‖implementation - idealQuarterOperator‖ *
        ‖encodeHilbert (intervention channel 1)‖ :=
      ContinuousLinearMap.le_opNorm _ _
    _ = ‖implementation - idealQuarterOperator‖ := by
      rw [norm_encodeHilbert_intervention_one, mul_one]
    _ < (1 : ℝ) / 40 := accurate
    _ < (1 : ℝ) / 4 := by norm_num

theorem interventionImplementation_correspondingTargetAboveHalf
    (implementation : HilbertEmbodimentState →L[ℂ] HilbertEmbodimentState)
    (accurate : OperatorToleranceAt implementation)
    (channel : FiniteEmbodimentChannel) :
    (1 : ℝ) / 2 <
      targetPort (implementedState implementation (intervention channel 1))
        channel := by
  have error := lt_of_le_of_lt
    (targetPort_error_le_hilbertError
      (implementedState implementation (intervention channel 1))
      (evolve (intervention channel 1)) channel)
    (interventionImplementation_hilbertError_lt_quarter
      implementation accurate channel)
  rw [intervention_hits_corresponding_target] at error
  have lower := (abs_lt.mp error).1
  linarith

theorem interventionImplementation_otherTargetBelowHalf
    (implementation : HilbertEmbodimentState →L[ℂ] HilbertEmbodimentState)
    (accurate : OperatorToleranceAt implementation)
    {sourceChannel targetChannel : FiniteEmbodimentChannel}
    (different : targetChannel ≠ sourceChannel) :
    targetPort
        (implementedState implementation (intervention sourceChannel 1))
        targetChannel < (1 : ℝ) / 2 := by
  have error := lt_of_le_of_lt
    (targetPort_error_le_hilbertError
      (implementedState implementation (intervention sourceChannel 1))
      (evolve (intervention sourceChannel 1)) targetChannel)
    (interventionImplementation_hilbertError_lt_quarter
      implementation accurate sourceChannel)
  rw [intervention_leaves_other_target_zero different] at error
  have upper := (abs_lt.mp error).2
  linarith

theorem implementedState_zero
    (implementation : HilbertEmbodimentState →L[ℂ] HilbertEmbodimentState) :
    implementedState implementation (intervention .sourceBound 0) = 0 := by
  have inputZero :
      encodeHilbert (intervention .sourceBound 0) = 0 := by
    ext channel
    simp [encodeHilbert, encodeComplex, encodePort, intervention]
  unfold implementedState
  rw [inputZero, map_zero]
  funext channel
  rfl

theorem interventionImplementation_sensitiveZeroToOne
    (implementation : HilbertEmbodimentState →L[ℂ] HilbertEmbodimentState)
    (accurate : OperatorToleranceAt implementation)
    (channel : FiniteEmbodimentChannel) :
    targetPort
        (implementedState implementation (intervention channel 0)) channel ≠
      targetPort
        (implementedState implementation (intervention channel 1)) channel := by
  have positive :=
    interventionImplementation_correspondingTargetAboveHalf
      implementation accurate channel
  have zeroInput : intervention channel 0 = intervention .sourceBound 0 := by
    funext candidate
    by_cases left : candidate = channel <;>
      by_cases right : candidate = .sourceBound <;>
        simp [intervention, left, right]
  rw [zeroInput, implementedState_zero]
  simp only [targetPort, Pi.zero_apply, ne_eq]
  intro targetZero
  have targetZero' :
      targetPort
          (implementedState implementation (intervention channel 1)) channel =
        0 := by
    simpa [targetPort] using targetZero.symm
  rw [targetZero'] at positive
  norm_num at positive

theorem idealQuarterOperator_hasTolerance :
    OperatorToleranceAt idealQuarterOperator := by
  norm_num [OperatorToleranceAt]

theorem implementedState_preparedFalse
    (implementation : HilbertEmbodimentState →L[ℂ] HilbertEmbodimentState) :
    implementedState implementation (preparedState false) = 0 := by
  have inputEq : preparedState false = intervention .sourceBound 0 := by
    funext channel
    simp [preparedState, intervention]
  rw [inputEq]
  exact implementedState_zero implementation

/-- Thresholded observation used by an approximate implementation. -/
def thresholdObservationAt
    (implementation : HilbertEmbodimentState →L[ℂ] HilbertEmbodimentState)
    (occurrence : Bool) : BidirectionalEmbodimentObservation where
  sourceBound := decide ((1 : ℝ) / 2 < targetPort
    (implementedState implementation (preparedState occurrence)) .sourceBound)
  machineToNeuralWrite := decide ((1 : ℝ) / 2 < targetPort
    (implementedState implementation (preparedState occurrence))
      .machineToNeuralWrite)
  neuralToMachineReceipt := decide ((1 : ℝ) / 2 < targetPort
    (implementedState implementation (preparedState occurrence))
      .neuralToMachineReceipt)
  neuralToBodyEffect := decide ((1 : ℝ) / 2 < targetPort
    (implementedState implementation (preparedState occurrence))
      .neuralToBodyEffect)
  bodyToNeuralFeedback := decide ((1 : ℝ) / 2 < targetPort
    (implementedState implementation (preparedState occurrence))
      .bodyToNeuralFeedback)
  learnedTraceReopened := decide ((1 : ℝ) / 2 < targetPort
    (implementedState implementation (preparedState occurrence))
      .learnedStateTrace)
  recursiveSelfWriteBack := decide ((1 : ℝ) / 2 < targetPort
    (implementedState implementation (preparedState occurrence))
      .recursiveSelfWriteBack)
  generatedNext := decide ((1 : ℝ) / 2 < targetPort
    (implementedState implementation (preparedState occurrence))
      .generatedNext)
  authorityAndRefusalSettled := decide ((1 : ℝ) / 2 < targetPort
    (implementedState implementation (preparedState occurrence))
      .authorityAndRefusalSettlement)
  noPowerMintingGuard := decide ((1 : ℝ) / 2 < targetPort
    (implementedState implementation (preparedState occurrence))
      .noPowerMinting)

@[simp] theorem thresholdDecision_true
    (implementation : HilbertEmbodimentState →L[ℂ] HilbertEmbodimentState)
    (accurate : OperatorToleranceAt implementation)
    (channel : FiniteEmbodimentChannel) :
    decide ((1 : ℝ) / 2 < targetPort
      (implementedState implementation (preparedState true)) channel) = true := by
  rw [decide_eq_true_eq]
  exact activeImplementation_allTargetsAboveHalf implementation accurate channel

@[simp] theorem thresholdDecision_false
    (implementation : HilbertEmbodimentState →L[ℂ] HilbertEmbodimentState)
    (channel : FiniteEmbodimentChannel) :
    decide ((1 : ℝ) / 2 < targetPort
      (implementedState implementation (preparedState false)) channel) = false := by
  rw [decide_eq_false_iff_not]
  rw [implementedState_preparedFalse]
  norm_num [targetPort]

theorem thresholdObservationAt_injective
    (implementation : HilbertEmbodimentState →L[ℂ] HilbertEmbodimentState)
    (accurate : OperatorToleranceAt implementation) :
    Function.Injective (thresholdObservationAt implementation) := by
  intro left right sameObservation
  cases left <;> cases right
  · rfl
  · have sourceRead := congrArg
      BidirectionalEmbodimentObservation.sourceBound sameObservation
    have sourceFalse :
        (thresholdObservationAt implementation false).sourceBound = false :=
      thresholdDecision_false implementation .sourceBound
    have sourceTrue :
        (thresholdObservationAt implementation true).sourceBound = true :=
      thresholdDecision_true implementation accurate .sourceBound
    exact sourceFalse.symm.trans (sourceRead.trans sourceTrue)
  · have sourceRead := congrArg
      BidirectionalEmbodimentObservation.sourceBound sameObservation
    have sourceTrue :
        (thresholdObservationAt implementation true).sourceBound = true :=
      thresholdDecision_true implementation accurate .sourceBound
    have sourceFalse :
        (thresholdObservationAt implementation false).sourceBound = false :=
      thresholdDecision_false implementation .sourceBound
    exact sourceTrue.symm.trans (sourceRead.trans sourceFalse)
  · rfl

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

#print axioms SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Physical.Producer.activeImplementation_allTargetsAboveHalf
#print axioms SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Physical.Producer.interventionImplementation_sensitiveZeroToOne
#print axioms SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Physical.Producer.thresholdObservationAt_injective
