import H0mework.Physics.PortCoupling.Additive
import H0mework.Physics.LCDesign.FrequencyFamily

/-!
# Frequency-matched LC coupling with bounded additive disturbance

The two robustness chains are joined at their actual compiled operator.  Any
positive normalized `L,C` pair at reference gain generates a named positive
quarter-period schedule.  At that schedule its linear operator is exactly the
accepted `99%` design centre, so any uniformly `1/8`-bounded, input-dependent
additive residual still generates the existing coupling crown.
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

open _root_.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Interface
open Physical.Interface

noncomputable section

theorem frequencyMatchedReferenceGain_operator_eq_designCentre
    (design : UniformFiniteLCTransducerNetworkDesign)
    (admissible : LCTransducerComponentAdmissibleAt design)
    (referenceGain : design.branch.transferGain = (99 : ℝ) / 100) :
    compiledLCTransducerOperator design
        (phaseMatchedQuarterDuration design) =
      compiledLCTransducerQuarterOperator
        ninetyNinePercentUnitLCTransducerDesign := by
  have distanceBound := norm_compiledLCTransducerOperator_sub_le
    design ninetyNinePercentUnitLCTransducerDesign
    (phaseMatchedQuarterDuration design) (Real.pi / 2)
  have referenceDesignGain :
      ninetyNinePercentUnitLCTransducerDesign.branch.transferGain =
        (99 : ℝ) / 100 := rfl
  rw [referenceGain, referenceDesignGain,
    phaseMatchedQuarterDuration_accumulatedPhase design admissible,
    ninetyNinePercentUnitLC_frequency_eq_one] at distanceBound
  norm_num at distanceBound
  unfold compiledLCTransducerQuarterOperator
  exact sub_eq_zero.mp distanceBound

theorem frequencyMatchedReferenceGain_linearTolerance
    (design : UniformFiniteLCTransducerNetworkDesign)
    (admissible : LCTransducerComponentAdmissibleAt design)
    (referenceGain : design.branch.transferGain = (99 : ℝ) / 100) :
    ‖compiledLCTransducerOperator design
          (phaseMatchedQuarterDuration design) - idealQuarterOperator‖ <
      (1 : ℝ) / 80 := by
  rw [frequencyMatchedReferenceGain_operator_eq_designCentre
    design admissible referenceGain]
  exact lt_of_le_of_lt ninetyNinePercentCenter_error_le_oneHundredth
    (by norm_num)

/-- The literal generated duration, exact accumulated phase and disturbed
coupling crown remain indexed by the same component design. -/
structure FrequencyMatchedAdditiveDisturbanceCrownAt
    (design : UniformFiniteLCTransducerNetworkDesign)
    (disturbance : EndpointDisturbance) : Prop where
  componentAdmissible : LCTransducerComponentAdmissibleAt design
  referenceGain : design.branch.transferGain = (99 : ℝ) / 100
  disturbanceBound : ∀ state, ‖disturbance state‖ < (1 : ℝ) / 8
  durationPositive : 0 < phaseMatchedQuarterDuration design
  accumulatedPhaseExact :
    normalizedLCAngularFrequency design *
      phaseMatchedQuarterDuration design = Real.pi / 2
  generatedCouplingCrown :
    let tolerant : AdditiveDisturbanceToleranceAt
        (compiledLCTransducerOperator design
          (phaseMatchedQuarterDuration design)) disturbance := {
      linearPartTolerance := frequencyMatchedReferenceGain_linearTolerance
        design componentAdmissible referenceGain
      disturbanceBound := disturbanceBound
    }
    SourceGeneratedTruthChildNeuralBodyCouplingLaw.SourceGeneratedTruthChildNeuralBodyCouplingCrownAt
      (additiveDisturbanceCertifiedTruthChildCouplingLaw
        (compiledLCTransducerOperator design
          (phaseMatchedQuarterDuration design)) disturbance tolerant)

theorem everyPositiveLCWithBoundedDisturbance_generatesCouplingCrown
    (inductance capacitance : ℝ)
    (inductancePositive : 0 < inductance)
    (capacitancePositive : 0 < capacitance)
    (disturbance : EndpointDisturbance)
    (disturbanceBound : ∀ state, ‖disturbance state‖ < (1 : ℝ) / 8) :
    FrequencyMatchedAdditiveDisturbanceCrownAt
      (lcDesignOfParameters inductance capacitance ((99 : ℝ) / 100))
      disturbance := by
  let design := lcDesignOfParameters inductance capacitance ((99 : ℝ) / 100)
  have admissible : LCTransducerComponentAdmissibleAt design := {
    inductancePositive := inductancePositive
    capacitancePositive := capacitancePositive
    transferGainPositive := by norm_num [design, lcDesignOfParameters]
    transferGainPassive := by norm_num [design, lcDesignOfParameters]
  }
  have gain : design.branch.transferGain = (99 : ℝ) / 100 := rfl
  let tolerant : AdditiveDisturbanceToleranceAt
      (compiledLCTransducerOperator design
        (phaseMatchedQuarterDuration design)) disturbance := {
    linearPartTolerance := frequencyMatchedReferenceGain_linearTolerance
      design admissible gain
    disturbanceBound := disturbanceBound
  }
  exact {
    componentAdmissible := admissible
    referenceGain := gain
    disturbanceBound := disturbanceBound
    durationPositive := phaseMatchedQuarterDuration_pos design admissible
    accumulatedPhaseExact :=
      phaseMatchedQuarterDuration_accumulatedPhase design admissible
    generatedCouplingCrown :=
      everyAdditiveDisturbanceWithinTolerance_generatesCouplingCrown
        (compiledLCTransducerOperator design
          (phaseMatchedQuarterDuration design)) disturbance tolerant
  }

theorem smallBias_falseSourceTarget_eq_oneThousandth_for
    (linearPart : HilbertEmbodimentState →L[ℂ] HilbertEmbodimentState) :
    targetPort
        (disturbedImplementedState linearPart smallNonzeroConstantBias
          (preparedState false)) .sourceBound = (1 : ℝ) / 1000 := by
  have inputZero : encodeHilbert (preparedState false) = 0 := by
    ext channel
    simp [encodeHilbert, encodeComplex, encodePort, preparedState]
  unfold disturbedImplementedState targetPort decodeHilbert decodeComplex
  rw [inputZero, map_zero, zero_add]
  simp [smallNonzeroConstantBias, encodeHilbert, encodeComplex, encodePort,
    evolve, intervention]

structure FrequencyMatchedVisibleBiasCrownAt
    (design : UniformFiniteLCTransducerNetworkDesign) : Prop where
  disturbanceNonzero : smallNonzeroConstantBias ≠ 0
  visibleFalseSourceTarget :
    targetPort
        (disturbedImplementedState
          (compiledLCTransducerOperator design
            (phaseMatchedQuarterDuration design))
          smallNonzeroConstantBias (preparedState false)) .sourceBound =
      (1 : ℝ) / 1000
  coupling : FrequencyMatchedAdditiveDisturbanceCrownAt
    design smallNonzeroConstantBias

/-- Premise-free in the disturbance coordinate and uniform over every
positive `L,C`: the named matched run carries a visible nonzero bias and still
generates the coupling crown. -/
theorem frequencyMatchedPositiveLCWithVisibleBias_constructible :
    ∀ inductance capacitance : ℝ,
      0 < inductance → 0 < capacitance →
        FrequencyMatchedVisibleBiasCrownAt
          (lcDesignOfParameters inductance capacitance
            ((99 : ℝ) / 100)) := by
  intro inductance capacitance inductancePositive capacitancePositive
  let design := lcDesignOfParameters inductance capacitance ((99 : ℝ) / 100)
  exact {
    disturbanceNonzero := smallNonzeroConstantBias_ne_zero
    visibleFalseSourceTarget :=
      smallBias_falseSourceTarget_eq_oneThousandth_for _
    coupling := everyPositiveLCWithBoundedDisturbance_generatesCouplingCrown
      inductance capacitance inductancePositive capacitancePositive
      smallNonzeroConstantBias smallNonzeroConstantBias_bound
  }

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

#print axioms SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Physical.Producer.frequencyMatchedReferenceGain_operator_eq_designCentre
#print axioms SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Physical.Producer.everyPositiveLCWithBoundedDisturbance_generatesCouplingCrown
#print axioms SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Physical.Producer.frequencyMatchedPositiveLCWithVisibleBias_constructible
