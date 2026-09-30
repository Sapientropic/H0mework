import H0mework.Physics.LCDesign.CalibratedRun

/-!
# Source-generated frequency-matched LC/transducer family

Positive `L` and `C` need not be close to the reference values.  They generate
their own positive angular frequency, and the controller schedules the exact
quarter-period for that frequency.  This closes accumulated phase by
construction and leaves only the already explicit transducer-gain window.
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

noncomputable section

theorem normalizedLCAngularFrequency_pos
    (design : UniformFiniteLCTransducerNetworkDesign)
    (admissible : LCTransducerComponentAdmissibleAt design) :
    0 < normalizedLCAngularFrequency design := by
  unfold normalizedLCAngularFrequency
  have productPositive :
      0 < design.branch.inductance * design.branch.capacitance :=
    mul_pos admissible.inductancePositive admissible.capacitancePositive
  exact inv_pos.mpr (Real.sqrt_pos.2 productPositive)

/-- Controller schedule generated from the installed component frequency. -/
def phaseMatchedQuarterDuration
    (design : UniformFiniteLCTransducerNetworkDesign) : ℝ :=
  (Real.pi / 2) / normalizedLCAngularFrequency design

theorem phaseMatchedQuarterDuration_pos
    (design : UniformFiniteLCTransducerNetworkDesign)
    (admissible : LCTransducerComponentAdmissibleAt design) :
    0 < phaseMatchedQuarterDuration design := by
  exact div_pos (half_pos Real.pi_pos)
    (normalizedLCAngularFrequency_pos design admissible)

theorem phaseMatchedQuarterDuration_accumulatedPhase
    (design : UniformFiniteLCTransducerNetworkDesign)
    (admissible : LCTransducerComponentAdmissibleAt design) :
    normalizedLCAngularFrequency design *
        phaseMatchedQuarterDuration design = Real.pi / 2 := by
  unfold phaseMatchedQuarterDuration
  field_simp [ne_of_gt (normalizedLCAngularFrequency_pos design admissible)]

/-- Gain-only certificate after the component-generated frequency has been
fed back into the schedule. -/
structure GainCalibratedLCTransducerDesignAt
    (design : UniformFiniteLCTransducerNetworkDesign) : Prop where
  componentAdmissible : LCTransducerComponentAdmissibleAt design
  transferGainError :
    |design.branch.transferGain - (99 : ℝ) / 100| < (1 : ℝ) / 400

theorem gainCalibratedDesign_generatesRunTolerance
    (design : UniformFiniteLCTransducerNetworkDesign)
    (calibrated : GainCalibratedLCTransducerDesignAt design) :
    CalibratedLCTransducerRunToleranceAt design
      (phaseMatchedQuarterDuration design) where
  componentAdmissible := calibrated.componentAdmissible
  transferGainError := calibrated.transferGainError
  accumulatedPhaseError := by
    rw [phaseMatchedQuarterDuration_accumulatedPhase
      design calibrated.componentAdmissible]
    norm_num

/-- The public result retains the literal scheduled duration and its exact
accumulated phase, not merely an existentially hidden successful run. -/
structure FrequencyMatchedLCTransducerCrownAt
    (design : UniformFiniteLCTransducerNetworkDesign) : Prop where
  durationPositive : 0 < phaseMatchedQuarterDuration design
  accumulatedPhaseExact :
    normalizedLCAngularFrequency design *
      phaseMatchedQuarterDuration design = Real.pi / 2
  generatedCouplingCrown :
    ∃ accurate : OperatorToleranceAt
        (compiledLCTransducerOperator design
          (phaseMatchedQuarterDuration design)),
      SourceGeneratedTruthChildNeuralBodyCouplingLaw.SourceGeneratedTruthChildNeuralBodyCouplingCrownAt
        (toleranceCertifiedTruthChildCouplingLaw
          (compiledLCTransducerOperator design
            (phaseMatchedQuarterDuration design)) accurate)

theorem everyGainCalibratedLCDesign_generatesCouplingCrown
    (design : UniformFiniteLCTransducerNetworkDesign)
    (calibrated : GainCalibratedLCTransducerDesignAt design) :
    FrequencyMatchedLCTransducerCrownAt design where
  durationPositive :=
    phaseMatchedQuarterDuration_pos design calibrated.componentAdmissible
  accumulatedPhaseExact :=
    phaseMatchedQuarterDuration_accumulatedPhase
      design calibrated.componentAdmissible
  generatedCouplingCrown :=
    everyCalibratedLCTransducerRun_generatesCouplingCrown
      design (phaseMatchedQuarterDuration design)
      (gainCalibratedDesign_generatesRunTolerance design calibrated)

def lcDesignOfParameters (inductance capacitance transferGain : ℝ) :
    UniformFiniteLCTransducerNetworkDesign where
  branch := { inductance, capacitance, transferGain }

theorem arbitraryPositiveLC_atReferenceGain_generatesCouplingCrown
    (inductance capacitance : ℝ)
    (inductancePositive : 0 < inductance)
    (capacitancePositive : 0 < capacitance) :
    FrequencyMatchedLCTransducerCrownAt
      (lcDesignOfParameters inductance capacitance ((99 : ℝ) / 100)) := by
  apply everyGainCalibratedLCDesign_generatesCouplingCrown
  exact {
    componentAdmissible := {
      inductancePositive := inductancePositive
      capacitancePositive := capacitancePositive
      transferGainPositive := by norm_num [lcDesignOfParameters]
      transferGainPassive := by norm_num [lcDesignOfParameters]
    }
    transferGainError := by norm_num [lcDesignOfParameters]
  }

/-- Uniform constructive family: every positive normalized LC pair has a
source-generated positive schedule whose compiled operator produces the
coupling crown at the reference passive gain. -/
theorem frequencyMatchedPositiveLCFamily_constructible :
    ∀ inductance capacitance : ℝ,
      0 < inductance → 0 < capacitance →
        FrequencyMatchedLCTransducerCrownAt
          (lcDesignOfParameters inductance capacitance
            ((99 : ℝ) / 100)) := by
  intro inductance capacitance inductancePositive capacitancePositive
  exact arbitraryPositiveLC_atReferenceGain_generatesCouplingCrown
    inductance capacitance inductancePositive capacitancePositive

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

#print axioms SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Physical.Producer.phaseMatchedQuarterDuration_accumulatedPhase
#print axioms SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Physical.Producer.everyGainCalibratedLCDesign_generatesCouplingCrown
#print axioms SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Physical.Producer.frequencyMatchedPositiveLCFamily_constructible
