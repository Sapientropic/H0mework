import H0mework.Physics.LCDesign.Sensitivity
import H0mework.Physics.LCDesign.Coupling

/-!
# Source-generated coupling from calibrated LC/transducer parameters

The abstract operator envelope is discharged by quantities available to a
component/run specification: branch admissibility, transfer-gain error and
accumulated phase error `|omega * duration - pi/2|`.

An explicit non-nominal run changes `L`, `C`, gain and scheduled duration.  Its
component certificate generates the operator tolerance and then the existing
coupling crown; no operator-distance or target verdict is supplied by the
caller.
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

/-- A component/run certificate.  The two numerical bounds precede and imply
operator-level acceptance. -/
structure CalibratedLCTransducerRunToleranceAt
    (design : UniformFiniteLCTransducerNetworkDesign)
    (duration : ℝ) : Prop where
  componentAdmissible : LCTransducerComponentAdmissibleAt design
  transferGainError :
    |design.branch.transferGain - (99 : ℝ) / 100| < (1 : ℝ) / 400
  accumulatedPhaseError :
    |normalizedLCAngularFrequency design * duration - Real.pi / 2| <
      (1 : ℝ) / 400

theorem calibratedLCTransducerRun_withinDesignTolerance
    (design : UniformFiniteLCTransducerNetworkDesign) (duration : ℝ)
    (calibrated : CalibratedLCTransducerRunToleranceAt design duration) :
    WithinNinetyNinePercentDesignToleranceAt
      (compiledLCTransducerOperator design duration) := by
  unfold WithinNinetyNinePercentDesignToleranceAt
    compiledLCTransducerQuarterOperator
  have distanceBound := norm_compiledLCTransducerOperator_sub_le
    design ninetyNinePercentUnitLCTransducerDesign duration (Real.pi / 2)
  have referenceGain :
      ninetyNinePercentUnitLCTransducerDesign.branch.transferGain =
        (99 : ℝ) / 100 := rfl
  rw [referenceGain, ninetyNinePercentUnitLC_frequency_eq_one] at distanceBound
  have phaseContribution :
      |(99 : ℝ) / 100| *
          |normalizedLCAngularFrequency design * duration -
            1 * (Real.pi / 2)| <
        |(99 : ℝ) / 100| * ((1 : ℝ) / 400) :=
    mul_lt_mul_of_pos_left (by simpa using calibrated.accumulatedPhaseError)
      (by norm_num)
  calc
    ‖compiledLCTransducerOperator design duration -
        compiledLCTransducerOperator
          ninetyNinePercentUnitLCTransducerDesign (Real.pi / 2)‖ ≤
      |design.branch.transferGain - (99 : ℝ) / 100| +
        |(99 : ℝ) / 100| *
          |normalizedLCAngularFrequency design * duration -
            1 * (Real.pi / 2)| := distanceBound
    _ < (1 : ℝ) / 400 + |(99 : ℝ) / 100| * ((1 : ℝ) / 400) :=
      add_lt_add calibrated.transferGainError phaseContribution
    _ < (1 : ℝ) / 200 := by norm_num

theorem everyCalibratedLCTransducerRun_generatesCouplingCrown
    (design : UniformFiniteLCTransducerNetworkDesign) (duration : ℝ)
    (calibrated : CalibratedLCTransducerRunToleranceAt design duration) :
    ∃ accurate : OperatorToleranceAt
        (compiledLCTransducerOperator design duration),
      SourceGeneratedTruthChildNeuralBodyCouplingLaw.SourceGeneratedTruthChildNeuralBodyCouplingCrownAt
        (toleranceCertifiedTruthChildCouplingLaw
          (compiledLCTransducerOperator design duration) accurate) :=
  everyImplementationWithinNinetyNinePercentLCDesign_generatesCouplingCrown
    (compiledLCTransducerOperator design duration)
    (calibratedLCTransducerRun_withinDesignTolerance
      design duration calibrated)

/-- A non-nominal component design with a separately scheduled run. -/
def calibratedFourUnitLCTransducerDesign :
    UniformFiniteLCTransducerNetworkDesign where
  branch := {
    inductance := 4
    capacitance := 4
    transferGain := (124 : ℝ) / 125
  }

def calibratedFourUnitScheduledDuration : ℝ :=
  2 * Real.pi + (1 : ℝ) / 1000

theorem calibratedFourUnitLCTransducerDesign_admissible :
    LCTransducerComponentAdmissibleAt
      calibratedFourUnitLCTransducerDesign where
  inductancePositive := by norm_num [calibratedFourUnitLCTransducerDesign]
  capacitancePositive := by norm_num [calibratedFourUnitLCTransducerDesign]
  transferGainPositive := by norm_num [calibratedFourUnitLCTransducerDesign]
  transferGainPassive := by norm_num [calibratedFourUnitLCTransducerDesign]

theorem calibratedFourUnitLC_frequency_eq_quarter :
    normalizedLCAngularFrequency calibratedFourUnitLCTransducerDesign =
      (1 : ℝ) / 4 := by
  norm_num [normalizedLCAngularFrequency,
    calibratedFourUnitLCTransducerDesign]

theorem calibratedFourUnitRun_parameterTolerance :
    CalibratedLCTransducerRunToleranceAt
      calibratedFourUnitLCTransducerDesign
      calibratedFourUnitScheduledDuration where
  componentAdmissible := calibratedFourUnitLCTransducerDesign_admissible
  transferGainError := by
    norm_num [calibratedFourUnitLCTransducerDesign]
  accumulatedPhaseError := by
    rw [calibratedFourUnitLC_frequency_eq_quarter]
    have phaseError :
        (1 : ℝ) / 4 * calibratedFourUnitScheduledDuration - Real.pi / 2 =
          (1 : ℝ) / 4000 := by
      unfold calibratedFourUnitScheduledDuration
      ring
    rw [phaseError, abs_of_pos (by norm_num)]
    norm_num

theorem calibratedFourUnitDesign_ne_reference :
    calibratedFourUnitLCTransducerDesign ≠
      ninetyNinePercentUnitLCTransducerDesign := by
  intro same
  have inductanceSame := congrArg
    (fun design : UniformFiniteLCTransducerNetworkDesign =>
      design.branch.inductance) same
  norm_num [calibratedFourUnitLCTransducerDesign,
    ninetyNinePercentUnitLCTransducerDesign] at inductanceSame

theorem calibratedFourUnitRun_generatesCouplingCrown :
    ∃ accurate : OperatorToleranceAt
        (compiledLCTransducerOperator calibratedFourUnitLCTransducerDesign
          calibratedFourUnitScheduledDuration),
      SourceGeneratedTruthChildNeuralBodyCouplingLaw.SourceGeneratedTruthChildNeuralBodyCouplingCrownAt
        (toleranceCertifiedTruthChildCouplingLaw
          (compiledLCTransducerOperator calibratedFourUnitLCTransducerDesign
            calibratedFourUnitScheduledDuration) accurate) :=
  everyCalibratedLCTransducerRun_generatesCouplingCrown
    calibratedFourUnitLCTransducerDesign
    calibratedFourUnitScheduledDuration
    calibratedFourUnitRun_parameterTolerance

structure CalibratedLCTransducerRunSynthesisAt
    (design : UniformFiniteLCTransducerNetworkDesign)
    (duration : ℝ) : Type where
  designNonReference : design ≠ ninetyNinePercentUnitLCTransducerDesign
  componentSlotCount : Fintype.card FiniteLCTransducerComponentSlot = 30
  parameterTolerance : CalibratedLCTransducerRunToleranceAt design duration
  operatorWithinDesignTolerance : WithinNinetyNinePercentDesignToleranceAt
    (compiledLCTransducerOperator design duration)
  generatedCouplingCrown :
    ∃ accurate : OperatorToleranceAt
        (compiledLCTransducerOperator design duration),
      SourceGeneratedTruthChildNeuralBodyCouplingLaw.SourceGeneratedTruthChildNeuralBodyCouplingCrownAt
        (toleranceCertifiedTruthChildCouplingLaw
          (compiledLCTransducerOperator design duration) accurate)

def calibratedFourUnitLCTransducerRunSynthesis :
    CalibratedLCTransducerRunSynthesisAt
      calibratedFourUnitLCTransducerDesign
      calibratedFourUnitScheduledDuration where
  designNonReference := calibratedFourUnitDesign_ne_reference
  componentSlotCount := finiteLCTransducerComponentSlot_cardinality
  parameterTolerance := calibratedFourUnitRun_parameterTolerance
  operatorWithinDesignTolerance :=
    calibratedLCTransducerRun_withinDesignTolerance
      calibratedFourUnitLCTransducerDesign
      calibratedFourUnitScheduledDuration
      calibratedFourUnitRun_parameterTolerance
  generatedCouplingCrown := calibratedFourUnitRun_generatesCouplingCrown

/-- Premise-free parameter-level synthesis for a non-reference component
design and a non-reference scheduled duration. -/
theorem calibratedNonNominalLCTransducerRun_constructible :
    Nonempty
      (CalibratedLCTransducerRunSynthesisAt
        calibratedFourUnitLCTransducerDesign
        calibratedFourUnitScheduledDuration) :=
  ⟨calibratedFourUnitLCTransducerRunSynthesis⟩

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

#print axioms SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Physical.Producer.calibratedLCTransducerRun_withinDesignTolerance
#print axioms SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Physical.Producer.everyCalibratedLCTransducerRun_generatesCouplingCrown
#print axioms SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Physical.Producer.calibratedNonNominalLCTransducerRun_constructible
