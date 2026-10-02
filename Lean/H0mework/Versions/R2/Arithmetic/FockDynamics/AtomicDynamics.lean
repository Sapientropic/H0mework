import H0mework.Versions.R2.Arithmetic.FockState.SpeciesMeasurement
import H0mework.Versions.R2.Arithmetic.FockDynamics.AtomicState
import H0mework.Versions.R2.Arithmetic.FockDynamics.SpeciesFlux

/-!
# Atomic particle dynamics generated from one physical current

The source classifier's terminal/step output is consumed immediately.  A
terminal receives its forced `two×two | odd×odd` species pattern.  A step
receives the existing operational receipt, Fock trace, coarse conservation,
and its ordered Z/2 current.  No caller submits a terminal, channel, receipt,
or species label.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ResponsibilityLifecycle
namespace LivingLawEvolution
namespace ConstructiveRoot
namespace NoIslandNoMagic
namespace CanonicalArithmeticState
namespace ParticleWaveFockAtomicProcess

open CanonicalUnitArithmeticEffectiveFactorRepairOrbitProducer
open CanonicalUnitArithmeticFullFactorEmissionProducer
open CanonicalUnitArithmeticOperationalFactorDecayProducer
open ParticleWaveFock
open ParticleWaveFockAtomicSpecies

noncomputable section

/-- The only terminal species sectors compatible with one generated even
particle current. -/
inductive GeneratedTerminalSpeciesAt
    {index : Nat} (current : PhysicalCurrentAt index)
    (terminal : PrimePairTerminalAt current.current) : Type
  | twoTwo
      (target_eq : repairTargetValue index = 4)
      (species :
        (generatedOrderedClassification current.current).leftSpecies? =
            some .two ∧
          (generatedOrderedClassification current.current).rightSpecies? =
            some .two) :
      GeneratedTerminalSpeciesAt current terminal
  | oddOdd
      (target_gt : 4 < repairTargetValue index)
      (species :
        (generatedOrderedClassification current.current).leftSpecies? =
            some .odd ∧
          (generatedOrderedClassification current.current).rightSpecies? =
            some .odd) :
      GeneratedTerminalSpeciesAt current terminal

def generateTerminalSpecies
    {index : Nat} (current : PhysicalCurrentAt index)
    (terminal : PrimePairTerminalAt current.current) :
    GeneratedTerminalSpeciesAt current terminal := by
  by_cases targetEq : repairTargetValue index = 4
  · exact .twoTwo targetEq
      (generatedOrderedClassification_target_four_is_two_two
        current.current targetEq)
  · have landing := split_landing current.current
    have leftFloor := splitLeft_atLeastTwo current.current
    have rightFloor := splitRight_atLeastTwo current.current
    have targetGt : 4 < repairTargetValue index := by omega
    exact .oddOdd targetGt
      (primePairTerminal_target_gt_four_is_odd_odd
        current.current targetGt terminal)

theorem generatedTerminalSpecies_not_mixed
    {index : Nat} (current : PhysicalCurrentAt index)
    (terminal : PrimePairTerminalAt current.current) :
    ¬ (generatedOrderedClassification current.current).IsMixed :=
  primePairTerminal_not_mixed current.current terminal

def channelSpeciesFlux
    {index : Nat} {current : EffectiveSplitAt index}
    (channel : FactorDecayChannelAt current) :
    SpeciesGrade × SpeciesGrade :=
  orderedSpeciesGrade channel.target - orderedSpeciesGrade current

/-- Operational realization of the classifier-selected actual channel. -/
structure GeneratedStepEffectAt
    {index : Nat} (current : PhysicalCurrentAt index)
    (event : SourceEventAt current)
    (step : GeneratedStepAt current event) : Type where
  private mk ::
  receipt : OperationalFactorDecayChannelReceiptAt step.channel
  receipt_eq : receipt = generateChannelReceipt step.channel
  fockTrace : GeneratedFactorDecayFockTraceAt step.channel receipt
  fockTrace_eq : fockTrace =
    generateFactorDecayFockTrace step.channel receipt
  sourceMeasurement : AtomicJointMeasurementTarget
  sourceMeasurement_eq : sourceMeasurement =
    atomicJointMeasurement current.current
  targetMeasurement : AtomicJointMeasurementTarget
  targetMeasurement_eq : targetMeasurement =
    atomicJointMeasurement step.channel.target
  speciesFlux : SpeciesGrade × SpeciesGrade
  speciesFlux_eq : speciesFlux = channelSpeciesFlux step.channel
  coarseMeasurementConserved :
    jointMeasurement (splitParticleState current.current) =
      jointMeasurement (splitParticleState step.channel.target)
  recollects :
    fockTrace.targetState + fockTrace.trace = fockTrace.sourceState
  applicable : step.channel ∈ current.applicableInventory

def generateStepEffect
    {index : Nat} {current : PhysicalCurrentAt index}
    {event : SourceEventAt current}
    (step : GeneratedStepAt current event) :
    GeneratedStepEffectAt current event step :=
  { receipt := generateChannelReceipt step.channel
    receipt_eq := rfl
    fockTrace := generateFactorDecayFockTrace step.channel
      (generateChannelReceipt step.channel)
    fockTrace_eq := rfl
    sourceMeasurement := atomicJointMeasurement current.current
    sourceMeasurement_eq := rfl
    targetMeasurement := atomicJointMeasurement step.channel.target
    targetMeasurement_eq := rfl
    speciesFlux := channelSpeciesFlux step.channel
    speciesFlux_eq := rfl
    coarseMeasurementConserved :=
      factorDecay_split_measurement_eq step.channel
    recollects := (generateFactorDecayFockTrace step.channel
      (generateChannelReceipt step.channel)).recollects
    applicable := step.applicable }

/-- Complete physical disposition emitted from one current. -/
inductive GeneratedDynamicsAt {index : Nat}
    (current : PhysicalCurrentAt index) : Type
  | terminal
      (generated : GeneratedTerminalAt current (generateEvent current))
      (species : GeneratedTerminalSpeciesAt current generated.terminal) :
      GeneratedDynamicsAt current
  | step
      (generated : GeneratedStepAt current (generateEvent current))
      (effect : GeneratedStepEffectAt current (generateEvent current) generated) :
      GeneratedDynamicsAt current

/-- The source event is consumed in the same definition that generates the
terminal species or the actual channel effect. -/
def generateDynamics {index : Nat}
    (current : PhysicalCurrentAt index) : GeneratedDynamicsAt current :=
  match generateDisposition current with
  | .terminal terminal =>
      .terminal terminal
        (generateTerminalSpecies current terminal.terminal)
  | .step step => .step step (generateStepEffect step)

theorem generatedDynamics_is_source_total {index : Nat}
    (current : PhysicalCurrentAt index) :
    Nonempty (GeneratedDynamicsAt current) :=
  ⟨generateDynamics current⟩

end

end ParticleWaveFockAtomicProcess
end CanonicalArithmeticState
end NoIslandNoMagic
end ConstructiveRoot
end LivingLawEvolution
end ResponsibilityLifecycle
end SaturationMonoid
