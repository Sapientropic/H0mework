import H0mework.Physics.RLCNetlist.Run

/-!
# Source-generated finite series-RLC netlist coupling

The finite code first emits a source-only three-node series-RLC run.  Solving
that literal run generates its differential, Kirchhoff, constitutive,
dissipation, and endpoint certificates.  The newly damped implementation then
enters the already proved additive-disturbance coupling theorem directly; no
lossless-netlist crown is transported into this result.
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
namespace Netlist
namespace Dissipative
namespace Producer

open _root_.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Interface
open _root_.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Physical.Interface
open _root_.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Physical.Producer
open _root_.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Physical.Netlist.Interface
open _root_.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Physical.Netlist.Producer
open _root_.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Physical.Netlist.Dissipative.Interface

noncomputable section

/-- The quantitative gate for the newly generated dissipative implementation.
Both bounds are derived upstream; neither is a caller premise. -/
theorem finiteSeriesRLCAdditiveTolerance
    (code : SourceOwnedNetlistCrosstalkCode) :
    AdditiveDisturbanceToleranceAt
      (finiteSeriesRLCImplementation code) smallNonzeroConstantBias where
  linearPartTolerance :=
    everyFiniteSeriesRLCImplementation_linearTolerance code
  disturbanceBound := smallNonzeroConstantBias_bound

/-- Direct consumer of the existing additive-disturbance crown, indexed by
the new series-RLC implementation rather than the former lossless operator. -/
theorem everyFiniteSeriesRLCCodeWithVisibleBias_constructible
    (code : SourceOwnedNetlistCrosstalkCode) :
    SourceGeneratedTruthChildNeuralBodyCouplingLaw.SourceGeneratedTruthChildNeuralBodyCouplingCrownAt
      (additiveDisturbanceCertifiedTruthChildCouplingLaw
        (finiteSeriesRLCImplementation code)
        smallNonzeroConstantBias
        (finiteSeriesRLCAdditiveTolerance code)) :=
  everyAdditiveDisturbanceWithinTolerance_generatesCouplingCrown _ _ _

/-- Complete generated physical receipt.  Its only input is the finite source
code; solved states, circuit laws, acceptance, and endpoint equality are all
outputs.  The coupling crown deliberately remains a downstream consumer and
is not stored in this receipt. -/
structure SourceGeneratedFiniteSeriesRLCNetlistRunAt
    (code : SourceOwnedNetlistCrosstalkCode) : Prop where
  nodeCardinality : Fintype.card FiniteSeriesRLCNode = 30
  coreElementCardinality : Fintype.card FiniteSeriesRLCCoreElement = 30
  elementCardinality : Fintype.card FiniteSeriesRLCNetlistElement = 42
  baseRunExact :
    (compileFiniteSeriesRLCNetlistRun code).baseRun =
      compileFiniteParallelLCNetlistRun code
  executedDurationPositive :
    0 < (compileFiniteSeriesRLCNetlistRun code).baseRun.executedDuration
  executedDurationNotExactQuarterPeriod :
    (compileFiniteSeriesRLCNetlistRun code).baseRun.executedDuration ≠
      Real.pi / 2
  independentBiasSourceNonzero :
    (compileFiniteSeriesRLCNetlistRun code).baseRun.endpointBiasAmplitude ≠ 0
  dampingPositive : ∀ channel,
    0 < (compileFiniteSeriesRLCNetlistRun code).dampingRateAt channel
  capacitancePositive : ∀ channel,
    0 < (compileFiniteSeriesRLCNetlistRun code).capacitanceAt channel
  inductancePositive : ∀ channel,
    0 < (compileFiniteSeriesRLCNetlistRun code).inductanceAt channel
  resistancePositive : ∀ channel,
    0 < (compileFiniteSeriesRLCNetlistRun code).seriesResistanceAt channel
  dampingGeneratedByResistance : ∀ channel,
    (compileFiniteSeriesRLCNetlistRun code).dampingRateAt channel =
      (compileFiniteSeriesRLCNetlistRun code).seriesResistanceAt channel /
        (2 * (compileFiniteSeriesRLCNetlistRun code).inductanceAt channel)
  naturalFrequencyPrecompensated : ∀ channel,
    finiteSeriesRLCNaturalAngularFrequencySqAt
        (compileFiniteSeriesRLCNetlistRun code) channel =
      finiteSeriesRLCDampedAngularFrequencyAt
          (compileFiniteSeriesRLCNetlistRun code) channel ^ 2 +
        (compileFiniteSeriesRLCNetlistRun code).dampingRateAt channel ^ 2
  underdamped : ∀ channel,
    0 < finiteSeriesRLCNaturalAngularFrequencySqAt
          (compileFiniteSeriesRLCNetlistRun code) channel -
        ((compileFiniteSeriesRLCNetlistRun code).seriesResistanceAt channel /
          (2 * (compileFiniteSeriesRLCNetlistRun code).inductanceAt channel)) ^ 2
  initialCondition : ∀ initial,
    finiteSeriesRLCFlowAt (compileFiniteSeriesRLCNetlistRun code) initial 0 =
      initial
  sourceDerivative : ∀ initial channel time,
    HasDerivAt
      (fun t => sourcePort
        (finiteSeriesRLCFlowAt (compileFiniteSeriesRLCNetlistRun code)
          initial t) channel)
      (-(compileFiniteSeriesRLCNetlistRun code).dampingRateAt channel *
          sourcePort (finiteSeriesRLCFlowAt
            (compileFiniteSeriesRLCNetlistRun code) initial time) channel -
        (compileFiniteSeriesRLCNetlistRun code).baseRun.frequencyAt channel *
          targetPort (finiteSeriesRLCFlowAt
            (compileFiniteSeriesRLCNetlistRun code) initial time) channel)
      time
  voltageDerivative : ∀ initial channel time,
    HasDerivAt
      (finiteSeriesRLCVoltageAt (compileFiniteSeriesRLCNetlistRun code)
        initial channel)
      (finiteSeriesRLCCurrentAt (compileFiniteSeriesRLCNetlistRun code)
        initial channel time) time
  currentDerivative : ∀ initial channel time,
    HasDerivAt
      (finiteSeriesRLCCurrentAt (compileFiniteSeriesRLCNetlistRun code)
        initial channel)
      (finiteSeriesRLCCurrentDerivativeAt
        (compileFiniteSeriesRLCNetlistRun code) initial channel time) time
  currentIsGeneratedShear : ∀ initial channel time,
    finiteSeriesRLCCurrentAt (compileFiniteSeriesRLCNetlistRun code)
        initial channel time =
      finiteSeriesRLCPhysicalCurrentShear
        (compileFiniteSeriesRLCNetlistRun code)
        (finiteSeriesRLCFlowAt (compileFiniteSeriesRLCNetlistRun code)
          initial time) channel
  kirchhoffCurrent : ∀ initial channel time node,
    finiteSeriesRLCNodeCurrentAt (compileFiniteSeriesRLCNetlistRun code)
      initial channel time node = 0
  resistorConstitutive : ∀ initial channel time,
    finiteSeriesRLCElementVoltageAt (compileFiniteSeriesRLCNetlistRun code)
        initial channel time .seriesResistor =
      (compileFiniteSeriesRLCNetlistRun code).seriesResistanceAt channel *
        finiteSeriesRLCCurrentAt (compileFiniteSeriesRLCNetlistRun code)
          initial channel time
  capacitorConstitutive : ∀ initial channel time,
    HasDerivAt
      (finiteSeriesRLCVoltageAt (compileFiniteSeriesRLCNetlistRun code)
        initial channel)
      (finiteSeriesRLCCurrentAt (compileFiniteSeriesRLCNetlistRun code)
          initial channel time /
        (compileFiniteSeriesRLCNetlistRun code).capacitanceAt channel)
      time
  inductorConstitutive : ∀ initial channel time,
    finiteSeriesRLCElementVoltageAt (compileFiniteSeriesRLCNetlistRun code)
        initial channel time .inductor =
      (compileFiniteSeriesRLCNetlistRun code).inductanceAt channel *
        finiteSeriesRLCCurrentDerivativeAt
          (compileFiniteSeriesRLCNetlistRun code) initial channel time
  voltageLoop : ∀ initial channel time,
    ∑ element : SeriesRLCCoreElementKind,
      finiteSeriesRLCElementVoltageAt (compileFiniteSeriesRLCNetlistRun code)
        initial channel time element = 0
  kirchhoffVoltage : ∀ initial channel time,
    (compileFiniteSeriesRLCNetlistRun code).inductanceAt channel *
        finiteSeriesRLCCurrentDerivativeAt
          (compileFiniteSeriesRLCNetlistRun code) initial channel time +
      (compileFiniteSeriesRLCNetlistRun code).seriesResistanceAt channel *
        finiteSeriesRLCCurrentAt (compileFiniteSeriesRLCNetlistRun code)
          initial channel time +
      finiteSeriesRLCVoltageAt (compileFiniteSeriesRLCNetlistRun code)
        initial channel time = 0
  energyDissipation : ∀ initial channel time,
    HasDerivAt
      (finiteSeriesRLCEnergyAt (compileFiniteSeriesRLCNetlistRun code)
        initial channel)
      (-2 * (compileFiniteSeriesRLCNetlistRun code).seriesResistanceAt channel *
        finiteSeriesRLCCurrentAt (compileFiniteSeriesRLCNetlistRun code)
          initial channel time ^ 2) time
  energyAntitone : ∀ initial channel,
    Antitone (finiteSeriesRLCEnergyAt
      (compileFiniteSeriesRLCNetlistRun code) initial channel)
  sourceImpulseStrictlyDissipates : ∀ channel,
    let run := compileFiniteSeriesRLCNetlistRun code
    let derivative := -2 * run.seriesResistanceAt channel *
      finiteSeriesRLCCurrentAt run (intervention channel 1) channel 0 ^ 2
    HasDerivAt
        (finiteSeriesRLCEnergyAt run (intervention channel 1) channel)
        derivative 0 ∧
      derivative < 0
  offDiagonalCrosstalkRead :
    finiteSeriesRLCImplementation code crosstalkSourceUnit
        .neuralToBodyEffect = (quantizedCrosstalkAmplitude code : ℂ)
  endpointCommutes : ∀ initial,
    finiteSeriesRLCEndpointOutputAt (compileFiniteSeriesRLCNetlistRun code)
        initial =
      encodeHilbert
        (disturbedImplementedState (finiteSeriesRLCImplementation code)
          smallNonzeroConstantBias initial)
  linearTolerance :
    ‖finiteSeriesRLCImplementation code - idealQuarterOperator‖ <
      (1 : ℝ) / 80

theorem sourceGeneratedFiniteSeriesRLCNetlistRun
    (code : SourceOwnedNetlistCrosstalkCode) :
    SourceGeneratedFiniteSeriesRLCNetlistRunAt code where
  nodeCardinality := finiteSeriesRLCNode_cardinality
  coreElementCardinality := finiteSeriesRLCCoreElement_cardinality
  elementCardinality := finiteSeriesRLCNetlistElement_cardinality
  baseRunExact := rfl
  executedDurationPositive := quantizedExecutedDuration_pos code.1
  executedDurationNotExactQuarterPeriod :=
    quantizedExecutedDuration_ne_pi_div_two code.1
  independentBiasSourceNonzero := by
    rw [compiledFiniteSeriesRLCNetlistRun_endpointBiasAmplitude]
    norm_num
  dampingPositive := fun _ => finiteSeriesRLCDampingRate_pos
  capacitancePositive := fun channel => by
    rw [compiledFiniteSeriesRLCNetlistRun_capacitanceAt]
    norm_num
  inductancePositive := compiledFiniteSeriesRLCNetlistRun_inductance_pos code
  resistancePositive := compiledFiniteSeriesRLC_resistance_pos code
  dampingGeneratedByResistance :=
    compiledFiniteSeriesRLC_damping_eq_resistance_div_two_inductance code
  naturalFrequencyPrecompensated :=
    compiledFiniteSeriesRLC_naturalFrequencySq_eq_damped_add_damping code
  underdamped := compiledFiniteSeriesRLC_underdamped code
  initialCondition := fun initial => finiteSeriesRLCFlowAt_zero _ initial
  sourceDerivative := fun initial channel time =>
    finiteSeriesRLC_source_hasDerivAt _ initial channel time
  voltageDerivative := fun initial channel time =>
    finiteSeriesRLC_voltage_hasDerivAt _ initial channel time
  currentDerivative := fun initial channel time =>
    finiteSeriesRLC_current_hasDerivAt _ initial channel time
  currentIsGeneratedShear := fun initial channel time =>
    finiteSeriesRLCCurrentAt_eq_physicalCurrentShear _ initial channel time
  kirchhoffCurrent := fun initial channel time node =>
    finiteSeriesRLC_kirchhoffCurrentLaw _ initial channel time node
  resistorConstitutive := fun initial channel time =>
    finiteSeriesRLC_resistorElementVoltage _ initial channel time
  capacitorConstitutive := fun initial channel time =>
    compiledFiniteSeriesRLC_capacitorConstitutiveLaw
      code initial channel time
  inductorConstitutive := fun initial channel time =>
    compiledFiniteSeriesRLC_inductorElementVoltage code initial channel time
  voltageLoop := fun initial channel time =>
    finiteSeriesRLC_elementVoltageLoop_telescope _ initial channel time
  kirchhoffVoltage := fun initial channel time =>
    compiledFiniteSeriesRLC_kirchhoffVoltageLaw code initial channel time
  energyDissipation := fun initial channel time =>
    compiledFiniteSeriesRLC_energy_hasDerivAt code initial channel time
  energyAntitone := fun initial channel =>
    compiledFiniteSeriesRLC_energy_antitone code initial channel
  sourceImpulseStrictlyDissipates :=
    compiledFiniteSeriesRLC_sourceImpulse_strictDissipation code
  offDiagonalCrosstalkRead := finiteSeriesRLCImplementation_offDiagonalRead code
  endpointCommutes := compiledFiniteSeriesRLCEndpointOutput_commutes code
  linearTolerance := everyFiniteSeriesRLCImplementation_linearTolerance code

/-- The finite family returns the new physical receipt together with a crown
whose law is indexed by the dissipative implementation itself. -/
theorem everyFiniteSeriesRLCCode_generatesRunAndDirectCouplingCrown
    (code : SourceOwnedNetlistCrosstalkCode) :
    SourceGeneratedFiniteSeriesRLCNetlistRunAt code ∧
      SourceGeneratedTruthChildNeuralBodyCouplingLaw.SourceGeneratedTruthChildNeuralBodyCouplingCrownAt
        (additiveDisturbanceCertifiedTruthChildCouplingLaw
          (finiteSeriesRLCImplementation code)
          smallNonzeroConstantBias
          (finiteSeriesRLCAdditiveTolerance code)) :=
  ⟨sourceGeneratedFiniteSeriesRLCNetlistRun code,
    everyFiniteSeriesRLCCodeWithVisibleBias_constructible code⟩

end

end Producer
end Dissipative
end Netlist
end Physical
end Coupling
end Canonical
end Embodied
end Immortality
end Consciousness
end NoIslandNoMagic
end SaturationMonoid

#print axioms SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Physical.Netlist.Dissipative.Producer.everyFiniteSeriesRLCCodeWithVisibleBias_constructible
#print axioms SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Physical.Netlist.Dissipative.Producer.sourceGeneratedFiniteSeriesRLCNetlistRun
#print axioms SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Physical.Netlist.Dissipative.Producer.everyFiniteSeriesRLCCode_generatesRunAndDirectCouplingCrown
