import H0mework.Physics.RLCNetlist.DimensionedRun
import H0mework.Physics.RLCNetlist.Coupling

/-!
# Source-generated finite dimensioned series-RLC netlist coupling

An exact finite code and arbitrary positive typed `(T₀,V₀,I₀)` scales generate
one dimensioned series-RLC run.  The receipt retains the source compiler,
physical component scaling, typed differential circuit laws, Joule
dissipation, inverse-shear normalization, and the actual physical-duration
endpoint square.  No coupling crown is stored in the physical receipt.

The downstream theorem feeds the same `finiteSeriesRLCImplementation` read by
that endpoint square directly to the existing additive-disturbance consumer.
It does not reuse or transport a lossless coupling crown.
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
namespace Dimensioned
namespace Producer

open _root_.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Interface
open _root_.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Physical.Interface
open _root_.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Physical.Producer
open _root_.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Physical.Netlist.Interface
open _root_.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Physical.Netlist.Producer
open _root_.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Physical.Netlist.Dissipative.Interface
open _root_.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Physical.Netlist.Dissipative.Producer
open _root_.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Physical.Units.Interface

noncomputable section

/-- One normalized time unit is one millisecond, one normalized voltage unit
one millivolt, and one normalized current unit one microampere.  This is a
concrete nonunit SI scale, not a claim about a calibrated device. -/
def millisecondMillivoltMicroampereScale : PositiveElectricalScale where
  timeScale := ((1 : ℝ) / 1000) • oneSISecond
  voltageScale := ((1 : ℝ) / 1000) • oneSIVolt
  currentScale := ((1 : ℝ) / 1000000) • oneSIAmpere
  timeScalePositive := by
    norm_num [oneSISecond]
  voltageScalePositive := by
    norm_num [oneSIVolt]
  currentScalePositive := by
    norm_num [oneSIAmpere]

def millisecondMillivoltMicroampereSource
    (code : SourceOwnedNetlistCrosstalkCode) : DimensionedSeriesRLCSource :=
  (code, millisecondMillivoltMicroampereScale)

/-! ## Generated source readback -/

theorem compiledFiniteDimensionedSeriesRLC_sourceReadback
    (source : DimensionedSeriesRLCSource) :
    (compileFiniteDimensionedSeriesRLCNetlistRun source).normalizedRun =
        compileFiniteSeriesRLCNetlistRun source.1 ∧
      (compileFiniteDimensionedSeriesRLCNetlistRun source).scale = source.2 :=
  ⟨compiledFiniteDimensionedSeriesRLC_normalizedRun source,
    compiledFiniteDimensionedSeriesRLC_scale source⟩

/-! ## Crown-free physical receipt -/

/-- Maximal physical output of one dimensioned source.  The only input is the
finite code paired with positive typed scales.  Every differential law,
normalization square, and endpoint equality is generated afterward; no
coupling law or crown is a field. -/
structure SourceGeneratedFiniteDimensionedSeriesRLCNetlistRunAt
    (source : DimensionedSeriesRLCSource) : Prop where
  normalizedRunReceipt : SourceGeneratedFiniteSeriesRLCNetlistRunAt source.1
  sourceCompilerInjective :
    Function.Injective compileFiniteDimensionedSeriesRLCNetlistRun
  sourceReadback :
    type_of% (compiledFiniteDimensionedSeriesRLC_sourceReadback source)
  capacitanceScaling :
    type_of% (compiledFiniteDimensionedSeriesRLC_capacitance_scaling source)
  inductanceScaling :
    type_of% (compiledFiniteDimensionedSeriesRLC_inductance_scaling source)
  resistanceScaling :
    type_of% (compiledFiniteDimensionedSeriesRLC_resistance_scaling source)
  dampingScaling :
    type_of% (compiledFiniteDimensionedSeriesRLC_damping_scaling source)
  frequencyScaling :
    type_of% (compiledFiniteDimensionedSeriesRLC_frequency_scaling source)
  durationScaling :
    type_of% (compiledFiniteDimensionedSeriesRLC_duration_scaling source)
  capacitancePositive :
    type_of% (compiledFiniteDimensionedSeriesRLC_capacitance_pos source)
  inductancePositive :
    type_of% (compiledFiniteDimensionedSeriesRLC_inductance_pos source)
  resistancePositive :
    type_of% (compiledFiniteDimensionedSeriesRLC_resistance_pos source)
  dampingPositive :
    type_of% (compiledFiniteDimensionedSeriesRLC_damping_pos source)
  dampedFrequencyPositive :
    type_of% (compiledFiniteDimensionedSeriesRLC_frequency_pos source)
  executedDurationPositive :
    type_of% (compiledFiniteDimensionedSeriesRLC_duration_pos source)
  dampingGeneratedByResistance :
    type_of%
      (compiledFiniteDimensionedSeriesRLC_damping_eq_resistanceDamping source)
  naturalFrequencyPrecompensated :
    type_of% (compiledFiniteDimensionedSeriesRLC_naturalFrequencySq_eq source)
  underdamped :
    type_of% (compiledFiniteDimensionedSeriesRLC_underdamped source)
  executedTimePullback :
    type_of%
      (compiledFiniteDimensionedSeriesRLC_normalizedTime_executedDuration
        source)
  inverseShearNormalizesEveryState :
    type_of%
      (compiledFiniteDimensionedSeriesRLC_normalize_stateOfNormalized source)
  inverseShearNormalizesWholeFlow :
    type_of% (compiledFiniteDimensionedSeriesRLC_normalize_flow source)
  typedCurrentShear :
    type_of% (compiledFiniteDimensionedSeriesRLCCurrent_shear source)
  voltageDerivative :
    type_of%
      (finiteDimensionedSeriesRLCVoltage_hasSIQuantityDerivAt
        (compileFiniteDimensionedSeriesRLCNetlistRun source))
  currentDerivative :
    type_of%
      (finiteDimensionedSeriesRLCCurrent_hasSIQuantityDerivAt
        (compileFiniteDimensionedSeriesRLCNetlistRun source))
  kirchhoffCurrent :
    type_of%
      (finiteDimensionedSeriesRLC_kirchhoffCurrentLaw
        (compileFiniteDimensionedSeriesRLCNetlistRun source))
  capacitorConstitutive :
    type_of%
      (compiledFiniteDimensionedSeriesRLC_capacitorConstitutiveLaw source)
  resistorVoltage :
    type_of%
      (finiteDimensionedSeriesRLC_resistorVoltageLaw
        (compileFiniteDimensionedSeriesRLCNetlistRun source))
  capacitorVoltage :
    type_of%
      (finiteDimensionedSeriesRLC_capacitorVoltageLaw
        (compileFiniteDimensionedSeriesRLCNetlistRun source))
  inductorVoltage :
    type_of% (compiledFiniteDimensionedSeriesRLC_inductorVoltageLaw source)
  kirchhoffVoltage :
    type_of% (compiledFiniteDimensionedSeriesRLC_kirchhoffVoltageLaw source)
  voltageLoop :
    type_of%
      (finiteDimensionedSeriesRLC_elementVoltageLoop_telescope
        (compileFiniteDimensionedSeriesRLCNetlistRun source))
  jouleEnergyScaling :
    type_of% (compiledFiniteDimensionedSeriesRLC_energy_scaling source)
  jouleEnergyDerivative :
    type_of%
      (compiledFiniteDimensionedSeriesRLC_energy_hasSIQuantityDerivAt source)
  jouleEnergyAntitone :
    type_of% (compiledFiniteDimensionedSeriesRLC_energy_antitone source)
  sourceImpulseStrictlyDissipates :
    type_of%
      (compiledFiniteDimensionedSeriesRLC_sourceImpulse_strictDissipation
        source)
  physicalTransducerNormalizes :
    type_of%
      (compiledFiniteDimensionedSeriesRLCTransducerOutput_eq_normalized source)
  physicalEndpointEqualsExisting :
    type_of%
      (compiledFiniteDimensionedSeriesRLCEndpointOutput_eq_existing source)
  physicalEndpointStateNormalizes :
    type_of% (compiledFiniteDimensionedSeriesRLCEndpoint_normalizes source)
  physicalEndpointCommutes :
    type_of% (compiledFiniteDimensionedSeriesRLCEndpoint_commutes source)
  physicalEndpointEqualsDisturbedImplementation :
    type_of% (compiledFiniteDimensionedSeriesRLCEndpoint_eq_disturbed source)
  actualExecutedEndpointCommutes :
    type_of%
      (compiledFiniteDimensionedSeriesRLC_actualExecutedEndpoint_commutes
        source)

theorem sourceGeneratedFiniteDimensionedSeriesRLCNetlistRun
    (source : DimensionedSeriesRLCSource) :
    SourceGeneratedFiniteDimensionedSeriesRLCNetlistRunAt source where
  normalizedRunReceipt := sourceGeneratedFiniteSeriesRLCNetlistRun source.1
  sourceCompilerInjective :=
    compileFiniteDimensionedSeriesRLCNetlistRun_injective
  sourceReadback := compiledFiniteDimensionedSeriesRLC_sourceReadback source
  capacitanceScaling :=
    compiledFiniteDimensionedSeriesRLC_capacitance_scaling source
  inductanceScaling :=
    compiledFiniteDimensionedSeriesRLC_inductance_scaling source
  resistanceScaling :=
    compiledFiniteDimensionedSeriesRLC_resistance_scaling source
  dampingScaling := compiledFiniteDimensionedSeriesRLC_damping_scaling source
  frequencyScaling :=
    compiledFiniteDimensionedSeriesRLC_frequency_scaling source
  durationScaling := compiledFiniteDimensionedSeriesRLC_duration_scaling source
  capacitancePositive :=
    compiledFiniteDimensionedSeriesRLC_capacitance_pos source
  inductancePositive := compiledFiniteDimensionedSeriesRLC_inductance_pos source
  resistancePositive := compiledFiniteDimensionedSeriesRLC_resistance_pos source
  dampingPositive := compiledFiniteDimensionedSeriesRLC_damping_pos source
  dampedFrequencyPositive :=
    compiledFiniteDimensionedSeriesRLC_frequency_pos source
  executedDurationPositive :=
    compiledFiniteDimensionedSeriesRLC_duration_pos source
  dampingGeneratedByResistance :=
    compiledFiniteDimensionedSeriesRLC_damping_eq_resistanceDamping source
  naturalFrequencyPrecompensated :=
    compiledFiniteDimensionedSeriesRLC_naturalFrequencySq_eq source
  underdamped := compiledFiniteDimensionedSeriesRLC_underdamped source
  executedTimePullback :=
    compiledFiniteDimensionedSeriesRLC_normalizedTime_executedDuration source
  inverseShearNormalizesEveryState :=
    compiledFiniteDimensionedSeriesRLC_normalize_stateOfNormalized source
  inverseShearNormalizesWholeFlow :=
    compiledFiniteDimensionedSeriesRLC_normalize_flow source
  typedCurrentShear := compiledFiniteDimensionedSeriesRLCCurrent_shear source
  voltageDerivative := finiteDimensionedSeriesRLCVoltage_hasSIQuantityDerivAt _
  currentDerivative := finiteDimensionedSeriesRLCCurrent_hasSIQuantityDerivAt _
  kirchhoffCurrent := finiteDimensionedSeriesRLC_kirchhoffCurrentLaw _
  capacitorConstitutive :=
    compiledFiniteDimensionedSeriesRLC_capacitorConstitutiveLaw source
  resistorVoltage := finiteDimensionedSeriesRLC_resistorVoltageLaw _
  capacitorVoltage := finiteDimensionedSeriesRLC_capacitorVoltageLaw _
  inductorVoltage :=
    compiledFiniteDimensionedSeriesRLC_inductorVoltageLaw source
  kirchhoffVoltage :=
    compiledFiniteDimensionedSeriesRLC_kirchhoffVoltageLaw source
  voltageLoop := finiteDimensionedSeriesRLC_elementVoltageLoop_telescope _
  jouleEnergyScaling := compiledFiniteDimensionedSeriesRLC_energy_scaling source
  jouleEnergyDerivative :=
    compiledFiniteDimensionedSeriesRLC_energy_hasSIQuantityDerivAt source
  jouleEnergyAntitone :=
    compiledFiniteDimensionedSeriesRLC_energy_antitone source
  sourceImpulseStrictlyDissipates :=
    compiledFiniteDimensionedSeriesRLC_sourceImpulse_strictDissipation source
  physicalTransducerNormalizes :=
    compiledFiniteDimensionedSeriesRLCTransducerOutput_eq_normalized source
  physicalEndpointEqualsExisting :=
    compiledFiniteDimensionedSeriesRLCEndpointOutput_eq_existing source
  physicalEndpointStateNormalizes :=
    compiledFiniteDimensionedSeriesRLCEndpoint_normalizes source
  physicalEndpointCommutes :=
    compiledFiniteDimensionedSeriesRLCEndpoint_commutes source
  physicalEndpointEqualsDisturbedImplementation :=
    compiledFiniteDimensionedSeriesRLCEndpoint_eq_disturbed source
  actualExecutedEndpointCommutes :=
    compiledFiniteDimensionedSeriesRLC_actualExecutedEndpoint_commutes source

/-! ## Direct downstream coupling consumer -/

/-- The tolerance used by the generated dimensioned endpoint.  It is indexed
by the dissipative series-RLC implementation itself, not by the former
lossless implementation. -/
theorem finiteDimensionedSeriesRLCAdditiveTolerance
    (source : DimensionedSeriesRLCSource) :
    AdditiveDisturbanceToleranceAt
      (finiteSeriesRLCImplementation source.1) smallNonzeroConstantBias where
  linearPartTolerance :=
    everyFiniteSeriesRLCImplementation_linearTolerance source.1
  disturbanceBound := smallNonzeroConstantBias_bound

/-- Direct application of the existing additive-disturbance consumer to the
same dissipative implementation reached by the dimensioned endpoint square. -/
theorem everyFiniteDimensionedSeriesRLCSource_generatesDirectCouplingCrown
    (source : DimensionedSeriesRLCSource) :
    SourceGeneratedTruthChildNeuralBodyCouplingLaw.SourceGeneratedTruthChildNeuralBodyCouplingCrownAt
      (additiveDisturbanceCertifiedTruthChildCouplingLaw
        (finiteSeriesRLCImplementation source.1)
        smallNonzeroConstantBias
        (finiteDimensionedSeriesRLCAdditiveTolerance source)) :=
  everyAdditiveDisturbanceWithinTolerance_generatesCouplingCrown _ _ _

end

end Producer
end Dimensioned
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

#print axioms SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Physical.Netlist.Dissipative.Dimensioned.Producer.sourceGeneratedFiniteDimensionedSeriesRLCNetlistRun
#print axioms SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Physical.Netlist.Dissipative.Dimensioned.Producer.everyFiniteDimensionedSeriesRLCSource_generatesDirectCouplingCrown
