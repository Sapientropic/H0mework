import H0mework.Physics.RLCNetlist.Topology
import H0mework.Physics.LCNetlist.Run

/-!
# Finite series-RLC netlist run kernel

A finite source code compiles to an explicit dissipative series-RLC run.  The
run stores only source-side component and execution rows.  Its trajectory,
branch currents, constitutive laws, dissipated energy, and endpoint output are
all solved from those rows rather than stored as target certificates.

The generated inductance precompensates the damping rate, so the requested
code frequency remains the exact damped oscillation frequency:

`alpha = 10^-6`, `C = 1`, `L = (omega^2 + alpha^2)^-1`, and `R = 2 alpha L`.
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

open _root_.SaturationMonoid.AffineRelaxation
open _root_.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Physical.Interface
open _root_.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Physical.Producer
open _root_.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Physical.Netlist.Interface
open _root_.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Physical.Netlist.Producer
open _root_.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Physical.Netlist.Dissipative.Interface

noncomputable section

/-- The same finite source code used by the lossless run kernel, without
importing or assuming any already-produced coupling law. -/
abbrev SourceOwnedNetlistCrosstalkCode :=
  FiniteQuantizedChannelLCRunCrosstalkCode

def finiteSeriesRLCDampingRate : ℝ := (1 : ℝ) / 1000000

theorem finiteSeriesRLCDampingRate_pos :
    0 < finiteSeriesRLCDampingRate := by
  norm_num [finiteSeriesRLCDampingRate]

/-- Source-emitted component and execution rows.  No solved output, tolerance,
receipt, coupling law, or crown is stored in this occurrence. -/
structure FiniteSeriesRLCNetlistRunOccurrence where
  baseRun : FiniteParallelLCNetlistRunOccurrence
  dampingRateAt : FiniteEmbodimentChannel → ℝ
  capacitanceAt : FiniteEmbodimentChannel → ℝ
  inductanceAt : FiniteEmbodimentChannel → ℝ
  seriesResistanceAt : FiniteEmbodimentChannel → ℝ

def compileFiniteSeriesRLCNetlistRun
    (code : SourceOwnedNetlistCrosstalkCode) :
    FiniteSeriesRLCNetlistRunOccurrence where
  baseRun := compileFiniteParallelLCNetlistRun code
  dampingRateAt := fun _channel => finiteSeriesRLCDampingRate
  capacitanceAt := fun _channel => 1
  inductanceAt := fun channel =>
    ((compileFiniteParallelLCNetlistRun code).frequencyAt channel ^ 2 +
      finiteSeriesRLCDampingRate ^ 2)⁻¹
  seriesResistanceAt := fun channel =>
    2 * finiteSeriesRLCDampingRate *
      ((compileFiniteParallelLCNetlistRun code).frequencyAt channel ^ 2 +
        finiteSeriesRLCDampingRate ^ 2)⁻¹

/-- Projection back to the source-only base run is already a complete code
readback because the established base compiler is injective. -/
theorem compileFiniteSeriesRLCNetlistRun_injective :
    Function.Injective compileFiniteSeriesRLCNetlistRun := by
  intro left right sameRun
  exact compileFiniteParallelLCNetlistRun_injective
    (congrArg FiniteSeriesRLCNetlistRunOccurrence.baseRun sameRun)

@[simp] theorem compiledFiniteSeriesRLCNetlistRun_baseRun
    (code : SourceOwnedNetlistCrosstalkCode) :
    (compileFiniteSeriesRLCNetlistRun code).baseRun =
      compileFiniteParallelLCNetlistRun code :=
  rfl

@[simp] theorem compiledFiniteSeriesRLCNetlistRun_dampingRateAt
    (code : SourceOwnedNetlistCrosstalkCode)
    (channel : FiniteEmbodimentChannel) :
    (compileFiniteSeriesRLCNetlistRun code).dampingRateAt channel =
      finiteSeriesRLCDampingRate :=
  rfl

@[simp] theorem compiledFiniteSeriesRLCNetlistRun_capacitanceAt
    (code : SourceOwnedNetlistCrosstalkCode)
    (channel : FiniteEmbodimentChannel) :
    (compileFiniteSeriesRLCNetlistRun code).capacitanceAt channel = 1 :=
  rfl

@[simp] theorem compiledFiniteSeriesRLCNetlistRun_inductanceAt
    (code : SourceOwnedNetlistCrosstalkCode)
    (channel : FiniteEmbodimentChannel) :
    (compileFiniteSeriesRLCNetlistRun code).inductanceAt channel =
      ((compileFiniteParallelLCNetlistRun code).frequencyAt channel ^ 2 +
        finiteSeriesRLCDampingRate ^ 2)⁻¹ :=
  rfl

@[simp] theorem compiledFiniteSeriesRLCNetlistRun_seriesResistanceAt
    (code : SourceOwnedNetlistCrosstalkCode)
    (channel : FiniteEmbodimentChannel) :
    (compileFiniteSeriesRLCNetlistRun code).seriesResistanceAt channel =
      2 * finiteSeriesRLCDampingRate *
        (compileFiniteSeriesRLCNetlistRun code).inductanceAt channel :=
  rfl

@[simp] theorem compiledFiniteSeriesRLCNetlistRun_executedDuration
    (code : SourceOwnedNetlistCrosstalkCode) :
    (compileFiniteSeriesRLCNetlistRun code).baseRun.executedDuration =
      quantizedExecutedDuration code.1 :=
  rfl

@[simp] theorem compiledFiniteSeriesRLCNetlistRun_directedCrosstalkAmplitude
    (code : SourceOwnedNetlistCrosstalkCode) :
    (compileFiniteSeriesRLCNetlistRun code).baseRun.directedCrosstalkAmplitude =
      quantizedCrosstalkAmplitude code :=
  rfl

@[simp] theorem compiledFiniteSeriesRLCNetlistRun_endpointBiasAmplitude
    (code : SourceOwnedNetlistCrosstalkCode) :
    (compileFiniteSeriesRLCNetlistRun code).baseRun.endpointBiasAmplitude =
      (1 : ℝ) / 1000 :=
  rfl

theorem compiledFiniteSeriesRLCNetlistRun_frequency_pos
    (code : SourceOwnedNetlistCrosstalkCode)
    (channel : FiniteEmbodimentChannel) :
    0 < (compileFiniteSeriesRLCNetlistRun code).baseRun.frequencyAt channel :=
  compiledFiniteParallelLCNetlistRun_frequency_pos code channel

theorem compiledFiniteSeriesRLCNetlistRun_inductance_pos
    (code : SourceOwnedNetlistCrosstalkCode)
    (channel : FiniteEmbodimentChannel) :
    0 < (compileFiniteSeriesRLCNetlistRun code).inductanceAt channel := by
  rw [compiledFiniteSeriesRLCNetlistRun_inductanceAt]
  exact inv_pos.mpr (add_pos_of_pos_of_nonneg
    (sq_pos_of_pos
      (compiledFiniteParallelLCNetlistRun_frequency_pos code channel))
    (sq_nonneg finiteSeriesRLCDampingRate))

theorem compiledFiniteSeriesRLC_resistance_pos
    (code : SourceOwnedNetlistCrosstalkCode)
    (channel : FiniteEmbodimentChannel) :
    0 < (compileFiniteSeriesRLCNetlistRun code).seriesResistanceAt channel := by
  rw [compiledFiniteSeriesRLCNetlistRun_seriesResistanceAt]
  exact mul_pos (mul_pos (by norm_num) finiteSeriesRLCDampingRate_pos)
    (compiledFiniteSeriesRLCNetlistRun_inductance_pos code channel)

theorem compiledFiniteSeriesRLCNetlistRun_frequency_damping_balance
    (code : SourceOwnedNetlistCrosstalkCode)
    (channel : FiniteEmbodimentChannel) :
    (compileFiniteSeriesRLCNetlistRun code).inductanceAt channel *
        ((compileFiniteSeriesRLCNetlistRun code).baseRun.frequencyAt channel ^ 2 +
          (compileFiniteSeriesRLCNetlistRun code).dampingRateAt channel ^ 2) =
      1 := by
  have denominatorPositive :
      0 < (compileFiniteParallelLCNetlistRun code).frequencyAt channel ^ 2 +
        finiteSeriesRLCDampingRate ^ 2 := by
    exact add_pos_of_pos_of_nonneg
      (sq_pos_of_pos
        (compiledFiniteParallelLCNetlistRun_frequency_pos code channel))
      (sq_nonneg finiteSeriesRLCDampingRate)
  simp only [compiledFiniteSeriesRLCNetlistRun_inductanceAt,
    compiledFiniteSeriesRLCNetlistRun_baseRun,
    compiledFiniteSeriesRLCNetlistRun_dampingRateAt]
  field_simp [denominatorPositive.ne']

/-- The base-run frequency is the damped angular frequency `ν`, not the
undamped natural frequency. -/
def finiteSeriesRLCDampedAngularFrequencyAt
    (run : FiniteSeriesRLCNetlistRunOccurrence)
    (channel : FiniteEmbodimentChannel) : ℝ :=
  run.baseRun.frequencyAt channel

def finiteSeriesRLCNaturalAngularFrequencySqAt
    (run : FiniteSeriesRLCNetlistRunOccurrence)
    (channel : FiniteEmbodimentChannel) : ℝ :=
  1 / (run.inductanceAt channel * run.capacitanceAt channel)

@[simp] theorem finiteSeriesRLCDampedAngularFrequencyAt_eq_baseFrequency
    (run : FiniteSeriesRLCNetlistRunOccurrence)
    (channel : FiniteEmbodimentChannel) :
    finiteSeriesRLCDampedAngularFrequencyAt run channel =
      run.baseRun.frequencyAt channel :=
  rfl

/-- `α = R / (2L)` for every compiled component row. -/
theorem compiledFiniteSeriesRLC_damping_eq_resistance_div_two_inductance
    (code : SourceOwnedNetlistCrosstalkCode)
    (channel : FiniteEmbodimentChannel) :
    (compileFiniteSeriesRLCNetlistRun code).dampingRateAt channel =
      (compileFiniteSeriesRLCNetlistRun code).seriesResistanceAt channel /
        (2 * (compileFiniteSeriesRLCNetlistRun code).inductanceAt channel) := by
  rw [compiledFiniteSeriesRLCNetlistRun_dampingRateAt,
    compiledFiniteSeriesRLCNetlistRun_seriesResistanceAt]
  have inductanceNonzero :
      (compileFiniteSeriesRLCNetlistRun code).inductanceAt channel ≠ 0 :=
    ne_of_gt (compiledFiniteSeriesRLCNetlistRun_inductance_pos code channel)
  field_simp [inductanceNonzero]

/-- `ω₀² = 1/(LC) = ν² + α²`; this is the precompensation identity that
distinguishes natural from damped frequency. -/
theorem compiledFiniteSeriesRLC_naturalFrequencySq_eq_damped_add_damping
    (code : SourceOwnedNetlistCrosstalkCode)
    (channel : FiniteEmbodimentChannel) :
    finiteSeriesRLCNaturalAngularFrequencySqAt
        (compileFiniteSeriesRLCNetlistRun code) channel =
      finiteSeriesRLCDampedAngularFrequencyAt
          (compileFiniteSeriesRLCNetlistRun code) channel ^ 2 +
        (compileFiniteSeriesRLCNetlistRun code).dampingRateAt channel ^ 2 := by
  simp only [finiteSeriesRLCNaturalAngularFrequencySqAt,
    finiteSeriesRLCDampedAngularFrequencyAt,
    compiledFiniteSeriesRLCNetlistRun_capacitanceAt,
    compiledFiniteSeriesRLCNetlistRun_inductanceAt,
    compiledFiniteSeriesRLCNetlistRun_baseRun,
    compiledFiniteSeriesRLCNetlistRun_dampingRateAt, mul_one, one_div,
    inv_inv]

theorem compiledFiniteSeriesRLC_dampedFrequency_pos
    (code : SourceOwnedNetlistCrosstalkCode)
    (channel : FiniteEmbodimentChannel) :
    0 < finiteSeriesRLCDampedAngularFrequencyAt
      (compileFiniteSeriesRLCNetlistRun code) channel :=
  compiledFiniteParallelLCNetlistRun_frequency_pos code channel

/-- Every emitted row is genuinely underdamped: the characteristic
discriminant leaves the strictly positive requested damped frequency square. -/
theorem compiledFiniteSeriesRLC_underdamped
    (code : SourceOwnedNetlistCrosstalkCode)
    (channel : FiniteEmbodimentChannel) :
    0 < finiteSeriesRLCNaturalAngularFrequencySqAt
          (compileFiniteSeriesRLCNetlistRun code) channel -
        ((compileFiniteSeriesRLCNetlistRun code).seriesResistanceAt channel /
          (2 * (compileFiniteSeriesRLCNetlistRun code).inductanceAt channel)) ^ 2 := by
  rw [← compiledFiniteSeriesRLC_damping_eq_resistance_div_two_inductance,
    compiledFiniteSeriesRLC_naturalFrequencySq_eq_damped_add_damping]
  nlinarith [sq_pos_of_pos
    (compiledFiniteSeriesRLC_dampedFrequency_pos code channel)]

/-! ## Exact dissipative trajectory -/

def finiteSeriesRLCScaleAt
    (run : FiniteSeriesRLCNetlistRunOccurrence)
    (channel : FiniteEmbodimentChannel) (time : ℝ) : ℝ :=
  Real.exp ((-run.dampingRateAt channel) * time)

def finiteSeriesRLCEnvelope (time : ℝ) : ℝ :=
  Real.exp (-finiteSeriesRLCDampingRate * time)

def finiteSeriesRLCFlowAt
    (run : FiniteSeriesRLCNetlistRunOccurrence)
    (initial : FiniteEmbodimentState) (time : ℝ) :
    FiniteEmbodimentState :=
  fun channel =>
    let scale := finiteSeriesRLCScaleAt run channel time
    let undamped := finiteParallelLCFlowAt run.baseRun initial time channel
    (scale * undamped.1, scale * undamped.2)

@[simp] theorem finiteSeriesRLCFlowAt_zero
    (run : FiniteSeriesRLCNetlistRunOccurrence)
    (initial : FiniteEmbodimentState) :
    finiteSeriesRLCFlowAt run initial 0 = initial := by
  funext channel
  simp [finiteSeriesRLCFlowAt, finiteSeriesRLCScaleAt]

def finiteSeriesRLCVoltageAt
    (run : FiniteSeriesRLCNetlistRunOccurrence)
    (initial : FiniteEmbodimentState) (channel : FiniteEmbodimentChannel)
    (time : ℝ) : ℝ :=
  targetPort (finiteSeriesRLCFlowAt run initial time) channel

/-- The physical current is obtained from the harmonic state by the explicit
shear `i = ν p - α v`; the stored source coordinate `p` is not silently
identified with circuit current. -/
def finiteSeriesRLCPhysicalCurrentShear
    (run : FiniteSeriesRLCNetlistRunOccurrence)
    (state : FiniteEmbodimentState) (channel : FiniteEmbodimentChannel) : ℝ :=
  finiteSeriesRLCDampedAngularFrequencyAt run channel *
      sourcePort state channel -
    run.dampingRateAt channel * targetPort state channel

/-- Physical series current in shifted-current coordinates. -/
def finiteSeriesRLCCurrentAt
    (run : FiniteSeriesRLCNetlistRunOccurrence)
    (initial : FiniteEmbodimentState) (channel : FiniteEmbodimentChannel)
    (time : ℝ) : ℝ :=
  run.baseRun.frequencyAt channel *
      sourcePort (finiteSeriesRLCFlowAt run initial time) channel -
    run.dampingRateAt channel *
      targetPort (finiteSeriesRLCFlowAt run initial time) channel

theorem finiteSeriesRLCCurrentAt_eq_physicalCurrentShear
    (run : FiniteSeriesRLCNetlistRunOccurrence)
    (initial : FiniteEmbodimentState) (channel : FiniteEmbodimentChannel)
    (time : ℝ) :
    finiteSeriesRLCCurrentAt run initial channel time =
      finiteSeriesRLCPhysicalCurrentShear run
        (finiteSeriesRLCFlowAt run initial time) channel :=
  rfl

/-- The shear is invertible on every compiled row because `ν > 0`. -/
theorem compiledFiniteSeriesRLC_sourcePort_eq_inverseCurrentShear
    (code : SourceOwnedNetlistCrosstalkCode)
    (initial : FiniteEmbodimentState) (channel : FiniteEmbodimentChannel)
    (time : ℝ) :
    sourcePort
        (finiteSeriesRLCFlowAt (compileFiniteSeriesRLCNetlistRun code)
          initial time) channel =
      (finiteSeriesRLCCurrentAt (compileFiniteSeriesRLCNetlistRun code)
          initial channel time +
        (compileFiniteSeriesRLCNetlistRun code).dampingRateAt channel *
          finiteSeriesRLCVoltageAt (compileFiniteSeriesRLCNetlistRun code)
            initial channel time) /
        finiteSeriesRLCDampedAngularFrequencyAt
          (compileFiniteSeriesRLCNetlistRun code) channel := by
  have frequencyNonzero :
      finiteSeriesRLCDampedAngularFrequencyAt
        (compileFiniteSeriesRLCNetlistRun code) channel ≠ 0 :=
    ne_of_gt (compiledFiniteSeriesRLC_dampedFrequency_pos code channel)
  rw [eq_div_iff frequencyNonzero]
  unfold finiteSeriesRLCCurrentAt finiteSeriesRLCVoltageAt
    finiteSeriesRLCDampedAngularFrequencyAt
  ring

def finiteSeriesRLCCurrentDerivativeAt
    (run : FiniteSeriesRLCNetlistRunOccurrence)
    (initial : FiniteEmbodimentState) (channel : FiniteEmbodimentChannel)
    (time : ℝ) : ℝ :=
  -2 * run.dampingRateAt channel * run.baseRun.frequencyAt channel *
      sourcePort (finiteSeriesRLCFlowAt run initial time) channel +
    (run.dampingRateAt channel ^ 2 -
        run.baseRun.frequencyAt channel ^ 2) *
      targetPort (finiteSeriesRLCFlowAt run initial time) channel

@[simp] theorem finiteSeriesRLCCurrentAt_zero
    (run : FiniteSeriesRLCNetlistRunOccurrence)
    (initial : FiniteEmbodimentState) (channel : FiniteEmbodimentChannel) :
    finiteSeriesRLCCurrentAt run initial channel 0 =
      run.baseRun.frequencyAt channel * sourcePort initial channel -
        run.dampingRateAt channel * targetPort initial channel := by
  simp [finiteSeriesRLCCurrentAt]

@[simp] theorem compiledFiniteSeriesRLCCurrentAt_zero_intervention
    (code : SourceOwnedNetlistCrosstalkCode)
    (channel : FiniteEmbodimentChannel) :
    finiteSeriesRLCCurrentAt (compileFiniteSeriesRLCNetlistRun code)
        (intervention channel 1) channel 0 =
      (compileFiniteParallelLCNetlistRun code).frequencyAt channel := by
  simp [finiteSeriesRLCCurrentAt, intervention, sourcePort, targetPort]

theorem finiteSeriesRLCScale_hasDerivAt
    (run : FiniteSeriesRLCNetlistRunOccurrence)
    (channel : FiniteEmbodimentChannel) (time : ℝ) :
    HasDerivAt (finiteSeriesRLCScaleAt run channel)
      (-run.dampingRateAt channel *
        finiteSeriesRLCScaleAt run channel time) time := by
  have inner :=
    (hasDerivAt_id' time).const_mul (-run.dampingRateAt channel)
  have exponential := inner.exp
  change HasDerivAt
    (fun t => Real.exp ((-run.dampingRateAt channel) * t))
    (-run.dampingRateAt channel *
      Real.exp ((-run.dampingRateAt channel) * time)) time
  exact exponential.congr_deriv (by ring)

theorem finiteSeriesRLC_source_hasDerivAt
    (run : FiniteSeriesRLCNetlistRunOccurrence)
    (initial : FiniteEmbodimentState) (channel : FiniteEmbodimentChannel)
    (time : ℝ) :
    HasDerivAt
      (fun t => sourcePort (finiteSeriesRLCFlowAt run initial t) channel)
      (-run.dampingRateAt channel *
          sourcePort (finiteSeriesRLCFlowAt run initial time) channel -
        run.baseRun.frequencyAt channel *
          targetPort (finiteSeriesRLCFlowAt run initial time) channel)
      time := by
  have scaleDerivative := finiteSeriesRLCScale_hasDerivAt run channel time
  have sourceDerivative := finiteParallelLC_source_hasDerivAt
    run.baseRun initial channel time
  have product := scaleDerivative.mul sourceDerivative
  rcases hbase : finiteParallelLCFlowAt run.baseRun initial time channel with
    ⟨momentum, position⟩
  change HasDerivAt
    (fun t => finiteSeriesRLCScaleAt run channel t *
      sourcePort (finiteParallelLCFlowAt run.baseRun initial t) channel) _ time
  convert product using 1
  all_goals try rfl
  all_goals simp [finiteSeriesRLCFlowAt, sourcePort, targetPort, hbase]
  all_goals ring

theorem finiteSeriesRLC_target_hasDerivAt
    (run : FiniteSeriesRLCNetlistRunOccurrence)
    (initial : FiniteEmbodimentState) (channel : FiniteEmbodimentChannel)
    (time : ℝ) :
    HasDerivAt
      (fun t => targetPort (finiteSeriesRLCFlowAt run initial t) channel)
      (run.baseRun.frequencyAt channel *
          sourcePort (finiteSeriesRLCFlowAt run initial time) channel -
        run.dampingRateAt channel *
          targetPort (finiteSeriesRLCFlowAt run initial time) channel)
      time := by
  have scaleDerivative := finiteSeriesRLCScale_hasDerivAt run channel time
  have targetDerivative := finiteParallelLC_target_hasDerivAt
    run.baseRun initial channel time
  have product := scaleDerivative.mul targetDerivative
  rcases hbase : finiteParallelLCFlowAt run.baseRun initial time channel with
    ⟨momentum, position⟩
  change HasDerivAt
    (fun t => finiteSeriesRLCScaleAt run channel t *
      targetPort (finiteParallelLCFlowAt run.baseRun initial t) channel) _ time
  convert product using 1
  all_goals try rfl
  all_goals simp [finiteSeriesRLCFlowAt, sourcePort, targetPort, hbase]
  all_goals ring

theorem finiteSeriesRLC_voltage_hasDerivAt
    (run : FiniteSeriesRLCNetlistRunOccurrence)
    (initial : FiniteEmbodimentState) (channel : FiniteEmbodimentChannel)
    (time : ℝ) :
    HasDerivAt (finiteSeriesRLCVoltageAt run initial channel)
      (finiteSeriesRLCCurrentAt run initial channel time) time := by
  change HasDerivAt
    (fun t => targetPort (finiteSeriesRLCFlowAt run initial t) channel) _ time
  exact finiteSeriesRLC_target_hasDerivAt run initial channel time

theorem finiteSeriesRLC_current_hasDerivAt
    (run : FiniteSeriesRLCNetlistRunOccurrence)
    (initial : FiniteEmbodimentState) (channel : FiniteEmbodimentChannel)
    (time : ℝ) :
    HasDerivAt (finiteSeriesRLCCurrentAt run initial channel)
      (finiteSeriesRLCCurrentDerivativeAt run initial channel time) time := by
  have sourceDerivative :=
    finiteSeriesRLC_source_hasDerivAt run initial channel time
  have targetDerivative :=
    finiteSeriesRLC_target_hasDerivAt run initial channel time
  have combined :=
    (sourceDerivative.const_mul (run.baseRun.frequencyAt channel)).sub
      (targetDerivative.const_mul (run.dampingRateAt channel))
  change HasDerivAt
    (fun t => run.baseRun.frequencyAt channel *
        sourcePort (finiteSeriesRLCFlowAt run initial t) channel -
      run.dampingRateAt channel *
        targetPort (finiteSeriesRLCFlowAt run initial t) channel) _ time
  exact combined.congr_deriv (by
    simp only [finiteSeriesRLCCurrentDerivativeAt]
    ring)

/-! ## Incidence and circuit laws -/

/-- All three oriented series-loop elements carry the same physical current;
their element-level incidence supplies the signs in KCL. -/
def finiteSeriesRLCElementCurrentAt
    (run : FiniteSeriesRLCNetlistRunOccurrence)
    (initial : FiniteEmbodimentState) (channel : FiniteEmbodimentChannel)
    (time : ℝ) (_element : SeriesRLCCoreElementKind) : ℝ :=
  finiteSeriesRLCCurrentAt run initial channel time

def finiteSeriesRLCNodeCurrentAt
    (run : FiniteSeriesRLCNetlistRunOccurrence)
    (initial : FiniteEmbodimentState) (channel : FiniteEmbodimentChannel)
    (time : ℝ) (node : SeriesRLCLocalNode) : ℝ :=
  ∑ element : SeriesRLCCoreElementKind,
    (seriesRLCCoreIncidence node element : ℝ) *
      finiteSeriesRLCElementCurrentAt run initial channel time element

/-- The resistor, inductor, and capacitor carry one loop current.  Their
element-level incidence cancels at the signal, internal-junction, and
reference nodes. -/
theorem finiteSeriesRLC_kirchhoffCurrentLaw
    (run : FiniteSeriesRLCNetlistRunOccurrence)
    (initial : FiniteEmbodimentState) (channel : FiniteEmbodimentChannel)
    (time : ℝ) (node : SeriesRLCLocalNode) :
    finiteSeriesRLCNodeCurrentAt run initial channel time node = 0 := by
  classical
  have elements : (Finset.univ : Finset SeriesRLCCoreElementKind) =
      {.seriesResistor, .inductor, .capacitor} := by
    ext element
    cases element <;> simp
  cases node <;>
    simp [finiteSeriesRLCNodeCurrentAt, elements,
      seriesRLCCoreIncidence, finiteSeriesRLCElementCurrentAt]

/-- With generated `C=1`, the actual voltage derivative is `i / C`. -/
theorem compiledFiniteSeriesRLC_capacitorConstitutiveLaw
    (code : SourceOwnedNetlistCrosstalkCode)
    (initial : FiniteEmbodimentState) (channel : FiniteEmbodimentChannel)
    (time : ℝ) :
    HasDerivAt
      (finiteSeriesRLCVoltageAt (compileFiniteSeriesRLCNetlistRun code)
        initial channel)
      (finiteSeriesRLCCurrentAt (compileFiniteSeriesRLCNetlistRun code)
          initial channel time /
        (compileFiniteSeriesRLCNetlistRun code).capacitanceAt channel)
      time := by
  simpa using finiteSeriesRLC_voltage_hasDerivAt
    (compileFiniteSeriesRLCNetlistRun code) initial channel time

/-- Exact series KVL: `L i' + R i + v = 0`. -/
theorem compiledFiniteSeriesRLC_kirchhoffVoltageLaw
    (code : SourceOwnedNetlistCrosstalkCode)
    (initial : FiniteEmbodimentState) (channel : FiniteEmbodimentChannel)
    (time : ℝ) :
    let run := compileFiniteSeriesRLCNetlistRun code
    run.inductanceAt channel *
        finiteSeriesRLCCurrentDerivativeAt run initial channel time +
      run.seriesResistanceAt channel *
        finiteSeriesRLCCurrentAt run initial channel time +
      finiteSeriesRLCVoltageAt run initial channel time = 0 := by
  dsimp
  let omega := (compileFiniteParallelLCNetlistRun code).frequencyAt channel
  let alpha := finiteSeriesRLCDampingRate
  let source := sourcePort
    (finiteSeriesRLCFlowAt (compileFiniteSeriesRLCNetlistRun code)
      initial time) channel
  let target := targetPort
    (finiteSeriesRLCFlowAt (compileFiniteSeriesRLCNetlistRun code)
      initial time) channel
  have denominatorPositive : 0 < omega ^ 2 + alpha ^ 2 := by
    exact add_pos_of_pos_of_nonneg
      (sq_pos_of_pos
        (compiledFiniteParallelLCNetlistRun_frequency_pos code channel))
      (sq_nonneg alpha)
  change (omega ^ 2 + alpha ^ 2)⁻¹ *
      (-2 * alpha * omega * source + (alpha ^ 2 - omega ^ 2) * target) +
    (2 * alpha * (omega ^ 2 + alpha ^ 2)⁻¹) *
      (omega * source - alpha * target) + target = 0
  field_simp [denominatorPositive.ne']
  ring

/-- Actual three-node voltage readout.  The internal junction is generated
from the resistor drop; it is not an additional stored run field. -/
def finiteSeriesRLCNodePotentialAt
    (run : FiniteSeriesRLCNetlistRunOccurrence)
    (initial : FiniteEmbodimentState) (channel : FiniteEmbodimentChannel)
    (time : ℝ) : SeriesRLCLocalNode → ℝ
  | .signal => finiteSeriesRLCVoltageAt run initial channel time
  | .seriesJunction =>
      -run.seriesResistanceAt channel *
        finiteSeriesRLCCurrentAt run initial channel time
  | .reference => 0

/-- Element voltage is the source-node potential minus target-node potential,
using the topology's explicit orientation. -/
def finiteSeriesRLCElementVoltageAt
    (run : FiniteSeriesRLCNetlistRunOccurrence)
    (initial : FiniteEmbodimentState) (channel : FiniteEmbodimentChannel)
    (time : ℝ) (element : SeriesRLCCoreElementKind) : ℝ :=
  finiteSeriesRLCNodePotentialAt run initial channel time
      (seriesRLCCoreElementSource element) -
    finiteSeriesRLCNodePotentialAt run initial channel time
      (seriesRLCCoreElementTarget element)

theorem finiteSeriesRLC_resistorElementVoltage
    (run : FiniteSeriesRLCNetlistRunOccurrence)
    (initial : FiniteEmbodimentState) (channel : FiniteEmbodimentChannel)
    (time : ℝ) :
    finiteSeriesRLCElementVoltageAt run initial channel time .seriesResistor =
      run.seriesResistanceAt channel *
        finiteSeriesRLCCurrentAt run initial channel time := by
  simp [finiteSeriesRLCElementVoltageAt, finiteSeriesRLCNodePotentialAt,
    seriesRLCCoreElementSource, seriesRLCCoreElementTarget]

theorem finiteSeriesRLC_capacitorElementVoltage
    (run : FiniteSeriesRLCNetlistRunOccurrence)
    (initial : FiniteEmbodimentState) (channel : FiniteEmbodimentChannel)
    (time : ℝ) :
    finiteSeriesRLCElementVoltageAt run initial channel time .capacitor =
      finiteSeriesRLCVoltageAt run initial channel time := by
  simp [finiteSeriesRLCElementVoltageAt, finiteSeriesRLCNodePotentialAt,
    seriesRLCCoreElementSource, seriesRLCCoreElementTarget]

/-- The three source-minus-target voltage drops telescope around the explicit
`reference → R → junction → L → signal → C → reference` loop. -/
theorem finiteSeriesRLC_elementVoltageLoop_telescope
    (run : FiniteSeriesRLCNetlistRunOccurrence)
    (initial : FiniteEmbodimentState) (channel : FiniteEmbodimentChannel)
    (time : ℝ) :
    ∑ element : SeriesRLCCoreElementKind,
      finiteSeriesRLCElementVoltageAt run initial channel time element = 0 := by
  classical
  have elements : (Finset.univ : Finset SeriesRLCCoreElementKind) =
      {.seriesResistor, .inductor, .capacitor} := by
    ext element
    cases element <;> simp
  simp [elements, finiteSeriesRLCElementVoltageAt,
    finiteSeriesRLCNodePotentialAt, seriesRLCCoreElementSource,
    seriesRLCCoreElementTarget]

/-- The inductor's source-minus-target potential drop is exactly `L i'`;
this makes the algebraic KVL theorem a literal potential-loop law. -/
theorem compiledFiniteSeriesRLC_inductorElementVoltage
    (code : SourceOwnedNetlistCrosstalkCode)
    (initial : FiniteEmbodimentState) (channel : FiniteEmbodimentChannel)
    (time : ℝ) :
    let run := compileFiniteSeriesRLCNetlistRun code
    finiteSeriesRLCElementVoltageAt run initial channel time .inductor =
      run.inductanceAt channel *
        finiteSeriesRLCCurrentDerivativeAt run initial channel time := by
  dsimp
  have kvl := compiledFiniteSeriesRLC_kirchhoffVoltageLaw
    code initial channel time
  dsimp at kvl
  simp only [finiteSeriesRLCElementVoltageAt,
    finiteSeriesRLCNodePotentialAt, seriesRLCCoreElementSource,
    seriesRLCCoreElementTarget]
  rw [compiledFiniteSeriesRLCNetlistRun_seriesResistanceAt,
    compiledFiniteSeriesRLCNetlistRun_inductanceAt,
    compiledFiniteParallelLCNetlistRun_frequencyAt]
  linarith

def finiteSeriesRLCEnergyAt
    (run : FiniteSeriesRLCNetlistRunOccurrence)
    (initial : FiniteEmbodimentState) (channel : FiniteEmbodimentChannel)
    (time : ℝ) : ℝ :=
  run.inductanceAt channel *
      finiteSeriesRLCCurrentAt run initial channel time ^ 2 +
    run.capacitanceAt channel *
      finiteSeriesRLCVoltageAt run initial channel time ^ 2

/-- The actual solved trajectory dissipates physical series-RLC energy at the
Joule rate `-2 R i^2` for the no-one-half energy normalization. -/
theorem compiledFiniteSeriesRLC_energy_hasDerivAt
    (code : SourceOwnedNetlistCrosstalkCode)
    (initial : FiniteEmbodimentState) (channel : FiniteEmbodimentChannel)
    (time : ℝ) :
    let run := compileFiniteSeriesRLCNetlistRun code
    HasDerivAt (finiteSeriesRLCEnergyAt run initial channel)
      (-2 * run.seriesResistanceAt channel *
        finiteSeriesRLCCurrentAt run initial channel time ^ 2) time := by
  dsimp
  let run := compileFiniteSeriesRLCNetlistRun code
  let current := finiteSeriesRLCCurrentAt run initial channel time
  let currentDerivative :=
    finiteSeriesRLCCurrentDerivativeAt run initial channel time
  let voltage := finiteSeriesRLCVoltageAt run initial channel time
  have currentHasDerivAt :=
    finiteSeriesRLC_current_hasDerivAt run initial channel time
  have voltageHasDerivAt :=
    finiteSeriesRLC_voltage_hasDerivAt run initial channel time
  have energyHasDerivAt :=
    ((currentHasDerivAt.pow 2).const_mul (run.inductanceAt channel)).add
      ((voltageHasDerivAt.pow 2).const_mul (run.capacitanceAt channel))
  have normalizedEnergyHasDerivAt :
      HasDerivAt (finiteSeriesRLCEnergyAt run initial channel)
        (2 * run.inductanceAt channel * current * currentDerivative +
          2 * run.capacitanceAt channel * voltage * current) time := by
    convert energyHasDerivAt using 1
    all_goals try rfl
    all_goals simp [current, currentDerivative, voltage]
    all_goals ring
  apply normalizedEnergyHasDerivAt.congr_deriv
  have kvl := compiledFiniteSeriesRLC_kirchhoffVoltageLaw
    code initial channel time
  change run.inductanceAt channel * currentDerivative +
      run.seriesResistanceAt channel * current + voltage = 0 at kvl
  have reactiveDrop :
      run.inductanceAt channel * currentDerivative + voltage =
        -run.seriesResistanceAt channel * current := by
    linarith
  rw [compiledFiniteSeriesRLCNetlistRun_capacitanceAt]
  calc
    2 * run.inductanceAt channel * current * currentDerivative +
        2 * 1 * voltage * current =
      2 * current *
        (run.inductanceAt channel * currentDerivative + voltage) := by ring
    _ = 2 * current * (-run.seriesResistanceAt channel * current) := by
      rw [reactiveDrop]
    _ = -2 * run.seriesResistanceAt channel * current ^ 2 := by ring

theorem compiledFiniteSeriesRLC_energyDerivative_nonpos
    (code : SourceOwnedNetlistCrosstalkCode)
    (initial : FiniteEmbodimentState) (channel : FiniteEmbodimentChannel)
    (time : ℝ) :
    -2 * (compileFiniteSeriesRLCNetlistRun code).seriesResistanceAt channel *
        finiteSeriesRLCCurrentAt (compileFiniteSeriesRLCNetlistRun code)
          initial channel time ^ 2 ≤ 0 := by
  have resistancePositive := compiledFiniteSeriesRLC_resistance_pos code channel
  have currentSquareNonnegative := sq_nonneg
    (finiteSeriesRLCCurrentAt (compileFiniteSeriesRLCNetlistRun code)
      initial channel time)
  nlinarith

/-- The physical energy is globally antitone in forward time, not merely
locally decreasing at the emitted endpoint. -/
theorem compiledFiniteSeriesRLC_energy_antitone
    (code : SourceOwnedNetlistCrosstalkCode)
    (initial : FiniteEmbodimentState) (channel : FiniteEmbodimentChannel) :
    Antitone (finiteSeriesRLCEnergyAt
      (compileFiniteSeriesRLCNetlistRun code) initial channel) := by
  apply antitone_of_deriv_nonpos
  · intro time
    exact (compiledFiniteSeriesRLC_energy_hasDerivAt
      code initial channel time).differentiableAt
  · intro time
    rw [(compiledFiniteSeriesRLC_energy_hasDerivAt
      code initial channel time).deriv]
    exact compiledFiniteSeriesRLC_energyDerivative_nonpos
      code initial channel time

/-- A unit source impulse witnesses strict Joule loss immediately: positivity
of both `R` and the damped frequency prevents the derivative from vanishing. -/
theorem compiledFiniteSeriesRLC_sourceImpulse_energyDerivative_neg
    (code : SourceOwnedNetlistCrosstalkCode)
    (channel : FiniteEmbodimentChannel) :
    -2 * (compileFiniteSeriesRLCNetlistRun code).seriesResistanceAt channel *
        finiteSeriesRLCCurrentAt (compileFiniteSeriesRLCNetlistRun code)
          (intervention channel 1) channel 0 ^ 2 < 0 := by
  rw [compiledFiniteSeriesRLCCurrentAt_zero_intervention]
  have resistancePositive := compiledFiniteSeriesRLC_resistance_pos code channel
  have frequencyPositive :=
    compiledFiniteParallelLCNetlistRun_frequency_pos code channel
  nlinarith [sq_pos_of_pos frequencyPositive]

theorem compiledFiniteSeriesRLC_sourceImpulse_strictDissipation
    (code : SourceOwnedNetlistCrosstalkCode)
    (channel : FiniteEmbodimentChannel) :
    let run := compileFiniteSeriesRLCNetlistRun code
    let derivative := -2 * run.seriesResistanceAt channel *
      finiteSeriesRLCCurrentAt run (intervention channel 1) channel 0 ^ 2
    HasDerivAt
        (finiteSeriesRLCEnergyAt run (intervention channel 1) channel)
        derivative 0 ∧
      derivative < 0 := by
  exact ⟨compiledFiniteSeriesRLC_energy_hasDerivAt
      code (intervention channel 1) channel 0,
    compiledFiniteSeriesRLC_sourceImpulse_energyDerivative_neg code channel⟩

/-! ## Exact generated output and implementation commuting -/

theorem encodePort_finiteSeriesRLCFlowAt
    (run : FiniteSeriesRLCNetlistRunOccurrence)
    (initial : FiniteEmbodimentState) (channel : FiniteEmbodimentChannel)
    (time : ℝ) :
    encodePort (finiteSeriesRLCFlowAt run initial time channel) =
      (finiteSeriesRLCScaleAt run channel time : ℂ) *
        encodePort (finiteParallelLCFlowAt run.baseRun initial time channel) := by
  rcases hbase : finiteParallelLCFlowAt run.baseRun initial time channel with
    ⟨momentum, position⟩
  apply Complex.ext
  · simp [finiteSeriesRLCFlowAt, encodePort, hbase]
  · simp [finiteSeriesRLCFlowAt, encodePort, hbase]

def finiteSeriesRLCTransducerOutputAt
    (run : FiniteSeriesRLCNetlistRunOccurrence)
    (initial : FiniteEmbodimentState) (time : ℝ) :
    HilbertEmbodimentState :=
  WithLp.toLp 2 (fun channel =>
    ((run.baseRun.branchAt channel).transferGain : ℂ) *
      encodePort (finiteSeriesRLCFlowAt run initial time channel))

theorem compiledFiniteSeriesRLCTransducerOutput_eq_compiledOperator
    (code : SourceOwnedNetlistCrosstalkCode)
    (initial : FiniteEmbodimentState) (time : ℝ) :
    finiteSeriesRLCTransducerOutputAt
        (compileFiniteSeriesRLCNetlistRun code) initial time =
      (finiteSeriesRLCEnvelope time : ℂ) •
        compiledChannelwiseLCTransducerOperator
          (finiteQuantizedChannelwiseDesign code.1.1) time
          (encodeHilbert initial) := by
  rw [← compiledFiniteParallelLCTransducerOutput_eq_compiledOperator
    code initial time]
  ext channel
  rw [PiLp.smul_apply]
  change (quantizedChannelGain code.1.1 channel : ℂ) *
      encodePort
        (finiteSeriesRLCFlowAt (compileFiniteSeriesRLCNetlistRun code)
          initial time channel) = _
  rw [encodePort_finiteSeriesRLCFlowAt]
  have scaleEq :
      finiteSeriesRLCScaleAt (compileFiniteSeriesRLCNetlistRun code)
          channel time = finiteSeriesRLCEnvelope time := by
    rfl
  rw [scaleEq]
  simp [finiteParallelLCTransducerOutputAt,
    compileFiniteSeriesRLCNetlistRun]
  ring

/-- The endpoint solver uses exactly the rational duration emitted in the run,
with no hidden replacement by `π/2`. -/
theorem compiledFiniteSeriesRLCTransducerOutput_at_executedDuration
    (code : SourceOwnedNetlistCrosstalkCode)
    (initial : FiniteEmbodimentState) :
    finiteSeriesRLCTransducerOutputAt
        (compileFiniteSeriesRLCNetlistRun code) initial
        (compileFiniteSeriesRLCNetlistRun code).baseRun.executedDuration =
      (finiteSeriesRLCEnvelope (quantizedExecutedDuration code.1) : ℂ) •
        compiledChannelwiseLCTransducerOperator
          (finiteQuantizedChannelwiseDesign code.1.1)
          (quantizedExecutedDuration code.1) (encodeHilbert initial) := by
  rw [compiledFiniteSeriesRLCNetlistRun_executedDuration]
  exact compiledFiniteSeriesRLCTransducerOutput_eq_compiledOperator
    code initial (quantizedExecutedDuration code.1)

def finiteSeriesRLCImplementation
    (code : SourceOwnedNetlistCrosstalkCode) :
    HilbertEmbodimentState →L[ℂ] HilbertEmbodimentState :=
  (finiteSeriesRLCEnvelope (quantizedExecutedDuration code.1) : ℂ) •
      compiledChannelwiseLCTransducerOperator
        (finiteQuantizedChannelwiseDesign code.1.1)
        (quantizedExecutedDuration code.1) +
    (quantizedCrosstalkAmplitude code : ℂ) • rankOneCrosstalkOperator

/-- The new damped implementation still exposes the generated off-diagonal
crosstalk coefficient exactly; its dissipative diagonal part cannot capture
the source coordinate at another channel. -/
theorem finiteSeriesRLCImplementation_offDiagonalRead
    (code : SourceOwnedNetlistCrosstalkCode) :
    finiteSeriesRLCImplementation code crosstalkSourceUnit
        .neuralToBodyEffect = (quantizedCrosstalkAmplitude code : ℂ) := by
  unfold finiteSeriesRLCImplementation
  simp only [add_apply, smul_apply]
  unfold crosstalkSourceUnit
  rw [PiLp.add_apply, PiLp.smul_apply]
  rw [compiledChannelwiseLCTransducerOperator_noCrossChannelCapture
    _ _ _ _ (by decide)]
  rw [rankOneCrosstalkOperator_apply]
  norm_num [PiLp.single_apply]

def finiteSeriesRLCLinearOutputAt
    (run : FiniteSeriesRLCNetlistRunOccurrence)
    (initial : FiniteEmbodimentState) : HilbertEmbodimentState :=
  finiteSeriesRLCTransducerOutputAt run initial run.baseRun.executedDuration +
    (run.baseRun.directedCrosstalkAmplitude : ℂ) •
      rankOneCrosstalkOperator (encodeHilbert initial)

def finiteSeriesRLCEndpointOutputAt
    (run : FiniteSeriesRLCNetlistRunOccurrence)
    (initial : FiniteEmbodimentState) : HilbertEmbodimentState :=
  finiteSeriesRLCLinearOutputAt run initial +
    (run.baseRun.endpointBiasAmplitude : ℂ) •
      finiteParallelLCBiasDirection

theorem compiledFiniteSeriesRLCLinearOutput_eq_implementation
    (code : SourceOwnedNetlistCrosstalkCode)
    (initial : FiniteEmbodimentState) :
    finiteSeriesRLCLinearOutputAt (compileFiniteSeriesRLCNetlistRun code)
        initial =
      finiteSeriesRLCImplementation code (encodeHilbert initial) := by
  unfold finiteSeriesRLCLinearOutputAt finiteSeriesRLCImplementation
  simp only [add_apply, smul_apply]
  change finiteSeriesRLCTransducerOutputAt
        (compileFiniteSeriesRLCNetlistRun code) initial
        (quantizedExecutedDuration code.1) +
      (quantizedCrosstalkAmplitude code : ℂ) •
        rankOneCrosstalkOperator (encodeHilbert initial) = _
  rw [compiledFiniteSeriesRLCTransducerOutput_eq_compiledOperator]

theorem compiledFiniteSeriesRLCEndpointOutput_eq_disturbedImplementation
    (code : SourceOwnedNetlistCrosstalkCode)
    (initial : FiniteEmbodimentState) :
    finiteSeriesRLCEndpointOutputAt (compileFiniteSeriesRLCNetlistRun code)
        initial =
      finiteSeriesRLCImplementation code (encodeHilbert initial) +
        smallNonzeroConstantBias initial := by
  rw [finiteSeriesRLCEndpointOutputAt,
    compiledFiniteSeriesRLCLinearOutput_eq_implementation]
  simp [compileFiniteSeriesRLCNetlistRun,
    compileFiniteParallelLCNetlistRun, finiteParallelLCBiasDirection,
    smallNonzeroConstantBias]

/-- Exact commuting with the newly generated dissipative implementation and
the existing independent endpoint disturbance. -/
theorem compiledFiniteSeriesRLCEndpointOutput_commutes
    (code : SourceOwnedNetlistCrosstalkCode)
    (initial : FiniteEmbodimentState) :
    finiteSeriesRLCEndpointOutputAt (compileFiniteSeriesRLCNetlistRun code)
        initial =
      encodeHilbert
        (disturbedImplementedState
          (finiteSeriesRLCImplementation code)
          smallNonzeroConstantBias initial) := by
  rw [encodeHilbert_disturbedImplementedState]
  exact compiledFiniteSeriesRLCEndpointOutput_eq_disturbedImplementation
    code initial

/-! The previously paid finite-code estimates survive this physical
dissipative compiler. -/

theorem finiteSeriesRLC_quantizedExecutedDuration_lt_two
    (code : SourceOwnedNetlistCrosstalkCode) :
    quantizedExecutedDuration code.1 < 2 := by
  cases h : code.1.2 <;>
    norm_num [quantizedExecutedDuration, rationalClockCentre,
      ternaryOffsetValue, h]

theorem finiteSeriesRLCEnvelope_sub_one_abs_lt
    (code : SourceOwnedNetlistCrosstalkCode) :
    |finiteSeriesRLCEnvelope (quantizedExecutedDuration code.1) - 1| <
      (1 : ℝ) / 500000 := by
  have durationPositive := quantizedExecutedDuration_pos code.1
  have xNonnegative :
      0 ≤ finiteSeriesRLCDampingRate * quantizedExecutedDuration code.1 :=
    mul_nonneg finiteSeriesRLCDampingRate_pos.le durationPositive.le
  have xSmall :
      finiteSeriesRLCDampingRate * quantizedExecutedDuration code.1 <
        (1 : ℝ) / 500000 := by
    dsimp [finiteSeriesRLCDampingRate]
    nlinarith [finiteSeriesRLC_quantizedExecutedDuration_lt_two code]
  have exponentialAtMostOne :
      Real.exp (-(finiteSeriesRLCDampingRate *
        quantizedExecutedDuration code.1)) ≤ 1 :=
    (Real.exp_le_one_iff).2 (by linarith)
  have tangent := Real.add_one_le_exp
    (-(finiteSeriesRLCDampingRate * quantizedExecutedDuration code.1))
  unfold finiteSeriesRLCEnvelope
  rw [show -finiteSeriesRLCDampingRate * quantizedExecutedDuration code.1 =
    -(finiteSeriesRLCDampingRate * quantizedExecutedDuration code.1) by ring]
  rw [abs_of_nonpos (sub_nonpos.mpr exponentialAtMostOne)]
  nlinarith

theorem finiteSeriesRLC_quantizedBaseOperator_norm_le_one
    (code : SourceOwnedNetlistCrosstalkCode) :
    ‖compiledChannelwiseLCTransducerOperator
        (finiteQuantizedChannelwiseDesign code.1.1)
        (quantizedExecutedDuration code.1)‖ ≤ 1 := by
  rw [compiledChannelwiseLCTransducerOperator,
    Matrix.l2_opNorm_toEuclideanCLM, Matrix.l2_opNorm_diagonal]
  refine (pi_norm_le_iff_of_nonneg (by norm_num)).2 ?_
  intro channel
  have admissible :=
    finiteQuantizedChannelwise_componentAdmissible code.1.1 channel
  rw [channelwiseTransducerCoefficient, norm_mul,
    Complex.norm_real, Real.norm_eq_abs,
    schrodingerScalarPhase_norm, mul_one]
  rw [abs_of_pos]
  · simpa [channelDesign] using admissible.transferGainPassive
  · simpa [channelDesign] using admissible.transferGainPositive

theorem finiteSeriesRLCDampingTerm_norm_lt
    (code : SourceOwnedNetlistCrosstalkCode) :
    ‖((finiteSeriesRLCEnvelope (quantizedExecutedDuration code.1) : ℂ) - 1) •
        compiledChannelwiseLCTransducerOperator
          (finiteQuantizedChannelwiseDesign code.1.1)
          (quantizedExecutedDuration code.1)‖ < (1 : ℝ) / 500000 := by
  rw [show (finiteSeriesRLCEnvelope
      (quantizedExecutedDuration code.1) : ℂ) - 1 =
    ((finiteSeriesRLCEnvelope
      (quantizedExecutedDuration code.1) - 1 : ℝ) : ℂ) by
      push_cast
      rfl]
  rw [norm_smul, Complex.norm_real, Real.norm_eq_abs]
  calc
    _ ≤ |finiteSeriesRLCEnvelope (quantizedExecutedDuration code.1) - 1| * 1 :=
      mul_le_mul_of_nonneg_left
        (finiteSeriesRLC_quantizedBaseOperator_norm_le_one code) (abs_nonneg _)
    _ < ((1 : ℝ) / 500000) * 1 :=
      mul_lt_mul_of_pos_right
        (finiteSeriesRLCEnvelope_sub_one_abs_lt code) zero_lt_one
    _ = (1 : ℝ) / 500000 := by norm_num

theorem everyFiniteSeriesRLCImplementation_linearTolerance
    (code : SourceOwnedNetlistCrosstalkCode) :
    ‖finiteSeriesRLCImplementation code - idealQuarterOperator‖ <
      (1 : ℝ) / 80 := by
  let base := compiledChannelwiseLCTransducerOperator
    (finiteQuantizedChannelwiseDesign code.1.1)
    (quantizedExecutedDuration code.1)
  let dampingTerm :=
    ((finiteSeriesRLCEnvelope (quantizedExecutedDuration code.1) : ℂ) - 1) •
      base
  let crossTerm :=
    (quantizedCrosstalkAmplitude code : ℂ) • rankOneCrosstalkOperator
  have baseBound : ‖base - idealQuarterOperator‖ < (41 : ℝ) / 4000 :=
    finiteQuantizedChannelLCRun_operatorToIdeal_tight code.1
  have dampingBound : ‖dampingTerm‖ < (1 : ℝ) / 500000 :=
    finiteSeriesRLCDampingTerm_norm_lt code
  have crossBound : ‖crossTerm‖ ≤ (1 : ℝ) / 1000 :=
    quantizedCrosstalkOperator_norm_le code
  calc
    ‖finiteSeriesRLCImplementation code - idealQuarterOperator‖ =
      ‖(base - idealQuarterOperator) + dampingTerm + crossTerm‖ := by
        congr 1
        unfold finiteSeriesRLCImplementation dampingTerm crossTerm base
        module
    _ ≤ (‖base - idealQuarterOperator‖ + ‖dampingTerm‖) +
        ‖crossTerm‖ := (norm_add_le _ _).trans
          (add_le_add (norm_add_le _ _) le_rfl)
    _ < (((41 : ℝ) / 4000) + (1 : ℝ) / 500000) +
        (1 : ℝ) / 1000 :=
      add_lt_add_of_lt_of_le (add_lt_add baseBound dampingBound) crossBound
    _ < (1 : ℝ) / 80 := by norm_num

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

#print axioms SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Physical.Netlist.Dissipative.Producer.compileFiniteSeriesRLCNetlistRun_injective
#print axioms SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Physical.Netlist.Dissipative.Producer.compiledFiniteSeriesRLC_naturalFrequencySq_eq_damped_add_damping
#print axioms SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Physical.Netlist.Dissipative.Producer.compiledFiniteSeriesRLC_underdamped
#print axioms SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Physical.Netlist.Dissipative.Producer.compiledFiniteSeriesRLC_sourcePort_eq_inverseCurrentShear
#print axioms SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Physical.Netlist.Dissipative.Producer.finiteSeriesRLC_source_hasDerivAt
#print axioms SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Physical.Netlist.Dissipative.Producer.finiteSeriesRLC_target_hasDerivAt
#print axioms SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Physical.Netlist.Dissipative.Producer.finiteSeriesRLC_current_hasDerivAt
#print axioms SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Physical.Netlist.Dissipative.Producer.finiteSeriesRLC_kirchhoffCurrentLaw
#print axioms SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Physical.Netlist.Dissipative.Producer.compiledFiniteSeriesRLC_capacitorConstitutiveLaw
#print axioms SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Physical.Netlist.Dissipative.Producer.compiledFiniteSeriesRLC_kirchhoffVoltageLaw
#print axioms SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Physical.Netlist.Dissipative.Producer.compiledFiniteSeriesRLC_inductorElementVoltage
#print axioms SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Physical.Netlist.Dissipative.Producer.compiledFiniteSeriesRLC_resistance_pos
#print axioms SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Physical.Netlist.Dissipative.Producer.compiledFiniteSeriesRLC_energy_hasDerivAt
#print axioms SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Physical.Netlist.Dissipative.Producer.compiledFiniteSeriesRLC_energy_antitone
#print axioms SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Physical.Netlist.Dissipative.Producer.compiledFiniteSeriesRLC_sourceImpulse_strictDissipation
#print axioms SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Physical.Netlist.Dissipative.Producer.compiledFiniteSeriesRLCTransducerOutput_at_executedDuration
#print axioms SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Physical.Netlist.Dissipative.Producer.finiteSeriesRLCImplementation_offDiagonalRead
#print axioms SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Physical.Netlist.Dissipative.Producer.everyFiniteSeriesRLCImplementation_linearTolerance
#print axioms SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Physical.Netlist.Dissipative.Producer.compiledFiniteSeriesRLCEndpointOutput_commutes
