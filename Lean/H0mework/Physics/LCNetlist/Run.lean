import H0mework.Physics.LCNetlist.Topology

/-!
# Finite quantized parallel-LC netlist run kernel

A finite code now compiles to a source-side run occurrence containing only
component rows, generated frequencies, an emitted rational duration, one
directed parasitic amplitude, and one independent endpoint-source amplitude.
It stores no solved trajectory, output operator, tolerance, receipt, or crown.

The solver constructs the trajectory.  Kirchhoff current/voltage laws,
capacitor and inductor constitutive equations, reactive-energy conservation,
and exact endpoint commuting are then proved from that trajectory.
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
namespace Producer

open _root_.SaturationMonoid.AffineRelaxation
open Physical.Interface Physical.Producer Netlist.Interface

noncomputable section

/-- Source fields emitted before circuit solution.  In particular, no target
operator or acceptance certificate is a field. -/
structure FiniteParallelLCNetlistRunOccurrence where
  branchAt : FiniteEmbodimentChannel → LCTransducerBranchDesign
  frequencyAt : FiniteEmbodimentChannel → ℝ
  executedDuration : ℝ
  directedCrosstalkAmplitude : ℝ
  endpointBiasAmplitude : ℝ

def compileFiniteParallelLCNetlistRun
    (code : FiniteQuantizedChannelLCRunCrosstalkCode) :
    FiniteParallelLCNetlistRunOccurrence where
  branchAt := (finiteQuantizedChannelwiseDesign code.1.1).branchAt
  frequencyAt := quantizedChannelFrequency code.1.1
  executedDuration := quantizedExecutedDuration code.1
  directedCrosstalkAmplitude := quantizedCrosstalkAmplitude code
  endpointBiasAmplitude := (1 : ℝ) / 1000

/-- A source-only readback of component rows, emitted duration, and parasitic
amplitude. -/
def finiteParallelLCNetlistRunConfiguration
    (run : FiniteParallelLCNetlistRunOccurrence) :=
  (((⟨run.branchAt⟩ : ChannelwiseFiniteLCTransducerNetworkDesign),
      run.executedDuration), run.directedCrosstalkAmplitude)

@[simp] theorem compiledFiniteParallelLCNetlistRun_configuration
    (code : FiniteQuantizedChannelLCRunCrosstalkCode) :
    finiteParallelLCNetlistRunConfiguration
        (compileFiniteParallelLCNetlistRun code) =
      finiteQuantizedChannelLCRunCrosstalkConfiguration code :=
  rfl

/-- No code direction is erased on entry to the netlist run carrier. -/
theorem compileFiniteParallelLCNetlistRun_injective :
    Function.Injective compileFiniteParallelLCNetlistRun := by
  intro left right sameRun
  apply finiteQuantizedChannelLCRunCrosstalkConfiguration_injective
  rw [← compiledFiniteParallelLCNetlistRun_configuration left,
    ← compiledFiniteParallelLCNetlistRun_configuration right]
  exact congrArg finiteParallelLCNetlistRunConfiguration sameRun

@[simp] theorem compiledFiniteParallelLCNetlistRun_frequencyAt
    (code : FiniteQuantizedChannelLCRunCrosstalkCode)
    (channel : FiniteEmbodimentChannel) :
    (compileFiniteParallelLCNetlistRun code).frequencyAt channel =
      quantizedChannelFrequency code.1.1 channel :=
  rfl

@[simp] theorem compiledFiniteParallelLCNetlistRun_capacitance
    (code : FiniteQuantizedChannelLCRunCrosstalkCode)
    (channel : FiniteEmbodimentChannel) :
    ((compileFiniteParallelLCNetlistRun code).branchAt channel).capacitance = 1 :=
  rfl

@[simp] theorem compiledFiniteParallelLCNetlistRun_gain
    (code : FiniteQuantizedChannelLCRunCrosstalkCode)
    (channel : FiniteEmbodimentChannel) :
    ((compileFiniteParallelLCNetlistRun code).branchAt channel).transferGain =
      quantizedChannelGain code.1.1 channel :=
  rfl

theorem compiledFiniteParallelLCNetlistRun_frequency_pos
    (code : FiniteQuantizedChannelLCRunCrosstalkCode)
    (channel : FiniteEmbodimentChannel) :
    0 < (compileFiniteParallelLCNetlistRun code).frequencyAt channel :=
  quantizedChannelFrequency_pos code.1.1 channel

theorem compiledFiniteParallelLCNetlistRun_inductance_frequency_sq
    (code : FiniteQuantizedChannelLCRunCrosstalkCode)
    (channel : FiniteEmbodimentChannel) :
    ((compileFiniteParallelLCNetlistRun code).branchAt channel).inductance *
        ((compileFiniteParallelLCNetlistRun code).frequencyAt channel) ^ 2 =
      1 := by
  have frequencyNonzero : quantizedChannelFrequency code.1.1 channel ≠ 0 :=
    ne_of_gt (quantizedChannelFrequency_pos code.1.1 channel)
  change ((quantizedChannelFrequency code.1.1 channel)⁻¹) ^ 2 *
      (quantizedChannelFrequency code.1.1 channel) ^ 2 = 1
  field_simp [frequencyNonzero]

/-! ## Generated circuit trajectory -/

def finiteParallelLCFlowAt
    (run : FiniteParallelLCNetlistRunOccurrence)
    (initial : FiniteEmbodimentState) (time : ℝ) :
    FiniteEmbodimentState :=
  fun channel => harmonicFlow (run.frequencyAt channel * time) initial channel

@[simp] theorem finiteParallelLCFlowAt_zero
    (run : FiniteParallelLCNetlistRunOccurrence)
    (initial : FiniteEmbodimentState) :
    finiteParallelLCFlowAt run initial 0 = initial := by
  funext channel
  simp [finiteParallelLCFlowAt]

def finiteParallelLCVoltageAt
    (run : FiniteParallelLCNetlistRunOccurrence)
    (initial : FiniteEmbodimentState) (channel : FiniteEmbodimentChannel)
    (time : ℝ) : ℝ :=
  targetPort (finiteParallelLCFlowAt run initial time) channel

def finiteParallelLCInductorCurrentAt
    (run : FiniteParallelLCNetlistRunOccurrence)
    (initial : FiniteEmbodimentState) (channel : FiniteEmbodimentChannel)
    (time : ℝ) : ℝ :=
  -run.frequencyAt channel *
    sourcePort (finiteParallelLCFlowAt run initial time) channel

def finiteParallelLCCapacitorCurrentAt
    (run : FiniteParallelLCNetlistRunOccurrence)
    (initial : FiniteEmbodimentState) (channel : FiniteEmbodimentChannel)
    (time : ℝ) : ℝ :=
  run.frequencyAt channel *
    sourcePort (finiteParallelLCFlowAt run initial time) channel

def finiteParallelLCElementCurrentAt
    (run : FiniteParallelLCNetlistRunOccurrence)
    (initial : FiniteEmbodimentState) (channel : FiniteEmbodimentChannel)
    (time : ℝ) : ParallelLCCoreElementKind → ℝ
  | .inductor => finiteParallelLCInductorCurrentAt run initial channel time
  | .capacitor => finiteParallelLCCapacitorCurrentAt run initial channel time

def finiteParallelLCElementVoltageAt
    (run : FiniteParallelLCNetlistRunOccurrence)
    (initial : FiniteEmbodimentState) (channel : FiniteEmbodimentChannel)
    (time : ℝ) (_element : ParallelLCCoreElementKind) : ℝ :=
  finiteParallelLCVoltageAt run initial channel time

def finiteParallelLCNodeCurrentAt
    (run : FiniteParallelLCNetlistRunOccurrence)
    (initial : FiniteEmbodimentState) (channel : FiniteEmbodimentChannel)
    (time : ℝ) (node : ParallelLCLocalNode) : ℝ :=
  ∑ element : ParallelLCCoreElementKind,
    (parallelLCCoreIncidence node element : ℝ) *
      finiteParallelLCElementCurrentAt run initial channel time element

/-- KCL is generated from the two oppositely valued branch currents at both
nodes; it is not a field of the run occurrence. -/
theorem finiteParallelLC_kirchhoffCurrentLaw
    (run : FiniteParallelLCNetlistRunOccurrence)
    (initial : FiniteEmbodimentState) (channel : FiniteEmbodimentChannel)
    (time : ℝ) (node : ParallelLCLocalNode) :
    finiteParallelLCNodeCurrentAt run initial channel time node = 0 := by
  classical
  have elements : (Finset.univ : Finset ParallelLCCoreElementKind) =
      {.inductor, .capacitor} := by
    ext element
    cases element <;> simp
  cases node <;>
    simp [finiteParallelLCNodeCurrentAt, elements,
      parallelLCCoreIncidence, finiteParallelLCElementCurrentAt,
      finiteParallelLCInductorCurrentAt,
      finiteParallelLCCapacitorCurrentAt]

/-- Both branches see the same two-node voltage: the parallel KVL law. -/
theorem finiteParallelLC_kirchhoffVoltageLaw
    (run : FiniteParallelLCNetlistRunOccurrence)
    (initial : FiniteEmbodimentState) (channel : FiniteEmbodimentChannel)
    (time : ℝ) (left right : ParallelLCCoreElementKind) :
    finiteParallelLCElementVoltageAt run initial channel time left =
      finiteParallelLCElementVoltageAt run initial channel time right :=
  rfl

theorem finiteParallelLC_source_hasDerivAt
    (run : FiniteParallelLCNetlistRunOccurrence)
    (initial : FiniteEmbodimentState) (channel : FiniteEmbodimentChannel)
    (time : ℝ) :
    HasDerivAt
      (fun t => sourcePort (finiteParallelLCFlowAt run initial t) channel)
      (-run.frequencyAt channel *
        targetPort (finiteParallelLCFlowAt run initial time) channel) time := by
  rcases hstate : initial channel with ⟨momentum, position⟩
  simp only [sourcePort, targetPort, finiteParallelLCFlowAt,
    harmonicFlow, hstate]
  have phase : HasDerivAt (fun t : ℝ => run.frequencyAt channel * t)
      (run.frequencyAt channel) time := by
    simpa using (hasDerivAt_id' time).const_mul (run.frequencyAt channel)
  have derivative :=
    ((Real.hasDerivAt_cos (run.frequencyAt channel * time)).comp time phase
      ).mul_const momentum |>.sub
      (((Real.hasDerivAt_sin (run.frequencyAt channel * time)).comp time phase
        ).mul_const position)
  convert derivative using 1
  all_goals try rfl
  all_goals ring

theorem finiteParallelLC_target_hasDerivAt
    (run : FiniteParallelLCNetlistRunOccurrence)
    (initial : FiniteEmbodimentState) (channel : FiniteEmbodimentChannel)
    (time : ℝ) :
    HasDerivAt
      (fun t => targetPort (finiteParallelLCFlowAt run initial t) channel)
      (run.frequencyAt channel *
        sourcePort (finiteParallelLCFlowAt run initial time) channel) time := by
  rcases hstate : initial channel with ⟨momentum, position⟩
  simp only [sourcePort, targetPort, finiteParallelLCFlowAt,
    harmonicFlow, hstate]
  have phase : HasDerivAt (fun t : ℝ => run.frequencyAt channel * t)
      (run.frequencyAt channel) time := by
    simpa using (hasDerivAt_id' time).const_mul (run.frequencyAt channel)
  have derivative :=
    ((Real.hasDerivAt_sin (run.frequencyAt channel * time)).comp time phase
      ).mul_const momentum |>.add
      (((Real.hasDerivAt_cos (run.frequencyAt channel * time)).comp time phase
        ).mul_const position)
  convert derivative using 1
  all_goals try rfl
  all_goals ring

theorem finiteParallelLC_voltage_hasDerivAt
    (run : FiniteParallelLCNetlistRunOccurrence)
    (initial : FiniteEmbodimentState) (channel : FiniteEmbodimentChannel)
    (time : ℝ) :
    HasDerivAt (finiteParallelLCVoltageAt run initial channel)
      (finiteParallelLCCapacitorCurrentAt run initial channel time) time := by
  change HasDerivAt
    (fun t => targetPort (finiteParallelLCFlowAt run initial t) channel)
    (run.frequencyAt channel *
      sourcePort (finiteParallelLCFlowAt run initial time) channel) time
  exact finiteParallelLC_target_hasDerivAt run initial channel time

theorem finiteParallelLC_inductorCurrent_hasDerivAt
    (run : FiniteParallelLCNetlistRunOccurrence)
    (initial : FiniteEmbodimentState) (channel : FiniteEmbodimentChannel)
    (time : ℝ) :
    HasDerivAt (finiteParallelLCInductorCurrentAt run initial channel)
      ((run.frequencyAt channel) ^ 2 *
        finiteParallelLCVoltageAt run initial channel time) time := by
  have sourceDerivative :=
    finiteParallelLC_source_hasDerivAt run initial channel time
  have scaled := sourceDerivative.const_mul (-run.frequencyAt channel)
  change HasDerivAt
    (fun t => -run.frequencyAt channel *
      sourcePort (finiteParallelLCFlowAt run initial t) channel)
    ((run.frequencyAt channel) ^ 2 *
      targetPort (finiteParallelLCFlowAt run initial time) channel) time
  exact scaled.congr_deriv (by ring)

/-- The compiled `C=1` branch satisfies `i_C = C * dv/dt`. -/
theorem compiledFiniteParallelLC_capacitorConstitutiveLaw
    (code : FiniteQuantizedChannelLCRunCrosstalkCode)
    (initial : FiniteEmbodimentState) (channel : FiniteEmbodimentChannel)
    (time : ℝ) :
    HasDerivAt
      (finiteParallelLCVoltageAt (compileFiniteParallelLCNetlistRun code)
        initial channel)
      (finiteParallelLCCapacitorCurrentAt
          (compileFiniteParallelLCNetlistRun code) initial channel time /
        ((compileFiniteParallelLCNetlistRun code).branchAt channel).capacitance)
      time := by
  simpa using finiteParallelLC_voltage_hasDerivAt
    (compileFiniteParallelLCNetlistRun code) initial channel time

/-- The generated derivative and `L * omega^2 = 1` jointly give the inductor
constitutive voltage law `v_L = L * di_L/dt`. -/
theorem compiledFiniteParallelLC_inductorConstitutiveLaw
    (code : FiniteQuantizedChannelLCRunCrosstalkCode)
    (initial : FiniteEmbodimentState) (channel : FiniteEmbodimentChannel)
    (time : ℝ) :
    ((compileFiniteParallelLCNetlistRun code).branchAt channel).inductance *
        ((compileFiniteParallelLCNetlistRun code).frequencyAt channel ^ 2 *
          finiteParallelLCVoltageAt (compileFiniteParallelLCNetlistRun code)
            initial channel time) =
      finiteParallelLCElementVoltageAt
        (compileFiniteParallelLCNetlistRun code) initial channel time
        .inductor := by
  rw [← mul_assoc,
    compiledFiniteParallelLCNetlistRun_inductance_frequency_sq]
  simp [finiteParallelLCElementVoltageAt]

/-! ## Reactive energy and exact endpoint solution -/

def finiteParallelLCReactiveEnergyAt
    (run : FiniteParallelLCNetlistRunOccurrence)
    (initial : FiniteEmbodimentState) (channel : FiniteEmbodimentChannel)
    (time : ℝ) : ℝ :=
  (run.branchAt channel).inductance *
      (finiteParallelLCInductorCurrentAt run initial channel time) ^ 2 +
    (run.branchAt channel).capacitance *
      (finiteParallelLCVoltageAt run initial channel time) ^ 2

theorem compiledFiniteParallelLC_reactiveEnergy_eq_channelEnergy
    (code : FiniteQuantizedChannelLCRunCrosstalkCode)
    (initial : FiniteEmbodimentState) (channel : FiniteEmbodimentChannel)
    (time : ℝ) :
    finiteParallelLCReactiveEnergyAt (compileFiniteParallelLCNetlistRun code)
        initial channel time =
      channelEnergy
        (finiteParallelLCFlowAt (compileFiniteParallelLCNetlistRun code)
          initial time) channel := by
  let run := compileFiniteParallelLCNetlistRun code
  let source := sourcePort (finiteParallelLCFlowAt run initial time) channel
  let target := targetPort (finiteParallelLCFlowAt run initial time) channel
  have balance :=
    compiledFiniteParallelLCNetlistRun_inductance_frequency_sq code channel
  change (run.branchAt channel).inductance *
      (-run.frequencyAt channel * source) ^ 2 + 1 * target ^ 2 =
    source ^ 2 + target ^ 2
  calc
    _ = ((run.branchAt channel).inductance *
          run.frequencyAt channel ^ 2) * source ^ 2 + target ^ 2 := by ring
    _ = source ^ 2 + target ^ 2 := by
      change ((compileFiniteParallelLCNetlistRun code).branchAt channel).inductance *
          (compileFiniteParallelLCNetlistRun code).frequencyAt channel ^ 2 *
            source ^ 2 + target ^ 2 = _
      rw [balance]
      ring

theorem compiledFiniteParallelLC_reactiveEnergy_conserved
    (code : FiniteQuantizedChannelLCRunCrosstalkCode)
    (initial : FiniteEmbodimentState) (channel : FiniteEmbodimentChannel)
    (time : ℝ) :
    finiteParallelLCReactiveEnergyAt (compileFiniteParallelLCNetlistRun code)
        initial channel time =
      finiteParallelLCReactiveEnergyAt (compileFiniteParallelLCNetlistRun code)
        initial channel 0 := by
  rw [compiledFiniteParallelLC_reactiveEnergy_eq_channelEnergy,
    compiledFiniteParallelLC_reactiveEnergy_eq_channelEnergy,
    finiteParallelLCFlowAt_zero]
  exact harmonicFlow_channelEnergy_conserved
    ((compileFiniteParallelLCNetlistRun code).frequencyAt channel * time)
    initial channel

theorem schrodingerScalarPhase_one_scaled_forNetlist (omega time : ℝ) :
    schrodingerScalarPhase 1 (omega * time) =
      schrodingerScalarPhase omega time := by
  simp [schrodingerScalarPhase, unitComplexPhaseWithRate]

def finiteParallelLCTransducerOutputAt
    (run : FiniteParallelLCNetlistRunOccurrence)
    (initial : FiniteEmbodimentState) (time : ℝ) :
    HilbertEmbodimentState :=
  WithLp.toLp 2 (fun channel =>
    ((run.branchAt channel).transferGain : ℂ) *
      encodePort ((finiteParallelLCFlowAt run initial time) channel))

theorem compiledFiniteParallelLCTransducerOutput_eq_compiledOperator
    (code : FiniteQuantizedChannelLCRunCrosstalkCode)
    (initial : FiniteEmbodimentState) (time : ℝ) :
    finiteParallelLCTransducerOutputAt
        (compileFiniteParallelLCNetlistRun code) initial time =
      compiledChannelwiseLCTransducerOperator
        (finiteQuantizedChannelwiseDesign code.1.1) time
        (encodeHilbert initial) := by
  ext channel
  rw [compiledChannelwiseLCTransducerOperator_apply]
  change (quantizedChannelGain code.1.1 channel : ℂ) *
      encodePort (harmonicFlow
        (quantizedChannelFrequency code.1.1 channel * time) initial channel) = _
  rw [encodePort_harmonicFlow,
    schrodingerScalarPhase_one_scaled_forNetlist]
  unfold channelwiseTransducerCoefficient
  rw [finiteQuantizedChannelwise_frequency_exact]
  simp [finiteQuantizedChannelwiseDesign, lcBranchRealizingFrequency,
    encodeHilbert, encodeComplex]
  ring

def finiteParallelLCLinearOutputAt
    (run : FiniteParallelLCNetlistRunOccurrence)
    (initial : FiniteEmbodimentState) : HilbertEmbodimentState :=
  finiteParallelLCTransducerOutputAt run initial run.executedDuration +
    (run.directedCrosstalkAmplitude : ℂ) •
      rankOneCrosstalkOperator (encodeHilbert initial)

def finiteParallelLCBiasDirection : HilbertEmbodimentState :=
  encodeHilbert (evolve (intervention .sourceBound 1))

def finiteParallelLCEndpointOutputAt
    (run : FiniteParallelLCNetlistRunOccurrence)
    (initial : FiniteEmbodimentState) : HilbertEmbodimentState :=
  finiteParallelLCLinearOutputAt run initial +
    (run.endpointBiasAmplitude : ℂ) • finiteParallelLCBiasDirection

theorem compiledFiniteParallelLCLinearOutput_eq_implementation
    (code : FiniteQuantizedChannelLCRunCrosstalkCode)
    (initial : FiniteEmbodimentState) :
    finiteParallelLCLinearOutputAt (compileFiniteParallelLCNetlistRun code)
        initial =
      finiteQuantizedCrosstalkImplementation code (encodeHilbert initial) := by
  unfold finiteParallelLCLinearOutputAt
    finiteQuantizedCrosstalkImplementation
  simp only [add_apply, smul_apply]
  rw [compiledFiniteParallelLCTransducerOutput_eq_compiledOperator]
  rfl

theorem compiledFiniteParallelLCEndpointOutput_eq_disturbedImplementation
    (code : FiniteQuantizedChannelLCRunCrosstalkCode)
    (initial : FiniteEmbodimentState) :
    finiteParallelLCEndpointOutputAt (compileFiniteParallelLCNetlistRun code)
        initial =
      finiteQuantizedCrosstalkImplementation code (encodeHilbert initial) +
        smallNonzeroConstantBias initial := by
  rw [finiteParallelLCEndpointOutputAt,
    compiledFiniteParallelLCLinearOutput_eq_implementation]
  simp [compileFiniteParallelLCNetlistRun, finiteParallelLCBiasDirection,
    smallNonzeroConstantBias]

/-- Exact commuting with the endpoint state consumed by the existing
coupling law. -/
theorem compiledFiniteParallelLCEndpointOutput_commutes
    (code : FiniteQuantizedChannelLCRunCrosstalkCode)
    (initial : FiniteEmbodimentState) :
    finiteParallelLCEndpointOutputAt (compileFiniteParallelLCNetlistRun code)
        initial =
      encodeHilbert
        (disturbedImplementedState
          (finiteQuantizedCrosstalkImplementation code)
          smallNonzeroConstantBias initial) := by
  rw [encodeHilbert_disturbedImplementedState]
  exact compiledFiniteParallelLCEndpointOutput_eq_disturbedImplementation
    code initial

end

end Producer
end Netlist
end Physical
end Coupling
end Canonical
end Embodied
end Immortality
end Consciousness
end NoIslandNoMagic
end SaturationMonoid

#print axioms SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Physical.Netlist.Producer.compileFiniteParallelLCNetlistRun_injective
#print axioms SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Physical.Netlist.Producer.finiteParallelLC_kirchhoffCurrentLaw
#print axioms SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Physical.Netlist.Producer.compiledFiniteParallelLC_capacitorConstitutiveLaw
#print axioms SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Physical.Netlist.Producer.compiledFiniteParallelLC_inductorConstitutiveLaw
#print axioms SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Physical.Netlist.Producer.compiledFiniteParallelLC_reactiveEnergy_conserved
#print axioms SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Physical.Netlist.Producer.compiledFiniteParallelLCEndpointOutput_commutes
