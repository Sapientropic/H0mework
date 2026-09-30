import H0mework.Physics.PortCoupling.State

/-!
# Finite continuous-time harmonic port dynamics

The ten finite embodiment port pairs evolve under one explicit one-parameter
real-linear flow.  In each pair the source port is the momentum coordinate
and the target port is the position coordinate.  Thus the flow satisfies
Hamilton's equations for `(source² + target²) / 2`, preserves exact energy,
and is reversible at every real time.

At one positive quarter-period the flow agrees with the existing reversible
port update on the source-prepared subspace.  This restriction is explicit:
the global swap has determinant `-1` on each pair and is not silently claimed
to be a Hamiltonian flow on arbitrary states.
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
namespace Interface

open _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.CausalCore

noncomputable section

/-- Ten uncoupled harmonic oscillators, with each pair ordered as
`(momentum, position)`. -/
def harmonicFlow (time : ℝ) (state : FiniteEmbodimentState) :
    FiniteEmbodimentState :=
  fun channel =>
    let momentum := sourcePort state channel
    let position := targetPort state channel
    (Real.cos time * momentum - Real.sin time * position,
      Real.sin time * momentum + Real.cos time * position)

@[simp] theorem harmonicFlow_zero (state : FiniteEmbodimentState) :
    harmonicFlow 0 state = state := by
  funext channel
  rcases hstate : state channel with ⟨momentum, position⟩
  simp [harmonicFlow, sourcePort, targetPort, hstate]

theorem harmonicFlow_add (time step : ℝ)
    (state : FiniteEmbodimentState) :
    harmonicFlow (time + step) state =
      harmonicFlow time (harmonicFlow step state) := by
  funext channel
  rcases state channel with ⟨momentum, position⟩
  apply Prod.ext
  · simp [harmonicFlow, sourcePort, targetPort, Real.cos_add, Real.sin_add]
    ring
  · simp [harmonicFlow, sourcePort, targetPort, Real.cos_add, Real.sin_add]
    ring

theorem harmonicFlow_neg_leftInverse (time : ℝ) :
    Function.LeftInverse (harmonicFlow (-time)) (harmonicFlow time) := by
  intro state
  rw [← harmonicFlow_add]
  simp

/-- Every time slice of the harmonic dynamics is a real-linear equivalence. -/
def harmonicFlowLinearEquiv (time : ℝ) :
    FiniteEmbodimentState ≃ₗ[ℝ] FiniteEmbodimentState where
  toFun := harmonicFlow time
  invFun := harmonicFlow (-time)
  left_inv := harmonicFlow_neg_leftInverse time
  right_inv := by
    intro state
    rw [← harmonicFlow_add]
    simp
  map_add' := by
    intro left right
    funext channel
    simp [harmonicFlow, sourcePort, targetPort]
    constructor <;> ring
  map_smul' := by
    intro scalar state
    funext channel
    simp [harmonicFlow, sourcePort, targetPort]
    constructor <;> ring

theorem harmonicFlowLinearEquiv_apply (time : ℝ)
    (state : FiniteEmbodimentState) :
    harmonicFlowLinearEquiv time state = harmonicFlow time state :=
  rfl

/-- World-owned graph for every real duration of the continuous trajectory. -/
structure HarmonicLawfulEvolutionAt
    (current : FiniteEmbodimentState) (time : ℝ)
    (candidate : FiniteEmbodimentState) : Type where
  evolution_eq : candidate = harmonicFlow time current

/-- A scheduled current carries both the physical state and the duration that
its source emitter will select. -/
abbrev HarmonicScheduledCurrent := FiniteEmbodimentState × ℝ

/-- The elapsed time is the exact occurrence.  Every requested duration can
be the emitted occurrence of the scheduled current `(state, duration)`. -/
def harmonicPhysicalWorld : World where
  Current := HarmonicScheduledCurrent
  OccurrenceAt := fun _current => ℝ
  EvolutionAt := fun _current => FiniteEmbodimentState
  emitted := fun current => current.2
  LawfulEvolutionAt := fun {current} time candidate =>
    HarmonicLawfulEvolutionAt current.1 time candidate

def harmonicNoSuspendedCausalMagic :
    NoSuspendedCausalMagic harmonicPhysicalWorld where
  realize := fun {current} time => harmonicFlow time current.1
  lawful := fun _time => ⟨rfl⟩
  lawful_unique := by
    intro _current _time candidate lawful
    exact lawful.evolution_eq

def harmonicProcess : Process harmonicPhysicalWorld :=
  harmonicNoSuspendedCausalMagic.toProcess

def harmonicEvolutionAt (state : FiniteEmbodimentState) (time : ℝ) :
    FiniteEmbodimentState :=
  harmonicNoSuspendedCausalMagic.realize (current := (state, time)) time

def harmonicEvolution_lawful
    (state : FiniteEmbodimentState) (time : ℝ) :
    harmonicPhysicalWorld.LawfulEvolutionAt
      (current := (state, time)) time (harmonicEvolutionAt state time) :=
  harmonicNoSuspendedCausalMagic.lawful time

@[simp] theorem harmonicEvolutionAt_eq
    (state : FiniteEmbodimentState) (time : ℝ) :
    harmonicEvolutionAt state time = harmonicFlow time state :=
  rfl

theorem harmonicProcess_generate
    (state : FiniteEmbodimentState) (time : ℝ) :
    harmonicProcess.generate (state, time) = harmonicFlow time state :=
  rfl

theorem harmonicFlow_channelEnergy_conserved
    (time : ℝ) (state : FiniteEmbodimentState)
    (channel : FiniteEmbodimentChannel) :
    channelEnergy (harmonicFlow time state) channel =
      channelEnergy state channel := by
  rcases state channel with ⟨momentum, position⟩
  simp [channelEnergy, harmonicFlow, sourcePort, targetPort]
  nlinarith [Real.sin_sq_add_cos_sq time]

theorem harmonicFlow_energy_conserved
    (time : ℝ) (state : FiniteEmbodimentState) :
    energy (harmonicFlow time state) = energy state := by
  unfold energy
  apply Finset.sum_congr rfl
  intro channel _membership
  exact harmonicFlow_channelEnergy_conserved time state channel

/-- The source/momentum coordinate obeys `p' = -q`. -/
theorem harmonicFlow_source_hasDerivAt
    (state : FiniteEmbodimentState) (channel : FiniteEmbodimentChannel)
    (time : ℝ) :
    HasDerivAt
      (fun t => sourcePort (harmonicFlow t state) channel)
      (-targetPort (harmonicFlow time state) channel) time := by
  rcases hstate : state channel with ⟨momentum, position⟩
  simp only [sourcePort, harmonicFlow, targetPort, hstate]
  have derivative :=
    (Real.hasDerivAt_cos time).mul_const momentum |>.sub
      ((Real.hasDerivAt_sin time).mul_const position)
  convert derivative using 1
  all_goals try rfl
  all_goals ring

/-- The target/position coordinate obeys `q' = p`. -/
theorem harmonicFlow_target_hasDerivAt
    (state : FiniteEmbodimentState) (channel : FiniteEmbodimentChannel)
    (time : ℝ) :
    HasDerivAt
      (fun t => targetPort (harmonicFlow t state) channel)
      (sourcePort (harmonicFlow time state) channel) time := by
  rcases hstate : state channel with ⟨momentum, position⟩
  simp only [sourcePort, harmonicFlow, targetPort, hstate]
  have derivative :=
    (Real.hasDerivAt_sin time).mul_const momentum |>.add
      ((Real.hasDerivAt_cos time).mul_const position)
  convert derivative using 1
  all_goals try rfl
  all_goals ring

def harmonicHamiltonian (ports : ℝ × ℝ) : ℝ :=
  (ports.1 ^ 2 + ports.2 ^ 2) / 2

theorem harmonicHamiltonian_hasDerivAt_source
    (momentum position : ℝ) :
    HasDerivAt
      (fun source => harmonicHamiltonian (source, position))
      momentum momentum := by
  simpa [harmonicHamiltonian] using
    (((hasDerivAt_id' momentum).pow 2).add_const (position ^ 2)).div_const 2

theorem harmonicHamiltonian_hasDerivAt_target
    (momentum position : ℝ) :
    HasDerivAt
      (fun target => harmonicHamiltonian (momentum, target))
      position position := by
  simpa [harmonicHamiltonian] using
    (((hasDerivAt_id' position).pow 2).const_add (momentum ^ 2)).div_const 2

/-- The two port equations are Hamilton's equations when the pair is ordered
as `(momentum, position)`. -/
theorem harmonicFlow_satisfiesPortHamiltonEquations
    (state : FiniteEmbodimentState) (channel : FiniteEmbodimentChannel)
    (time : ℝ) :
    HasDerivAt
        (fun t => sourcePort (harmonicFlow t state) channel)
        (-targetPort (harmonicFlow time state) channel) time ∧
      HasDerivAt
        (fun t => targetPort (harmonicFlow t state) channel)
        (sourcePort (harmonicFlow time state) channel) time :=
  ⟨harmonicFlow_source_hasDerivAt state channel time,
    harmonicFlow_target_hasDerivAt state channel time⟩

/-- The actual signal preparations occupy the subspace whose target ports
are initially zero. -/
def SourcePreparedState (state : FiniteEmbodimentState) : Prop :=
  ∀ channel, targetPort state channel = 0

theorem preparedState_sourcePrepared (occurrence : Bool) :
    SourcePreparedState (preparedState occurrence) := by
  intro channel
  cases occurrence <;> simp [preparedState, targetPort]

theorem intervention_sourcePrepared
    (channel : FiniteEmbodimentChannel) (value : ℝ) :
    SourcePreparedState (intervention channel value) := by
  intro candidate
  by_cases same : candidate = channel <;>
    simp [intervention, targetPort, same]

/-- A positive quarter-period realizes the reversible port endpoint on every
source-prepared state, not merely on the distinguished Boolean occurrence. -/
theorem harmonicFlow_pi_div_two_eq_evolve_of_sourcePrepared
    (state : FiniteEmbodimentState) (prepared : SourcePreparedState state) :
    harmonicFlow (Real.pi / 2) state = evolve state := by
  funext channel
  rcases hstate : state channel with ⟨momentum, position⟩
  have position_zero : position = 0 := by
    simpa [targetPort, hstate] using prepared channel
  simp [harmonicFlow, evolve, sourcePort, targetPort, hstate,
    position_zero, Real.cos_pi_div_two, Real.sin_pi_div_two]

theorem harmonicFlow_pi_div_two_eq_evolve_on_prepared
    (occurrence : Bool) :
    harmonicFlow (Real.pi / 2) (preparedState occurrence) =
      evolutionAtOccurrence occurrence := by
  simpa [evolutionAtOccurrence, physicalNoSuspendedCausalMagic] using
    harmonicFlow_pi_div_two_eq_evolve_of_sourcePrepared
      (preparedState occurrence) (preparedState_sourcePrepared occurrence)

theorem harmonicFlow_pi_div_two_eq_evolve_on_intervention
    (channel : FiniteEmbodimentChannel) (value : ℝ) :
    harmonicFlow (Real.pi / 2) (intervention channel value) =
      evolve (intervention channel value) :=
  harmonicFlow_pi_div_two_eq_evolve_of_sourcePrepared
    (intervention channel value) (intervention_sourcePrepared channel value)

theorem harmonicIntervention_hits_correspondingTarget
    (channel : FiniteEmbodimentChannel) (value : ℝ) :
    targetPort
        (harmonicFlow (Real.pi / 2) (intervention channel value)) channel =
      value := by
  rw [harmonicFlow_pi_div_two_eq_evolve_on_intervention]
  exact intervention_hits_corresponding_target channel value

theorem harmonicIntervention_leavesOtherTargetZero
    {sourceChannel targetChannel : FiniteEmbodimentChannel}
    (different : targetChannel ≠ sourceChannel) (value : ℝ) :
    targetPort
        (harmonicFlow (Real.pi / 2) (intervention sourceChannel value))
        targetChannel = 0 := by
  rw [harmonicFlow_pi_div_two_eq_evolve_on_intervention]
  exact intervention_leaves_other_target_zero different value

theorem harmonicIntervention_sensitive
    (channel : FiniteEmbodimentChannel) {left right : ℝ}
    (different : left ≠ right) :
    targetPort
        (harmonicFlow (Real.pi / 2) (intervention channel left)) channel ≠
      targetPort
        (harmonicFlow (Real.pi / 2) (intervention channel right)) channel := by
  simpa only [harmonicIntervention_hits_correspondingTarget] using different

theorem harmonicFourDirectionalInterventionSensitive :
    (∀ {left right : ℝ}, left ≠ right →
      targetPort
          (harmonicFlow (Real.pi / 2)
            (intervention .machineToNeuralWrite left))
          .machineToNeuralWrite ≠
        targetPort
          (harmonicFlow (Real.pi / 2)
            (intervention .machineToNeuralWrite right))
          .machineToNeuralWrite) ∧
    (∀ {left right : ℝ}, left ≠ right →
      targetPort
          (harmonicFlow (Real.pi / 2)
            (intervention .neuralToMachineReceipt left))
          .neuralToMachineReceipt ≠
        targetPort
          (harmonicFlow (Real.pi / 2)
            (intervention .neuralToMachineReceipt right))
          .neuralToMachineReceipt) ∧
    (∀ {left right : ℝ}, left ≠ right →
      targetPort
          (harmonicFlow (Real.pi / 2)
            (intervention .neuralToBodyEffect left))
          .neuralToBodyEffect ≠
        targetPort
          (harmonicFlow (Real.pi / 2)
            (intervention .neuralToBodyEffect right))
          .neuralToBodyEffect) ∧
    (∀ {left right : ℝ}, left ≠ right →
      targetPort
          (harmonicFlow (Real.pi / 2)
            (intervention .bodyToNeuralFeedback left))
          .bodyToNeuralFeedback ≠
        targetPort
          (harmonicFlow (Real.pi / 2)
            (intervention .bodyToNeuralFeedback right))
          .bodyToNeuralFeedback) :=
  ⟨harmonicIntervention_sensitive _, harmonicIntervention_sensitive _,
    harmonicIntervention_sensitive _, harmonicIntervention_sensitive _⟩

end

end Interface
end Physical
end Coupling
end Canonical
end Embodied
end Immortality
end Consciousness
end NoIslandNoMagic
end SaturationMonoid

#print axioms SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Physical.Interface.harmonicFlow_add
#print axioms SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Physical.Interface.harmonicNoSuspendedCausalMagic
#print axioms SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Physical.Interface.harmonicFlow_energy_conserved
#print axioms SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Physical.Interface.harmonicFlow_satisfiesPortHamiltonEquations
#print axioms SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Physical.Interface.harmonicFlow_pi_div_two_eq_evolve_of_sourcePrepared
#print axioms SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Physical.Interface.harmonicFourDirectionalInterventionSensitive
