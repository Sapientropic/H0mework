import H0mework.Realization.Relations.FintypeDerivation
import H0mework.Foundation.Semantics.CausalRealization
import Mathlib

/-!
# Finite reversible physical port coupling

This proof-free carrier has ten disjoint source/target port pairs. One real
linear involution swaps every pair, preserves the exact sum-of-squares energy,
and exposes intervention sensitivity at each target port. Consciousness,
body certification, coupling verdicts and continuation proofs occur nowhere
in this physical layer.
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

inductive FiniteEmbodimentChannel where
  | sourceBound
  | machineToNeuralWrite
  | neuralToMachineReceipt
  | neuralToBodyEffect
  | bodyToNeuralFeedback
  | learnedStateTrace
  | recursiveSelfWriteBack
  | generatedNext
  | authorityAndRefusalSettlement
  | noPowerMinting
  deriving DecidableEq, Repr, FintypeViaProxy

abbrev FiniteEmbodimentState := FiniteEmbodimentChannel → ℝ × ℝ

def sourcePort (state : FiniteEmbodimentState)
    (channel : FiniteEmbodimentChannel) : ℝ :=
  (state channel).1

def targetPort (state : FiniteEmbodimentState)
    (channel : FiniteEmbodimentChannel) : ℝ :=
  (state channel).2

/-- One physical evolution swaps source and target at every port pair. -/
def evolve (state : FiniteEmbodimentState) : FiniteEmbodimentState :=
  fun channel => (state channel).swap

theorem evolve_involutive : Function.Involutive evolve := by
  intro state
  funext channel
  simp [evolve]

/-- The common ten-port update is one real-linear equivalence. -/
def evolveLinearEquiv :
    FiniteEmbodimentState ≃ₗ[ℝ] FiniteEmbodimentState where
  toFun := evolve
  invFun := evolve
  left_inv := evolve_involutive
  right_inv := evolve_involutive
  map_add' := by
    intro left right
    funext channel
    simp [evolve]
  map_smul' := by
    intro scalar state
    funext channel
    simp [evolve]

def channelEnergy (state : FiniteEmbodimentState)
    (channel : FiniteEmbodimentChannel) : ℝ :=
  sourcePort state channel ^ 2 + targetPort state channel ^ 2

def energy (state : FiniteEmbodimentState) : ℝ :=
  Finset.univ.sum (channelEnergy state)

theorem evolve_channelEnergy_conserved
    (state : FiniteEmbodimentState) (channel : FiniteEmbodimentChannel) :
    channelEnergy (evolve state) channel = channelEnergy state channel := by
  rcases state channel with ⟨source, target⟩
  simp [channelEnergy, sourcePort, targetPort, evolve, add_comm]

theorem evolve_energy_conserved (state : FiniteEmbodimentState) :
    energy (evolve state) = energy state := by
  unfold energy
  apply Finset.sum_congr rfl
  intro channel _membership
  exact evolve_channelEnergy_conserved state channel

/-- An occurrence prepares every source port at its Boolean amplitude and all
target ports at zero. -/
def preparedState (occurrence : Bool) : FiniteEmbodimentState :=
  fun _channel => if occurrence then (1, 0) else (0, 0)

structure FiniteEmbodimentLawfulEvolutionAt
    (occurrence : Bool) (candidate : FiniteEmbodimentState) : Type where
  evolution_eq : candidate = evolve (preparedState occurrence)

/-- The same Boolean is both the emitted physical occurrence and the coupling
occurrence. `Bool.not` selects it from the current. -/
def physicalWorld : World where
  Current := Bool
  OccurrenceAt := fun _current => Bool
  EvolutionAt := fun _current => FiniteEmbodimentState
  emitted := Bool.not
  LawfulEvolutionAt := fun {_current} occurrence candidate =>
    FiniteEmbodimentLawfulEvolutionAt occurrence candidate

def physicalNoSuspendedCausalMagic :
    NoSuspendedCausalMagic physicalWorld where
  realize := fun occurrence => evolve (preparedState occurrence)
  lawful := fun _occurrence => ⟨rfl⟩
  lawful_unique := by
    intro _current _occurrence candidate lawful
    exact lawful.evolution_eq

def physicalProcess : Process physicalWorld :=
  physicalNoSuspendedCausalMagic.toProcess

def evolutionAtOccurrence (occurrence : Bool) : FiniteEmbodimentState :=
  physicalNoSuspendedCausalMagic.realize
    (current := Bool.not occurrence) occurrence

theorem occurrence_emitted (occurrence : Bool) :
    physicalWorld.emitted (Bool.not occurrence) = occurrence := by
  cases occurrence <;> rfl

def evolution_lawful (occurrence : Bool) :
    physicalWorld.LawfulEvolutionAt
      (current := Bool.not occurrence) occurrence
      (evolutionAtOccurrence occurrence) :=
  physicalNoSuspendedCausalMagic.lawful occurrence

/-- Change exactly one source port. -/
def intervention (channel : FiniteEmbodimentChannel) (value : ℝ) :
    FiniteEmbodimentState :=
  fun candidate => if candidate = channel then (value, 0) else (0, 0)

theorem intervention_hits_corresponding_target
    (channel : FiniteEmbodimentChannel) (value : ℝ) :
    targetPort (evolve (intervention channel value)) channel = value := by
  simp [targetPort, evolve, intervention]

theorem intervention_leaves_other_target_zero
    {sourceChannel targetChannel : FiniteEmbodimentChannel}
    (different : targetChannel ≠ sourceChannel) (value : ℝ) :
    targetPort (evolve (intervention sourceChannel value)) targetChannel =
      0 := by
  simp [targetPort, evolve, intervention, different]

/-- Varying only this source port changes its corresponding target after the
same physical evolution. -/
theorem intervention_sensitive
    (channel : FiniteEmbodimentChannel) {left right : ℝ}
    (different : left ≠ right) :
    targetPort (evolve (intervention channel left)) channel ≠
      targetPort (evolve (intervention channel right)) channel := by
  simpa [intervention_hits_corresponding_target] using different

theorem fourDirectionalInterventionSensitive :
    (∀ {left right : ℝ}, left ≠ right →
      targetPort (evolve (intervention .machineToNeuralWrite left))
          .machineToNeuralWrite ≠
        targetPort (evolve (intervention .machineToNeuralWrite right))
          .machineToNeuralWrite) ∧
    (∀ {left right : ℝ}, left ≠ right →
      targetPort (evolve (intervention .neuralToMachineReceipt left))
          .neuralToMachineReceipt ≠
        targetPort (evolve (intervention .neuralToMachineReceipt right))
          .neuralToMachineReceipt) ∧
    (∀ {left right : ℝ}, left ≠ right →
      targetPort (evolve (intervention .neuralToBodyEffect left))
          .neuralToBodyEffect ≠
        targetPort (evolve (intervention .neuralToBodyEffect right))
          .neuralToBodyEffect) ∧
    (∀ {left right : ℝ}, left ≠ right →
      targetPort (evolve (intervention .bodyToNeuralFeedback left))
          .bodyToNeuralFeedback ≠
        targetPort (evolve (intervention .bodyToNeuralFeedback right))
          .bodyToNeuralFeedback) :=
  ⟨intervention_sensitive _, intervention_sensitive _,
    intervention_sensitive _, intervention_sensitive _⟩

theorem channel_cardinality : Fintype.card FiniteEmbodimentChannel = 10 := by
  decide

end Interface
end Physical
end Coupling
end Canonical
end Embodied
end Immortality
end Consciousness
end NoIslandNoMagic
end SaturationMonoid

#print axioms SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Physical.Interface.evolve_energy_conserved
#print axioms SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Physical.Interface.intervention_sensitive
#print axioms SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Physical.Interface.fourDirectionalInterventionSensitive
