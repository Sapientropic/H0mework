import H0mework.Physics.MotherLaws.RestrictionEmbeddingCarrier
import H0mework.Versions.R2.Physics.MotherLaws.RestrictionExtension
import H0mework.Versions.R2.Physics.MotherLaws.RestrictionInterpreter
import H0mework.Versions.R2.Realization.SourceComparison.History
import Mathlib.Topology.MetricSpace.Gluing

set_option autoImplicit false

namespace SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherProcessLaws

open MotherStreamLaws MotherClosedRestrictions Topology
open ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
open RawGeneratedRoot.SourceComparison

noncomputable section

universe u

abbrev TotalEvent (D : RawGeneratedRoot.Dynamics.{u}) := Sigma D.EventAt
abbrev Input (D : RawGeneratedRoot.Dynamics.{u}) := D.State ⊕ TotalEvent D

variable (D : RawGeneratedRoot.Dynamics.{u})
variable [MetricSpace D.State] [TopologicalSpace.SeparableSpace D.State] [CompleteSpace D.State]
variable [MetricSpace (TotalEvent D)] [TopologicalSpace.SeparableSpace (TotalEvent D)] [CompleteSpace (TotalEvent D)]

/-- This metric retains the existing sum topology and complete uniformity. -/
local instance processInputMetric : MetricSpace (Input D) := Metric.metricSpaceSum

def inputEmbedding : Input D → Stream := MotherClosedEmbedding.embed (Input D)

theorem inputEmbedding_closed : IsClosedEmbedding (inputEmbedding D) :=
  MotherClosedEmbedding.embed_isClosedEmbedding (Input D)

/-- The original process enters the fixed mother executor by one law. Every
legal event is retained, including events outside the emitter's image. -/
theorem regular_process_map
    (emit_continuous : Continuous (fun state : D.State => (⟨state, D.emit state⟩ : TotalEvent D)))
    (update_continuous : Continuous (fun event : TotalEvent D => D.update event.2)) :
    ∃ law : Law, ∃ initial : MotherStreamFormation.Carrier,
    ∃ map : Map D (MotherLawInterpreter.dynamics law initial),
      (∀ state : D.State, map.state state = inputEmbedding D (Sum.inl state)) ∧
      (∀ actual : TotalEvent D, map.event (current := actual.1) actual.2 = inputEmbedding D (Sum.inr actual)) ∧
      Function.Injective map.state ∧
      Function.Injective (fun actual : TotalEvent D => map.event (current := actual.1) actual.2) ∧
      (∀ actual : TotalEvent D,
        (MotherClosedEmbedding.ontoRange (Input D)).symm
          ⟨inputEmbedding D (Sum.inr actual), ⟨Sum.inr actual, rfl⟩⟩ = Sum.inr actual) ∧
      (∀ index : ℕ, map.state (RawGeneratedRoot.currentAt D index) =
        RawGeneratedRoot.currentAt (MotherLawInterpreter.dynamics law initial) index) ∧
      (∀ index : ℕ, map.history (historyAt D index) =
        historyAt (MotherLawInterpreter.dynamics law initial) index) ∧
      (∀ (state : D.State) (event : D.EventAt state),
        map.state (RawGeneratedRoot.generatedSuccessor D (state := state) event).targetCurrent =
          (RawGeneratedRoot.generatedSuccessor (MotherLawInterpreter.dynamics law initial)
            (state := map.state state) (map.event (current := state) event)).targetCurrent) ∧
      (∀ past : History D,
        (RawGeneratedRoot.generatedSuccessor D (state := (visit past).current) (D.emit (visit past).current)).ledgerEvolution.destination
            (RawGeneratedRoot.entry D (visit past).current) =
          ⟨RawGeneratedRoot.entry D (D.update (D.emit (visit past).current)),
            .transferred (D.emit (visit past).current) rfl rfl (Nat.le_refl _)⟩ ∧
        (RawGeneratedRoot.generatedSuccessor (MotherLawInterpreter.dynamics law initial)
          (state := (visit (map.history past)).current)
          ((MotherLawInterpreter.dynamics law initial).emit (visit (map.history past)).current)).ledgerEvolution.destination
            (RawGeneratedRoot.entry (MotherLawInterpreter.dynamics law initial) (visit (map.history past)).current) =
          ⟨RawGeneratedRoot.entry (MotherLawInterpreter.dynamics law initial)
              ((MotherLawInterpreter.dynamics law initial).update
                ((MotherLawInterpreter.dynamics law initial).emit (visit (map.history past)).current)),
            .transferred ((MotherLawInterpreter.dynamics law initial).emit (visit (map.history past)).current)
              rfl rfl (Nat.le_refl _)⟩ ∧
        map.state (RawGeneratedRoot.generatedSuccessor D (state := (visit past).current) (D.emit (visit past).current)).targetCurrent =
          (RawGeneratedRoot.generatedSuccessor (MotherLawInterpreter.dynamics law initial)
            (state := (visit (map.history past)).current)
            ((MotherLawInterpreter.dynamics law initial).emit (visit (map.history past)).current)).targetCurrent) := by
  let onState : D.State → Stream := fun state => inputEmbedding D (Sum.inr ⟨state, D.emit state⟩)
  let onEvent : TotalEvent D → Stream := fun event => inputEmbedding D (Sum.inl (D.update event.2))
  have stateContinuous : Continuous onState :=
    (inputEmbedding_closed D).continuous.comp (continuous_inr.comp emit_continuous)
  have eventContinuous : Continuous onEvent :=
    (inputEmbedding_closed D).continuous.comp (continuous_inl.comp update_continuous)
  let actualStep : C(Input D, Stream) := ⟨Sum.elim onState onEvent, stateContinuous.sumElim eventContinuous⟩
  obtain ⟨law, generated⟩ := exists_law_on_closed_embedding (inputEmbedding D) (inputEmbedding_closed D) actualStep
  obtain ⟨initial, initial_read⟩ := MotherStreamFormation.read_surjective (inputEmbedding D (Sum.inl D.initial))
  let map : Map D (MotherLawInterpreter.dynamics law initial) := {
    state := fun state => inputEmbedding D (Sum.inl state)
    event := fun {state} event => inputEmbedding D (Sum.inr (⟨state, event⟩ : TotalEvent D))
    initial := initial_read.symm
    emitted := fun state => (generated (Sum.inl state)).symm
    updated := fun {state} event => (generated (Sum.inr (⟨state, event⟩ : TotalEvent D))).symm }
  have states_injective : Function.Injective map.state :=
    (inputEmbedding_closed D).injective.comp Sum.inl_injective
  have events_injective : Function.Injective (fun actual : TotalEvent D => map.event (current := actual.1) actual.2) :=
    (inputEmbedding_closed D).injective.comp Sum.inr_injective
  refine ⟨law, initial, map, fun _ => rfl, fun _ => rfl, states_injective, events_injective,
    fun actual => MotherClosedEmbedding.recover_embed (Input D) (Sum.inr actual),
    map.generated, map.history_at, ?_, map.whole_row⟩
  intro state event
  exact map.updated (current := state) event

end
end SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherProcessLaws
