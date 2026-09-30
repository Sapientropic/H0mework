import H0mework.Versions.X.Fock.HistoryConditional.WindowPrecisionConsumer

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceWindowPrecision

open SourceCopyProgram (Index)
open SourceCopyCurrentCoordinates (maximumIndex)
open SourceOperatorObservationAcquisition (Window)
open SourceGeneratedAcquisitionContinuation SourceGeneratedRuntimeHistoryProbability
open SourceConditionalModel (Actors)
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime
noncomputable section

def StageLaw (runtime : LivingRuntimeState process) (material : SourceGeneratedRuntimeMaterialStageAt runtime) : Prop :=
  type_of% material.factorizes ∧
  (∀ index : Index (inventoryBound runtime), ∀ nonunit : index.val ≠ 0, ∀ steps : Nat,
    type_of% (reader_original runtime index nonunit steps) ∧ type_of% (readout_continuous runtime index nonunit steps) ∧
    type_of% (mass_original runtime index nonunit steps) ∧ type_of% (clock_original runtime index nonunit steps) ∧
    (∀ coordinate, type_of% (hilbert_original runtime index nonunit steps coordinate)) ∧
    (∀ coefficients : Coefficients runtime index steps,
      type_of% (energy_source runtime index steps coefficients) ∧
        ∀ samples : Window runtime index, type_of% (evaluate_bound runtime index steps coefficients samples)) ∧
    ∀ error : Window runtime index, type_of% (readout_bound runtime index nonunit steps error) ∧
      type_of% (action_readout_bound runtime index nonunit steps error) ∧
      ∀ target : SourceJointClockGraph.Carrier, type_of% (error_bound runtime index nonunit steps target error)) ∧
  ∀ nonunit : (maximumIndex runtime).val ≠ 0, ∀ key : ZMod 2,
    (∀ error : Window runtime (maximumIndex runtime),
      type_of% (effect_bound runtime nonunit (fun index : Nat => (index : ZMod 2)) key error)) ∧
    ∀ supported : key ∈ ((historyPMF (inventoryBound runtime)).map (fun actor : Actors runtime => (actor.val : ZMod 2))).support,
      ∀ error : Window runtime (maximumIndex runtime),
        type_of% (conditional_bound runtime nonunit (fun index : Nat => (index : ZMod 2)) key supported error) ∧
        type_of% (conditional_next_bound runtime nonunit (fun index : Nat => (index : ZMod 2)) key supported error)

theorem stage_law (runtime : LivingRuntimeState process) (material : SourceGeneratedRuntimeMaterialStageAt runtime) :
    StageLaw runtime material := by
  dsimp only [StageLaw]
  with_reducible exact ⟨material.factorizes,
    fun index nonunit steps => ⟨reader_original runtime index nonunit steps, readout_continuous runtime index nonunit steps,
      mass_original runtime index nonunit steps, clock_original runtime index nonunit steps,
      fun coordinate => hilbert_original runtime index nonunit steps coordinate,
      fun coefficients => ⟨energy_source runtime index steps coefficients,
        fun samples => evaluate_bound runtime index steps coefficients samples⟩,
      fun error => ⟨readout_bound runtime index nonunit steps error, action_readout_bound runtime index nonunit steps error,
        fun target => error_bound runtime index nonunit steps target error⟩⟩,
    fun nonunit key => ⟨fun error => effect_bound runtime nonunit (fun index : Nat => (index : ZMod 2)) key error,
      fun supported error => ⟨conditional_bound runtime nonunit (fun index : Nat => (index : ZMod 2)) key supported error,
        conditional_next_bound runtime nonunit (fun index : Nat => (index : ZMod 2)) key supported error⟩⟩⟩

end
end SourceWindowPrecision
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
