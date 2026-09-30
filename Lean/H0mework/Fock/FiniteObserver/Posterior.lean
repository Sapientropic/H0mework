import H0mework.Fock.FiniteObserver.Row

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceFiniteObserverCalculation

variable {Key : Type*} [DecidableEq Key]

def posteriorCalculate (bound scale steps phase : Nat) (read : Nat → Key) (key : Key) : Fin (bound + steps + 1) → ℚ :=
  rowCalculate (bound + steps) scale bound phase (SourceConditionalNativeObservers.generate read bound key).2

open SourceGeneratedAcquisitionContinuation
open SourceCopyProgram (Index)
open SourceCopyTemporalBoundary (recordedPrefix)
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime
noncomputable section

theorem posterior_word (runtime : LivingRuntimeState process) (read : Nat → Key) (key : Key) :
    SourceJointClockGraph.read (SourceConditionalRationalStream.embedWord
      (SourceConditionalNativeKeys.word (inventoryBound runtime)
        (SourceConditionalNativeObservers.generate read (inventoryBound runtime) key).2)) =
      SourceConditionalNativePosterior.decoder runtime read key := by
  have actorSource (actor : SourceConditionalModel.Actors runtime) :
      SourceJointClockGraph.read (SourceConditionalRationalStream.embedWord
        (SourceConditionalRationalStream.sourceWord (inventoryBound runtime) actor)) =
        SourceConditionalVector.realizeModel runtime (SourceConditionalModel.nextRead runtime actor) := by
    rw [SourceConditionalRationalStream.source_embed, SourceConditionalVector.realized_next, SourceConditionalVector.actor_material]
    rfl
  simp only [SourceConditionalNativeKeys.word, LinearMap.coe_mk, AddHom.coe_mk, map_sum,
    SourceConditionalNativePosterior.decoder, SourceConditionalNativePosterior.model]
  apply Finset.sum_congr rfl
  intro actor _
  rw [map_smul]
  change SourceJointClockGraph.read
    (((SourceConditionalNativeObservers.generate read (inventoryBound runtime) key).2 actor : ℂ) • _) = _
  rw [map_smul, actorSource, map_smul]

def window (runtime : LivingRuntimeState process) (index : Index (inventoryBound runtime)) (steps length : Nat)
    (read : Nat → Key) (key : Key) (phase : Fin (length + 1)) : SourceJointClockGraph.Carrier :=
  finiteRead (inventoryBound runtime + steps)
    (fun actor => (posteriorCalculate (inventoryBound runtime) (index.val + 1) steps phase.val read key actor : ℂ))

theorem window_source (runtime : LivingRuntimeState process) (index : Index (inventoryBound runtime)) (steps length : Nat)
    (read : Nat → Key) (key : Key) :
    window runtime index steps length read key =
      recordedPrefix runtime index steps length (SourceConditionalNativePosterior.decoder runtime read key) := by
  funext phase
  simp only [window, posteriorCalculate, row_calculate_source]
  rw [observer_calculated, row_word_time, posterior_word, SourceCopyTemporalBoundary.prefix_source]

end
end SourceFiniteObserverCalculation
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
