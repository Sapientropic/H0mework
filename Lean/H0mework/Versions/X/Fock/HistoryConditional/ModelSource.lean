import H0mework.Probability.Source.ConditionalNextImage
import H0mework.Versions.X.Fock.HistoryConditional.Source
import H0mework.Versions.X.Fock.CopyGraph.SharedNextSourceStepSource
import H0mework.Versions.X.Fock.CopyGraph.CurrentCoordinatesJoint
import H0mework.Versions.X.Fock.SourceHistoryClock.PosteriorTasks

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceConditionalModel

open SourceGeneratedAcquisitionContinuation SourceGeneratedRuntimeHistoryProbability
open SourceGeneratedActionObservationHistory (Model projection)
open SourceCopyCurrentCoordinates (jointObserver jointModelEquiv)
open SourceCopyNativeModelStep (sourceValue)
open SourceObservationInvariantControls (parity)
open SourceConditionalNext (conditionalNext)
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime
noncomputable section
attribute [local instance] SourceConditionalNext.Image.valuesFintype SourceConditionalNext.Image.valuesMeasurable
  SourceConditionalNext.Image.valuesSingleton

abbrev Actors (runtime : LivingRuntimeState process) := Fin (inventoryBound runtime + 1)
abbrev NextModel (runtime : LivingRuntimeState process) :=
  Model SourceJointClockGraph.action.toLinearMap (jointObserver runtime.tick.next)

def read (runtime : LivingRuntimeState process) : Actors runtime → ZMod 2 :=
  SourceConditionalHistory.Runtime.observation runtimeSeed (inventoryBound runtime) parity

def nextRead (runtime : LivingRuntimeState process) (index : Actors runtime) : NextModel runtime :=
  projection SourceJointClockGraph.action.toLinearMap (jointObserver runtime.tick.next)
    (sourceValue ((history runtimeSeed (inventoryBound runtime)).stageAt index).next)

theorem positive (runtime : LivingRuntimeState process) (index : Actors runtime) :
    index ∈ (historyPMF (inventoryBound runtime)).support := by
  simp only [historyPMF, PMF.mem_support_uniformOfFintype]

theorem read_source (runtime : LivingRuntimeState process) (index : Actors runtime) : read runtime index = (index.val : ZMod 2) := by
  change parity (runtimeAt index.val).state = _
  rw [runtimeAt_state]
  rfl

theorem next_action (runtime : LivingRuntimeState process) (index : Actors runtime) :
    nextRead runtime index = projection SourceJointClockGraph.action.toLinearMap (jointObserver runtime.tick.next)
      (SourceJointClockGraph.action (sourceValue (runtimeSeed.advance index.val))) := by
  rw [SourceCopyNativeModelStep.source_value_next]
  rfl

def clockRead (runtime : LivingRuntimeState process) (value : NextModel runtime) : ℂ :=
  (jointModelEquiv runtime.tick.next value).2.2

theorem clock_original (runtime : LivingRuntimeState process) (index : Actors runtime) :
    clockRead runtime (nextRead runtime index) =
      (SourceClockModel.clockRead (SourceWeightedRecovery.Runtime.Actor.History.Clock.futureModel (inventoryBound runtime) 0 index) : ℂ) := by
  rw [clockRead, nextRead, SourceCopyCurrentCoordinates.joint_model_source]
  change SourceJointClockGraph.clock (sourceValue ((history runtimeSeed (inventoryBound runtime)).stageAt index).next) =
    (SourceClockModel.clockRead (SourceClockModel.projection
      (SourceOperationNative.point ((history runtimeSeed (inventoryBound runtime)).stageAt index).next)) : ℂ)
  rw [sourceValue, SourceJointClockGraph.clock_source, SourceClockComplex.clock_native, SourceClockModel.clockRead_source]

theorem clock_source (runtime : LivingRuntimeState process) (index : Actors runtime) :
    clockRead runtime (nextRead runtime index) = (index.val : ℂ) + 2 := by
  rw [clock_original, SourceWeightedRecovery.Runtime.Actor.History.Clock.futureModel_source,
    SourceClockModel.Fock.clock_current, runtimeAt_scanIndex]
  push_cast
  ring

def information (runtime : LivingRuntimeState process) : ℝ :=
  SourceConditionalNext.conditionalEntropy (historyPMF (inventoryBound runtime)) (read runtime)
    (SourceConditionalNext.Image.actual (nextRead runtime)) (positive runtime)

theorem information_zero_iff (runtime : LivingRuntimeState process) : information runtime = 0 ↔
    ∀ left right : Actors runtime, read runtime left = read runtime right → nextRead runtime left = nextRead runtime right :=
  SourceConditionalNext.Image.entropy_zero_iff _ _ _ _

theorem conditional_original (runtime : LivingRuntimeState process) (value : ZMod 2)
    (supported : value ∈ ((historyPMF (inventoryBound runtime)).map (read runtime)).support) :
    (conditionalNext (historyPMF (inventoryBound runtime)) (read runtime) (SourceConditionalNext.Image.actual (nextRead runtime)) value supported).map Subtype.val =
      conditionalNext (historyPMF (inventoryBound runtime)) (read runtime) (nextRead runtime) value supported :=
  SourceConditionalNext.Image.conditional_original _ _ _ _ _

theorem mean_original (runtime : LivingRuntimeState process) (decode : NextModel runtime → ℂ) (value : ZMod 2)
    (supported : value ∈ ((historyPMF (inventoryBound runtime)).map (read runtime)).support) :
    SourceConditionalNext.mean (historyPMF (inventoryBound runtime)) (read runtime) (SourceConditionalNext.Image.actual (nextRead runtime))
      (fun item => decode item.val) value supported =
      SourceWeightedRecovery.conditionalMean (historyPMF (inventoryBound runtime)) (read runtime) (decode ∘ nextRead runtime) value supported :=
  SourceConditionalNext.Image.mean_original _ _ _ _ _ _

theorem error_variance (runtime : LivingRuntimeState process) (decode : NextModel runtime → ℂ) (decoder : ZMod 2 → ℂ) :
    type_of% (SourceConditionalNext.Image.error_variance_original (historyPMF (inventoryBound runtime)) (read runtime)
      (nextRead runtime) decode (positive runtime) decoder) :=
  SourceConditionalNext.Image.error_variance_original _ _ _ _ (positive runtime) decoder

end
end SourceConditionalModel
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
