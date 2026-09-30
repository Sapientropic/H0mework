import H0mework.Versions.X.Fock.HistoryConditional.ActualImageMinimal

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceActualImageStep

open SourceConditionalModel (Actors nextRead)
open SourceGeneratedAcquisitionContinuation SourceGeneratedRuntimeHistoryProbability
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime
noncomputable section
universe u

theorem step_pmf (runtime : LivingRuntimeState process) (source : PMF (Actors runtime)) :
    (source.map (SourceConditionalNext.Image.actual (nextRead runtime))).map (step runtime) =
      (source.map (advanceIndex runtime)).map (SourceConditionalNext.Image.actual (nextRead runtime.tick.next)) := by
  rw [PMF.map_comp, PMF.map_comp]
  apply congrArg (fun readout => source.map readout)
  funext index
  exact step_actual runtime index

theorem retain_pmf (runtime : LivingRuntimeState process) (source : PMF (Actors runtime)) :
    (source.map (SourceConditionalNext.Image.actual (nextRead runtime))).map (retain runtime) =
      (source.map (keepIndex runtime)).map (SourceConditionalNext.Image.actual (nextRead runtime.tick.next)) := by
  rw [PMF.map_comp, PMF.map_comp]
  apply congrArg (fun readout => source.map readout)
  funext index
  exact retain_actual runtime index

theorem conditional_step (runtime : LivingRuntimeState process) {Observed : Type u} (observation : Actors runtime → Observed)
    (value : Observed) (supported : value ∈ ((historyPMF (inventoryBound runtime)).map observation).support) :
    (SourceConditionalNext.conditionalNext (historyPMF (inventoryBound runtime)) observation
      (SourceConditionalNext.Image.actual (nextRead runtime)) value supported).map (step runtime) =
      ((SourceConditionalHistory.conditional (historyPMF (inventoryBound runtime)) observation value supported).map (advanceIndex runtime)).map
        (SourceConditionalNext.Image.actual (nextRead runtime.tick.next)) :=
  step_pmf runtime _

theorem conditional_retain (runtime : LivingRuntimeState process) {Observed : Type u} (observation : Actors runtime → Observed)
    (value : Observed) (supported : value ∈ ((historyPMF (inventoryBound runtime)).map observation).support) :
    (SourceConditionalNext.conditionalNext (historyPMF (inventoryBound runtime)) observation
      (SourceConditionalNext.Image.actual (nextRead runtime)) value supported).map (retain runtime) =
      ((SourceConditionalHistory.conditional (historyPMF (inventoryBound runtime)) observation value supported).map (keepIndex runtime)).map
        (SourceConditionalNext.Image.actual (nextRead runtime.tick.next)) :=
  retain_pmf runtime _

end
end SourceActualImageStep
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
