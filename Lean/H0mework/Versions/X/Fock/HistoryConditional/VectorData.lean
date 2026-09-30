import H0mework.Versions.X.Fock.HistoryConditional.ModelMaterial

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceConditionalVector

open SourceConditionalModel (Actors NextModel nextRead)
open SourceGeneratedAcquisitionContinuation SourceGeneratedRuntimeHistoryProbability
open SourceCopyCurrentCoordinates (maximumIndex jointModelEquiv realize)
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime
noncomputable section
universe u

def estimate (runtime : LivingRuntimeState process) {Observed : Type u} (read : Actors runtime → Observed)
    (value : Observed) (supported : value ∈ ((historyPMF (inventoryBound runtime)).map read).support) : NextModel runtime :=
  ∑ index : Actors runtime,
    ((SourceConditionalHistory.conditional (historyPMF (inventoryBound runtime)) read value supported index).toReal : ℂ) •
      nextRead runtime index

def realizeModel (runtime : LivingRuntimeState process) : NextModel runtime →ₗ[ℂ] SourceJointClockGraph.Carrier :=
  (realize runtime.tick.next (maximumIndex runtime.tick.next) 0).comp (jointModelEquiv runtime.tick.next).toLinearMap

theorem estimate_realization (runtime : LivingRuntimeState process) {Observed : Type u} (read : Actors runtime → Observed)
    (value : Observed) (supported : value ∈ ((historyPMF (inventoryBound runtime)).map read).support) :
    realizeModel runtime (estimate runtime read value supported) =
      ∑ index : Actors runtime,
        ((SourceConditionalHistory.conditional (historyPMF (inventoryBound runtime)) read value supported index).toReal : ℂ) •
          realizeModel runtime (nextRead runtime index) := by
  simp only [estimate, map_sum, map_smul]

theorem full_clock_original (runtime : LivingRuntimeState process) (value : ℤ × ℤ)
    (supported : value ∈ ((historyPMF (inventoryBound runtime)).map (SourceConditionalModel.fullRead runtime)).support) :
    estimate runtime (SourceConditionalModel.fullRead runtime) value supported = SourceConditionalModel.modelEstimate runtime value supported := rfl

def dynamicEstimate (runtime : LivingRuntimeState process) (depth : Nat) (index : Actors runtime) : NextModel runtime :=
  estimate runtime (SourceConditionalModel.dynamicRead runtime depth) (SourceConditionalModel.dynamicRead runtime depth index)
    (SourceWeightedRecovery.observed_supported (historyPMF (inventoryBound runtime)) (SourceConditionalModel.dynamicRead runtime depth) index
      (SourceConditionalModel.positive runtime index))

end
end SourceConditionalVector
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
