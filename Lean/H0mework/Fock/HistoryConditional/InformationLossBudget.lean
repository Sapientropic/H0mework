import H0mework.Fock.HistoryConditional.InformationLossRatio

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceConditionalInformationLoss

open SourceGeneratedAcquisitionContinuation SourceGeneratedRuntimeHistoryProbability
open SourceConditionalModel (Actors nextRead positive)
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime
noncomputable section
attribute [local instance] SourceConditionalNext.Image.valuesFintype SourceConditionalNext.Image.valuesMeasurable
  SourceConditionalNext.Image.valuesSingleton
variable {Fine Coarse : Type*} [DecidableEq Fine] [DecidableEq Coarse]

def amount (runtime : LivingRuntimeState process) (read : Nat → Fine) (forget : Fine → Coarse) : ℝ :=
  ∑ actor : Actors runtime, (historyPMF (inventoryBound runtime) actor).toReal *
    Real.log ((SourceConditionalNativeMerge.count read forget (inventoryBound runtime)
      (SourceConditionalNativeObservers.generate read (inventoryBound runtime)) (forget (read actor.val)) : ℝ) /
        ((SourceConditionalNativeObservers.generate read (inventoryBound runtime) (read actor.val)).1 : ℝ))

theorem information_balance (runtime : LivingRuntimeState process) (read : Nat → Fine) (forget : Fine → Coarse) :
    SourceConditionalNext.conditionalEntropy (historyPMF (inventoryBound runtime)) (fun actor : Actors runtime => read actor.val)
      (SourceConditionalNext.Image.actual (nextRead runtime)) (positive runtime) + amount runtime read forget =
    SourceConditionalNext.conditionalEntropy (historyPMF (inventoryBound runtime)) (fun actor : Actors runtime => forget (read actor.val))
      (SourceConditionalNext.Image.actual (nextRead runtime)) (positive runtime) := by
  rw [amount, ← native_ratio]
  ring

theorem recovery_budget [MeasurableSpace Coarse] [MeasurableSingletonClass Coarse]
    (runtime : LivingRuntimeState process) (read : Nat → Fine) (forget : Fine → Coarse) :
    SourceConditionalInventory.cost (inventoryBound runtime) (fun actor : Actors runtime => forget (read actor.val)) /
      (inventoryBound runtime + 1 : ℝ) +
    (Real.exp (2 * (SourceConditionalNext.conditionalEntropy (historyPMF (inventoryBound runtime))
      (fun actor : Actors runtime => read actor.val) (SourceConditionalNext.Image.actual (nextRead runtime)) (positive runtime) +
        amount runtime read forget)) - 1) / 12 ≤
      (∑ actor : Actors runtime, (historyPMF (inventoryBound runtime) actor).toReal *
        ‖SourceConditionalVector.realizeModel runtime (nextRead runtime actor) -
          SourceConditionalNativePosterior.decoder runtime read (read actor.val)‖ ^ 2) +
        SourceConditionalMergeLoss.gap runtime read forget := by
  have generated := SourceGInformationCost.decoder_information_lower (inventoryBound runtime)
    (fun actor : Actors runtime => forget (read actor.val)) (SourceConditionalMergeLoss.decoder runtime read forget)
  rw [← SourceInformationReadback.model_information runtime (fun actor : Actors runtime => forget (read actor.val)),
    ← information_balance runtime read forget] at generated
  simp only [SourceConditionalInventory.values_original] at generated
  rw [SourceConditionalMergeLoss.loss] at generated
  exact generated

end
end SourceConditionalInformationLoss
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
