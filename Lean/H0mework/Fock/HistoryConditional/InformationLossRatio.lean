import H0mework.Fock.HistoryConditional.InformationLossSource

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

theorem native_ratio (runtime : LivingRuntimeState process) (read : Nat → Fine) (forget : Fine → Coarse) :
    SourceConditionalNext.conditionalEntropy (historyPMF (inventoryBound runtime)) (fun actor : Actors runtime => forget (read actor.val))
      (SourceConditionalNext.Image.actual (nextRead runtime)) (positive runtime) -
    SourceConditionalNext.conditionalEntropy (historyPMF (inventoryBound runtime)) (fun actor : Actors runtime => read actor.val)
      (SourceConditionalNext.Image.actual (nextRead runtime)) (positive runtime) =
      ∑ actor : Actors runtime, (historyPMF (inventoryBound runtime) actor).toReal *
        Real.log ((SourceConditionalNativeMerge.count read forget (inventoryBound runtime)
          (SourceConditionalNativeObservers.generate read (inventoryBound runtime)) (forget (read actor.val)) : ℝ) /
            ((SourceConditionalNativeObservers.generate read (inventoryBound runtime) (read actor.val)).1 : ℝ)) := by
  have coarse := information_count runtime (forget ∘ read)
  simp only [Function.comp_apply] at coarse
  rw [coarse, information_count runtime read, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro actor _
  have finePositive := SourceConditionalNativePosterior.count_positive read (inventoryBound runtime) (read actor.val) actor rfl
  have coarsePositive := SourceConditionalNativePosterior.count_positive (forget ∘ read) (inventoryBound runtime) (forget (read actor.val)) actor rfl
  have fineNonzero : ((SourceConditionalNativeObservers.generate read (inventoryBound runtime) (read actor.val)).1 : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr finePositive.ne'
  have coarseNonzero : ((SourceConditionalNativeObservers.generate (forget ∘ read) (inventoryBound runtime) (forget (read actor.val))).1 : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr coarsePositive.ne'
  rw [SourceConditionalNativeMerge.count_generated, Real.log_div coarseNonzero fineNonzero]
  ring

end
end SourceConditionalInformationLoss
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
