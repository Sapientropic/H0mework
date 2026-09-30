import H0mework.Fock.HistoryConditional.InformationLossMass

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceConditionalInformationLoss

open SourceGeneratedAcquisitionContinuation SourceGeneratedRuntimeHistoryProbability
open SourceConditionalModel (Actors positive)
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime
noncomputable section
attribute [local instance] SourceConditionalNext.Image.valuesFintype SourceConditionalNext.Image.valuesMeasurable
  SourceConditionalNext.Image.valuesSingleton
variable {Fine Coarse : Type*} [DecidableEq Fine] [DecidableEq Coarse]
local notation "entropy" =>
  SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Population.entropy

theorem conditional_information (read : Nat → Fine) (forget : Fine → Coarse) (bound : Nat) (value : Coarse)
    (supported : value ∈ ((historyPMF bound).map (fun actor : Fin (bound + 1) => forget (read actor.val))).support) :
    entropy (SourceConditionalNext.conditionalNext (historyPMF bound) (fun actor : Fin (bound + 1) => forget (read actor.val))
      (SourceConditionalNext.Image.actual (fun actor : Fin (bound + 1) => read actor.val)) value supported) =
      ∑ actor : Fin (bound + 1), (SourceConditionalHistory.conditional (historyPMF bound)
        (fun index : Fin (bound + 1) => forget (read index.val)) value supported actor).toReal *
        Real.log ((SourceConditionalNativeMerge.count read forget bound (SourceConditionalNativeObservers.generate read bound) value : ℝ) /
          ((SourceConditionalNativeObservers.generate read bound (read actor.val)).1 : ℝ)) := by
  rw [conditional_entropy_readback, ← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro actor _
  by_cases seen : forget (read actor.val) = value
  · have fineNonzero : ((SourceConditionalNativeObservers.generate read bound (read actor.val)).1 : ℝ) ≠ 0 :=
      Nat.cast_ne_zero.mpr (SourceConditionalNativePosterior.count_positive read bound _ actor rfl).ne'
    have coarseNonzero : (SourceConditionalNativeMerge.count read forget bound (SourceConditionalNativeObservers.generate read bound) value : ℝ) ≠ 0 := by
      rw [SourceConditionalNativeMerge.count_generated]
      exact Nat.cast_ne_zero.mpr (SourceConditionalNativePosterior.count_positive (forget ∘ read) bound _ actor seen).ne'
    rw [fine_mass read forget bound value supported actor seen,
      Real.log_div fineNonzero coarseNonzero, Real.log_div coarseNonzero fineNonzero]
    ring
  · have absent : SourceConditionalHistory.conditional (historyPMF bound)
        (fun index : Fin (bound + 1) => forget (read index.val)) value supported actor = 0 := by
      rw [SourceConditionalHistory.conditional_apply, if_neg seen]
    rw [absent, ENNReal.toReal_zero, zero_mul, zero_mul, neg_zero]

theorem conditional_is_amount (runtime : LivingRuntimeState process) (read : Nat → Fine) (forget : Fine → Coarse) :
    SourceConditionalNext.conditionalEntropy (historyPMF (inventoryBound runtime))
      (fun actor : Actors runtime => forget (read actor.val))
      (SourceConditionalNext.Image.actual (fun actor : Actors runtime => read actor.val)) (positive runtime) =
      amount runtime read forget := by
  rw [SourceConditionalNext.conditionalEntropy]
  simp only [conditional_information]
  exact SourceVectorMoment.conditional_average (historyPMF (inventoryBound runtime))
    (fun actor : Actors runtime => forget (read actor.val)) (positive runtime)
    (fun actor value => Real.log
      ((SourceConditionalNativeMerge.count read forget (inventoryBound runtime)
        (SourceConditionalNativeObservers.generate read (inventoryBound runtime)) value : ℝ) /
        ((SourceConditionalNativeObservers.generate read (inventoryBound runtime) (read actor.val)).1 : ℝ)))

end
end SourceConditionalInformationLoss
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
