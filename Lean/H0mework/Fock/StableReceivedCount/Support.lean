import H0mework.Fock.StableReceivedCount.Source

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceStableReceivedCount

open SourceGeneratedAcquisitionContinuation
open SourceCopyCurrentCoordinates (maximumIndex)
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime
noncomputable section

theorem support_source (runtime : LivingRuntimeState process) (nonunit : (maximumIndex runtime).val ≠ 0)
    (samples : SourceRationalWindowReadout.Samples (inventoryBound runtime) ((maximumIndex runtime).val + 1)) :
    support (inventoryBound runtime) (maximumIndex runtime).val nonunit samples =
      SourcePosteriorStability.restoredSupport runtime
        (SourceWindowPosterior.model runtime nonunit (SourceRationalWindowReadout.embed runtime (maximumIndex runtime) 0 samples)) := by
  classical
  ext actor
  simp only [support, SourcePosteriorStability.restoredSupport, Finset.mem_filter, Finset.mem_univ, true_and,
    read_weight_source, lt_max_iff, not_lt.mpr (SourcePosteriorStability.threshold_positive runtime).le, or_false]
  rw [← threshold_source]
  exact (Rat.cast_lt (K := ℝ)).symm

theorem count_source (runtime : LivingRuntimeState process) (nonunit : (maximumIndex runtime).val ≠ 0)
    (samples : SourceRationalWindowReadout.Samples (inventoryBound runtime) ((maximumIndex runtime).val + 1)) :
    count (inventoryBound runtime) (maximumIndex runtime).val nonunit samples =
      (SourcePosteriorStability.restoredSupport runtime
        (SourceWindowPosterior.model runtime nonunit (SourceRationalWindowReadout.embed runtime (maximumIndex runtime) 0 samples))).card := by
  rw [count, support_source]

end
end SourceStableReceivedCount
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
