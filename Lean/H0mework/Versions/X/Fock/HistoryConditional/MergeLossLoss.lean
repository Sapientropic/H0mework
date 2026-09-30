import H0mework.Versions.X.Fock.HistoryConditional.MergeLossSource

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceConditionalMergeLoss

open SourceGeneratedAcquisitionContinuation SourceGeneratedRuntimeHistoryProbability
open SourceConditionalModel (Actors nextRead positive)
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime
noncomputable section
variable {Fine Coarse : Type*} [DecidableEq Fine] [DecidableEq Coarse]

theorem loss (runtime : LivingRuntimeState process) (read : Nat → Fine) (forget : Fine → Coarse) :
    (∑ actor : Actors runtime, (historyPMF (inventoryBound runtime) actor).toReal *
      ‖SourceConditionalVector.realizeModel runtime (nextRead runtime actor) - decoder runtime read forget (forget (read actor.val))‖ ^ 2) =
    (∑ actor : Actors runtime, (historyPMF (inventoryBound runtime) actor).toReal *
      ‖SourceConditionalVector.realizeModel runtime (nextRead runtime actor) -
        SourceConditionalNativePosterior.decoder runtime read (read actor.val)‖ ^ 2) +
    (∑ actor : Actors runtime, (historyPMF (inventoryBound runtime) actor).toReal *
      ‖SourceConditionalNativePosterior.decoder runtime read (read actor.val) - decoder runtime read forget (forget (read actor.val))‖ ^ 2) := by
  let source := historyPMF (inventoryBound runtime)
  let query : Actors runtime → Fine := fun actor => read actor.val
  let values : Actors runtime → SourceJointClockGraph.Carrier :=
    fun actor => SourceConditionalVector.realizeModel runtime (nextRead runtime actor)
  have means (actor : Actors runtime) :
      SourceVectorMoment.mean (SourceConditionalHistory.conditional source query (query actor)
        (SourceWeightedRecovery.observed_supported source query actor (positive runtime actor))) values =
          SourceConditionalNativePosterior.decoder runtime read (query actor) :=
    (SourceConditionalNativePosterior.decoder_mean runtime read (read actor.val)
      (SourceWeightedRecovery.observed_supported source query actor (positive runtime actor))).symm
  have fine := SourceVectorMoment.conditional_error source query (positive runtime) values
    (SourceConditionalNativePosterior.decoder runtime read)
  simp only [means, sub_self, norm_zero, zero_pow (by decide : 2 ≠ 0), mul_zero, Finset.sum_const_zero, add_zero] at fine
  have coarse := SourceVectorMoment.conditional_error source query (positive runtime) values
    (decoder runtime read forget ∘ forget)
  rw [← fine] at coarse
  simp only [means, Function.comp_apply] at coarse
  dsimp only [source, query, values] at coarse
  with_reducible exact coarse

end
end SourceConditionalMergeLoss
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
