import H0mework.Versions.X.Fock.HistoryModel.CoarseCode.OptimalRiskBirth
import H0mework.Versions.X.Fock.HistoryConditional.InformationLossRecovery
import H0mework.Versions.X.Fock.HistoryConditional.GWordInverseSource
import H0mework.Versions.X.Fock.HistoryModel.CoarseCode.BirthRecovery

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceWordFieldCode

open SourceGeneratedActionWords.Fock
open SourceGeneratedAcquisitionContinuation SourceGeneratedRuntimeHistoryProbability
open SourceConditionalModel (Actors positive)
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime
noncomputable section

/-- The physical G value is fixed by the executed source word; the query is separate. -/
def gTask (runtime : LivingRuntimeState process)
    (taskWord : List (Letter (inventoryBound runtime + 1))) :
    Actors runtime → SourceJointClockGraph.Carrier :=
  SourceCompiledGWord.image runtime (inventoryBound runtime + 1) taskWord

def gFineMean {Fine : Type*} [DecidableEq Fine]
    (runtime : LivingRuntimeState process)
    (taskWord : List (Letter (inventoryBound runtime + 1)))
    (read : Nat → Fine) (key : Fine) : SourceJointClockGraph.Carrier :=
  SourceCompiledGWord.effect (inventoryBound runtime + 1) taskWord
    (SourceConditionalNativePosterior.decoder runtime read key)

def gCoarseMean {Fine Coarse : Type*} [DecidableEq Fine] [DecidableEq Coarse]
    (runtime : LivingRuntimeState process)
    (taskWord : List (Letter (inventoryBound runtime + 1)))
    (read : Nat → Fine) (forget : Fine → Coarse) (key : Coarse) :
    SourceJointClockGraph.Carrier :=
  SourceCompiledGWord.effect (inventoryBound runtime + 1) taskWord
    (SourceConditionalMergeLoss.decoder runtime read forget key)

def gRisk {Key : Type*} (runtime : LivingRuntimeState process)
    (taskWord : List (Letter (inventoryBound runtime + 1)))
    (read : Nat → Key) (decoder : Key → SourceJointClockGraph.Carrier) : ℝ :=
  ∑ actor : Actors runtime, (historyPMF (inventoryBound runtime) actor).toReal *
    ‖gTask runtime taskWord actor - decoder (read actor.val)‖ ^ 2

def gGap {Fine Coarse : Type*} [DecidableEq Fine] [DecidableEq Coarse]
    (runtime : LivingRuntimeState process)
    (taskWord : List (Letter (inventoryBound runtime + 1)))
    (read : Nat → Fine) (forget : Fine → Coarse) : ℝ :=
  ∑ actor : Actors runtime, (historyPMF (inventoryBound runtime) actor).toReal *
    ‖gFineMean runtime taskWord read (read actor.val) -
      gCoarseMean runtime taskWord read forget (forget (read actor.val))‖ ^ 2

/-- A fixed G action pays exactly the extra conditional mean mismatch when its
    source observation is merged. Both risks use the original history weights. -/
theorem gRisk_refinement {Fine Coarse : Type*} [DecidableEq Fine] [DecidableEq Coarse]
    (runtime : LivingRuntimeState process)
    (taskWord : List (Letter (inventoryBound runtime + 1)))
    (read : Nat → Fine) (forget : Fine → Coarse) :
    gRisk runtime taskWord (forget ∘ read)
      (gCoarseMean runtime taskWord read forget) =
    gRisk runtime taskWord read (gFineMean runtime taskWord read) +
      gGap runtime taskWord read forget := by
  let source := historyPMF (inventoryBound runtime)
  let query : Actors runtime → Fine := fun actor => read actor.val
  let value := gTask runtime taskWord
  have means (actor : Actors runtime) :
      SourceVectorMoment.mean
        (SourceConditionalHistory.conditional source query (query actor)
          (SourceWeightedRecovery.observed_supported source query actor (positive runtime actor))) value =
        gFineMean runtime taskWord read (query actor) := by
    exact SourceCompiledGWord.conditional_decoder runtime (inventoryBound runtime + 1)
      taskWord read (read actor.val)
      (SourceWeightedRecovery.observed_supported source query actor (positive runtime actor))
  have fine := SourceVectorMoment.conditional_error source query (positive runtime)
    value (gFineMean runtime taskWord read)
  simp only [means, sub_self, norm_zero, zero_pow (by decide : 2 ≠ 0),
    mul_zero, Finset.sum_const_zero, add_zero] at fine
  have coarse := SourceVectorMoment.conditional_error source query (positive runtime)
    value (gCoarseMean runtime taskWord read forget ∘ forget)
  rw [← fine] at coarse
  simp only [means, Function.comp_apply] at coarse
  dsimp only [source, query, value, gRisk, gGap] at coarse
  exact coarse

theorem gRisk_optimal_account {Key : Type*} [DecidableEq Key]
    [MeasurableSpace Key] [MeasurableSingletonClass Key]
    (runtime : LivingRuntimeState process)
    (taskWord : List (Letter (inventoryBound runtime + 1)))
    (read : Nat → Key) :
    gRisk runtime taskWord read (gFineMean runtime taskWord read) =
      SourceConditionalInventory.cost (inventoryBound runtime)
        (fun actor : Actors runtime => read actor.val) / (inventoryBound runtime + 1 : ℝ) +
      ((SourceCopyWordAffine.compile
        (taskWord.map SourceCopyNativeWord.encode)).1 : ℝ) ^ 2 *
      ‖SourceWeightedRecovery.residual (historyPMF (inventoryBound runtime))
        (fun actor : Actors runtime => read actor.val)
        (SourceWeightedRecovery.taskValue (historyPMF (inventoryBound runtime))
          (SourceJointClockGraph.clock ∘ SourceConditionalInventory.values
            (inventoryBound runtime)))‖ ^ 2 := by
  have account := SourceCompiledGWord.error_account runtime
    (inventoryBound runtime + 1) taskWord
    (fun actor : Actors runtime => read actor.val)
    (gFineMean runtime taskWord read)
  have means (actor : Actors runtime) :
      SourceCompiledGWord.effect (inventoryBound runtime + 1) taskWord
        (SourceVectorMoment.mean
          (SourceConditionalHistory.conditional (historyPMF (inventoryBound runtime))
            (fun actor : Actors runtime => read actor.val) (read actor.val)
            (SourceWeightedRecovery.observed_supported _ _ actor
              (SourceUniformFibreVariance.source_positive _ actor)))
          (SourceConditionalInventory.values (inventoryBound runtime))) =
        gFineMean runtime taskWord read (read actor.val) := by
    rw [← SourceCompiledGWord.mean_effect]
    simpa only [SourceCompiledGWord.image_original, Function.comp_apply, gFineMean] using
      SourceCompiledGWord.conditional_decoder runtime (inventoryBound runtime + 1)
        taskWord read (read actor.val)
        (SourceWeightedRecovery.observed_supported _ _ actor
          (SourceUniformFibreVariance.source_positive _ actor))
  simp_rw [means] at account
  simp only [sub_self, norm_zero, zero_pow (by decide : 2 ≠ 0), mul_zero,
    Finset.sum_const_zero, add_zero] at account
  exact account

theorem gGap_zero_iff_source_gap {Fine Coarse : Type*}
    [DecidableEq Fine] [DecidableEq Coarse]
    (runtime : LivingRuntimeState process)
    (taskWord : List (Letter (inventoryBound runtime + 1)))
    (read : Nat → Fine) (forget : Fine → Coarse) :
    gGap runtime taskWord read forget = 0 ↔
      SourceConditionalMergeLoss.gap runtime read forget = 0 := by
  rw [gGap, Finset.sum_eq_zero_iff_of_nonneg
    (fun _ _ => mul_nonneg ENNReal.toReal_nonneg (sq_nonneg _)),
    SourceConditionalMergeLoss.gap_zero_iff]
  constructor
  · intro all actor
    have term := all actor (Finset.mem_univ actor)
    have weight : (historyPMF (inventoryBound runtime) actor).toReal ≠ 0 := by
      rw [SourceUniformFibreVariance.source_weight]
      positivity
    have equal := sub_eq_zero.mp (norm_eq_zero.mp
      (sq_eq_zero_iff.mp ((mul_eq_zero.mp term).resolve_left weight)))
    have lifted := congrArg (SourceGWordInverse.recover
      (inventoryBound runtime + 1) taskWord) equal
    simpa only [gFineMean, gCoarseMean, SourceGWordInverse.recover_effect] using lifted
  · intro all actor _
    have equal := congrArg (SourceCompiledGWord.effect
      (inventoryBound runtime + 1) taskWord) (all actor)
    rw [show gFineMean runtime taskWord read (read actor.val) =
      gCoarseMean runtime taskWord read forget (forget (read actor.val)) from equal]
    simp

theorem gGap_zero_iff_information_zero {Fine Coarse : Type*}
    [DecidableEq Fine] [DecidableEq Coarse]
    (runtime : LivingRuntimeState process)
    (taskWord : List (Letter (inventoryBound runtime + 1)))
    (read : Nat → Fine) (forget : Fine → Coarse) :
    gGap runtime taskWord read forget = 0 ↔
      SourceConditionalInformationLoss.amount runtime read forget = 0 := by
  rw [gGap_zero_iff_source_gap, SourceConditionalInformationLoss.amount_zero_iff_gap]

theorem gGap_nonnegative {Fine Coarse : Type*}
    [DecidableEq Fine] [DecidableEq Coarse]
    (runtime : LivingRuntimeState process)
    (taskWord : List (Letter (inventoryBound runtime + 1)))
    (read : Nat → Fine) (forget : Fine → Coarse) :
    0 ≤ gGap runtime taskWord read forget :=
  Finset.sum_nonneg fun _ _ => mul_nonneg ENNReal.toReal_nonneg (sq_nonneg _)

theorem actual_transported_copy_g_gap_positive :
    0 < gGap (runtimeAt 4)
      (SourceWordFutureBitGrowth.nextWordAt 3 [SourceWordDynamicNext.copyOne])
      (SourceWordObservedCode.readAt (inventoryBound (runtimeAt 4))
        (SourceWordFutureBitGrowth.nextWordAt 3 []))
      (SourceWordFutureBit.bitWord (inventoryBound (runtimeAt 4) + 1)
        (SourceWordFutureBitGrowth.nextWordAt 3 [SourceWordDynamicNext.copyOne])) := by
  let taskWord := SourceWordFutureBitGrowth.nextWordAt 3 [SourceWordDynamicNext.copyOne]
  let read := SourceWordObservedCode.readAt (inventoryBound (runtimeAt 4))
    (SourceWordFutureBitGrowth.nextWordAt 3 [])
  let forget := SourceWordFutureBit.bitWord (inventoryBound (runtimeAt 4) + 1) taskWord
  have positive := actual_birth_copy_information_amount_positive
  have nozero : gGap (runtimeAt 4) taskWord read forget ≠ 0 := by
    intro zero
    exact (ne_of_gt positive) ((gGap_zero_iff_information_zero
      (runtimeAt 4) taskWord read forget).mp zero)
  exact lt_of_le_of_ne (gGap_nonnegative (runtimeAt 4) taskWord read forget)
    (Ne.symm nozero)


end
end SourceWordFieldCode
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
