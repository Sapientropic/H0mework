import H0mework.Versions.X.Fock.SourceHistoryClock.GraphGeometry

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceGeneratedJointClockGraph

open SourceGeneratedAcquisitionMeasure SourceGeneratedAcquisitionContinuation SourceGeneratedAcquisitionJoint
open SourceGeneratedJointTime SourceJointClockGraph Filter
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime
noncomputable section

def fieldRead (depth bound : Nat) : FieldSpace depth bound →ₗ[ℂ] SourceJointClockGraph.Carrier :=
  SourceJointClockGraph.read.comp (word depth bound)

def nextFieldRead (depth bound : Nat) : NextSpace depth bound →ₗ[ℂ] SourceJointClockGraph.Carrier :=
  SourceJointClockGraph.read.comp (nextWord depth bound)

theorem original_time_square (depth bound : Nat) (value : FieldSpace depth bound) :
    nextFieldRead depth bound (timeTransfer depth bound value) =
      SourceJointClockGraph.action (fieldRead depth bound value) := by
  change SourceJointClockGraph.read (nextWord depth bound (timeTransfer depth bound value)) = _
  rw [next_word_transfer]
  exact (SourceJointClockGraph.action_source _).symm

theorem original_time_recovery (depth bound : Nat) (value : NextSpace depth bound) :
    fieldRead depth bound (timePullback depth bound value) =
      SourceJointClockGraph.recover (nextFieldRead depth bound value) := by
  have actual := original_time_square depth bound (timePullback depth bound value)
  rw [show timeTransfer depth bound (timePullback depth bound value) = value from
    IsometricRetainedTransfer.transfer_pullback (timePullback depth bound) value] at actual
  rw [actual, SourceJointClockGraph.recover_action]

theorem next_residual_zero (depth bound : Nat) (value : NextSpace depth bound) :
    SourceJointClockGraph.residual (nextFieldRead depth bound value) = 0 := by
  change nextFieldRead depth bound value -
    SourceJointClockGraph.action (SourceJointClockGraph.recover (nextFieldRead depth bound value)) = 0
  rw [← original_time_recovery, ← original_time_square]
  rw [show timeTransfer depth bound (timePullback depth bound value) = value from
    IsometricRetainedTransfer.transfer_pullback (timePullback depth bound) value, sub_self]

theorem original_field_norm (depth bound : Nat) (value : FieldSpace depth bound) :
    ‖fieldRead depth bound value‖ ^ 2 = ‖value‖ ^ 2 +
      (bound + 1 : ℝ) * ‖∫ index, SourceGeneratedActionWords.Fock.OriginalHilbert.Actor.currentPullback depth bound value index
        ∂(SourceGeneratedRuntimeHistoryProbability.historyPMF bound).toMeasure‖ ^ 2 +
      ‖SourceClockComplex.clock (word depth bound value)‖ ^ 2 := by
  change ‖SourceJointClockGraph.read (word depth bound value)‖ ^ 2 = _
  rw [SourceJointClockGraph.norm_sq, SourceJointClockGraph.joint_source, SourceJointClockGraph.clock_source]
  change ‖SourceGeneratedAcquisitionJoint.joint depth bound value‖ ^ 2 +
    ‖SourceClockComplex.clock (word depth bound value)‖ ^ 2 = _
  rw [joint_norm_sq]


theorem realization_graph (round : Nat) (sourceWord : Nat →₀ ℂ) :
    fieldRead (depth (sourceRound round sourceWord)) (inventoryBound (sourceRound round sourceWord))
      (realizeWord round sourceWord) = SourceJointClockGraph.read sourceWord :=
  congrArg SourceJointClockGraph.read (realization_word round sourceWord)

theorem whole_graph_closure (round : Nat) :
    (⨆ future : Nat, LinearMap.range (fieldRead (depth (roundRuntime (round + future)))
      (inventoryBound (roundRuntime (round + future))))).topologicalClosure = ⊤ := by
  have sourceIncluded : SourceJointClockGraph.read.range ≤
      ⨆ future : Nat, LinearMap.range (fieldRead (depth (roundRuntime (round + future)))
        (inventoryBound (roundRuntime (round + future)))) := by
    rintro _ ⟨sourceWord, rfl⟩
    exact (le_iSup (fun future : Nat => LinearMap.range (fieldRead (depth (roundRuntime (round + future)))
      (inventoryBound (roundRuntime (round + future))))) (demand round sourceWord))
        ⟨realizeWord round sourceWord, realization_graph round sourceWord⟩
  apply top_unique
  rw [← SourceJointClockGraph.range_read_closure_eq_top]
  exact Submodule.topologicalClosure_mono sourceIncluded

theorem native_realization_graph (round : Nat) (sourceWord : Nat →₀ ℤ) :
    fieldRead (depth (sourceRound round (SourceClockComplex.ofNative sourceWord)))
      (inventoryBound (sourceRound round (SourceClockComplex.ofNative sourceWord)))
      (realizeWord round (SourceClockComplex.ofNative sourceWord)) =
        WithLp.toLp 2 (SourceMassCompletion.nativeRead sourceWord,
          (SourceClockModel.clockRead (SourceClockModel.projection sourceWord) : ℂ)) := by
  rw [realization_graph, SourceJointClockGraph.native_read]

end
end SourceGeneratedJointClockGraph
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
