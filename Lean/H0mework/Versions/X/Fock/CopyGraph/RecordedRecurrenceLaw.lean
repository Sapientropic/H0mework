import H0mework.Versions.X.Fock.CopyGraph.RecordedRecurrenceKernel

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceCopyRecordedRecurrence

open SourceCopyProgram (Index)
open SourceCopyTimeModel (time)
open SourceCopyTemporalBoundary (observer recordedPrefix)
open SourceGeneratedAcquisitionContinuation SourceGeneratedActionObservationHistory
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime
open scoped Classical
noncomputable section

def windowBound (runtime : LivingRuntimeState process) (index : Index (inventoryBound runtime)) (steps : Nat) : Nat :=
  cutoff runtime index steps + 2

def priorIndex (runtime : LivingRuntimeState process) (index : Index (inventoryBound runtime)) (steps : Nat) :
    Fin (windowBound runtime index steps + 1) := ⟨cutoff runtime index steps + 1, by unfold windowBound; omega⟩

def coefficients (runtime : LivingRuntimeState process) (index : Index (inventoryBound runtime)) (steps : Nat) :
    Fin (windowBound runtime index steps + 1) → ℂ :=
  Pi.single (Fin.last (windowBound runtime index steps)) 2 - Pi.single (priorIndex runtime index steps) 1

theorem weighted_sum (runtime : LivingRuntimeState process) (index : Index (inventoryBound runtime)) (steps : Nat)
    (values : Fin (windowBound runtime index steps + 1) → SourceJointClockGraph.Carrier) :
    (∑ phase, coefficients runtime index steps phase • values phase) =
      (2 : ℂ) • values (Fin.last (windowBound runtime index steps)) - values (priorIndex runtime index steps) := by
  simp only [coefficients, Pi.sub_apply, sub_smul, Finset.sum_sub_distrib, Pi.single_apply,
    ite_smul, zero_smul, Finset.sum_ite_eq', Finset.mem_univ, if_true, one_smul]

private theorem rearrange (a b c : SourceJointClockGraph.Carrier) (law : a - b + c = 0) : a = b - c := by
  apply eq_sub_iff_add_eq.mpr
  apply sub_eq_zero.mp
  calc
    a + c - b = a - b + c := by abel
    _ = 0 := law

theorem observed_recurrence (runtime : LivingRuntimeState process) (index : Index (inventoryBound runtime))
    (steps : Nat) (target : SourceJointClockGraph.Carrier) :
    observer runtime index steps (time (windowBound runtime index steps + 1) target) =
      (2 : ℂ) • observer runtime index steps (time (windowBound runtime index steps) target) -
        observer runtime index steps (time (cutoff runtime index steps + 1) target) := by
  have source := observer_difference_zero runtime index steps target
  rw [difference, map_add, map_sub, map_smul] at source
  exact rearrange _ _ _ source

theorem source_law (runtime : LivingRuntimeState process) (index : Index (inventoryBound runtime)) (steps : Nat) :
    (observer runtime index steps).comp (SourceJointClockGraph.action.toLinearMap ^ (windowBound runtime index steps + 1)) =
      ∑ phase : Fin (windowBound runtime index steps + 1), coefficients runtime index steps phase •
        stageEvaluator SourceJointClockGraph.action.toLinearMap (observer runtime index steps) phase.val := by
  apply LinearMap.ext
  intro target
  simp only [LinearMap.comp_apply, LinearMap.sum_apply, LinearMap.smul_apply, stageEvaluator,
    ← ContinuousLinearMap.toLinearMap_pow]
  change observer runtime index steps (time (windowBound runtime index steps + 1) target) =
    ∑ phase : Fin (windowBound runtime index steps + 1), coefficients runtime index steps phase • observer runtime index steps (time phase.val target)
  rw [weighted_sum]
  exact observed_recurrence runtime index steps target

theorem advance_source (runtime : LivingRuntimeState process) (index : Index (inventoryBound runtime)) (steps : Nat) :
    (FiniteRecurrence.advance (windowBound runtime index steps) (coefficients runtime index steps)).comp
      (recordedPrefix runtime index steps (windowBound runtime index steps)) =
    (recordedPrefix runtime index steps (windowBound runtime index steps)).comp SourceJointClockGraph.action.toLinearMap :=
  FiniteRecurrence.advance_source SourceJointClockGraph.action.toLinearMap (observer runtime index steps)
    (windowBound runtime index steps) (coefficients runtime index steps) (source_law runtime index steps)

theorem full_future_fibre (runtime : LivingRuntimeState process) (index : Index (inventoryBound runtime)) (steps : Nat)
    (left right : SourceJointClockGraph.Carrier) :
    recordedPrefix runtime index steps (windowBound runtime index steps) left =
        recordedPrefix runtime index steps (windowBound runtime index steps) right ↔
      projection SourceJointClockGraph.action.toLinearMap (observer runtime index steps) left =
        projection SourceJointClockGraph.action.toLinearMap (observer runtime index steps) right :=
  FiniteRecurrence.prefix_fibre_iff_model SourceJointClockGraph.action.toLinearMap (observer runtime index steps)
    (windowBound runtime index steps) (coefficients runtime index steps) (source_law runtime index steps) left right

end
end SourceCopyRecordedRecurrence
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
