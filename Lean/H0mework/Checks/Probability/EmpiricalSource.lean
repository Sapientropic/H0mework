import H0mework.Probability.Empirical.History
import H0mework.Realization.HistoryTopology.Compactness
import H0mework.Arithmetic.FockDynamics.RootRuntime
import Mathlib.Data.ZMod.Basic
import Mathlib.MeasureTheory.Function.LpSeminorm.Indicator

/-! An actual finite Fock history loses its initial pulse in transfer and retains it in the residual. -/

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceGeneratedEmpiricalHilbert.Controls

open SourceOperationNative SourceGeneratedActionObservationHistory
open SourceGeneratedScalarCofinalTopology.NativeProbability SourceGeneratedRuntimeHistoryProbability
open NoIslandNoMagic.CanonicalArithmeticState MeasureTheory

noncomputable section

def pulse : ParticleWaveFockRuntime.process.State → ZMod 2 := fun state => if state = 0 then 1 else 0

local instance : UniformSpace (Field pulse) := fieldUniform pulse
local instance : MeasurableSpace (Field pulse) := fieldBorel pulse
local instance : BorelSpace (Field pulse) := ⟨rfl⟩
local instance : T2Space (Field pulse) := field_t2 pulse

private theorem source_iterate (state stage : Nat) :
    ((sourceAction ParticleWaveFockRuntime.process) ^ stage)
        (statePoint ParticleWaveFockRuntime.process state) =
      statePoint ParticleWaveFockRuntime.process (state + stage) := by
  induction stage with
  | zero => rfl
  | succ stage inductionHypothesis =>
      rw [pow_succ']
      change sourceAction ParticleWaveFockRuntime.process
        (((sourceAction ParticleWaveFockRuntime.process) ^ stage)
          (statePoint ParticleWaveFockRuntime.process state)) = _
      rw [inductionHypothesis, sourceAction_statePoint]
      rfl

theorem point_successors_equal (left right : Nat) :
    fieldPoint pulse (left + 1) = fieldPoint pulse (right + 1) := by
  apply (source_fibre_iff (sourceAction ParticleWaveFockRuntime.process)
    (observer ParticleWaveFockRuntime.process pulse) _ _).mpr
  intro stage
  rw [source_iterate, source_iterate, observer_statePoint, observer_statePoint]
  simp [pulse]

theorem point_zero_ne_one : fieldPoint pulse 0 ≠ fieldPoint pulse 1 := by
  intro same
  have first := congrArg (fun value => stageRead (sourceAction ParticleWaveFockRuntime.process)
    (observer ParticleWaveFockRuntime.process pulse) 0 value 0) same
  simp only [fieldPoint, source_reads_stage] at first
  change observer ParticleWaveFockRuntime.process pulse (statePoint ParticleWaveFockRuntime.process 0) =
    observer ParticleWaveFockRuntime.process pulse (statePoint ParticleWaveFockRuntime.process 1) at first
  simp only [observer_statePoint] at first
  exact (one_ne_zero : (1 : ZMod 2) ≠ 0) first

theorem sample_mass_ne_zero (index : Fin 2) :
    (empirical pulse (ParticleWaveFockRuntime.runtimeAt 0) 1).toMeasure {fieldPoint pulse index.val} ≠ 0 := by
  change (fieldPMF pulse (ParticleWaveFockRuntime.runtimeAt 0) 1).toMeasure _ ≠ 0
  rw [PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _)]
  apply (PMF.mem_support_iff _ _).mp
  apply (fieldPMF_support_iff pulse (ParticleWaveFockRuntime.runtimeAt 0) 1 _).mpr
  exact ⟨index, congrArg (fieldPoint pulse) (ParticleWaveFockRuntime.runtimeAt_state index.val)⟩

theorem ae_at_sample (index : Fin 2) {predicate : Field pulse → Prop}
    (proof : ∀ᵐ point ∂(empirical pulse (ParticleWaveFockRuntime.runtimeAt 0) 1).toMeasure, predicate point) :
    predicate (fieldPoint pulse index.val) := by
  obtain ⟨point, member, holds⟩ := Measure.exists_mem_of_measure_ne_zero_of_ae
    (sample_mass_ne_zero index) (ae_restrict_of_ae proof)
  exact Set.mem_singleton_iff.mp member ▸ holds

def indicator : Field pulse → ℂ := ({fieldPoint pulse 0} : Set (Field pulse)).indicator (fun _ => 1)

theorem indicator_memLp :
    MemLp indicator 2 (empirical pulse (ParticleWaveFockRuntime.runtimeAt 0) 1).toMeasure :=
  MemLp.indicator (measurableSet_singleton _) (memLp_const (1 : ℂ))

def indicatorValue : Space pulse (ParticleWaveFockRuntime.runtimeAt 0) 1 := indicator_memLp.toLp indicator

theorem indicator_residual_ne_zero :
    residual pulse (ParticleWaveFockRuntime.runtimeAt 0) 1 indicatorValue ≠ 0 := by
  intro vanished
  obtain ⟨next, same⟩ := (residual_zero_iff pulse (ParticleWaveFockRuntime.runtimeAt 0) 1 _).mp vanished
  have pulled := pullback_ae pulse (ParticleWaveFockRuntime.runtimeAt 0) 1 next
  change pullback pulse (ParticleWaveFockRuntime.runtimeAt 0) 1 next = indicatorValue at same
  rw [same] at pulled
  have raw : indicator =ᵐ[(empirical pulse (ParticleWaveFockRuntime.runtimeAt 0) 1).toMeasure]
      next ∘ fieldAction pulse := indicator_memLp.coeFn_toLp.symm.trans pulled
  have first : (1 : ℂ) = next (fieldPoint pulse 1) := by
    have found := ae_at_sample 0 raw
    dsimp only [Function.comp_apply] at found
    rw [fieldPoint_action] at found
    change indicator (fieldPoint pulse 0) = next (fieldPoint pulse 1) at found
    simpa [indicator] using found
  have second : (0 : ℂ) = next (fieldPoint pulse 2) := by
    have found := ae_at_sample 1 raw
    dsimp only [Function.comp_apply] at found
    rw [fieldPoint_action] at found
    change indicator (fieldPoint pulse 1) = next (fieldPoint pulse 2) at found
    simpa [indicator, point_zero_ne_one.symm] using found
  exact (one_ne_zero : (1 : ℂ) ≠ 0)
    (first.trans ((congrArg next (point_successors_equal 0 1)).trans second.symm))

theorem indicator_transfer_norm_lt :
    ‖transfer pulse (ParticleWaveFockRuntime.runtimeAt 0) 1 indicatorValue‖ < ‖indicatorValue‖ := by
  have energy := energy_decomposition pulse (ParticleWaveFockRuntime.runtimeAt 0) 1 indicatorValue
  have loss := sq_pos_of_pos (norm_pos_iff.mpr indicator_residual_ne_zero)
  nlinarith only [energy, loss, norm_nonneg indicatorValue,
    norm_nonneg (transfer pulse (ParticleWaveFockRuntime.runtimeAt 0) 1 indicatorValue)]

theorem retained_pulse_reconstructed :
    reconstruct pulse (ParticleWaveFockRuntime.runtimeAt 0) 1
      (retainedUpdate pulse (ParticleWaveFockRuntime.runtimeAt 0) 1 indicatorValue) = indicatorValue :=
  reconstruct_split pulse (ParticleWaveFockRuntime.runtimeAt 0) 1 indicatorValue

theorem two_step_retains_initial_pulse :
    ((retainedHistory pulse (ParticleWaveFockRuntime.runtimeAt 0) 1 2 indicatorValue).2.1.2).val ≠ 0 :=
  indicator_residual_ne_zero

end
end SourceGeneratedEmpiricalHilbert.Controls
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
