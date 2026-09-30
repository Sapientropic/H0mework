import H0mework.Probability.Runtime.InvariantCluster
import H0mework.Versions.X.Arithmetic.FockDynamics.RootRuntime
import Mathlib.Data.ZMod.Basic

/-! A finite observation of the original Fock runtime has a nonstationary one-sample law. -/

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceObservationInvariantControls

open SourceGeneratedScalarCofinalTopology.NativeProbability
open SourceGeneratedRuntimeHistoryProbability SourceGeneratedActionObservationHistory
open SourceOperationNative MeasureTheory

open NoIslandNoMagic.CanonicalArithmeticState

noncomputable section

/-- This finite readout is a coarse observation of the original native state. -/
def parity : ParticleWaveFockRuntime.process.State → ZMod 2 := fun state => state

theorem fieldPoint_first (state : ParticleWaveFockRuntime.process.State) :
    stageRead (sourceAction ParticleWaveFockRuntime.process) (observer ParticleWaveFockRuntime.process parity) 0
      (fieldPoint parity state) 0 = parity state :=
  (source_reads_stage (sourceAction ParticleWaveFockRuntime.process) (observer ParticleWaveFockRuntime.process parity) 0
    (statePoint ParticleWaveFockRuntime.process state) 0).trans (observer_statePoint ParticleWaveFockRuntime.process parity state)

theorem fieldPoint_zero_ne_one : fieldPoint parity 0 ≠ fieldPoint parity 1 := by
  intro equality
  have readEquality := congrArg (fun value =>
    stageRead (sourceAction ParticleWaveFockRuntime.process) (observer ParticleWaveFockRuntime.process parity) 0 value 0) equality
  exact (zero_ne_one : (0 : ZMod 2) ≠ 1)
    ((fieldPoint_first 0).symm.trans (readEquality.trans (fieldPoint_first 1)))

private theorem single_sample (runtime : LivingRuntimeState ParticleWaveFockRuntime.process) :
    fieldPMF parity runtime 0 = PMF.pure (fieldPoint parity runtime.state) := by
  rw [fieldPMF, statePMF, PMF.map_comp]
  have constant : (fieldPoint parity ∘ sample runtime 0) =
      Function.const (Fin 1) (fieldPoint parity runtime.state) := by
    funext index
    have zero : index = 0 := Fin.eq_zero index
    subst index
    rfl
  rw [constant, PMF.map_const]

theorem initial_sample_not_invariant :
    letI : MeasurableSpace (Field parity) := fieldBorel parity
    (fieldPMF parity (ParticleWaveFockRuntime.runtimeAt 0) 0).toMeasure.map (fieldAction parity) ≠
      (fieldPMF parity (ParticleWaveFockRuntime.runtimeAt 0) 0).toMeasure := by
  let : UniformSpace (Field parity) := fieldUniform parity
  let : MeasurableSpace (Field parity) := fieldBorel parity
  let : BorelSpace (Field parity) := ⟨rfl⟩
  let : T2Space (Field parity) := field_t2 parity
  rw [fieldMeasure_next]
  simp only [single_sample, PMF.toMeasure_pure]
  change Measure.dirac (fieldPoint parity 1) ≠ Measure.dirac (fieldPoint parity 0)
  exact dirac_ne_dirac fieldPoint_zero_ne_one.symm

theorem full_history_cluster_fibre_nonempty_ne_initial :
    letI : UniformSpace (Field parity) := fieldUniform parity
    letI : MeasurableSpace (Field parity) := fieldBorel parity
    letI : BorelSpace (Field parity) := ⟨rfl⟩
    Nonempty (HistoryCluster parity (ParticleWaveFockRuntime.runtimeAt 0)) ∧
      ∀ cluster : HistoryCluster parity (ParticleWaveFockRuntime.runtimeAt 0),
        (cluster.val : Measure (Field parity)) ≠
          (fieldPMF parity (ParticleWaveFockRuntime.runtimeAt 0) 0).toMeasure := by
  let : UniformSpace (Field parity) := fieldUniform parity
  let : MeasurableSpace (Field parity) := fieldBorel parity
  let : BorelSpace (Field parity) := ⟨rfl⟩
  refine ⟨historyCluster_nonempty parity (ParticleWaveFockRuntime.runtimeAt 0), ?_⟩
  intro cluster equality
  have preserved :=
    (historyCluster_measurePreserving parity (ParticleWaveFockRuntime.runtimeAt 0) cluster).map_eq
  rw [equality] at preserved
  exact initial_sample_not_invariant preserved

end
end SourceObservationInvariantControls
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
