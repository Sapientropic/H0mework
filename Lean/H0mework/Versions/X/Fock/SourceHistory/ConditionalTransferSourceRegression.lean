import H0mework.Probability.Source.Conditional
import H0mework.Versions.X.Checks.Probability.EmpiricalSource

/-! The original pulse's actual next observation retains both distinct source occurrences. -/

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceConditionalTransfer.Pulse

open SourceGeneratedRuntimeHistoryProbability SourceGeneratedEmpiricalHilbert.Controls
open SourceGeneratedScalarCofinalTopology.NativeProbability
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime

noncomputable section

abbrev runtime := runtimeAt 0

def nextObservation (index : Fin 2) : Field pulse :=
  fieldAction pulse (fieldPoint pulse (sample runtime 1 index))

def query : Field pulse := nextObservation 0

theorem nextObservation_eq (index : Fin 2) :
    nextObservation index = fieldPoint pulse (index.val + 1) := by
  rw [nextObservation, fieldPoint_action]
  exact congrArg (fun state => fieldPoint pulse (state + 1)) (runtimeAt_state index.val)

theorem nextObservation_constant (index : Fin 2) : nextObservation index = query := by
  rw [nextObservation_eq, query, nextObservation_eq]
  exact point_successors_equal index.val 0

theorem query_supported :
    query ∈ ((historyPMF 1).map nextObservation).support :=
  (PMF.mem_support_map_iff _ _ _).mpr ⟨0, by simp [historyPMF], rfl⟩

def conditional : PMF (Fin 2) :=
  SourceConditionalHistory.conditional (historyPMF 1) nextObservation query query_supported

theorem observed_pure : (historyPMF 1).map nextObservation = PMF.pure query := by
  have constant : nextObservation = Function.const (Fin 2) query := funext nextObservation_constant
  rw [constant, PMF.map_const]

theorem conditional_eq_history : conditional = historyPMF 1 := by
  apply PMF.ext
  intro index
  have weighted := SourceConditionalHistory.weighted_conditional (historyPMF 1)
    nextObservation query query_supported index
  change (historyPMF 1).map nextObservation query * conditional index = _ at weighted
  rw [observed_pure, PMF.pure_apply_self, one_mul, if_pos (nextObservation_constant index)] at weighted
  exact weighted

theorem conditional_apply (index : Fin 2) : conditional index = (2 : ENNReal)⁻¹ := by
  rw [conditional_eq_history, historyPMF_apply]
  norm_num

theorem retains_both : (0 : Fin 2) ∈ conditional.support ∧ (1 : Fin 2) ∈ conditional.support := by
  simp [conditional_eq_history, historyPMF]

theorem original_points_distinct :
    fieldPoint pulse (sample runtime 1 0) ≠ fieldPoint pulse (sample runtime 1 1) :=
  point_zero_ne_one

end
end SourceConditionalTransfer.Pulse
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
