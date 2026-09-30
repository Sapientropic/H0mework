import H0mework.Fock.CopyGraph.CorrectionMoments

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceConditionalCorrection

open SourceWeightedRecovery SourceGeneratedRuntimeHistoryProbability
open SourceConditionalGraphDecoder (action)
open SourceCopyProgram (Index scale)
open scoped InnerProductSpace
noncomputable section
universe u
variable {Observed : Type u} [MeasurableSpace Observed] [MeasurableSingletonClass Observed]

def clockPair (bound : Nat) (query : Fin (bound + 1) → Observed) (value : Space (historyPMF bound)) : ℂ :=
  inner ℂ (residual (historyPMF bound) query (taskValue (historyPMF bound) (SourceGeneratedJointClock.signal bound)))
    (residual (historyPMF bound) query value)

private theorem root_square (bound : Nat) : (Real.sqrt (bound + 1 : ℝ) : ℂ) ^ 2 = (bound + 1 : ℂ) := by
  exact_mod_cast Real.sq_sqrt (by positivity : (0 : ℝ) ≤ bound + 1)

theorem gram (depth bound : Nat) (index : Index depth) (query : Fin (bound + 1) → Observed)
    (value : Space (observed (historyPMF bound) query)) :
    (action depth bound index query).adjoint (action depth bound index query value) =
      value + ((bound + 1 : ℂ) * inner ℂ (one bound query) value) • one bound query +
        ((scale depth index : ℂ) ^ 2 * (bound + 1 : ℂ) * inner ℂ (clockMean bound query) value) • clockMean bound query := by
  apply ext_inner_left ℂ
  intro proposal
  rw [ContinuousLinearMap.adjoint_inner_right, SourceConditionalGraphDecoder.action_source,
    SourceConditionalGraphDecoder.action_source, SourceConditionalGraphDecoder.copy_inner,
    (pullback (historyPMF bound) query).inner_map_map, mass_pullback, mass_pullback, clock_pullback, clock_pullback]
  simp only [inner_add_right, inner_smul_right, Complex.real_smul, map_mul, Complex.conj_ofReal, inner_conj_symm]
  have square := root_square bound
  ring_nf at square ⊢
  rw [square]
  ring

theorem forcing (depth bound : Nat) (index : Index depth) (query : Fin (bound + 1) → Observed)
    (value : Space (historyPMF bound)) :
    (action depth bound index query).adjoint
      (SourceConditionalGraph.copyRead depth bound index (residual (historyPMF bound) query value)) =
        ((scale depth index : ℂ) ^ 2 * (bound + 1 : ℂ) * clockPair bound query value) • clockMean bound query := by
  apply ext_inner_left ℂ
  intro proposal
  rw [ContinuousLinearMap.adjoint_inner_right, SourceConditionalGraphDecoder.conditional_inner,
    clock_pullback, SourceConditionalGraph.residual_clock, inner_smul_right]
  simp only [Complex.real_smul, map_mul, Complex.conj_ofReal, inner_conj_symm]
  unfold clockPair
  have square := root_square bound
  ring_nf at square ⊢
  rw [square]
  ring

theorem correction_equation (depth bound : Nat) (index : Index depth) (query : Fin (bound + 1) → Observed)
    (value : Space (historyPMF bound)) :
    let delta := correction depth bound index query value
    delta + ((bound + 1 : ℂ) * inner ℂ (one bound query) delta) • one bound query +
      ((scale depth index : ℂ) ^ 2 * (bound + 1 : ℂ) * inner ℂ (clockMean bound query) delta) • clockMean bound query =
        ((scale depth index : ℂ) ^ 2 * (bound + 1 : ℂ) * clockPair bound query value) • clockMean bound query := by
  have generated := source_equation depth bound index query value
  rw [gram, forcing] at generated
  exact generated

end
end SourceConditionalCorrection
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
