import H0mework.Versions.R2.Probability.Empirical.ConditionalFormula
import H0mework.Versions.R2.Fock.SourceHistory.ConditionalTransferSourceRegression

/-! The actual merging pulse computes the old transfer and both retained source residual values. -/

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceConditionalTransfer.Pulse

open SourceGeneratedRuntimeHistoryProbability SourceGeneratedEmpiricalHilbert
open SourceGeneratedEmpiricalHilbert.Controls
open SourceGeneratedScalarCofinalTopology.NativeProbability
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime

noncomputable section

theorem next_query_supported : query ∈ (fieldPMF pulse runtime.tick.next 1).support := by
  rw [nextPMF_from_indices]
  exact query_supported

theorem source_zero_value : indicatorValue (fieldSample pulse runtime 1 0) = 1 := by
  calc
    _ = indicator (fieldPoint pulse 0) := Controls.ae_at_sample 0 indicator_memLp.coeFn_toLp
    _ = 1 := by simp [indicator]

theorem source_one_value : indicatorValue (fieldSample pulse runtime 1 1) = 0 := by
  calc
    _ = indicator (fieldPoint pulse 1) := Controls.ae_at_sample 1 indicator_memLp.coeFn_toLp
    _ = 0 := by simp [indicator, point_zero_ne_one.symm]

theorem conditionalValue_half :
    conditionalValue pulse runtime 1 indicatorValue query next_query_supported = (1 / 2 : ℂ) := by
  unfold conditionalValue
  change ∑ index : Fin 2, (conditional index).toReal •
    indicatorValue (fieldSample pulse runtime 1 index) = _
  rw [Fin.sum_univ_two, source_zero_value, source_one_value]
  norm_num [conditional_apply]

theorem transfer_half : transfer pulse runtime 1 indicatorValue query = (1 / 2 : ℂ) :=
  (transfer_at_atom pulse runtime 1 indicatorValue query next_query_supported).trans conditionalValue_half

theorem residual_zero_value : residual pulse runtime 1 indicatorValue
    (fieldSample pulse runtime 1 0) = (1 / 2 : ℂ) := by
  have whole := congrArg (fun value : Space pulse runtime 1 => value (fieldSample pulse runtime 1 0))
    (pullback_transfer_add_residual pulse runtime 1 indicatorValue)
  have combined := SourceConditionalTransfer.ae_at_sample pulse runtime 1 0
    (MeasureTheory.Lp.coeFn_add (pullback pulse runtime 1 (transfer pulse runtime 1 indicatorValue))
      (residual pulse runtime 1 indicatorValue))
  rw [whole] at combined
  simp only [Pi.add_apply] at combined
  rw [pullback_at_sample, source_zero_value] at combined
  change (1 : ℂ) = transfer pulse runtime 1 indicatorValue query + _ at combined
  rw [transfer_half] at combined
  linear_combination -combined

theorem residual_one_value : residual pulse runtime 1 indicatorValue
    (fieldSample pulse runtime 1 1) = (-1 / 2 : ℂ) := by
  have whole := congrArg (fun value : Space pulse runtime 1 => value (fieldSample pulse runtime 1 1))
    (pullback_transfer_add_residual pulse runtime 1 indicatorValue)
  have combined := SourceConditionalTransfer.ae_at_sample pulse runtime 1 1
    (MeasureTheory.Lp.coeFn_add (pullback pulse runtime 1 (transfer pulse runtime 1 indicatorValue))
      (residual pulse runtime 1 indicatorValue))
  rw [whole] at combined
  simp only [Pi.add_apply] at combined
  rw [pullback_at_sample, source_one_value] at combined
  have same : nextAtom pulse runtime 1 1 = query := nextObservation_constant 1
  rw [same, transfer_half] at combined
  linear_combination -combined

theorem transfer_is_neither_source :
    transfer pulse runtime 1 indicatorValue query ≠ 0 ∧
      transfer pulse runtime 1 indicatorValue query ≠ 1 := by
  rw [transfer_half]
  norm_num

end
end SourceConditionalTransfer.Pulse
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
