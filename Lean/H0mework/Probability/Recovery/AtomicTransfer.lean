import H0mework.Probability.Recovery.AtomicReader

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceGeneratedAtomicObservation

open SourceWeightedRecovery

noncomputable section

universe u v w

variable {Current : Type v} {Next : Type w} [NormedAddCommGroup Current] [InnerProductSpace ℂ Current]
  [CompleteSpace Current] [NormedAddCommGroup Next] [InnerProductSpace ℂ Next] [CompleteSpace Next]

theorem norm_reader_transfer (pullback : Next →ₗᵢ[ℂ] Current) (reader : Next →L[ℂ] ℂ) :
    ‖reader.comp (IsometricRetainedTransfer.transfer pullback)‖ = ‖reader‖ := by
  apply le_antisymm
  · apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg reader)
    intro value
    exact (reader.le_opNorm _).trans
      (mul_le_mul_of_nonneg_left (IsometricRetainedTransfer.transfer_norm_le pullback value)
        (norm_nonneg reader))
  · apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
    intro value
    have bound := (reader.comp (IsometricRetainedTransfer.transfer pullback)).le_opNorm (pullback value)
    simpa only [ContinuousLinearMap.comp_apply, IsometricRetainedTransfer.transfer_pullback,
      LinearIsometry.norm_map] using bound

variable {A : Type u} [MeasurableSpace A] [MeasurableSingletonClass A]
variable (source : PMF A) (point : A) (supported : point ∈ source.support)
variable {Origin : Type v} [NormedAddCommGroup Origin] [InnerProductSpace ℂ Origin] [CompleteSpace Origin]
variable (pullback : Space source →ₗᵢ[ℂ] Origin)

theorem source_query_norm :
    ‖(evalAtContinuous source point supported).comp (IsometricRetainedTransfer.transfer pullback)‖ =
      1 / Real.sqrt (source point).toReal :=
  (norm_reader_transfer pullback (evalAtContinuous source point supported)).trans
    (evalAtContinuous_norm source point supported)

theorem source_query_error (left right : Origin) :
    ‖evalAtContinuous source point supported (IsometricRetainedTransfer.transfer pullback left) -
        evalAtContinuous source point supported (IsometricRetainedTransfer.transfer pullback right)‖ ≤
      (1 / Real.sqrt (source point).toReal) * ‖left - right‖ := by
  let query := (evalAtContinuous source point supported).comp (IsometricRetainedTransfer.transfer pullback)
  have bound := query.le_opNorm (left - right)
  have actual := source_query_norm source point supported pullback
  change ‖query‖ = _ at actual
  rw [actual, map_sub] at bound
  exact bound

end
end SourceGeneratedAtomicObservation
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
