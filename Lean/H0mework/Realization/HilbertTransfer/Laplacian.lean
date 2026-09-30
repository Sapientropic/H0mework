import H0mework.Realization.HilbertTransfer.Retained

/-! An actual difference square generates Laplacian compression and its full transverse residual. -/

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace IsometricRetainedTransfer.LaplacianRefinement

noncomputable section

universe u v

variable {Source : Type u} {Observed : Type v}
variable [NormedAddCommGroup Source] [InnerProductSpace ℂ Source] [CompleteSpace Source]
variable [NormedAddCommGroup Observed] [InnerProductSpace ℂ Observed] [CompleteSpace Observed]
variable (pullback : Observed →ₗᵢ[ℂ] Source)
variable (sourceDifference : Source →L[ℂ] Source) (observedDifference : Observed →L[ℂ] Observed)
variable (square : sourceDifference.comp pullback.toContinuousLinearMap =
  pullback.toContinuousLinearMap.comp observedDifference)

include square

theorem adjoint_square :
    (transfer pullback).comp sourceDifference.adjoint =
      observedDifference.adjoint.comp (transfer pullback) := by
  have adjointSquare := congrArg (fun operator => operator.adjoint) square
  simpa only [ContinuousLinearMap.adjoint_comp, transfer] using adjointSquare

theorem compression :
    (transfer pullback).comp
        ((sourceDifference.adjoint.comp sourceDifference).comp pullback.toContinuousLinearMap) =
      observedDifference.adjoint.comp observedDifference := by
  ext value
  change transfer pullback (sourceDifference.adjoint (sourceDifference (pullback value))) =
    observedDifference.adjoint (observedDifference value)
  have sourceSquare := DFunLike.congr_fun square value
  change sourceDifference (pullback value) = pullback (observedDifference value) at sourceSquare
  rw [sourceSquare]
  have adjointSquare := DFunLike.congr_fun
    (adjoint_square pullback sourceDifference observedDifference square)
    (pullback (observedDifference value))
  simpa only [ContinuousLinearMap.comp_apply, transfer_pullback] using adjointSquare

theorem image_decomposition (value : Observed) :
    sourceDifference.adjoint (sourceDifference (pullback value)) =
      pullback (observedDifference.adjoint (observedDifference value)) +
        residual pullback (sourceDifference.adjoint (sourceDifference (pullback value))) := by
  have compressed := DFunLike.congr_fun
    (compression pullback sourceDifference observedDifference square) value
  have reconstructed := pullback_transfer_add_residual pullback
    (sourceDifference.adjoint (sourceDifference (pullback value)))
  change transfer pullback (sourceDifference.adjoint (sourceDifference (pullback value))) =
    observedDifference.adjoint (observedDifference value) at compressed
  rw [compressed] at reconstructed
  exact reconstructed.symm

theorem residual_eq_adjoint (value : Observed) :
    residual pullback (sourceDifference.adjoint (sourceDifference (pullback value))) =
      residual pullback (sourceDifference.adjoint (pullback (observedDifference value))) := by
  have sourceSquare := DFunLike.congr_fun square value
  exact congrArg (fun image => residual pullback (sourceDifference.adjoint image)) sourceSquare

theorem image_commutes_iff (value : Observed) :
    sourceDifference.adjoint (sourceDifference (pullback value)) =
        pullback (observedDifference.adjoint (observedDifference value)) ↔
      residual pullback (sourceDifference.adjoint (sourceDifference (pullback value))) = 0 := by
  have decomposition := image_decomposition pullback sourceDifference observedDifference square value
  constructor
  · intro commutes
    exact add_left_cancel ((decomposition.symm.trans commutes).trans (add_zero _).symm)
  · intro vanished
    simpa only [vanished, add_zero] using decomposition

theorem operator_commutes_iff :
    (sourceDifference.adjoint.comp sourceDifference).comp pullback.toContinuousLinearMap =
        pullback.toContinuousLinearMap.comp (observedDifference.adjoint.comp observedDifference) ↔
      (residual pullback).comp
        ((sourceDifference.adjoint.comp sourceDifference).comp pullback.toContinuousLinearMap) = 0 := by
  constructor
  · intro commutes
    ext value
    exact (image_commutes_iff pullback sourceDifference observedDifference square value).mp
      (DFunLike.congr_fun commutes value)
  · intro vanished
    ext value
    exact (image_commutes_iff pullback sourceDifference observedDifference square value).mpr
      (DFunLike.congr_fun vanished value)

theorem retained_image (value : Observed) :
    retainedUpdate pullback (sourceDifference.adjoint (sourceDifference (pullback value))) =
      (observedDifference.adjoint (observedDifference value),
        retainedResidual pullback (sourceDifference.adjoint (pullback (observedDifference value)))) := by
  apply Prod.ext
  · exact DFunLike.congr_fun (compression pullback sourceDifference observedDifference square) value
  · apply Subtype.ext
    exact residual_eq_adjoint pullback sourceDifference observedDifference square value

theorem image_energy (value : Observed) :
    ‖sourceDifference.adjoint (sourceDifference (pullback value))‖ ^ 2 =
      ‖observedDifference.adjoint (observedDifference value)‖ ^ 2 +
        ‖residual pullback (sourceDifference.adjoint (sourceDifference (pullback value)))‖ ^ 2 := by
  have compressed := DFunLike.congr_fun
    (compression pullback sourceDifference observedDifference square) value
  have energy := energy_decomposition pullback
    (sourceDifference.adjoint (sourceDifference (pullback value)))
  change transfer pullback (sourceDifference.adjoint (sourceDifference (pullback value))) =
    observedDifference.adjoint (observedDifference value) at compressed
  rwa [compressed] at energy

end
end IsometricRetainedTransfer.LaplacianRefinement
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
