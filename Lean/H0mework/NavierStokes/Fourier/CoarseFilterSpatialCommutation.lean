import H0mework.NavierStokes.Fourier.CoarseFilterCore

/-!
# Spatial derivative commutation for the concrete coarse filter

The compact-kernel theorem in Mathlib differentiates convolution through
the compact factor.  A periodic physical field need not have compact
support, so it cannot be inserted into the other side of that theorem
directly.

Here the same source scale generates an internal localization bump at each
observation point.  On a neighborhood large enough to contain every
kernel-visible argument, the bump is exactly one.  The localized field is
compactly supported and agrees with the original field together with its
Fréchet derivative wherever the convolution can see it.  This discharges
the compact-support proof cost internally and removes the localization from
the theorem mouth.

The result is the whole-carrier commuting update

`D (Kₛ f) = Kₛ (D f)`

for every `C¹` field.  No periodicity, target equation, commutation
certificate, or output faithfulness premise is required.
-/

open scoped Convolution Topology
open MeasureTheory Metric Filter

namespace SaturationMonoid
namespace NavierStokes
namespace ThreeDimensionalPeriodicCoarseFilterSpatialCommutation

open ThreeDimensionalPeriodicCoarseFilterCore

noncomputable section

/--
The proof-local cutoff is one on the kernel-visible ball and vanishes
outside a slightly larger ball.
-/
noncomputable def localizationBump
    (s : CoarseScale) (x : PhysicalSpace) : ContDiffBump x where
  rIn := s.radius + 1
  rOut := s.radius + 2
  rIn_pos := add_pos s.radius_pos zero_lt_one
  rIn_lt_rOut := by
    linarith

noncomputable def localizedField {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (s : CoarseScale) (x : PhysicalSpace)
    (f : PhysicalSpace → E) : PhysicalSpace → E :=
  fun y => localizationBump s x y • f y

lemma shifted_mem_localization_closedBall
    (s : CoarseScale) (x y t : PhysicalSpace)
    (hy : y ∈ ball x 1)
    (ht : t ∈ ball (0 : PhysicalSpace) s.radius) :
    y - t ∈ closedBall x (s.radius + 1) := by
  rw [mem_closedBall, dist_eq_norm]
  rw [show y - t - x = (y - x) - t by abel]
  calc
    ‖(y - x) - t‖ ≤ ‖y - x‖ + ‖t‖ := norm_sub_le _ _
    _ ≤ 1 + s.radius := (add_lt_add
      (by simpa [mem_ball, dist_eq_norm] using hy)
      (by simpa [mem_ball, dist_eq_norm] using ht)).le
    _ = s.radius + 1 := by ring

lemma kernel_mem_support_ball
    (s : CoarseScale) (t : PhysicalSpace)
    (ht : coarseKernel s t ≠ 0) :
    t ∈ ball (0 : PhysicalSpace) s.radius := by
  have htSupport : t ∈ Function.support (coarseKernel s) := by
    simpa [Function.mem_support] using ht
  rw [coarseKernel, (coarseBump s).support_normed_eq] at htSupport
  exact htSupport

lemma localizedField_eq_of_mem_closedBall {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (s : CoarseScale) (x y : PhysicalSpace)
    (f : PhysicalSpace → E)
    (hy : y ∈ closedBall x (s.radius + 1)) :
    localizedField s x f y = f y := by
  rw [localizedField,
    (localizationBump s x).one_of_mem_closedBall hy, one_smul]

lemma coarseKernel_smul_localizedField_eq {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (s : CoarseScale) (x y : PhysicalSpace)
    (f : PhysicalSpace → E)
    (hy : y ∈ ball x 1) (t : PhysicalSpace) :
    coarseKernel s t • localizedField s x f (y - t) =
      coarseKernel s t • f (y - t) := by
  by_cases hkt : coarseKernel s t = 0
  · simp [hkt]
  · rw [localizedField_eq_of_mem_closedBall s x (y - t) f
      (shifted_mem_localization_closedBall s x y t hy
        (kernel_mem_support_ball s t hkt))]

lemma coarseFilter_eventuallyEq_localizedField {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (s : CoarseScale) (x : PhysicalSpace)
    (f : PhysicalSpace → E) :
    coarseFilter s (localizedField s x f) =ᶠ[𝓝 x]
      coarseFilter s f := by
  filter_upwards [Metric.ball_mem_nhds x zero_lt_one] with y hy
  simp only [coarseFilter, convolution_def,
    ContinuousLinearMap.lsmul_apply]
  apply integral_congr_ae
  filter_upwards with t
  exact coarseKernel_smul_localizedField_eq s x y f hy t

lemma localizedField_hasCompactSupport {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (s : CoarseScale) (x : PhysicalSpace)
    (f : PhysicalSpace → E) :
    HasCompactSupport (localizedField s x f) :=
  (localizationBump s x).hasCompactSupport.smul_right

lemma localizedField_contDiff {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (s : CoarseScale) (x : PhysicalSpace)
    (f : PhysicalSpace → E)
    (hf : ContDiff ℝ 1 f) :
    ContDiff ℝ 1 (localizedField s x f) :=
  (localizationBump s x).contDiff.smul hf

lemma sub_mem_localization_ball
    (s : CoarseScale) (x t : PhysicalSpace)
    (ht : t ∈ ball (0 : PhysicalSpace) s.radius) :
    x - t ∈ ball x (s.radius + 1) := by
  rw [mem_ball, dist_eq_norm]
  rw [show x - t - x = -t by abel, norm_neg]
  have ht' : ‖t‖ < s.radius := by
    simpa [mem_ball, dist_eq_norm] using ht
  linarith

lemma localizedField_eventuallyEq_at_sub {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (s : CoarseScale) (x t : PhysicalSpace)
    (f : PhysicalSpace → E)
    (ht : t ∈ ball (0 : PhysicalSpace) s.radius) :
    localizedField s x f =ᶠ[𝓝 (x - t)] f := by
  filter_upwards [
    (localizationBump s x).eventuallyEq_one_of_mem_ball
      (sub_mem_localization_ball s x t ht)] with y hy
  simp [localizedField, hy]

lemma fderiv_localizedField_eq_of_kernel_ne_zero {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (s : CoarseScale) (x t : PhysicalSpace)
    (f : PhysicalSpace → E)
    (ht : coarseKernel s t ≠ 0) :
    fderiv ℝ (localizedField s x f) (x - t) =
      fderiv ℝ f (x - t) :=
  (localizedField_eventuallyEq_at_sub s x t f
    (kernel_mem_support_ball s t ht)).fderiv_eq

lemma derivativeConvolution_localized_eq {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (s : CoarseScale) (x : PhysicalSpace)
    (f : PhysicalSpace → E) :
    (coarseKernel s ⋆[
      (ContinuousLinearMap.lsmul ℝ ℝ).precompR PhysicalSpace,
      volume] fderiv ℝ (localizedField s x f)) x =
    (coarseKernel s ⋆[
      (ContinuousLinearMap.lsmul ℝ ℝ).precompR PhysicalSpace,
      volume] fderiv ℝ f) x := by
  simp only [convolution_def]
  apply integral_congr_ae
  filter_upwards with t
  by_cases ht : coarseKernel s t = 0
  · simp [ht]
  · rw [fderiv_localizedField_eq_of_kernel_ne_zero s x t f ht]

/--
The source-generated localization removes the compact-support restriction
from the derivative-through-convolution theorem.
-/
theorem coarseFilter_hasFDerivAt_filterFDeriv {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (s : CoarseScale) (f : PhysicalSpace → E)
    (hf : ContDiff ℝ 1 f) (x : PhysicalSpace) :
    HasFDerivAt (coarseFilter s f)
      ((coarseKernel s ⋆[
        (ContinuousLinearMap.lsmul ℝ ℝ).precompR PhysicalSpace,
        volume] fderiv ℝ f) x) x := by
  have hk : LocallyIntegrable (coarseKernel s) volume :=
    (coarseKernel_contDiff s).continuous.locallyIntegrable
  have hlocal :=
    (localizedField_hasCompactSupport s x f).hasFDerivAt_convolution_right
      (ContinuousLinearMap.lsmul ℝ ℝ) hk
      (localizedField_contDiff s x f hf) x
  rw [derivativeConvolution_localized_eq s x f] at hlocal
  exact hlocal.congr_of_eventuallyEq
    (coarseFilter_eventuallyEq_localizedField s x f).symm

lemma derivativeConvolution_eq_coarseFilter_fderiv {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (s : CoarseScale) (f : PhysicalSpace → E) :
    (coarseKernel s ⋆[
      (ContinuousLinearMap.lsmul ℝ ℝ).precompR PhysicalSpace,
      volume] fderiv ℝ f) =
      coarseFilter s (fderiv ℝ f) := by
  funext x
  simp only [coarseFilter, convolution_def]
  apply integral_congr_ae
  filter_upwards with t
  ext v
  rfl

/-- The actual whole-carrier spatial commuting square. -/
theorem fderiv_coarseFilter_eq_coarseFilter_fderiv {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (s : CoarseScale) (f : PhysicalSpace → E)
    (hf : ContDiff ℝ 1 f) :
    fderiv ℝ (coarseFilter s f) =
      coarseFilter s (fderiv ℝ f) := by
  funext x
  calc
    fderiv ℝ (coarseFilter s f) x =
        (coarseKernel s ⋆[
          (ContinuousLinearMap.lsmul ℝ ℝ).precompR PhysicalSpace,
          volume] fderiv ℝ f) x :=
      (coarseFilter_hasFDerivAt_filterFDeriv s f hf x).fderiv
    _ = coarseFilter s (fderiv ℝ f) x :=
      congrFun (derivativeConvolution_eq_coarseFilter_fderiv s f) x

/--
A concrete continuous-linear observer commutes with the same coarse update
when the convolution genuinely exists.
-/
theorem coarseFilter_comp_continuousLinearMap
    {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    (s : CoarseScale) (L : E →L[ℝ] F)
    (f : PhysicalSpace → E)
    (hf : LocallyIntegrable f volume)
    (x : PhysicalSpace) :
    coarseFilter s (fun y => L (f y)) x =
      L (coarseFilter s f x) := by
  have hint : Integrable
      (fun t => coarseKernel s t • f (x - t)) volume :=
    ((coarseKernel_hasCompactSupport s).convolutionExists_left
      (ContinuousLinearMap.lsmul ℝ ℝ)
      (coarseKernel_contDiff s).continuous hf x).integrable
  simpa only [coarseFilter, convolution_def,
    ContinuousLinearMap.lsmul_apply, map_smul] using
      L.integral_comp_comm hint

end

end ThreeDimensionalPeriodicCoarseFilterSpatialCommutation
end NavierStokes
end SaturationMonoid
