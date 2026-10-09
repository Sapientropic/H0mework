import H0mework.Versions.R9c73a630.Chemistry.LAlanineRefinementSource.Contractions
import H0mework.Versions.R9c73a630.Chemistry.LAlanineRefinementDensity.IntegrationBudget

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.BasinRefinement.SourceLaplaceProducer

open SourceFiniteData SourceFiniteChecks SourceJetIncidence SourceGaussianModel SourceLaplaceIntegers
open Set Filter
open scoped BigOperators Interval Topology

noncomputable section

theorem actual_envelope_bound (axis : Fin 3) :
    laplacianSecondEnvelope densityMatrixBound sourceOrbitalBound axis ≤ axisBound axis :=
  Finset.sum_le_sum (fun innerAxis _ => actual_fourth_envelopes innerAxis axis)

theorem source_laplacianSecond_bound (x : Point) (inside : InsideCube boxCentre boxRadius x)
    (axis : Fin 3) : |laplacianSecond sourceTerms densityMatrix axis x| ≤ (axisBound axis : ℝ) := by
  exact (laplacianSecond_abs_bound sourceTerms densityMatrix densityMatrixBound sourceOrbitalBound x axis
    actual_density_matrix_envelope (full_source_jets_bounded x inside)).trans
      (by exact_mod_cast actual_envelope_bound axis)

theorem sourceSlice_second_bound (point : Point) (axis : Fin 3) (transverse : TransverseInside point axis)
    (time : ℝ) (inside : time ∈ Icc (lower axis) (upper axis)) :
    |iteratedDeriv 2 (sourceSlice point axis) time| ≤ (axisBound axis : ℝ) := by
  change |iteratedDeriv 2
    (fun t => laplacian sourceTerms densityMatrix (Function.update point axis t)) time| ≤ _
  rw [laplacian_slice_second_at]
  exact source_laplacianSecond_bound _ (slice_inside point axis transverse time inside) axis

private theorem sourceSlice_within_second_bound (point : Point) (axis : Fin 3)
    (transverse : TransverseInside point axis) :
    ∀ time, |iteratedDerivWithin 2 (sourceSlice point axis) [[lower axis, upper axis]] time| ≤ (axisBound axis : ℝ) := by
  intro time
  by_cases inside : time ∈ [[lower axis, upper axis]]
  · rw [iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_uIcc (interval_ordered axis).ne)
      (sourceSlice_contDiff point axis).contDiffAt inside]
    exact sourceSlice_second_bound point axis transverse time
      (by simpa only [uIcc_of_le (interval_ordered axis).le] using inside)
  · rw [show (2 : Nat) = 1 + 1 from rfl, iteratedDerivWithin_succ,
      derivWithin_zero_of_notMem_closure (by
        simpa only [uIcc_of_le (interval_ordered axis).le, closure_Icc] using inside), abs_zero]
    exact_mod_cast (axisBound_positive axis).le

theorem sourceSlice_trapezoidal_bound (point : Point) (axis : Fin 3) (transverse : TransverseInside point axis)
    (panels : Nat) (positive : 0 < panels) :
    |trapezoidal_error (sourceSlice point axis) panels (lower axis) (upper axis)| ≤ errorBudget axis panels := by
  have source := trapezoidal_error_le_of_c2 (sourceSlice_contDiff point axis).contDiffOn
    (sourceSlice_within_second_bound point axis transverse) positive
  simpa only [errorBudget, abs_of_pos (sub_pos.mpr (interval_ordered axis))] using source

theorem sourceSlice_error_tendsto_zero (point : Point) (axis : Fin 3) (transverse : TransverseInside point axis) :
    Tendsto (fun n : Nat => |trapezoidal_error (sourceSlice point axis) n (lower axis) (upper axis)|) atTop (𝓝 0) := by
  apply squeeze_zero' (Eventually.of_forall (fun _ => abs_nonneg _)) _ (errorBudget_tendsto_zero axis)
  exact Filter.eventually_atTop.2 ⟨1, fun n hn => sourceSlice_trapezoidal_bound point axis transverse n (by omega)⟩

theorem sourceSlice_integral_convergence (point : Point) (axis : Fin 3) (transverse : TransverseInside point axis) :
    Tendsto (fun n : Nat => trapezoidal_integral (sourceSlice point axis) n (lower axis) (upper axis)) atTop
      (𝓝 (∫ t in lower axis..upper axis, sourceSlice point axis t)) := by
  apply tendsto_iff_dist_tendsto_zero.mpr
  simpa only [Real.dist_eq, trapezoidal_error] using sourceSlice_error_tendsto_zero point axis transverse

def sourceLaplaceClosure : Prop :=
  type_of% actual_axis_bounds ∧
  type_of% source_laplacianSecond_bound ∧
  type_of% sourceSlice_trapezoidal_bound ∧
  type_of% actual_doubling_budget ∧
  type_of% actual_doubling_strict ∧
  type_of% actual_bisection_readout ∧
  type_of% sourceSlice_integral_convergence

theorem sourceGeneratedContinuousLaplacianRefinement : sourceLaplaceClosure :=
  ⟨actual_axis_bounds, source_laplacianSecond_bound, sourceSlice_trapezoidal_bound,
    actual_doubling_budget, actual_doubling_strict, actual_bisection_readout, sourceSlice_integral_convergence⟩

end
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.BasinRefinement.SourceLaplaceProducer
