import H0mework.Versions.R3bbcbd59.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.CanonicalPreparationSourceFieldLocalized
import H0mework.Versions.AB.Physics.LowEnergy.AlphaSource.CanonicalPhysicalLaplace
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.MeasureTheory.Integral.DominatedConvergence

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationVacuumCausalFieldResponse
open SourceFiniteUnitary CanonicalGradedVariation
open GaussCoreHilbert CanonicalPhysicalSpatial CanonicalGradedSpatialSource
open FullYSourceCutoffVolterra GaussUnitaryHistory
open scoped Topology Interval

section Variation
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
local instance : NormedAlgebra ℚ (E →L[ℂ] E) := NormedAlgebra.restrictScalars ℚ ℂ _
local instance : NormedAlgebra ℝ (E →L[ℂ] E) := NormedAlgebra.restrictScalars ℝ ℂ _

theorem variationBetween_continuous (C B : E →L[ℂ] E) (t : ℝ) :
    Continuous (fun r : ℝ=>variationBetween C B r t) := by
  apply intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
  change Continuous (fun x : ℝ×ℝ=>time (C+x.1 • B) x.2 * ((-Complex.I) • B) * time C (t-x.2))
  unfold SourceFiniteUnitary.time
  fun_prop

/-- The original Duhamel identity yields the perturbation derivative also for the raw,
non-self-adjoint Yukawa generator. -/
theorem parameter_derivative_full (C B : E →L[ℂ] E) (t : ℝ) :
    HasDerivAt (fun r : ℝ=>time (C+r • B) t) (variation C B t) 0 := by
  rw [hasDerivAt_iff_tendsto_slope]
  have limit : Filter.Tendsto (fun r : ℝ=>variationBetween C B r t) (𝓝[≠] 0) (𝓝 (variation C B t)) :=
    ((variationBetween_continuous C B t).tendsto 0).mono_left nhdsWithin_le_nhds
  apply limit.congr'
  filter_upwards [self_mem_nhdsWithin] with r hr
  have nonzero : r≠0 := hr
  simp only [slope,sub_zero,zero_smul,add_zero,vsub_eq_sub,parameter_difference]
  rw [smul_smul,inv_mul_cancel₀ nonzero,one_smul]

end Variation

abbrev Op := H →L[ℂ] H
local instance : NormedAlgebra ℝ Op := NormedAlgebra.restrictScalars ℝ ℂ _

theorem actual_fullY_field_derivative (f : PreparationVacuumMixedFieldReturn.Field289)
    (p : PhysicalMomentum) (phi : PreparationVacuumSourceFieldFamily.Localizer)
    (cut : ℕ) (F : Index) (t : ℝ) :
    HasDerivAt (fun r : ℝ=>time
      (compression p F+cutoff cut+r • PreparationVacuumSourceFieldFamily.localizedGauss f p phi) t)
      (variation (compression p F+cutoff cut)
        (PreparationVacuumSourceFieldFamily.localizedGauss f p phi) t) 0 :=
  parameter_derivative_full _ _ t

end LowEnergy.PreparationVacuumCausalFieldResponse
