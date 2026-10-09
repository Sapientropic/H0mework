import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.BasinRefinement.Continuous.WholeBand.GlobalSource.Differential.Field

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinRefinement.GlobalSource.Differential
open SourceGaussianModel ContinuousGradient Set Filter
open _root_.LAlanineTrueFlowDifferential
noncomputable section

def fieldOnPath : Path → Path := pathComp field field_contDiff
def derivativeOnPath (x : Point) : Path →L[ℝ] Path := pathCompDeriv field field_contDiff (actualPath x)

theorem derivativeOnPath_apply (x : Point) (v : Path) (t : Time) :
    derivativeOnPath x v t = derivative (actualPath x t) (v t) := by
  rw [derivativeOnPath,pathCompDeriv_apply,(field_hasFDerivAt _).fderiv]

theorem derivativeOnPath_bound (x : Point) : ‖derivativeOnPath x‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro v
  apply (ContinuousMap.norm_le _ (by positivity)).mpr
  intro t
  rw [derivativeOnPath_apply]
  exact ((derivative (actualPath x t)).le_opNorm_of_le (v.norm_coe_le_norm t)).trans
    (mul_le_mul_of_nonneg_right (derivative_bound _) (norm_nonneg v))

theorem original_integral_equation (x : Point) (t : Time) :
    actualPath x t = x + volterra (fieldOnPath (actualPath x)) t := by
  have integral := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun u _ => actual_derivative x u)
    ((field_contDiff.continuous.comp ((flow_continuous x).comp (continuous_const.mul continuous_id))).intervalIntegrable 0 (t : ℝ))
  have primitive : volterra (fieldOnPath (actualPath x)) t =
      ∫ u in 0..(t : ℝ), field (flow x (spatialStep*u)) := by
    rw [volterra_apply]
    apply intervalIntegral.integral_congr
    intro u inside
    have inTime : u ∈ Icc (-(1/2) : ℝ) (1/2) :=
      uIcc_subset_Icc (show (0 : ℝ) ∈ Icc (-(1/2) : ℝ) (1/2) by constructor <;> norm_num) t.property inside
    change field (flow x (spatialStep*((projIcc (-(1/2) : ℝ) (1/2) (by norm_num) u : Time) : ℝ))) = _
    rw [projIcc_of_mem _ inTime]
  rw [primitive]
  simp only [mul_zero,flow_starts] at integral
  change flow x (spatialStep*(t : ℝ)) = _
  rw [integral]
  abel

theorem path_integral_equation (x : Point) :
    actualPath x = pathConst x + volterra (fieldOnPath (actualPath x)) := by
  apply ContinuousMap.ext
  intro t
  exact original_integral_equation x t

end
end LAlanine40K2025.BasinRefinement.GlobalSource.Differential
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
