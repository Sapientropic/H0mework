import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.BasinRefinement.Continuous.WholeBand.GlobalSource.Differential.Path

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinRefinement.GlobalSource.Differential
open SourceGaussianModel
open _root_.LAlanineTrueFlowDifferential
noncomputable section

theorem field_lipschitz : LipschitzWith 1 field := by
  apply lipschitzWith_of_nnnorm_fderiv_le (fun x => (field_hasFDerivAt x).differentiableAt)
  intro x
  rw [(field_hasFDerivAt x).fderiv]
  exact_mod_cast derivative_bound x

theorem path_field_distance (u v : Path) : ‖fieldOnPath u-fieldOnPath v‖ ≤ ‖u-v‖ := by
  apply (ContinuousMap.norm_le _ (norm_nonneg _)).mpr
  intro t
  have bound := field_lipschitz.norm_sub_le (u t) (v t)
  change ‖field (u t)-field (v t)‖ ≤ _
  have localBound : ‖field (u t)-field (v t)‖ ≤ ‖u t-v t‖ := by
    simpa only [NNReal.coe_one,one_mul] using bound
  exact localBound.trans ((u-v).norm_coe_le_norm t)

theorem solvedPath_eq_actual (x : Point) (u : Path)
    (equation : u = pathConst x+volterra (fieldOnPath u)) : u = actualPath x := by
  have difference : u-actualPath x = volterra (fieldOnPath u-fieldOnPath (actualPath x)) := by
    rw [map_sub]
    linear_combination equation-path_integral_equation x
  have bound : ‖u-actualPath x‖ ≤ (1/2 : ℝ)*‖u-actualPath x‖ := by
    calc
      _ = ‖volterra (fieldOnPath u-fieldOnPath (actualPath x))‖ := congrArg norm difference
      _ ≤ ‖volterra‖*‖fieldOnPath u-fieldOnPath (actualPath x)‖ := volterra.le_opNorm _
      _ ≤ (1/2 : ℝ)*‖u-actualPath x‖ :=
        mul_le_mul norm_volterra_le (path_field_distance u (actualPath x)) (norm_nonneg _) (by norm_num)
  have zero : ‖u-actualPath x‖ = 0 := by nlinarith [norm_nonneg (u-actualPath x)]
  exact sub_eq_zero.mp (norm_eq_zero.mp zero)

end
end LAlanine40K2025.BasinRefinement.GlobalSource.Differential
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
