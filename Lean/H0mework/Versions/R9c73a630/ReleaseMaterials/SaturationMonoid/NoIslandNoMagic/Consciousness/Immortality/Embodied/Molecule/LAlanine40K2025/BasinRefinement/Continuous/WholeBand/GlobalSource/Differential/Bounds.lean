import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.BasinRefinement.Continuous.WholeBand.GlobalSource.Differential.Matrix

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinRefinement.GlobalSource.Differential
open SourceGaussianModel
open _root_.LAlanineTrueFlowDifferential
noncomputable section

theorem response_norm (x : Point) (h : Space) : ‖response x h‖ ≤ 2*‖h‖ := by
  have equation := response_integral_equation x h
  have bound : ‖response x h‖ ≤ ‖h‖+(1/2 : ℝ)*‖response x h‖ := by
    calc
      _ = ‖pathConst h+volterra (derivativeOnPath x (response x h))‖ := congrArg norm equation
      _ ≤ ‖pathConst h‖+‖volterra (derivativeOnPath x (response x h))‖ := norm_add_le _ _
      _ ≤ ‖h‖+(1/2 : ℝ)*‖response x h‖ := by
        have first : ‖pathConst h‖ = ‖h‖ := by
          apply le_antisymm
          · exact (ContinuousMap.norm_le _ (norm_nonneg h)).mpr (fun _ => le_rfl)
          · exact (pathConst h).norm_coe_le_norm zeroTime
        rw [first]
        apply add_le_add_right
        calc
          _ ≤ ‖volterra‖*‖derivativeOnPath x (response x h)‖ := volterra.le_opNorm _
          _ ≤ (1/2 : ℝ)*(1*‖response x h‖) :=
            mul_le_mul norm_volterra_le ((derivativeOnPath x).le_opNorm_of_le le_rfl |>.trans
              (mul_le_mul_of_nonneg_right (derivativeOnPath_bound x) (norm_nonneg _))) (norm_nonneg _) (by norm_num)
          _ = _ := by rw [one_mul]
  linarith

theorem flowDerivative_bound (x : Point) (t : Time) : ‖flowDerivative x t‖ ≤ 2 := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
  intro h
  exact (response x h).norm_coe_le_norm t |>.trans (response_norm x h)

theorem responseMatrix_entry_bound (x : Point) (t : Time) (i j : Fin 3) : |responseMatrix x t i j| ≤ 2 := by
  change |responseCurve x (Pi.single j 1) t i| ≤ _
  rw [responseCurve_actual]
  have bound := (norm_le_pi_norm (response x (Pi.single j 1) t) i).trans
    ((response x (Pi.single j 1)).norm_coe_le_norm t |>.trans (response_norm x (Pi.single j 1)))
  simpa only [Real.norm_eq_abs,Pi.norm_single,norm_one,mul_one] using bound

end
end LAlanine40K2025.BasinRefinement.GlobalSource.Differential
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
