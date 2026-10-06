import H0mework.Versions.AB.Physics.LowEnergy.FullQuantum.GaugeGreen.State

/-! A source-controlled finite Neumann step preserves the actual gauge equation. -/
set_option autoImplicit false
namespace SaturationMonoid.PhysicsCore.LowEnergy.FullQuantum.GaugeGreen
open FullSpace ProofFreeRicherAnholonomicSource PerturbedGreen
noncomputable section

theorem step_small (point : BasePoint) (energy damping : ℝ) (positive : 0<damping)
    (W : SpatialOperators) (symmetric : IsSelfAdjoint W) (parameter delta : ℝ)
    (generated : ResolventAt point energy damping positive W parameter)
    (small : |delta| *damping⁻¹*‖W‖<1) :
    ‖(delta : ℂ) • (generated.value*(-W))‖<1 := by
  rw [norm_smul,Complex.norm_real,Real.norm_eq_abs]
  calc
    _ ≤ |delta| *(damping⁻¹*‖W‖) := by
      apply mul_le_mul_of_nonneg_left _ (abs_nonneg delta)
      exact (norm_mul_le _ _).trans (by
        rw [norm_neg]
        exact mul_le_mul_of_nonneg_right (generated.norm point energy damping positive W symmetric parameter) (norm_nonneg _))
    _ < 1 := by simpa only [mul_assoc] using small

private theorem inverse_fixed (G W : SpatialOperators) (delta : ℝ)
    (small : ‖(delta : ℂ) • (G*(-W))‖<1) (source : FullMatterL2) :
    PerturbedGreen.response G (-W) (delta : ℂ) source=
      G (source+(delta : ℂ) • W (PerturbedGreen.response G (-W) (delta : ℂ) source)) := by
  let field := PerturbedGreen.response G (-W) (delta : ℂ) source
  have inverse := Ring.mul_inverse_cancel _ (PerturbedGreen.correction_isUnit G (-W) (delta : ℂ) small)
  have read := congrArg (fun A : SpatialOperators => A (G source)) inverse
  change field+(delta : ℂ) • G (-(W field))=G source at read
  rw [map_neg,smul_neg] at read
  rw [← sub_eq_add_neg] at read
  change field=G (source+(delta : ℂ) • W field)
  rw [map_add,map_smul]
  exact sub_eq_iff_eq_add.mp read

def advance (point : BasePoint) (energy damping : ℝ) (positive : 0<damping)
    (W : SpatialOperators) (symmetric : IsSelfAdjoint W) (parameter delta : ℝ)
    (generated : ResolventAt point energy damping positive W parameter)
    (small : |delta| *damping⁻¹*‖W‖<1) : ResolventAt point energy damping positive W (parameter+delta) where
  value := PerturbedGreen.response generated.value (-W) (delta : ℂ)
  solves source := by
    let field := PerturbedGreen.response generated.value (-W) (delta : ℂ) source
    have fixed : field=generated.value (source+(delta : ℂ) • W field) :=
      inverse_fixed generated.value W delta (step_small point energy damping positive W symmetric parameter delta generated small) source
    have previous := generated.solves (source+(delta : ℂ) • W field)
    rw [← fixed] at previous
    change field=freeR point energy damping positive (source+((parameter+delta : ℝ) : ℂ) • W field)
    calc
      _ = freeR point energy damping positive ((source+(delta : ℂ) • W field)+(parameter : ℂ) • W field) := previous
      _ = _ := by
        congr 1
        rw [Complex.ofReal_add,add_smul]
        abel

end
end SaturationMonoid.PhysicsCore.LowEnergy.FullQuantum.GaugeGreen
