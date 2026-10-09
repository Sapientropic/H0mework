import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed.IntegerEnergy.ChargedProgram.ThirdSpectrum
set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed
open scoped Matrix MatrixOrder ComplexOrder Matrix.Norms.L2Operator
noncomputable section

theorem energy_lower_from_order
    (A rho : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ)
    (hrho : rho.PosSemidef) (floor : ℝ)
    (hfloor : floor • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) ≤ A) :
    floor*rho.trace.re ≤ (A*rho).trace.re := by
  let P := A-floor • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ)
  have hP : P.PosSemidef := Matrix.nonneg_iff_posSemidef.mp (sub_nonneg.mpr hfloor)
  obtain ⟨B,hB⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hrho.nonneg
  have hp := hP.mul_mul_conjTranspose_same B
  have htr : 0 ≤ (B*P*Bᴴ).trace.re := (Complex.nonneg_iff.mp hp.trace_nonneg).1
  have cyc : (P*rho).trace = (B*P*Bᴴ).trace := by
    rw [hB,Matrix.star_eq_conjTranspose]
    rw [← Matrix.mul_assoc]
    exact Matrix.trace_mul_cycle P Bᴴ B
  have scalar : ((floor • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ))*rho).trace.re =
      floor*rho.trace.re := by simp
  have difference : (P*rho).trace.re =
      (A*rho).trace.re-floor*rho.trace.re := by
    dsimp [P]
    rw [sub_mul,Matrix.trace_sub,Complex.sub_re,scalar]
  rw [←cyc] at htr
  linarith only [difference,htr]

end
end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
