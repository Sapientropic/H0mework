import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.NumericFree

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse
open Collision Load.Source
open scoped Matrix MatrixOrder ComplexOrder Matrix.Norms.L2Operator
noncomputable section

theorem coefficients_star : star plusCoefficient=minusCoefficient := by
  simp only [plusCoefficient,minusCoefficient,Complex.star_def,map_sub,map_inv₀,map_add,map_mul,map_pow,
    Complex.conj_ofReal,Complex.conj_I]
  congr 2
  ring

theorem numeric_environment_hermitian : numericEnvironmentRead.IsHermitian := by
  apply Matrix.IsHermitian.add
  · exact Matrix.isHermitian_one.smul (by simp : star (numericDonorEnergy : ℂ)=(numericDonorEnergy : ℂ))
  · exact Powered.Dynamics.controllerHamiltonian_hermitian 2

theorem numeric_projector_hermitian : numericProjector.IsHermitian :=
  ((Spectrum.basisPure_positive ((Donor.calculatedTop,Donor.calculatedTop),(1 : Fin 2))).kronecker Matrix.PosSemidef.one).isHermitian

theorem numeric_core_hermitian : numericCoreInverse.IsHermitian := by
  have env : (Matrix.kronecker (1 : Matrix PairController PairController ℂ) numericEnvironmentRead).IsHermitian :=
    by
      change _ᴴ = _
      simp only [Matrix.kronecker,Matrix.conjTranspose_kronecker,Matrix.conjTranspose_one,numeric_environment_hermitian.eq]
  have realStar (x : ℝ) : star (x : ℂ)=(x : ℂ) := by simp
  have reverse : star minusCoefficient=plusCoefficient := by rw [← coefficients_star,star_star]
  change star numericCoreInverse=numericCoreInverse
  simp only [numericCoreInverse,star_add,star_smul,star_sub,star_mul,star_inv₀,star_pow,realStar,
    actual_numeric_load_hermitian.isSelfAdjoint.star_eq,numeric_projector_hermitian.isSelfAdjoint.star_eq,
    loadInteraction_hermitian.isSelfAdjoint.star_eq,env.isSelfAdjoint.star_eq,coefficients_star,reverse]
  abel

end
end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
