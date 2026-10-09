import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Order.Normalization

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite
open Propagation.Interface Load.Source Scaled.Order
open scoped Matrix MatrixOrder ComplexOrder Matrix.Norms.L2Operator
noncomputable section

def donorProjection : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ :=
  Matrix.diagonal (fun i => if i.1=1 then (1 : ℂ) else 0)

private theorem diagonal_left_restriction {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (d : ι → ℂ) (M : Matrix ι ι ℂ) (f : κ → ι) :
    (Matrix.diagonal d*M).submatrix f f=Matrix.diagonal (fun i => d (f i))*M.submatrix f f := by
  ext i j
  simp only [Matrix.submatrix_apply,Matrix.diagonal_mul]

private theorem diagonal_right_restriction {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (d : ι → ℂ) (M : Matrix ι ι ℂ) (f : κ → ι) :
    (M*Matrix.diagonal d).submatrix f f=M.submatrix f f*Matrix.diagonal (fun i => d (f i)) := by
  ext i j
  simp only [Matrix.submatrix_apply,Matrix.mul_diagonal]

theorem source_donor_left : (numericProjector*loadInteraction).submatrix (diagonalPCE 97) (diagonalPCE 97)=
    donorProjection*controllerEnvironmentExchange := by
  rw [projector_diagonal,diagonal_left_restriction,diagonal_CE]
  congr 1
  ext i j
  simp [donorProjection,diagonalPCE,Donor.calculatedTop]

theorem source_donor_right : (loadInteraction*numericProjector).submatrix (diagonalPCE 97) (diagonalPCE 97)=
    controllerEnvironmentExchange*donorProjection := by
  rw [projector_diagonal,diagonal_right_restriction,diagonal_CE]
  congr 1
  ext i j
  simp [donorProjection,diagonalPCE,Donor.calculatedTop]

def donorCore : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ :=
  diagonalOrdinary (Donor.calculatedEnergy 97)+
    (-(sineHat : ℂ)^2-Complex.I*cosineHat*sineHat) • (donorProjection*controllerEnvironmentExchange)+
    (-(sineHat : ℂ)^2+Complex.I*cosineHat*sineHat) • (controllerEnvironmentExchange*donorProjection)

private theorem restrict_expression {ι κ : Type*} (H D L R : Matrix ι ι ℂ)
    (s l r : ℂ) (f : κ → ι) :
    (H-s • D+l • L+r • R).submatrix f f=
      H.submatrix f f-s • D.submatrix f f+l • L.submatrix f f+r • R.submatrix f f := rfl

theorem source_donor_core : rationalCore.submatrix (diagonalPCE 97) (diagonalPCE 97)=donorCore := by
  rw [rationalCore,restrict_expression,source_donor_left,source_donor_right,numeric_diagonal_load,diagonal_environment]
  rfl

end
end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
