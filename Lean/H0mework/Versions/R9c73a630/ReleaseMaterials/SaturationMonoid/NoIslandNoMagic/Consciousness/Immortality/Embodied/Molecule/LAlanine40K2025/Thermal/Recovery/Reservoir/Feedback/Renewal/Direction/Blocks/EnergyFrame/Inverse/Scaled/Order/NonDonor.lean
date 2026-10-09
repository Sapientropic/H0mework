import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Order.Load

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Order
open Propagation.Interface Load.Source
open scoped Matrix MatrixOrder ComplexOrder Matrix.Norms.L2Operator
noncomputable section

theorem projector_diagonal : numericProjector=Matrix.diagonal
    (fun i : PairController × Fin 2 => if i.1=((Donor.calculatedTop,Donor.calculatedTop),(1 : Fin 2)) then (1 : ℂ) else 0) := by
  ext i j
  simp only [numericProjector,Donor.calculatedDonor,Spectrum.basisPure,Matrix.kronecker,Matrix.kroneckerMap_apply,
    Matrix.diagonal_apply,Matrix.one_apply]
  by_cases same : i=j
  · subst j
    simp
  · by_cases first : i.1=j.1
    · have second : i.2 ≠ j.2 := fun equal => same (Prod.ext first equal)
      simp [same,first,second]
    · simp [same,first]

theorem orbit_avoids_donor (a b : Basis) (distinct : a ≠ b) (p : Fin 2 × Fin 2) :
    orbitPC a b p ≠ ((Donor.calculatedTop,Donor.calculatedTop),(1 : Fin 2)) := by
  rcases p with ⟨o,c⟩
  fin_cases o <;> simp only [orbitPC,Fin.zero_eta,Fin.isValue,ite_true]
  all_goals
    intro same
    have equal := congrArg Prod.fst same
    have first := congrArg Prod.fst equal
    have second := congrArg Prod.snd equal
    apply distinct
    first | exact first.trans second.symm | exact second.trans first.symm

private theorem diagonal_left_zero {ι κ : Type*} [Fintype ι] [DecidableEq ι]
    (d : ι → ℂ) (M : Matrix ι ι ℂ) (f : κ → ι) (zero : ∀ i, d (f i)=0) :
    (Matrix.diagonal d*M).submatrix f f=0 := by
  ext i j
  simp only [Matrix.submatrix_apply,Matrix.diagonal_mul,zero,zero_mul,Matrix.zero_apply]

private theorem diagonal_right_zero {ι κ : Type*} [Fintype ι] [DecidableEq ι]
    (d : ι → ℂ) (M : Matrix ι ι ℂ) (f : κ → ι) (zero : ∀ i, d (f i)=0) :
    (M*Matrix.diagonal d).submatrix f f=0 := by
  ext i j
  simp only [Matrix.submatrix_apply,Matrix.mul_diagonal,zero,mul_zero,Matrix.zero_apply]

theorem nondonor_left_block (a b : Basis) (distinct : a ≠ b) (M : LoadedJoint) :
    (numericProjector*M).submatrix (orbitPCE a b) (orbitPCE a b)=0 := by
  rw [projector_diagonal]
  exact diagonal_left_zero _ M (orbitPCE a b) (by
    intro i
    simp only [orbitPCE,orbit_avoids_donor a b distinct i.1,ite_false])

theorem nondonor_right_block (a b : Basis) (distinct : a ≠ b) (M : LoadedJoint) :
    (M*numericProjector).submatrix (orbitPCE a b) (orbitPCE a b)=0 := by
  rw [projector_diagonal]
  exact diagonal_right_zero _ M (orbitPCE a b) (by
    intro i
    simp only [orbitPCE,orbit_avoids_donor a b distinct i.1,ite_false])

end
end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Order
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
