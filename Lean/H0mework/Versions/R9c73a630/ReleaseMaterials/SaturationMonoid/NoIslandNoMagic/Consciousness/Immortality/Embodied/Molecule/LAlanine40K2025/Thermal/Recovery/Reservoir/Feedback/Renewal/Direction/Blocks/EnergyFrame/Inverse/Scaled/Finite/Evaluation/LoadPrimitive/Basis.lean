import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Primitive.LocalFlows

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive
open Propagation.Interface Load.Source
open scoped Matrix BigOperators Matrix.Norms.L2Operator
noncomputable section

abbrev NativeIndex := (Fin 2 × Fin 2) × Fin 2

def flatten : NativeIndex ≃ Fin 8 :=
  (Equiv.prodCongr (finProdFinEquiv : Fin 2 × Fin 2 ≃ Fin 4) (Equiv.refl (Fin 2))).trans finProdFinEquiv

def basisQ : Matrix (Fin 8) (Fin 8) ℚ :=
  !![1,0,0,0,1,0,0,0;
     0,1,0,0,0,0,0,1;
     0,0,1,0,0,0,1,0;
     0,0,0,1,0,1,0,0;
     1,0,0,0,-1,0,0,0;
     0,-1,0,0,0,0,0,1;
     0,0,-1,0,0,0,1,0;
     0,0,0,1,0,-1,0,0]

def inverseQ : Matrix (Fin 8) (Fin 8) ℚ := (1/2 : ℚ) • basisQ.transpose

def castMatrix (A : Matrix (Fin 8) (Fin 8) ℚ) : Matrix (Fin 8) (Fin 8) ℂ := fun i j => (A i j : ℂ)

def basis : Matrix (Fin 8) (Fin 8) ℂ := castMatrix basisQ

def inverse : Matrix (Fin 8) (Fin 8) ℂ := castMatrix inverseQ

theorem rational_basis_left : inverseQ*basisQ=1 := by decide +kernel

theorem rational_basis_right : basisQ*inverseQ=1 := by decide +kernel

theorem cast_mul (A B : Matrix (Fin 8) (Fin 8) ℚ) : castMatrix (A*B)=castMatrix A*castMatrix B := by
  ext i j
  simp only [castMatrix,Matrix.mul_apply,Rat.cast_sum,Rat.cast_mul]

theorem cast_one : castMatrix 1=1 := by
  ext i j
  by_cases same : i=j <;> simp [castMatrix,Matrix.one_apply,same]

theorem basis_left : inverse*basis=1 := by
  rw [inverse,basis,← cast_mul,rational_basis_left,cast_one]

theorem basis_right : basis*inverse=1 := by
  rw [inverse,basis,← cast_mul,rational_basis_right,cast_one]

end
end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
