import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadDiagonal.Source
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadDiagonal.Material
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.MatrixSource

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadDiagonal
open Propagation.Interface Propagation.Producer Load.Source
open scoped Matrix BigOperators Matrix.Norms.L2Operator
noncomputable section

def sourceRaw (a : Basis) : Matrix RawIndex RawIndex ℂ :=
  raw (middle (fun k => Scalar.value (LoadPrimitive.sourceCoefficient a a 3 k)))
    (Scalar.value (Scalar.polynomial (Primitive.scalarSeed (LoadPrimitive.sourceSum a a 1) 1) 14))
    (Scalar.value (Scalar.polynomial (Primitive.scalarSeed (LoadPrimitive.sourceSum a a 5) 1) 14))

def numericMiddle (a : Basis) (M : Material a) : Matrix (Fin 2) (Fin 2) ℂ :=
  middle ![Scalar.value M.centre,Scalar.value M.beta,Scalar.value M.gamma]

def numericRaw (a : Basis) (M : Material a) : Matrix RawIndex RawIndex ℂ :=
  raw (numericMiddle a M) (Scalar.value M.lower) (Scalar.value M.upper)

def numericLoad (a : Basis) (M : Material a) : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ :=
  (numericRaw a M).submatrix toNative.symm toNative.symm

theorem source_coefficients (a : Basis) :
    (fun k => Scalar.value (LoadPrimitive.sourceCoefficient a a 3 k))=
      LoadPrimitive.coefficientPolynomial (2*(Donor.calculatedEnergy a : ℂ)+3) 0
        (((nativeClockStep : ℝ) : ℂ)*(-Complex.I)) 14 := by
  funext k
  simpa only [Rat.cast_ofNat,sub_self,two_mul] using LoadPrimitive.original_source_coefficient a a 3 k

theorem source_raw_original (a : Basis) : sourceRaw a=rawValue (Donor.calculatedEnergy a) (nativeClockStep : ℝ) := by
  unfold sourceRaw rawValue
  rw [source_coefficients,LoadPrimitive.source_scalar_value,LoadPrimitive.source_scalar_value]
  simp only [Rat.cast_one,Rat.cast_ofNat,two_mul]

private theorem join_sub {ι κ : Type*} (A C : Matrix ι ι ℂ) (B D : Matrix κ κ ℂ) :
    Matrix.fromBlocks A 0 0 B-Matrix.fromBlocks C 0 0 D=Matrix.fromBlocks (A-C) 0 0 (B-D) := by
  simp only [sub_eq_add_neg,Matrix.fromBlocks_neg,Matrix.fromBlocks_add,neg_zero,add_zero]

theorem raw_sub (M N : Matrix (Fin 2) (Fin 2) ℂ) (a b c d : ℂ) :
    raw M a b-raw N c d=raw (M-N) (a-c) (b-d) := by
  simp only [raw,join_sub,← map_sub]

theorem raw_norm (M : Matrix (Fin 2) (Fin 2) ℂ) (a b : ℂ) :
    ‖raw M a b‖ ≤ max ‖a‖ (max ‖M‖ ‖b‖) := by
  unfold raw
  apply (LoadPrimitive.join_norm _ _).trans
  rw [LoadPrimitive.scalar_norm]
  apply max_le_max (le_refl _) ((LoadPrimitive.join_norm _ _).trans ?_)
  rw [LoadPrimitive.scalar_norm]

end
end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadDiagonal
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
