import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Flow
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Material
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.StarBounds

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive
open Propagation.Interface Propagation.Producer Load.Source
open scoped Matrix BigOperators Matrix.Norms.L2Operator
noncomputable section

def numericBlock (a b : Basis) (M : Material a b) : Matrix (Fin 8) (Fin 8) ℂ :=
  splice (starAssembly (sourceDelta a b : ℂ) (fun k => Scalar.value (M.plus k)))
    (starAssembly (sourceDelta a b : ℂ) (fun k => Scalar.value (M.minus k)))
    (Scalar.value M.upper) (Scalar.value M.lower)

def sourceBlock (a b : Basis) : Matrix (Fin 8) (Fin 8) ℂ :=
  splice (starAssembly (sourceDelta a b : ℂ) (fun k => Scalar.value (sourceCoefficient a b 1 k)))
    (starAssembly (sourceDelta a b : ℂ) (fun k => Scalar.value (sourceCoefficient a b 3 k)))
    (Scalar.value (Scalar.polynomial (Primitive.scalarSeed (sourceSum a b 5) 1) 14))
    (Scalar.value (Scalar.polynomial (Primitive.scalarSeed (sourceSum a b (-1)) 1) 14))

def numericLoad (a b : Basis) (M : Material a b) : Matrix NativeIndex NativeIndex ℂ :=
  (basis*numericBlock a b M*inverse).submatrix flatten flatten

theorem source_scalar_value (a b : Basis) (offset : ℚ) :
    Scalar.value (Scalar.polynomial (Primitive.scalarSeed (sourceSum a b offset) 1) 14)=
      Primitive.scalarPolynomial ((((nativeClockStep : ℝ) : ℂ)*(-Complex.I))*
        ((Donor.calculatedEnergy a : ℂ)+Donor.calculatedEnergy b+(offset : ℂ))) 14 := by
  rw [Scalar.value_polynomial,Primitive.scalar_seed_original]
  simp only [Rat.cast_one,one_mul,source_sum_value]
  rfl

theorem source_block_original (a b : Basis) : sourceBlock a b=
    sharedValue (Donor.calculatedEnergy a) (Donor.calculatedEnergy b) (nativeClockStep : ℝ) := by
  unfold sourceBlock sharedValue
  simp only [original_source_coefficient,source_delta_value,source_scalar_value,Rat.cast_ofNat,
    Rat.cast_neg,Rat.cast_one,sub_eq_add_neg]

private theorem join_sub {ι κ : Type*} (A C : Matrix ι ι ℂ) (B D : Matrix κ κ ℂ) :
    Matrix.fromBlocks A 0 0 B-Matrix.fromBlocks C 0 0 D=Matrix.fromBlocks (A-C) 0 0 (B-D) := by
  simp only [sub_eq_add_neg,Matrix.fromBlocks_neg,Matrix.fromBlocks_add,neg_zero,add_zero]

theorem raw_sub (M N U V : Matrix (Fin 3) (Fin 3) ℂ) (a b c d : ℂ) :
    raw M N a b-raw U V c d=raw (M-U) (N-V) (a-c) (b-d) := by
  simp only [raw,join_sub,← map_sub]

theorem splice_sub (M N U V : Matrix (Fin 3) (Fin 3) ℂ) (a b c d : ℂ) :
    splice M N a b-splice U V c d=splice (M-U) (N-V) (a-c) (b-d) :=
  congrArg (fun A : Matrix RawIndex RawIndex ℂ => A.submatrix joinEquiv.symm joinEquiv.symm) (raw_sub M N U V a b c d)

end
end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
