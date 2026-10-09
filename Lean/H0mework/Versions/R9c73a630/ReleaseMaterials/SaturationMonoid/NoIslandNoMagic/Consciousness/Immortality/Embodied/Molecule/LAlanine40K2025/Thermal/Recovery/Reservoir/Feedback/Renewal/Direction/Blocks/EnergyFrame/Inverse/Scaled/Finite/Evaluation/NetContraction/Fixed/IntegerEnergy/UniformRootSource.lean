import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed.IntegerEnergy.UniformRootBound
set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed
open Propagation.Interface RationalMatrix SquareRoot
open scoped Matrix MatrixOrder ComplexOrder Matrix.Norms.L2Operator
noncomputable section

private theorem ordinary_effect_complement (a b : Basis) :
    SquareRoot.Full.ordinaryEffect a b (-1)=
      1-SquareRoot.Full.ordinaryEffect a b 1 := by
  simp only [SquareRoot.Full.ordinaryEffect,effect_cast,Rat.cast_one,Rat.cast_neg,
    one_smul,neg_one_smul,normalized_complement]

theorem source_ordinary_factor_norms_two (a b : Basis) (ordered : a < b) :
    ‖qvalue (factorQ (SquareRoot.Full.allOrdinary a b ordered).1)‖ ≤ (2 : ℝ) ∧
    ‖qvalue (factorQ (SquareRoot.Full.allOrdinary a b ordered).2)‖ ≤ (2 : ℝ) := by
  let G := SquareRoot.Full.allOrdinary a b ordered
  have positive := SquareRoot.Full.ordinary_positive a b ordered.ne
  have complementPlus : 0 ≤ (1 : Matrix (Fin 8) (Fin 8) ℂ)-
      SquareRoot.Full.ordinaryEffect a b 1 := by
    rw [← ordinary_effect_complement]
    exact positive.2
  have complementMinus : 0 ≤ (1 : Matrix (Fin 8) (Fin 8) ℂ)-
      SquareRoot.Full.ordinaryEffect a b (-1) := by
    rw [ordinary_effect_complement]
    simpa using positive.1
  constructor
  · exact factor_norm_two_of_effect G.1 positive.1 complementPlus
  · exact factor_norm_two_of_effect G.2 positive.2 complementMinus

def sourceOrdinaryRootInt (a b : Basis) (ordered : a < b) :
    MatrixInt LoadPrimitive.NativeIndex LoadPrimitive.NativeIndex :=
  submatrix (gramInt (SquareRoot.Full.allOrdinary a b ordered).1)
    tripleIndex tripleIndex

def sourceOrdinaryComplementInt (a b : Basis) (ordered : a < b) :
    MatrixInt LoadPrimitive.NativeIndex LoadPrimitive.NativeIndex :=
  submatrix (gramInt (SquareRoot.Full.allOrdinary a b ordered).2)
    tripleIndex tripleIndex

theorem source_ordinary_gram_errors (a b : Basis) (ordered : a < b) :
    ‖value (gramInt (SquareRoot.Full.allOrdinary a b ordered).1)-
      qvalue (rootGramQ (SquareRoot.Full.allOrdinary a b ordered).1)‖ ≤
        (1/10^25 : ℝ) ∧
    ‖value (gramInt (SquareRoot.Full.allOrdinary a b ordered).2)-
      qvalue (rootGramQ (SquareRoot.Full.allOrdinary a b ordered).2)‖ ≤
        (1/10^25 : ℝ) := by
  have factors := source_ordinary_factor_norms_two a b ordered
  constructor
  · exact (gram_int_error _ (by norm_num)
      (factors.1.trans (by norm_num))).trans (by norm_num)
  · exact (gram_int_error _ (by norm_num)
      (factors.2.trans (by norm_num))).trans (by norm_num)

theorem source_ordinary_root_int_error (a b : Basis) (ordered : a < b) :
    ‖value (sourceOrdinaryRootInt a b ordered)-qvalue (rootOrdinaryQ a b ordered)‖ ≤
      (1/10^25 : ℝ) := by
  rw [sourceOrdinaryRootInt,rootOrdinaryQ,value_submatrix,qvalue_submatrix]
  change ‖(value (gramInt (SquareRoot.Full.allOrdinary a b ordered).1)-
    qvalue (rootGramQ (SquareRoot.Full.allOrdinary a b ordered).1)).submatrix
      tripleIndex tripleIndex‖ ≤ _
  rw [Finite.reindex_norm]
  exact (source_ordinary_gram_errors a b ordered).1

theorem source_ordinary_complement_int_error (a b : Basis) (ordered : a < b) :
    ‖value (sourceOrdinaryComplementInt a b ordered)-
      qvalue (complementOrdinaryQ a b ordered)‖ ≤ (1/10^25 : ℝ) := by
  rw [sourceOrdinaryComplementInt,complementOrdinaryQ,value_submatrix,qvalue_submatrix]
  change ‖(value (gramInt (SquareRoot.Full.allOrdinary a b ordered).2)-
    qvalue (rootGramQ (SquareRoot.Full.allOrdinary a b ordered).2)).submatrix
      tripleIndex tripleIndex‖ ≤ _
  rw [Finite.reindex_norm]
  exact (source_ordinary_gram_errors a b ordered).2

end
end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
