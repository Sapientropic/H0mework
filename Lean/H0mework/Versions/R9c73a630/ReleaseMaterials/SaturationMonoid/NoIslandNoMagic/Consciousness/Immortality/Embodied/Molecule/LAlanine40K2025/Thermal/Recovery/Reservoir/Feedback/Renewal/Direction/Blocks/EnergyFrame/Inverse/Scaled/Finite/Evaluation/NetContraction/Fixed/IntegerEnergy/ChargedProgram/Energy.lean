import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed.IntegerEnergy.ChargedProgram.Source

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed
open Propagation.Interface Contraction Load.Source
open scoped BigOperators

def chargedWeightedInt (a b : Basis)
    (V : MatrixInt (OrdinaryFull ⊕ OrdinaryFull) (Fin 2 × Fin 2)) :
    MatrixInt (Fin 2 × Fin 2) (OrdinaryFull ⊕ OrdinaryFull) :=
  let pc := quantize (ordinaryPCFullQ a b)
  pairCols
    (multiply (adjoint (submatrix V Sum.inl id)) pc)
    (multiply (adjoint (submatrix V Sum.inr id)) pc)

theorem charged_weighted_original (a b : Basis)
    (V : MatrixInt (OrdinaryFull ⊕ OrdinaryFull) (Fin 2 × Fin 2)) :
    chargedWeightedInt a b V = multiply (adjoint V) (sourceOrdinaryPCInt a b) := by
  have rows := pair_rows_decomposition V
  calc
    chargedWeightedInt a b V =
      multiply
        (pairCols (adjoint (submatrix V Sum.inl id))
          (adjoint (submatrix V Sum.inr id)))
        (intFourBlocks (quantize (ordinaryPCFullQ a b))
          zeroIntBlock zeroIntBlock (quantize (ordinaryPCFullQ a b))) := by
            unfold chargedWeightedInt
            exact (weighted_pair_columns _ _ _).symm
    _ = multiply (adjoint V) (sourceOrdinaryPCInt a b) := by
      rw [← adjoint_pair_rows,rows,ordinary_pc_pointer_blocks]

def chargedQuadraticInt (a b : Basis)
    (V : MatrixInt (OrdinaryFull ⊕ OrdinaryFull) (Fin 2 × Fin 2)) :
    MatrixInt (Fin 2 × Fin 2) (Fin 2 × Fin 2) :=
  multiply (chargedWeightedInt a b V) V

theorem charged_quadratic_original (a b : Basis)
    (V : MatrixInt (OrdinaryFull ⊕ OrdinaryFull) (Fin 2 × Fin 2)) :
    chargedQuadraticInt a b V =
      multiply (multiply (adjoint V) (sourceOrdinaryPCInt a b)) V := by
  rw [chargedQuadraticInt,charged_weighted_original]

def chargedNetInt (a b : Basis) (ordered : a < b) :
    MatrixInt (Fin 2 × Fin 2) (Fin 2 × Fin 2) :=
  sub (chargedQuadraticInt a b (chargedElevenInt a b ordered))
    (chargedQuadraticInt a b (chargedNineInt a b ordered))

theorem charged_net_original (a b : Basis) (ordered : a < b) :
    chargedNetInt a b ordered = sourceOrdinaryNetInt a b ordered := by
  rw [chargedNetInt,charged_quadratic_original,charged_quadratic_original,
    charged_eleven_original,charged_nine_original,sourceOrdinaryNetInt]

def chargedGainNumeratorInt (a b : Basis) (ordered : a < b) : Int :=
  ∑ i : Fin 2 × Fin 2,
    (multiply (chargedNetInt a b ordered) (sourceOrdinaryBodyInt a b)).re i i

theorem charged_gain_original (a b : Basis) (ordered : a < b) :
    chargedGainNumeratorInt a b ordered =
      sourceOrdinaryGainNumeratorInt a b ordered := by
  rw [chargedGainNumeratorInt,charged_net_original,
    sourceOrdinaryGainNumeratorInt,sourceOrdinaryEnergyProductInt]

end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
