import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed.IntegerEnergy.HeadMass.HeadError
set_option autoImplicit false
set_option maxRecDepth 8192
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed
open Propagation.Interface Load.Source Collision Contraction Powered.Dynamics
open scoped Matrix BigOperators Matrix.Norms.L2Operator
noncomputable section

def diagonalChargedSelect (e : Fin 2) : Fin 2 × Fin 2 := (1,e)

def sourceDiagonalColumnsInt (a : Basis) (different : a ≠ 97) :
    MatrixInt (DiagonalFull ⊕ DiagonalFull) (Fin 2 × Fin 2) :=
  quantize (sourceColumnsQ (s(a,a)) (diagonalFullEquiv a different)
    diagonalInjection)

def sourceDiagonalReceivedQ (a : Basis) : MatrixQ (Fin 2 × Fin 2)
    (Fin 2 × Fin 2) :=
  (receivedBlockQ (s(a,a))).submatrix (Scaled.Order.diagonalPCEEquiv a)
    (Scaled.Order.diagonalPCEEquiv a)

def sourceDiagonalReceivedInt (a : Basis) :
    MatrixInt (Fin 2 × Fin 2) (Fin 2 × Fin 2) :=
  quantize (sourceDiagonalReceivedQ a)

def sourceDiagonalEntranceInt (a : Basis) (different : a ≠ 97) :=
  multiply (sourceDiagonalColumnsInt a different) (sourceDiagonalReceivedInt a)

def sourceDiagonalEntranceQ (a : Basis) (different : a ≠ 97) :=
  entranceColumnsQ (s(a,a)) (Scaled.Order.diagonalPCEEquiv a)
    (diagonalFullEquiv a different) diagonalInjection

def sourceDiagonalLoadInt (a : Basis) (different : a ≠ 97) :=
  quantize (coordinateLoadQ (s(a,a)) (diagonalFullEquiv a different))

def sourceDiagonalSupplyInt (a : Basis) (different : a ≠ 97) :=
  quantize (coordinateSupplyQ (s(a,a)) (diagonalFullEquiv a different))

def sourceDiagonalWeakInt (a : Basis) (different : a ≠ 97) :=
  quantize (coordinateWeakQ (s(a,a)) (diagonalFullEquiv a different))

def sourceDiagonalAfterSupply1Int (a : Basis) (different : a ≠ 97) :=
  multiply (sourceDiagonalSupplyInt a different) (sourceDiagonalEntranceInt a different)

def sourceDiagonalAfterSupply1Q (a : Basis) (different : a ≠ 97) :=
  qmultiply (coordinateSupplyQ (s(a,a)) (diagonalFullEquiv a different))
    (sourceDiagonalEntranceQ a different)

def sourceDiagonalAfterSupply2Int (a : Basis) (different : a ≠ 97) :=
  multiply (sourceDiagonalSupplyInt a different) (sourceDiagonalAfterSupply1Int a different)

def sourceDiagonalAfterSupply2Q (a : Basis) (different : a ≠ 97) :=
  qmultiply (coordinateSupplyQ (s(a,a)) (diagonalFullEquiv a different))
    (sourceDiagonalAfterSupply1Q a different)

def sourceDiagonalNineInt (a : Basis) (different : a ≠ 97) :=
  multiply (sourceDiagonalLoadInt a different) (sourceDiagonalAfterSupply2Int a different)

def sourceDiagonalAfterWeakInt (a : Basis) (different : a ≠ 97) :=
  multiply (sourceDiagonalWeakInt a different) (sourceDiagonalNineInt a different)

def sourceDiagonalAfterWeakQ (a : Basis) (different : a ≠ 97) :=
  qmultiply (coordinateWeakQ (s(a,a)) (diagonalFullEquiv a different))
    (nineColumnsQ (s(a,a)) (Scaled.Order.diagonalPCEEquiv a)
      (diagonalFullEquiv a different) diagonalInjection)

def sourceDiagonalElevenInt (a : Basis) (different : a ≠ 97) :=
  multiply (sourceDiagonalLoadInt a different) (sourceDiagonalAfterWeakInt a different)

def sourceDiagonalNineSelectedInt (a : Basis) (different : a ≠ 97) :=
  submatrix (sourceDiagonalNineInt a different) id diagonalChargedSelect

def sourceDiagonalNineSelectedQ (a : Basis) (different : a ≠ 97) :=
  (nineColumnsQ (s(a,a)) (Scaled.Order.diagonalPCEEquiv a)
    (diagonalFullEquiv a different) diagonalInjection).submatrix id
      diagonalChargedSelect

def sourceDiagonalElevenSelectedInt (a : Basis) (different : a ≠ 97) :=
  submatrix (sourceDiagonalElevenInt a different) id diagonalChargedSelect

def sourceDiagonalElevenSelectedQ (a : Basis) (different : a ≠ 97) :=
  (elevenColumnsQ (s(a,a)) (Scaled.Order.diagonalPCEEquiv a)
    (diagonalFullEquiv a different) diagonalInjection).submatrix id
      diagonalChargedSelect

def sourceDiagonalPCInt (a : Basis) (different : a ≠ 97) :=
  quantize (coordinatePCQ (s(a,a)) (diagonalFullEquiv a different))

def sourceDiagonalNetInt (a : Basis) (different : a ≠ 97) :=
  sub
    (multiply (multiply (adjoint (sourceDiagonalElevenSelectedInt a different))
      (sourceDiagonalPCInt a different)) (sourceDiagonalElevenSelectedInt a different))
    (multiply (multiply (adjoint (sourceDiagonalNineSelectedInt a different))
      (sourceDiagonalPCInt a different)) (sourceDiagonalNineSelectedInt a different))

def sourceDiagonalQNet (a : Basis) (different : a ≠ 97) :
    Matrix (Fin 2) (Fin 2) ℂ :=
  ((qvalue (sourceDiagonalElevenSelectedQ a different))ᴴ *
    qvalue (coordinatePCQ (s(a,a)) (diagonalFullEquiv a different))) *
    qvalue (sourceDiagonalElevenSelectedQ a different)-
  ((qvalue (sourceDiagonalNineSelectedQ a different))ᴴ *
    qvalue (coordinatePCQ (s(a,a)) (diagonalFullEquiv a different))) *
    qvalue (sourceDiagonalNineSelectedQ a different)

def sourceDiagonalBodyInt (a : Basis) : MatrixInt (Fin 2) (Fin 2) :=
  quantize (qscale (pairQ (a,a) (a,a)) environmentQ)

def sourceDiagonalEnergyProductInt (a : Basis) (different : a ≠ 97) :=
  multiply (sourceDiagonalNetInt a different) (sourceDiagonalBodyInt a)

def sourceDiagonalGainNumeratorInt (a : Basis) (different : a ≠ 97) : Int :=
  ∑ i : Fin 2, (sourceDiagonalEnergyProductInt a different).re i i

def sourceDiagonalGainIntQ (a : Basis) (different : a ≠ 97) : ℚ :=
  (sourceDiagonalGainNumeratorInt a different : ℚ)/(scale : ℚ)

end
end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
