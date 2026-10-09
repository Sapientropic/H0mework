import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed.IntegerEnergy.UniformPulseConsumer
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed.IntegerEnergy.Base
set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed
open Propagation.Interface Load.Source Load.Producer.StrictThermal Contraction Evaluate
open scoped Matrix BigOperators Matrix.Norms.L2Operator
noncomputable section

def sourceOrdinaryPCInt (a b : Basis) :
    MatrixInt (OrdinaryFull ⊕ OrdinaryFull) (OrdinaryFull ⊕ OrdinaryFull) :=
  quantize (ordinaryPCPointerQ a b)

def sourceOrdinaryNineSelectedInt (a b : Basis) (ordered : a < b) :
    MatrixInt (OrdinaryFull ⊕ OrdinaryFull) (Fin 2 × Fin 2) :=
  submatrix (sourceOrdinaryNineInt a b ordered) id chargedInjection

def sourceOrdinaryElevenSelectedInt (a b : Basis) (ordered : a < b) :
    MatrixInt (OrdinaryFull ⊕ OrdinaryFull) (Fin 2 × Fin 2) :=
  submatrix (sourceOrdinaryElevenInt a b ordered) id chargedInjection

def sourceOrdinaryNetInt (a b : Basis) (ordered : a < b) :
    MatrixInt (Fin 2 × Fin 2) (Fin 2 × Fin 2) :=
  sub
    (multiply (multiply (adjoint (sourceOrdinaryElevenSelectedInt a b ordered))
      (sourceOrdinaryPCInt a b)) (sourceOrdinaryElevenSelectedInt a b ordered))
    (multiply (multiply (adjoint (sourceOrdinaryNineSelectedInt a b ordered))
      (sourceOrdinaryPCInt a b)) (sourceOrdinaryNineSelectedInt a b ordered))

def sourceOrdinaryBodyInt (a b : Basis) :
    MatrixInt (Fin 2 × Fin 2) (Fin 2 × Fin 2) :=
  quantize (qkron (ordinaryPairBlockQ a b) environmentQ)

def sourceOrdinaryEnergyProductInt (a b : Basis) (ordered : a < b) :
    MatrixInt (Fin 2 × Fin 2) (Fin 2 × Fin 2) :=
  multiply (sourceOrdinaryNetInt a b ordered) (sourceOrdinaryBodyInt a b)

def sourceOrdinaryGainNumeratorInt (a b : Basis) (ordered : a < b) : Int :=
  ∑ i : Fin 2 × Fin 2, (sourceOrdinaryEnergyProductInt a b ordered).re i i

def sourceOrdinaryGainIntQ (a b : Basis) (ordered : a < b) : ℚ :=
  (sourceOrdinaryGainNumeratorInt a b ordered : ℚ)/(scale : ℚ)

def sourceOrdinaryQNet (a b : Basis) (ordered : a < b) :
    Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ :=
  ((qvalue ((ordinaryElevenColumnsQ a b ordered).submatrix id chargedInjection))ᴴ *
    qvalue (ordinaryPCPointerQ a b)) *
    qvalue ((ordinaryElevenColumnsQ a b ordered).submatrix id chargedInjection)-
  ((qvalue ((ordinaryNineColumnsQ a b ordered).submatrix id chargedInjection))ᴴ *
    qvalue (ordinaryPCPointerQ a b)) *
    qvalue ((ordinaryNineColumnsQ a b ordered).submatrix id chargedInjection)

theorem source_first_gain_program_same :
    sourceOrdinaryGainIntQ (0 : Basis) (1 : Basis) (by decide)=
      sourceFirstGainIntQ := rfl

theorem source_first_net_program_same :
    sourceOrdinaryNetInt (0 : Basis) (1 : Basis) (by decide)=
      sourceFirstNetInt := rfl

end
end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
