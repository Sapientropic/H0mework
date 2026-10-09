import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed.SharpPulses.Consumer
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed.ConcreteOrdinary.Energy
set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed
open Propagation.Interface Load.Source Load.Producer.StrictThermal Contraction Evaluate
open scoped Matrix BigOperators Matrix.Norms.L2Operator
noncomputable section

def sourceFirstPCInt : MatrixInt (OrdinaryFull ⊕ OrdinaryFull)
    (OrdinaryFull ⊕ OrdinaryFull) :=
  quantize (ordinaryPCPointerQ (0 : Basis) (1 : Basis))

def sourceFirstNineSelectedInt : MatrixInt (OrdinaryFull ⊕ OrdinaryFull)
    (Fin 2 × Fin 2) := submatrix sourceFirstNineInt id chargedInjection

def sourceFirstElevenSelectedInt : MatrixInt (OrdinaryFull ⊕ OrdinaryFull)
    (Fin 2 × Fin 2) := submatrix sourceFirstElevenInt id chargedInjection

def sourceFirstNetInt : MatrixInt (Fin 2 × Fin 2) (Fin 2 × Fin 2) :=
  sub
    (multiply (multiply (adjoint sourceFirstElevenSelectedInt) sourceFirstPCInt)
      sourceFirstElevenSelectedInt)
    (multiply (multiply (adjoint sourceFirstNineSelectedInt) sourceFirstPCInt)
      sourceFirstNineSelectedInt)

def sourceFirstBodyInt : MatrixInt (Fin 2 × Fin 2) (Fin 2 × Fin 2) :=
  quantize (qkron (ordinaryPairBlockQ (0 : Basis) (1 : Basis)) environmentQ)

def sourceFirstEnergyProductInt : MatrixInt (Fin 2 × Fin 2) (Fin 2 × Fin 2) :=
  multiply sourceFirstNetInt sourceFirstBodyInt

def sourceFirstGainNumeratorInt : Int :=
  ∑ i : Fin 2 × Fin 2, (sourceFirstEnergyProductInt.re i i)

def sourceFirstGainIntQ : ℚ := (sourceFirstGainNumeratorInt : ℚ) / (scale : ℚ)

theorem source_first_pc_original :
    Spec.pcObservable.submatrix
      (ordinaryPointerAddress (0 : Basis) (1 : Basis) (by decide))
      (ordinaryPointerAddress (0 : Basis) (1 : Basis) (by decide)) =
      ordinaryPCPointerQ (0 : Basis) (1 : Basis) :=
  ordinary_pc_pointer_source 0 1 (by decide)

theorem source_first_gain_original :
    ordinaryFastGainQ (0 : Basis) (1 : Basis) (by decide) =
      smallGainQ (s((0 : Basis),1)) :=
  ordinary_fast_gain_original 0 1 (by decide)

end
end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
