import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed.ConcreteOrdinary.PC
set_option autoImplicit false
set_option maxRecDepth 4096
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed
open Propagation.Interface Load.Source Collision Contraction Evaluate
open scoped Matrix BigOperators
noncomputable section

def ordinaryFastGainQ (a b : Basis) (ordered : a < b) : ℚ :=
  let nine := (ordinaryNineColumnsQ a b ordered).submatrix id chargedInjection
  let eleven := (ordinaryElevenColumnsQ a b ordered).submatrix id chargedInjection
  let pc := ordinaryPCPointerQ a b
  let net := qmultiply (qmultiply (qadjoint eleven) pc) eleven-
    qmultiply (qmultiply (qadjoint nine) pc) nine
  Spec.energyQ net (qkron (ordinaryPairBlockQ a b) environmentQ)

theorem ordinary_fast_gain_value (a b : Basis) (ordered : a < b) :
    (ordinaryFastGainQ a b ordered : ℝ)=Compact.ordinaryEnergy a b ordered.ne := by
  simp only [ordinaryFastGainQ,Spec.energyQ_value,qvalue_sub,qvalue_multiply,
    qvalue_adjoint,qvalue_submatrix,ordinary_nine_columns_value,
    ordinary_eleven_columns_value,qvalue_kron,
    ordinary_pair_block_value,environmentQ_value]
  rw [ordinary_pc_pointer_value a b ordered]
  rfl

theorem ordinary_fast_gain_original (a b : Basis) (ordered : a < b) :
    ordinaryFastGainQ a b ordered=smallGainQ (s(a,b)) := by
  apply Rat.cast_injective (α := ℝ)
  rw [ordinary_fast_gain_value,← Compact.ordinary_energy_exact a b ordered.ne,
    ← block_gain_small,block_gain_value]

end
end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
