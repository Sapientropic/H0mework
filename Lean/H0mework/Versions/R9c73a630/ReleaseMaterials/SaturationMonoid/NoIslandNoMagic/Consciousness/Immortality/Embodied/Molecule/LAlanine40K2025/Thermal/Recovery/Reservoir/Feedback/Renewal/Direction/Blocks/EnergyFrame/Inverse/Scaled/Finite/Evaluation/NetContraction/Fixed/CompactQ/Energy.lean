import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed.CompactQ.Columns

set_option autoImplicit false
set_option maxRecDepth 8192
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed
open Propagation.Interface Load.Source Collision Contraction Powered.Dynamics
open scoped Matrix BigOperators
noncomputable section
variable {β δ : Type*} [Fintype β] [Fintype δ]
def compactSelectedNetQ {ζ : Type*} (k : Sym2 Basis) (body : β ≃ BodyFiber k)
    (full : δ ≃ FullFiber k) (insert : β → δ) (select : ζ → β) : MatrixQ ζ ζ :=
  let pc := coordinatePCQ k full
  let nine := (nineColumnsQ k body full insert).submatrix id select
  let eleven := (elevenColumnsQ k body full insert).submatrix id select
  qmultiply (qmultiply (qadjoint eleven) pc) eleven-
    qmultiply (qmultiply (qadjoint nine) pc) nine

theorem compact_selected_net_value {ζ : Type*} (k : Sym2 Basis) (body : β ≃ BodyFiber k)
    (full : δ ≃ FullFiber k) (insert : β → δ) (select : ζ → β) :
    qvalue (compactSelectedNetQ k body full insert select)=
      Compact.selectedNet k body full insert select := by
  simp only [compactSelectedNetQ,qvalue_sub,qvalue_multiply,qvalue_adjoint,qvalue_submatrix,
    coordinate_pc_value,nine_columns_value,eleven_columns_value]
  rfl

def ordinaryPairBlockQ (a b : Basis) : MatrixQ (Fin 2) (Fin 2) :=
  pairQ.submatrix (pairAddress a b) (pairAddress a b)

theorem ordinary_pair_block_value (a b : Basis) :
    qvalue (ordinaryPairBlockQ a b)=originalPairBlock a b := by
  rw [ordinaryPairBlockQ,qvalue_submatrix,pairQ_value]
  rfl

def ordinaryCompactGainQ (a b : Basis) (different : a ≠ b) : ℚ :=
  Spec.energyQ
    (compactSelectedNetQ (s(a,b)) (Scaled.Order.offDiagonalPCEEquiv a b different)
      (ordinaryFullEquiv a b different) ordinaryInjection chargedInjection)
    (qkron (ordinaryPairBlockQ a b) environmentQ)

theorem ordinary_compact_gain_value (a b : Basis) (different : a ≠ b) :
    (ordinaryCompactGainQ a b different : ℝ)=Compact.ordinaryEnergy a b different := by
  rw [ordinaryCompactGainQ,Spec.energyQ_value,compact_selected_net_value,
    qvalue_kron,ordinary_pair_block_value,environmentQ_value]
  rfl

theorem ordinary_compact_gain_original (a b : Basis) (different : a ≠ b) :
    ordinaryCompactGainQ a b different=smallGainQ (s(a,b)) := by
  apply Rat.cast_injective (α := ℝ)
  rw [ordinary_compact_gain_value,← Compact.ordinary_energy_exact a b different,
    ← block_gain_small,block_gain_value]

def diagonalCompactGainQ (a : Basis) (different : a ≠ 97) : ℚ :=
  Spec.energyQ
    (compactSelectedNetQ (s(a,a)) (Scaled.Order.diagonalPCEEquiv a)
      (diagonalFullEquiv a different) diagonalInjection (fun e : Fin 2 => (1,e)))
    (qscale (pairQ (a,a) (a,a)) environmentQ)

theorem diagonal_compact_gain_value (a : Basis) (different : a ≠ 97) :
    (diagonalCompactGainQ a different : ℝ)=Compact.diagonalEnergy a different := by
  rw [diagonalCompactGainQ,Spec.energyQ_value,compact_selected_net_value,
    qvalue_scale,environmentQ_value]
  have pair : Scalar.value (pairQ (a,a) (a,a))=InputProducts.pair (a,a) (a,a) :=
    congrFun (congrFun pairQ_value (a,a)) (a,a)
  rw [pair]
  rfl

theorem diagonal_compact_gain_original (a : Basis) (different : a ≠ 97) :
    diagonalCompactGainQ a different=smallGainQ (s(a,a)) := by
  apply Rat.cast_injective (α := ℝ)
  rw [diagonal_compact_gain_value,← Compact.diagonal_energy_exact a different,
    ← block_gain_small,block_gain_value]

def donorCompactGainQ : ℚ :=
  Spec.energyQ
    (compactSelectedNetQ (s((97 : Basis),97)) (Scaled.Order.diagonalPCEEquiv 97)
      donorFullEquiv donorInjection (fun e : Fin 2 => (1,e)))
    (qscale (pairQ (97,97) (97,97)) environmentQ)

theorem donor_compact_gain_value : (donorCompactGainQ : ℝ)=Compact.donorEnergy := by
  rw [donorCompactGainQ,Spec.energyQ_value,compact_selected_net_value,
    qvalue_scale,environmentQ_value]
  have pair : Scalar.value (pairQ (97,97) (97,97))=InputProducts.pair (97,97) (97,97) :=
    congrFun (congrFun pairQ_value (97,97)) (97,97)
  rw [pair]
  rfl

theorem donor_compact_gain_original :
    donorCompactGainQ=smallGainQ (s((97 : Basis),97)) := by
  apply Rat.cast_injective (α := ℝ)
  rw [donor_compact_gain_value,← Compact.donor_energy_exact,
    ← block_gain_small,block_gain_value]


end
end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
