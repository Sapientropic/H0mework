import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed.ConcreteDiagonal.Received
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed.IntegerEnergy.Table

set_option autoImplicit false
set_option maxRecDepth 16384
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed
open Propagation.Interface Load.Source Contraction Evaluate
open scoped Matrix BigOperators

def diagonalFullFin : DiagonalFull ≃ Fin 16 :=
  let pair : (Fin 2 × Fin 2) ≃ Fin 4 := finProdFinEquiv
  let sum : ((Fin 2 × Fin 2) ⊕ (Fin 2 × Fin 2)) ≃ Fin 8 :=
    (Equiv.sumCongr pair pair).trans finSumFinEquiv
  (Equiv.prodCongr sum (Equiv.refl (Fin 2))).trans finProdFinEquiv

def diagonalPointerFin : (DiagonalFull ⊕ DiagonalFull) ≃ Fin 32 :=
  (Equiv.sumCongr diagonalFullFin diagonalFullFin).trans finSumFinEquiv

def firstSixDiagonalGainNumeratorInt (a : Fin 6) : Int := Id.run do
  let entrance := fromTable (toTable (firstSixEntranceInt a)
    diagonalPointerFin pairFin) diagonalPointerFin pairFin
  let supply := fromTable (toTable (quantize (diagonalPointerSupplyQ (firstSixBasis a)))
    diagonalPointerFin diagonalPointerFin) diagonalPointerFin diagonalPointerFin
  let load := fromTable (toTable (quantize (diagonalPointerLoadQ (firstSixBasis a)))
    diagonalPointerFin diagonalPointerFin) diagonalPointerFin diagonalPointerFin
  let weak := fromTable (toTable (quantize (diagonalPointerWeakQ (firstSixBasis a)))
    diagonalPointerFin diagonalPointerFin) diagonalPointerFin diagonalPointerFin
  let supply1 := fromTable (toTable (multiply supply entrance)
    diagonalPointerFin pairFin) diagonalPointerFin pairFin
  let supply2 := fromTable (toTable (multiply supply supply1)
    diagonalPointerFin pairFin) diagonalPointerFin pairFin
  let nine := fromTable (toTable (multiply load supply2)
    diagonalPointerFin pairFin) diagonalPointerFin pairFin
  let afterWeak := fromTable (toTable (multiply weak nine)
    diagonalPointerFin pairFin) diagonalPointerFin pairFin
  let eleven := fromTable (toTable (multiply load afterWeak)
    diagonalPointerFin pairFin) diagonalPointerFin pairFin
  let nineSelected := fromTable (toTable (submatrix nine id diagonalChargedSelect)
    diagonalPointerFin (Equiv.refl (Fin 2))) diagonalPointerFin (Equiv.refl (Fin 2))
  let elevenSelected := fromTable (toTable (submatrix eleven id diagonalChargedSelect)
    diagonalPointerFin (Equiv.refl (Fin 2))) diagonalPointerFin (Equiv.refl (Fin 2))
  let pc := fromTable (toTable (quantize (diagonalPCPointerQ (firstSixBasis a)))
    diagonalPointerFin diagonalPointerFin) diagonalPointerFin diagonalPointerFin
  let nineWeighted := fromTable (toTable (multiply (adjoint nineSelected) pc)
    (Equiv.refl (Fin 2)) diagonalPointerFin) (Equiv.refl (Fin 2)) diagonalPointerFin
  let elevenWeighted := fromTable (toTable (multiply (adjoint elevenSelected) pc)
    (Equiv.refl (Fin 2)) diagonalPointerFin) (Equiv.refl (Fin 2)) diagonalPointerFin
  let nineEnergy := fromTable (toTable (multiply nineWeighted nineSelected)
    (Equiv.refl (Fin 2)) (Equiv.refl (Fin 2))) (Equiv.refl (Fin 2)) (Equiv.refl (Fin 2))
  let elevenEnergy := fromTable (toTable (multiply elevenWeighted elevenSelected)
    (Equiv.refl (Fin 2)) (Equiv.refl (Fin 2))) (Equiv.refl (Fin 2)) (Equiv.refl (Fin 2))
  let net := fromTable (toTable (sub elevenEnergy nineEnergy)
    (Equiv.refl (Fin 2)) (Equiv.refl (Fin 2))) (Equiv.refl (Fin 2)) (Equiv.refl (Fin 2))
  let body := fromTable (toTable (sourceDiagonalBodyInt (firstSixBasis a))
    (Equiv.refl (Fin 2)) (Equiv.refl (Fin 2))) (Equiv.refl (Fin 2)) (Equiv.refl (Fin 2))
  let product := multiply net body
  return ∑ i : Fin 2, product.re i i

theorem first_six_diagonal_gain_original (a : Fin 6) :
    firstSixDiagonalGainNumeratorInt a =
      sourceDiagonalGainNumeratorInt (firstSixBasis a) (first_six_different a) := by
  simp only [firstSixDiagonalGainNumeratorInt,from_to_table,
    sourceDiagonalGainNumeratorInt,sourceDiagonalEnergyProductInt,
    sourceDiagonalNetInt,sourceDiagonalElevenSelectedInt,
    sourceDiagonalNineSelectedInt,sourceDiagonalElevenInt,
    sourceDiagonalNineInt,sourceDiagonalAfterWeakInt,
    sourceDiagonalAfterSupply2Int,sourceDiagonalAfterSupply1Int]
  rw [← first_six_entrance_source a,
    ← source_diagonal_supply_concrete (firstSixBasis a) (first_six_different a),
    ← source_diagonal_load_concrete (firstSixBasis a) (first_six_different a),
    ← source_diagonal_weak_concrete (firstSixBasis a) (first_six_different a),
    ← source_diagonal_pc_concrete (firstSixBasis a) (first_six_different a)]
  rfl

end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
