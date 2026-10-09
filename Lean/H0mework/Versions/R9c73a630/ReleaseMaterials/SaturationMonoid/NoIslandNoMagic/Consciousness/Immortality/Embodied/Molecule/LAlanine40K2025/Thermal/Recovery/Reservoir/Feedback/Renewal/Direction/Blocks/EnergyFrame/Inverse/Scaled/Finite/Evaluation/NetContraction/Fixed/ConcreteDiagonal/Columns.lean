import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed.ConcreteDiagonal.FirstSixPointer

set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 1600000
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed
open Propagation.Interface Load.Source Contraction Evaluate
open scoped Matrix BigOperators

def firstSixSourceColumnsQ (a : Fin 6) :
    MatrixQ (DiagonalFull ⊕ DiagonalFull) (Fin 2 × Fin 2) :=
  qmultiply ((firstSixPointerQ a).submatrix id Sum.inl)
    ((diagonalSupplyFullQ (firstSixBasis a)).submatrix id diagonalInjection)

theorem first_six_columns_source (a : Fin 6) :
    sourceDiagonalColumnsInt (firstSixBasis a) (first_six_different a) =
      quantize (firstSixSourceColumnsQ a) := by
  let body := firstSixBasis a
  let different := first_six_different a
  have pointer :
      (pointerBlockQ s(body,body)).submatrix
        (coordinatePointer s(body,body) (diagonalFullEquiv body different))
        (fun i => coordinatePointer s(body,body) (diagonalFullEquiv body different) (.inl i)) =
          (firstSixPointerQ a).submatrix id Sum.inl := by
    funext i j
    change Spec.pointer (diagonalPointerAddress body different i)
      (diagonalPointerAddress body different (.inl j)) =
        firstSixPointerQ a i (.inl j)
    have source := congrFun (congrFun
      (diagonal_pointer_source body different) i) (.inl j)
    change Spec.pointer (diagonalPointerAddress body different i)
      (diagonalPointerAddress body different (.inl j)) =
        diagonalPointerQ body different i (.inl j) at source
    have same : diagonalPointerQ body different = firstSixPointerQ a :=
      first_six_pointer_source a
    rw [same] at source
    exact source
  have supply :
      (supplyBlockQ s(body,body)).submatrix (diagonalFullEquiv body different)
        (fun i => diagonalFullEquiv body different (diagonalInjection i)) =
          (diagonalSupplyFullQ body).submatrix id diagonalInjection := by
    funext i j
    change Spec.supply ((diagonalFullEquiv body different i).val)
      ((diagonalFullEquiv body different (diagonalInjection j)).val) =
        diagonalSupplyFullQ body i (diagonalInjection j)
    exact congrFun (congrFun (diagonal_supply_full_source body different) i)
      (diagonalInjection j)
  change quantize (qmultiply
    ((pointerBlockQ s(body,body)).submatrix
      (coordinatePointer s(body,body) (diagonalFullEquiv body different))
      (fun i => coordinatePointer s(body,body) (diagonalFullEquiv body different) (.inl i)))
    ((supplyBlockQ s(body,body)).submatrix (diagonalFullEquiv body different)
      (fun i => diagonalFullEquiv body different (diagonalInjection i)))) = _
  rw [pointer,supply]
  rfl

end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
