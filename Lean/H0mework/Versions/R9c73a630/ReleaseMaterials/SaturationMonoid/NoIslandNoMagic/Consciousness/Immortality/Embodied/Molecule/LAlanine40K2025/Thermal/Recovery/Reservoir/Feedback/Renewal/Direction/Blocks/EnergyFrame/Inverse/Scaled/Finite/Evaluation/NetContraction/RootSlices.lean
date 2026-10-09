import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.SourceSlices
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Contraction.Observable

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction
open Propagation.Interface Load.Source Collision Contraction
open scoped Matrix
noncomputable section
local instance : Fintype (Sym2 Basis) := Fintype.ofFinite _

open SquareRoot.Full

private theorem family_ordered (a b : Basis) (ordered : a ≤ b) :
    fiberFamily allOrdinary allDiagonal paidDonor s(a,b)=orderedFiber allOrdinary allDiagonal paidDonor a b ordered := by
  let make (p : {p : Basis × Basis // p.1 ≤ p.2}) := orderedFiber allOrdinary allDiagonal paidDonor p.val.1 p.val.2 p.property
  have equal {p q : {p : Basis × Basis // p.1 ≤ p.2}} (h : p=q) : HEq (make p) (make q) := by cases h; rfl
  apply eq_of_heq
  apply (eqRec_heq _ _).trans
  exact equal (sorted_source a b ordered)

private theorem family_ordinary (a b : Basis) (ordered : a < b) :
    fiberFamily allOrdinary allDiagonal paidDonor s(a,b)=offFiber a b ordered.ne (allOrdinary a b ordered) := by
  rw [family_ordered a b ordered.le]
  simp only [orderedFiber,dif_neg ordered.ne]

private theorem diagonal_at (a : Fin 97) :
    diagonalAt allDiagonal paidDonor a.castSucc=diagonalFiber a (allDiagonal a) := by
  have different : a.castSucc ≠ (97 : Basis) := by
    intro same
    have hv : a.val=97 := congrArg Fin.val same
    have range := a.isLt
    omega
  unfold diagonalAt
  rw [dif_neg different]
  rfl

private theorem family_diagonal (a : Fin 97) :
    fiberFamily allOrdinary allDiagonal paidDonor s(a.castSucc,a.castSucc)=diagonalFiber a (allDiagonal a) := by
  rw [family_ordered a.castSucc a.castSucc le_rfl]
  simpa [orderedFiber] using diagonal_at a

private theorem family_donor :
    fiberFamily allOrdinary allDiagonal paidDonor s((97 : Basis),97)=donorFiber paidDonor := by
  rw [family_ordered (97 : Basis) 97 le_rfl]
  simp [orderedFiber,diagonalAt]

private theorem cancel_frame {ι κ : Type*} (e : ι ≃ κ) (M : Matrix ι ι ℂ) :
    (M.submatrix e.symm e.symm).submatrix e e=M := by
  ext i j
  simp only [Matrix.submatrix_apply,Equiv.symm_apply_apply]

theorem root_ordinary (a b : Basis) (ordered : a < b) :
    SquareRoot.Full.sourceRoot.submatrix (Scaled.Order.orbitPCE a b) (Scaled.Order.orbitPCE a b)=
      (allOrdinary a b ordered).1.value.submatrix tripleIndex tripleIndex := by
  change (restrict pceOrbit s(a,b) SquareRoot.Full.sourceRoot).submatrix (Scaled.Order.offDiagonalPCEEquiv a b ordered.ne)
    (Scaled.Order.offDiagonalPCEEquiv a b ordered.ne)=_
  rw [SquareRoot.Full.sourceRoot,rootApproximation,assemble_restriction,family_ordinary a b ordered]
  exact cancel_frame _ _

theorem root_diagonal (a : Fin 97) :
    SquareRoot.Full.sourceRoot.submatrix (Scaled.Order.diagonalPCE a.castSucc) (Scaled.Order.diagonalPCE a.castSucc)=
      (allDiagonal a).1.value.submatrix pairIndex pairIndex := by
  change (restrict pceOrbit s(a.castSucc,a.castSucc) SquareRoot.Full.sourceRoot).submatrix (Scaled.Order.diagonalPCEEquiv a.castSucc)
    (Scaled.Order.diagonalPCEEquiv a.castSucc)=_
  rw [SquareRoot.Full.sourceRoot,rootApproximation,assemble_restriction,family_diagonal]
  exact cancel_frame _ _

theorem root_donor :
    SquareRoot.Full.sourceRoot.submatrix (Scaled.Order.diagonalPCE 97) (Scaled.Order.diagonalPCE 97)=
      paidDonor.1.value.submatrix pairIndex pairIndex := by
  change (restrict pceOrbit s((97 : Basis),97) SquareRoot.Full.sourceRoot).submatrix (Scaled.Order.diagonalPCEEquiv 97)
    (Scaled.Order.diagonalPCEEquiv 97)=_
  rw [SquareRoot.Full.sourceRoot,rootApproximation,assemble_restriction,family_donor]
  exact cancel_frame _ _

theorem complement_ordinary (a b : Basis) (ordered : a < b) :
    SquareRoot.Full.sourceComplement.submatrix (Scaled.Order.orbitPCE a b) (Scaled.Order.orbitPCE a b)=
      (allOrdinary a b ordered).2.value.submatrix tripleIndex tripleIndex := by
  change (restrict pceOrbit s(a,b) SquareRoot.Full.sourceComplement).submatrix (Scaled.Order.offDiagonalPCEEquiv a b ordered.ne)
    (Scaled.Order.offDiagonalPCEEquiv a b ordered.ne)=_
  rw [SquareRoot.Full.sourceComplement,complementApproximation,assemble_restriction,family_ordinary a b ordered]
  exact cancel_frame _ _

theorem complement_diagonal (a : Fin 97) :
    SquareRoot.Full.sourceComplement.submatrix (Scaled.Order.diagonalPCE a.castSucc) (Scaled.Order.diagonalPCE a.castSucc)=
      (allDiagonal a).2.value.submatrix pairIndex pairIndex := by
  change (restrict pceOrbit s(a.castSucc,a.castSucc) SquareRoot.Full.sourceComplement).submatrix (Scaled.Order.diagonalPCEEquiv a.castSucc)
    (Scaled.Order.diagonalPCEEquiv a.castSucc)=_
  rw [SquareRoot.Full.sourceComplement,complementApproximation,assemble_restriction,family_diagonal]
  exact cancel_frame _ _

theorem complement_donor :
    SquareRoot.Full.sourceComplement.submatrix (Scaled.Order.diagonalPCE 97) (Scaled.Order.diagonalPCE 97)=
      paidDonor.2.value.submatrix pairIndex pairIndex := by
  change (restrict pceOrbit s((97 : Basis),97) SquareRoot.Full.sourceComplement).submatrix (Scaled.Order.diagonalPCEEquiv 97)
    (Scaled.Order.diagonalPCEEquiv 97)=_
  rw [SquareRoot.Full.sourceComplement,complementApproximation,assemble_restriction,family_donor]
  exact cancel_frame _ _

end
end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
