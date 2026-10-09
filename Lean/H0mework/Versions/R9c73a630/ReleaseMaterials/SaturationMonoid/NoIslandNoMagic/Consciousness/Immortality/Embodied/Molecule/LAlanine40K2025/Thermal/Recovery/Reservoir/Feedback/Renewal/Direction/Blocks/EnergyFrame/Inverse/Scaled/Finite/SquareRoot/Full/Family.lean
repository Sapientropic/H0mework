import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.SquareRoot.Full.Fibers
import Mathlib.Data.Sym.Sym2.Order

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.SquareRoot.Full
open Propagation.Interface Load.Source Scaled.Order
open scoped Matrix MatrixOrder ComplexOrder Matrix.Norms.L2Operator
noncomputable section
local instance : Fintype (Sym2 Basis) := Fintype.ofFinite _

variable (ordinaryRows : ∀ a b : Basis, a < b → OrdinaryPair a b)
  (diagonalRows : ∀ a : Fin 97, DiagonalPair a) (donorRow : DonorPair)

omit ordinaryRows in
def diagonalAt (a : Basis) : FiberRoots s(a,a) := by
  by_cases last : a=(97 : Basis)
  · subst a
    exact donorFiber donorRow
  · have range : a.val < 97 := by
      have size := a.isLt
      have different : a.val ≠ 97 := fun same => last (Fin.ext same)
      omega
    let i : Fin 97 := ⟨a.val,range⟩
    have same : i.castSucc=a := Fin.ext rfl
    rw [← same]
    exact diagonalFiber i (diagonalRows i)

def orderedFiber (a b : Basis) (ordered : a ≤ b) : FiberRoots s(a,b) := by
  by_cases same : a=b
  · subst b
    exact diagonalAt diagonalRows donorRow a
  · have strict : a < b := lt_of_le_of_ne ordered same
    exact offFiber a b same (ordinaryRows a b strict)

def fiberFamily (k : Sym2 Basis) : FiberRoots k := by
  let pair := Sym2.sortEquiv k
  have same : s(pair.val.1,pair.val.2)=k := Sym2.sortEquiv.symm_apply_apply k
  exact same ▸ orderedFiber ordinaryRows diagonalRows donorRow pair.val.1 pair.val.2 pair.property

def rootApproximation : LoadedJoint := assemble pceOrbit (fun k => (fiberFamily ordinaryRows diagonalRows donorRow k).root)
def complementApproximation : LoadedJoint := assemble pceOrbit (fun k => (fiberFamily ordinaryRows diagonalRows donorRow k).complement)

theorem whole_root_errors :
    ‖CFC.sqrt finiteEffect-rootApproximation ordinaryRows diagonalRows donorRow‖ ≤ (2/10^7 : ℝ) ∧
    ‖CFC.sqrt (1-finiteEffect)-complementApproximation ordinaryRows diagonalRows donorRow‖ ≤ (2/10^7 : ℝ) := by
  constructor
  · exact assemble_error pceOrbit _ (preserves_sqrt finite_effect_preserves) _ _ (by norm_num)
      (fun k => (fiberFamily ordinaryRows diagonalRows donorRow k).root_error)
  · exact assemble_error pceOrbit _ (preserves_sqrt (preserves_sub (preserves_one pceOrbit) finite_effect_preserves)) _ _ (by norm_num)
      (fun k => (fiberFamily ordinaryRows diagonalRows donorRow k).complement_error)

end
end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.SquareRoot.Full
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
