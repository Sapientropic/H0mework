import H0mework.Physics.LowEnergy.FullQuantum.TriangularTime
import H0mework.Physics.LowEnergyMatterSpace.Source
import Mathlib.LinearAlgebra.Matrix.Kronecker

/-! The complete matter carrier retains the original Hermitian spatial principal. -/
set_option autoImplicit false
open scoped Matrix Kronecker BigOperators InnerProductSpace
namespace SaturationMonoid.PhysicsCore.LowEnergy.FullQuantum.FullSpace
open DiracCliffordRepresentation DiracExteriorMatterAction YangMills.FullPairing
open Stage9C.Material.SpinPair
noncomputable section
local instance : DecidableEq Sector := Classical.decEq _

def spinMatrix (matrix : DiracMatrix) : Matrix Index Index ℂ := matrix ⊗ₖ (1 : Matrix Sector Sector ℂ)

theorem spin_coordinates (matrix : DiracMatrix) (matter : DiracExteriorMatterCarrier) :
    naturalCoordinates (diracMatrixMatterAction matrix matter)=
      ((Matrix.toEuclideanCLM (n := Index) (𝕜 := ℂ)) (spinMatrix matrix)) (naturalCoordinates matter) := by
  ext index
  rcases index with ⟨spin,sector⟩
  change naturalCoordinates (diracMatrixMatterAction matrix matter) (spin,sector)=
    (spinMatrix matrix*ᵥ(fun j => naturalCoordinates matter j)) (spin,sector)
  simp only [naturalCoordinates_apply,diracMatrixMatterAction,LinearMap.coe_mk,AddHom.coe_mk,
    map_sum,map_smul,Finsupp.finsetSum_apply,Finsupp.smul_apply,smul_eq_mul,
    spinMatrix,Matrix.mulVec,dotProduct,Fintype.sum_prod_type,Matrix.kroneckerMap_apply]
  apply Finset.sum_congr rfl
  intro other _
  simp [Matrix.one_apply]

theorem spin_hermitian (matrix : DiracMatrix) (symmetric : matrix.conjTranspose=matrix) :
    (spinMatrix matrix).conjTranspose=spinMatrix matrix := by
  rw [spinMatrix,Matrix.conjTranspose_kronecker,symmetric,Matrix.conjTranspose_one]

def principalMatrix (momentum : Fin 3 → ℝ) : Matrix Index Index ℂ :=
  ∑ j, (-(lapse : ℂ)*(momentum j : ℂ)) • spinMatrix (diracGammaZero*diracGamma j.succ)

theorem principalMatrix_hermitian (momentum : Fin 3 → ℝ) :
    (principalMatrix momentum).conjTranspose=principalMatrix momentum := by
  simp only [principalMatrix,Matrix.conjTranspose_sum,Matrix.conjTranspose_smul]
  apply Finset.sum_congr rfl
  intro j _
  rw [spin_hermitian _ (diracGammaZero_mul_spatial_isHermitian j).eq]
  simp

theorem principalMatrix_continuous : Continuous principalMatrix := by
  unfold principalMatrix
  fun_prop

end
end SaturationMonoid.PhysicsCore.LowEnergy.FullQuantum.FullSpace
