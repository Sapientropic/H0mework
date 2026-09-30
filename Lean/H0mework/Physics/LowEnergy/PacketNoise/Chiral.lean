import H0mework.Physics.LowEnergy.PacketNoise.Continuity
import H0mework.Physics.LowEnergy.FullQuantum.CoframeResponse.Boundary

/-! The actual boundary weight preserves the original Dirac graph by its source gamma-five anticommutation, including the bounded zero-order term. -/
set_option autoImplicit false
open MeasureTheory
open scoped Matrix Kronecker InnerProductSpace
namespace SaturationMonoid.PhysicsCore.LowEnergy.PacketNoise
open FullQuantum FullSpace SpatialGreen SpatialWeak
open YangMills.FullPairing ProofFreeRicherAnholonomicSource Stage9C.Material.SpinPair
open DiracCliffordRepresentation DiracExteriorMatterAction Triangular
open StageNineHolonomicField Stage9C.Dynamics.Homogeneous
noncomputable section
local instance chiralSector : DecidableEq Sector := Classical.decEq _

def chiral : FiberOperators := operator (CoframeResponse.boundaryWeight actual 0)

theorem chiral_source : chiral=(spinScale : ℂ) • operator (diracMatrixMatterAction diracGammaFive) := by
  rw [chiral,CoframeResponse.boundaryWeight_actual,operator_smul]

theorem chiral_selfAdjoint : star chiral=chiral := by
  have gamma : diracGammaFive.conjTranspose=diracGammaFive := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [diracGammaFive,Matrix.conjTranspose_apply]
  have spin : star (operator (diracMatrixMatterAction diracGammaFive))=
      operator (diracMatrixMatterAction diracGammaFive) := by
    rw [spin_operator,← map_star]
    exact congrArg (Matrix.toEuclideanCLM (n := Index) (𝕜 := ℂ)) (spin_hermitian _ gamma)
  rw [chiral_source,star_smul,spin]
  simp

theorem actual_spatial_operator (point : BasePoint) (j : Fin 3) :
    spatial point j=operator (diracMatrixMatterAction (diracGamma j.succ)) := by
  unfold spatial gammaMother
  rw [actual_coframe,homogeneousInverseGamma lapse lapse_pos.ne']
  simp

theorem spatial_chiral_anticommutes (point : BasePoint) (j : Fin 3) :
    chiral*spatial point j+spatial point j*chiral=0 := by
  have matrix : spinMatrix diracGammaFive*spinMatrix (diracGamma j.succ)+
      spinMatrix (diracGamma j.succ)*spinMatrix diracGammaFive=0 := by
    simp only [spinMatrix,← Matrix.mul_kronecker_mul,Matrix.one_mul,
      ← Matrix.add_kronecker,diracGammaFive_anticommutes,Matrix.zero_kronecker]
  have lifted : operator (diracMatrixMatterAction diracGammaFive)*operator (diracMatrixMatterAction (diracGamma j.succ))+
      operator (diracMatrixMatterAction (diracGamma j.succ))*operator (diracMatrixMatterAction diracGammaFive)=0 := by
    rw [spin_operator,spin_operator,← map_mul,← map_mul,← map_add,matrix,map_zero]
  rw [chiral_source,actual_spatial_operator,smul_mul_assoc,mul_smul_comm]
  have scaled := congrArg (fun x : FiberOperators => (spinScale : ℂ) • x) lifted
  have zero : (spinScale : ℂ) • (0 : FiberOperators)=0 := by ext v i; simp
  rw [zero] at scaled
  simpa only [smul_add] using! scaled

def chiralContact (point : BasePoint) (energy damping : ℝ) : FiberOperators :=
  constant point energy damping*chiral+chiral*constant point energy damping

theorem symbol_chiral (point : BasePoint) (energy damping : ℝ) (frequency : Position) :
    symbol point energy damping frequency*chiral=
      chiralContact point energy damping-chiral*symbol point energy damping frequency := by
  rw [symbol_affine,chiralContact]
  simp only [sub_mul,mul_sub,Finset.sum_mul,Finset.mul_sum,smul_mul_assoc,mul_smul_comm]
  have anti (j : Fin 3) : spatial point j*chiral= -(chiral*spatial point j) :=
    eq_neg_of_add_eq_zero_right (spatial_chiral_anticommutes point j)
  simp only [anti,smul_neg,Finset.sum_neg_distrib]
  abel

end
end SaturationMonoid.PhysicsCore.LowEnergy.PacketNoise
