import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.BasinRefinement.Continuous.WholeBand.Basin.Weak.Test
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinRefinement.WholeBandBasin.Weak
open SourceGaussianModel Set Filter
open scoped Topology
noncomputable section

def unitBump : ContDiffBump (0 : Point) := ⟨1,2,by norm_num,by norm_num⟩
def unitTest : Test := ⟨unitBump,unitBump.contDiff,unitBump.hasCompactSupport⟩
def cutoffScale (n : ℕ) : ℝ := ((n : ℝ)+1)⁻¹

theorem cutoffScale_positive (n : ℕ) : 0 < cutoffScale n := by unfold cutoffScale; positivity
theorem cutoffScale_le_one (n : ℕ) : cutoffScale n ≤ 1 := by
  unfold cutoffScale
  apply (inv_le_one₀ (by positivity)).mpr
  norm_num

def scaleHomeomorph (c : ℝ) (nonzero : c ≠ 0) : Point ≃ₜ Point where
  toFun := fun x => c • x
  invFun := fun x => c⁻¹ • x
  left_inv := fun x => by simp [smul_smul,nonzero]
  right_inv := fun x => by simp [smul_smul,nonzero]
  continuous_toFun := continuous_id.const_smul c
  continuous_invFun := continuous_id.const_smul c⁻¹

def cutoff (n : ℕ) : Test where
  value := fun x => unitTest.value (cutoffScale n • x)
  smooth := unitTest.smooth.comp (contDiff_id.const_smul (cutoffScale n))
  compact := unitTest.compact.comp_homeomorph (scaleHomeomorph (cutoffScale n) (cutoffScale_positive n).ne')

theorem cutoff_range (n : ℕ) (x : Point) : 0 ≤ (cutoff n).value x ∧ (cutoff n).value x ≤ 1 :=
  ⟨unitBump.nonneg,unitBump.le_one⟩

theorem cutoff_derivative (n : ℕ) (x : Point) :
    (cutoff n).derivative x = cutoffScale n • unitTest.derivative (cutoffScale n • x) := by
  have chain := (unitTest.hasFDerivAt (cutoffScale n • x)).comp x
    ((hasFDerivAt_id x).const_smul (cutoffScale n))
  have equal : (unitTest.derivative (cutoffScale n • x)).comp
      (cutoffScale n • ContinuousLinearMap.id ℝ Point) = cutoffScale n • unitTest.derivative (cutoffScale n • x) := by
    ext h
    simp only [ContinuousLinearMap.comp_apply,_root_.smul_apply,ContinuousLinearMap.id_apply,map_smul]
  change HasFDerivAt (cutoff n).value _ x at chain
  rw [equal] at chain
  exact chain.fderiv

theorem cutoffScale_tends_zero : Tendsto cutoffScale atTop (𝓝 (0 : ℝ)) := by
  unfold cutoffScale
  exact tendsto_inv_atTop_zero.comp (tendsto_atTop_add_const_right atTop (1 : ℝ) tendsto_natCast_atTop_atTop)

theorem cutoff_tends_one (x : Point) : Tendsto (fun n => (cutoff n).value x) atTop (𝓝 1) := by
  have scaled : Tendsto (fun n => cutoffScale n • x) atTop (𝓝 (0 : Point)) := by
    simpa only [zero_smul] using cutoffScale_tends_zero.smul_const x
  have tends := unitTest.smooth.continuous.continuousAt.tendsto.comp scaled
  have atZero : unitTest.value 0 = 1 := unitBump.one_of_mem_closedBall (by simp [unitBump])
  simpa only [cutoff,atZero,Function.comp_def] using tends

theorem cutoff_derivative_bounds : ∃ C ≥ 0, ∀ n x, ‖(cutoff n).derivative x‖ ≤ cutoffScale n*C := by
  obtain ⟨_,_,_,_,C,nonnegative,_,bounded,_⟩ := unitTest.bounds
  refine ⟨C,nonnegative,fun n x => ?_⟩
  rw [cutoff_derivative,norm_smul,Real.norm_eq_abs,abs_of_pos (cutoffScale_positive n)]
  exact mul_le_mul_of_nonneg_left (bounded _) (cutoffScale_positive n).le

end
end LAlanine40K2025.BasinRefinement.WholeBandBasin.Weak
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
