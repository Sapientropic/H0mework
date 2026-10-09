import H0mework.Versions.R9c73a630.ReleaseMaterials.Scratch.LowEnergyRetardedCouncil.ActualFourBlockResponse.SourceActualSylvesterKernels

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
noncomputable section
namespace LowEnergy.ActualSylvesterGram
open SourceJointResidualEnergy ActualSylvesterKernels ActualVectorJointCost MeasureTheory
open scoped BigOperators InnerProductSpace

/-- Orthogonal output channels retain all complex interference between input channels. -/
theorem actual_orthogonal_price {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    {ι : Type*} [Fintype ι] (advanced : Bool) (μ : ℝ) (hμ : 0 < μ)
    (a : ι → ℝ) (v : ι × ι → V)
    (hv : ∀i j k l,i ≠ k → inner ℂ (v (i,j)) (v (k,l)) = 0) :
    (∑ij : ι × ι,∑kl : ι × ι,causalKernel advanced μ (a ij.1) (a ij.2)
      (a kl.1) (a kl.2) * inner ℂ (v ij) (v kl)).re =
      Real.pi/μ * ‖∑ij : ι × ι,coefficient advanced μ (a ij.1) (a ij.2) • v ij‖^2 +
      ∫w : ℝ,‖∑ij : ι × ι,pole (if advanced then -μ else μ) (a ij.2) w •
        (coefficient advanced μ (a ij.1) (a ij.2) • v ij)‖^2 := by
  classical
  let u := fun ij : ι × ι => coefficient advanced μ (a ij.1) (a ij.2) • v ij
  have hc (ij kl : ι × ι) :
      causalKernel advanced μ (a ij.1) (a ij.2) (a kl.1) (a kl.2) * inner ℂ (v ij) (v kl) =
      ((Real.pi/μ : ℝ) : ℂ) * inner ℂ (u ij) (u kl) +
        twoKernel advanced μ (a ij.2) (a kl.2) * inner ℂ (u ij) (u kl) := by
    by_cases h : ij.1 = kl.1
    · rw [←h,actual_repeated_four_pole advanced μ _ _ _ hμ]
      simp only [u,inner_smul_left,inner_smul_right,starRingEnd_apply,←h]
      ring
    · have hz : inner ℂ (v ij) (v kl) = 0 := hv ij.1 ij.2 kl.1 kl.2 h
      simp only [u,inner_smul_left,inner_smul_right,starRingEnd_apply,hz,mul_zero,add_zero]
  have hs : (∑ij,∑kl,causalKernel advanced μ (a ij.1) (a ij.2)
      (a kl.1) (a kl.2) * inner ℂ (v ij) (v kl)) =
      ((Real.pi/μ : ℝ) : ℂ) * (∑ij,∑kl,inner ℂ (u ij) (u kl)) +
      (∑ij,∑kl,twoKernel advanced μ (a ij.2) (a kl.2) * inner ℂ (u ij) (u kl)) := by
    simp_rw [hc,Finset.sum_add_distrib,←Finset.mul_sum]
  have hn : (∑ij,∑kl,inner ℂ (u ij) (u kl)).re = ‖∑ij,u ij‖^2 := (sum_norm_sq u).symm
  have hi := actual_single_gram_integral advanced μ hμ (fun ij : ι × ι => a ij.2) u
  change _ = Real.pi/μ * ‖∑ij,u ij‖^2 + ∫w : ℝ,‖∑ij,pole (if advanced then -μ else μ) (a ij.2) w • u ij‖^2
  rw [hs,Complex.add_re,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero,hn,←hi]

end LowEnergy.ActualSylvesterGram
