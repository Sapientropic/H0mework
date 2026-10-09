import H0mework.Versions.R9c73a630.ReleaseMaterials.Scratch.LowEnergyRetardedCouncil.ActualFourBlockElastic.SourceActualCandidateBraPairData
set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 3000000
noncomputable section
namespace LowEnergy.ActualCandidateBra
open ActualCandidateVertexEntries

lemma sqrt30_factor : (Real.sqrt 30 : ℂ) = (Real.sqrt 2 : ℂ)*(Real.sqrt 15 : ℂ) := by
  have h : Real.sqrt (30 : ℝ) = Real.sqrt 2 * Real.sqrt 15 := by
    rw [←Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)]
    norm_num
  exact_mod_cast h

lemma sqrt2_square : (Real.sqrt 2 : ℂ)^2 = 2 := by
  have h := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
  exact_mod_cast h

lemma sqrt15_square : (Real.sqrt 15 : ℂ)^2 = 15 := by
  have h := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 15)
  exact_mod_cast h

/-- The independent source branch is the original minus-conjugate at both
vertices, so its quadratic CAR contraction is the conjugate of the primal. -/
theorem actual_tensor_neg_star (A B : Matrix Support Support ℂ) :
    tensor (fun i j => -star (A i j)) (fun i j => -star (B i j)) = star (tensor A B) := by
  simp only [tensor, star_add, star_mul, star_div₀, star_neg, star_ofNat, star_one]
  ring

theorem actual_tensor_symmetric (A B : Matrix Support Support ℂ) :
    tensor A B = tensor B A := by
  unfold tensor
  ring

end LowEnergy.ActualCandidateBra
