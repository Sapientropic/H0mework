import H0mework.Versions.R9c73a630.ReleaseMaterials.Scratch.LowEnergyRetardedCouncil.ActualFourBlockResponse.SourceActualVectorJointCost

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.ActualTwoResolventPoleIdentity
open SourceFourPoleEnergyClosed ActualVectorJointCost

/-- The original causal Sylvester multiplier; no same-cause weighted norm
comparison is used between the two independent signed lines. -/
def coefficient (advanced : Bool) (μ a b : ℝ) : ℂ :=
  if advanced then star ((gap μ a b)⁻¹) else (gap μ a b)⁻¹

def twoCoefficient (advanced : Bool) (μ a b : ℝ) : ℂ :=
  if advanced then star (2*(Real.pi : ℂ)/gap μ a b) else 2*(Real.pi : ℂ)/gap μ a b

private theorem star_gap (μ a b : ℝ) : star (gap μ a b)=gap μ b a := by
  simp only [gap,star_add,star_mul,Complex.star_def,Complex.conj_ofReal,
    map_ofNat,Complex.conj_I,map_sub]
  ring

theorem actual_equal_left_kernel (μ a b d : ℝ) (hμ : 0<μ) :
    closedKernel μ a b a d=
      (gap μ b a)⁻¹*(gap μ a d)⁻¹*
        ((Real.pi : ℂ)/(μ : ℂ)+2*(Real.pi : ℂ)/gap μ b d) := by
  have hμc : (μ : ℂ)≠0 := by exact_mod_cast hμ.ne'
  unfold closedKernel
  have haa : gap μ a a=2*(μ : ℂ) := by unfold gap; ring
  rw [haa]
  field_simp [gap_ne μ b a hμ,gap_ne μ a d hμ,gap_ne μ b d hμ,hμc]
  unfold gap
  ring

/-- Equal output channels give a positive boundary kernel plus the original
single-resolvent kernel. Both signed lines preserve the complex coefficients. -/
theorem actual_causal_equal_left_kernel (advanced : Bool) (μ a b d : ℝ) (hμ : 0<μ) :
    causalKernel advanced μ a b a d=
      star (coefficient advanced μ a b)*coefficient advanced μ a d*
        ((Real.pi : ℂ)/(μ : ℂ)+twoCoefficient advanced μ b d) := by
  have hp := actual_equal_left_kernel μ a b d hμ
  have hs : star ((gap μ a b)⁻¹)=(gap μ b a)⁻¹ := by rw [star_inv₀,star_gap]
  cases advanced
  · simpa only [causalKernel,coefficient,twoCoefficient,Bool.false_eq_true,ite_false,hs] using hp
  · have h := congrArg star hp
    simp only [causalKernel,coefficient,twoCoefficient,ite_true,star_mul,star_add,star_div₀,
      Complex.star_def,Complex.conj_ofReal,hs] at h ⊢
    convert h using 1
    ring

end LowEnergy.ActualTwoResolventPoleIdentity
