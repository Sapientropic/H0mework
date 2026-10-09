import H0mework.Physics.LowEnergy.PacketFeedback.Leading

/-! The complete ordered four-branch Gram has a true quadratic-time limit and is linear in the two source vertex coefficients. -/
set_option autoImplicit false
open scoped InnerProductSpace
namespace SaturationMonoid.PhysicsCore.LowEnergy.PacketPairResponse
open PacketFeedback Filter Topology
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

def fourGram (same opposite : ℝ) (branch : Bool → E) : ℝ :=
  (1/2 : ℝ)*∑ first, ∑ second, (if first=second then same else opposite)*
    (inner ℂ (branch first) (branch second)).re

theorem fourGram_coordinates (same opposite : ℝ) (branch : Bool → E) :
    fourGram same opposite branch=(1/2 : ℝ)*
      (((same-opposite)/2)*‖branch true-branch false‖^2+
        ((same+opposite)/2)*‖branch true+branch false‖^2) := by
  simp only [fourGram,Fintype.sum_bool,Bool.false_eq_true,Bool.true_eq_false,↓reduceIte]
  simp only [← RCLike.re_eq_complex_re]
  rw [inner_self_eq_norm_sq (𝕜 := ℂ),inner_self_eq_norm_sq (𝕜 := ℂ),
    inner_re_symm (𝕜 := ℂ) (branch false) (branch true),norm_sub_sq (𝕜 := ℂ),norm_add_sq (𝕜 := ℂ)]
  ring

theorem fourGram_leading (same opposite : ℝ) (branch : ℝ → Bool → E) (direction : E)
    (initial : ∀ sign, branch 0 sign=0)
    (derivative : ∀ sign, HasDerivAt (fun time => branch time sign) direction 0) :
    Tendsto (fun time : ℝ => fourGram same opposite (branch time)/time^2) (𝓝[≠] 0)
      (𝓝 ((same+opposite)*‖direction‖^2)) := by
  have difference : HasDerivAt (fun time => branch time true-branch time false) 0 0 := by
    have actual := (derivative true).sub (derivative false)
    rw [sub_self] at actual
    exact actual
  have sum := (derivative true).add (derivative false)
  have twice : ‖direction+direction‖^2=4*‖direction‖^2 := by
    rw [← two_smul ℝ direction]
    norm_num [norm_smul,mul_pow]
  have generated := (quadratic_norm_leading ((same-opposite)/2) ((same+opposite)/2)
    (fun time => branch time true-branch time false) (fun time => branch time true+branch time false)
    (direction+direction) (by rw [initial true,initial false,sub_self])
    (by rw [initial true,initial false,zero_add]) difference sum).const_mul (1/2 : ℝ)
  rw [twice] at generated
  convert! generated using 1
  · funext time
    rw [fourGram_coordinates]
    ring
  · ring

theorem fourGram_tensor (sameT oppositeT sameL oppositeL weight : ℝ) (branch : Bool → E) :
    fourGram (sameT+(sameL-sameT)*weight) (oppositeT+(oppositeL-oppositeT)*weight) branch=
      fourGram sameT oppositeT branch+
        (fourGram sameL oppositeL branch-fourGram sameT oppositeT branch)*weight := by
  simp_rw [fourGram_coordinates]
  ring

theorem fourGram_real_smul (same opposite scalar : ℝ) (branch : Bool → E) :
    fourGram same opposite (fun sign => scalar • branch sign)=scalar^2*fourGram same opposite branch := by
  simp_rw [fourGram_coordinates]
  rw [← smul_sub,← smul_add]
  simp only [norm_smul,Real.norm_eq_abs,mul_pow,sq_abs]
  ring

theorem fourGram_constant (same opposite : ℝ) (field : E) :
    fourGram same opposite (fun _ => field)=(same+opposite)*‖field‖^2 := by
  rw [fourGram_coordinates,sub_self,norm_zero,zero_pow (by decide : (2 : ℕ)≠0),mul_zero,zero_add,
    ← two_smul ℝ field]
  norm_num [norm_smul,mul_pow]
  ring

end
end SaturationMonoid.PhysicsCore.LowEnergy.PacketPairResponse
