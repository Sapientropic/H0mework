import H0mework.Versions.R9c73a630.ReleaseMaterials.Scratch.LowEnergyRetardedCouncil.ActualFourBlockResponse.SourceActualSylvesterPoleIdentity

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
noncomputable section
namespace LowEnergy.ActualSylvesterKernels
open SourceJointResidualEnergy SourceFourPoleEnergyClosed ActualVectorJointCost
open SourceResolventBandLimit MeasureTheory
open scoped BigOperators InnerProductSpace

abbrev coefficient := ActualTwoResolventPoleIdentity.coefficient
abbrev twoKernel := ActualTwoResolventPoleIdentity.twoCoefficient

private theorem gap_star (μ a b : ℝ) : star (gap μ a b) = gap μ b a := by
  simp only [gap,map_add,map_mul,map_sub,Complex.star_def,Complex.conj_ofReal,
    Complex.conj_ofNat,Complex.conj_I]
  ring

theorem actual_repeated_four_pole (advanced : Bool) (μ a b d : ℝ) (hμ : 0 < μ) :
    causalKernel advanced μ a b a d =
      star (coefficient advanced μ a b) * coefficient advanced μ a d *
        (((Real.pi / μ : ℝ) : ℂ) + twoKernel advanced μ b d) := by
  simpa only [Complex.ofReal_div] using
    ActualTwoResolventPoleIdentity.actual_causal_equal_left_kernel advanced μ a b d hμ

theorem pole_star (μ a w : ℝ) : pole (-μ) a w = star (pole μ a w) := by
  simp only [pole,line,map_inv₀,map_sub,map_add,map_mul,Complex.star_def,
    Complex.conj_ofReal,Complex.conj_I,Complex.ofReal_neg]
  congr 1
  ring

private theorem two_integrable (advanced : Bool) (μ a b : ℝ) (hμ : 0 < μ) :
    Integrable (fun w => star (pole (if advanced then -μ else μ) a w) *
      pole (if advanced then -μ else μ) b w) := by
  cases advanced with
  | false => exact two_pole_integrable μ a b hμ
  | true =>
    simpa only [↓reduceIte,pole_star,star_star,mul_comm] using
      (two_pole_integrable μ b a hμ)

private theorem two_integral (advanced : Bool) (μ a b : ℝ) (hμ : 0 < μ) :
    (∫ w : ℝ, star (pole (if advanced then -μ else μ) a w) *
      pole (if advanced then -μ else μ) b w) = twoKernel advanced μ a b := by
  cases advanced with
  | false => exact two_pole_closed μ a b hμ
  | true =>
    simp only [↓reduceIte,pole_star,star_star]
    have he : (fun w : ℝ => pole μ a w * star (pole μ b w)) =
        (fun w : ℝ => star (pole μ b w) * pole μ a w) := by
      funext w
      ring
    rw [he]
    change twoPole μ b a = _
    rw [two_pole_closed μ b a hμ]
    simp only [twoKernel,ActualTwoResolventPoleIdentity.twoCoefficient,↓reduceIte,
      map_div₀,map_mul,Complex.star_def,Complex.conj_ofReal,Complex.conj_ofNat]
    change 2*(Real.pi : ℂ)/gap μ b a = 2*(Real.pi : ℂ)/star (gap μ a b)
    rw [gap_star]

theorem sum_norm_sq {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    {ι : Type*} [Fintype ι] (v : ι → V) :
    ‖∑i,v i‖^2 = (∑i,∑j,inner ℂ (v i) (v j)).re := by
  rw [←inner_self_eq_norm_sq (𝕜 := ℂ),sum_inner]
  simp only [inner_sum]
  rfl

private theorem single_pointwise {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    {ι : Type*} [Fintype ι] (advanced : Bool) (μ : ℝ) (a : ι → ℝ)
    (v : ι → V) (w : ℝ) :
    ‖∑i,pole (if advanced then -μ else μ) (a i) w • v i‖^2 =
    (∑i,∑j,(star (pole (if advanced then -μ else μ) (a i) w) *
      pole (if advanced then -μ else μ) (a j) w) * inner ℂ (v i) (v j)).re := by
  rw [sum_norm_sq]
  apply congrArg Complex.re
  simp only [inner_smul_left,inner_smul_right,starRingEnd_apply]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem actual_single_gram_integrable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    {ι : Type*} [Fintype ι] (advanced : Bool) (μ : ℝ) (hμ : 0 < μ)
    (a : ι → ℝ) (v : ι → V) :
    Integrable (fun w : ℝ => ‖∑i,pole (if advanced then -μ else μ) (a i) w • v i‖^2) := by
  have hi := integrable_finsetSum Finset.univ (fun i _ =>
    integrable_finsetSum Finset.univ (fun j _ =>
      (two_integrable advanced μ (a i) (a j) hμ).mul_const (inner ℂ (v i) (v j))))
  exact hi.re.congr (Filter.Eventually.of_forall (fun w => (single_pointwise advanced μ a v w).symm))

theorem actual_single_gram_integral {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    {ι : Type*} [Fintype ι] (advanced : Bool) (μ : ℝ) (hμ : 0 < μ)
    (a : ι → ℝ) (v : ι → V) :
    (∫w : ℝ,‖∑i,pole (if advanced then -μ else μ) (a i) w • v i‖^2) =
      (∑i,∑j,twoKernel advanced μ (a i) (a j) * inner ℂ (v i) (v j)).re := by
  have hi (i j : ι) := (two_integrable advanced μ (a i) (a j) hμ).mul_const (inner ℂ (v i) (v j))
  simp_rw [single_pointwise advanced μ a v]
  change (∫w : ℝ,RCLike.re (∑i,∑j,
    (star (pole (if advanced then -μ else μ) (a i) w) *
      pole (if advanced then -μ else μ) (a j) w) * inner ℂ (v i) (v j))) = _
  rw [integral_re (integrable_finsetSum Finset.univ
    (fun i _ => integrable_finsetSum Finset.univ (fun j _ => hi i j)))]
  rw [integral_finsetSum Finset.univ
    (fun i _ => integrable_finsetSum Finset.univ (fun j _ => hi i j))]
  simp_rw [integral_finsetSum Finset.univ (fun j _ => hi _ j),integral_mul_const,
    two_integral advanced μ _ _ hμ]
  rfl

end LowEnergy.ActualSylvesterKernels
