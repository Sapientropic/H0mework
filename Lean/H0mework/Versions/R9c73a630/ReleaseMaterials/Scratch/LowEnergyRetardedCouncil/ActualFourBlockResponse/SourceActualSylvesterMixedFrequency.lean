import H0mework.Versions.R9c73a630.ReleaseMaterials.Scratch.LowEnergyRetardedCouncil.ActualFourBlockResponse.SourceActualTwoResolventSylvester
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxRecDepth 4096
set_option maxHeartbeats 1800000
noncomputable section
namespace LowEnergy.ActualSylvesterMixedFrequency
open GaussCoreHilbert GaussDiagonalHistory GaussUnitaryHistory
open FullYSourceResolventGraphSplice SourceJointResidualEnergy SourceResolventBandLimit
open ActualSylvesterChannels ActualSylvesterKernels ActualTwoResolventSylvester
open ActualVectorJointCost SourceFourPoleEnergyClosed MeasureTheory
open Lean Meta Elab Term
open scoped BigOperators InnerProductSpace

elab "paid_mixed_kernel%" field:ident : term => do
  let ns := Name.str (Name.str (Name.num `_private.H0mework.Versions.R9c73a630.ReleaseMaterials.Scratch.LowEnergyRetardedCouncil.ActualFourBlockResponse.SourceActualSylvesterKernels 0) "LowEnergy") "ActualSylvesterKernels"
  let name := Name.str ns field.getId.eraseMacroScopes.toString
  unless (← getEnv).contains name do throwError "Missing paid two-pole kernel"
  mkConstWithFreshMVarLevels name

elab "paid_mixed_source%" field:ident : term => do
  let ns := Name.str (Name.str (Name.num `_private.H0mework.Versions.R9c73a630.ReleaseMaterials.Scratch.LowEnergyRetardedCouncil.ActualFourBlockResponse.SourceActualTwoResolventSylvester 0) "LowEnergy") "ActualTwoResolventSylvester"
  let name := Name.str ns field.getId.eraseMacroScopes.toString
  unless (← getEnv).contains name do throwError "Missing paid source channel identity"
  mkConstWithFreshMVarLevels name

private theorem gap_star (μ a b : ℝ) : star (gap μ a b) = gap μ b a := by
  simp only [gap,star_add,star_mul,star_sub,Complex.star_def,
    Complex.conj_ofReal,Complex.conj_ofNat,Complex.conj_I]
  ring

/-- The two ordered mixed terms retain their complex interference on either causal line. -/
theorem actual_mixed_kernel (advanced : Bool) (μ a b d : ℝ) (hμ : 0 < μ) :
    (coefficient advanced μ a d + star (coefficient advanced μ a b)) *
      twoKernel advanced μ b d = (2*(μ : ℂ)) * causalKernel advanced μ a b a d := by
  rw [actual_repeated_four_pole advanced μ a b d hμ]
  have hμc : (μ : ℂ) ≠ 0 := by exact_mod_cast hμ.ne'
  have hp : ((gap μ a d)⁻¹ + (gap μ b a)⁻¹) * (2*(Real.pi : ℂ)/gap μ b d) =
      (2*(μ : ℂ)) * ((gap μ b a)⁻¹*(gap μ a d)⁻¹ *
        (((Real.pi/μ : ℝ) : ℂ) + 2*(Real.pi : ℂ)/gap μ b d)) := by
    rw [Complex.ofReal_div]
    field_simp [gap_ne μ b a hμ,gap_ne μ a d hμ,gap_ne μ b d hμ,hμc]
    unfold gap
    ring
  have hr (x : ℝ) : star (x : ℂ) = (x : ℂ) := by
    simp only [Complex.star_def,Complex.conj_ofReal]
  have htwo : star (2 : ℂ) = (2 : ℂ) := map_ofNat (starRingEnd ℂ) 2
  cases advanced with
  | false =>
    simpa only [coefficient,ActualTwoResolventPoleIdentity.coefficient,twoKernel,
      ActualTwoResolventPoleIdentity.twoCoefficient,Bool.false_eq_true,ite_false,
      star_inv₀,gap_star] using hp
  | true =>
    have hs := congrArg star hp
    simp only [star_add,star_mul,hr,htwo] at hs
    simp only [coefficient,ActualTwoResolventPoleIdentity.coefficient,twoKernel,
      ActualTwoResolventPoleIdentity.twoCoefficient,ite_true,star_inv₀,
      gap_star] at hs ⊢
    linear_combination hs

private theorem finite_pair_pointwise {V : Type*} [NormedAddCommGroup V]
    [InnerProductSpace ℂ V] {ι : Type*} [Fintype ι]
    (p k : ι → ℂ) (v : ι → V) :
    inner ℂ (∑ i,p i • v i) (∑ i,p i • (k i • v i)) +
      inner ℂ (∑ i,p i • (k i • v i)) (∑ i,p i • v i) =
      ∑ i,∑ j,((k j + star (k i)) * (star (p i)*p j)) * inner ℂ (v i) (v j) := by
  rw [sum_inner,sum_inner]
  simp only [inner_sum,inner_smul_left,inner_smul_right,
    starRingEnd_apply,←Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

private theorem finite_pair_integrable {V : Type*} [NormedAddCommGroup V]
    [InnerProductSpace ℂ V] {ι : Type*} [Fintype ι]
    (advanced : Bool) (μ : ℝ) (hμ : 0 < μ) (b : ι → ℝ) (k : ι → ℂ) (v : ι → V) :
    Integrable (fun w : ℝ =>
      inner ℂ (∑ i,pole (if advanced then -μ else μ) (b i) w • v i)
        (∑ i,pole (if advanced then -μ else μ) (b i) w • (k i • v i)) +
      inner ℂ (∑ i,pole (if advanced then -μ else μ) (b i) w • (k i • v i))
        (∑ i,pole (if advanced then -μ else μ) (b i) w • v i)) := by
  simp_rw [finite_pair_pointwise]
  exact integrable_finsetSum Finset.univ (fun i _ =>
    integrable_finsetSum Finset.univ (fun j _ =>
      (((paid_mixed_kernel% two_integrable) advanced μ (b i) (b j) hμ).const_mul
        (k j + star (k i))).mul_const (inner ℂ (v i) (v j))))

private theorem finite_pair_integral {V : Type*} [NormedAddCommGroup V]
    [InnerProductSpace ℂ V] {ι : Type*} [Fintype ι]
    (advanced : Bool) (μ : ℝ) (hμ : 0 < μ) (b : ι → ℝ) (k : ι → ℂ) (v : ι → V) :
    (∫ w : ℝ,
      inner ℂ (∑ i,pole (if advanced then -μ else μ) (b i) w • v i)
        (∑ i,pole (if advanced then -μ else μ) (b i) w • (k i • v i)) +
      inner ℂ (∑ i,pole (if advanced then -μ else μ) (b i) w • (k i • v i))
        (∑ i,pole (if advanced then -μ else μ) (b i) w • v i)) =
      ∑ i,∑ j,((k j + star (k i))*twoKernel advanced μ (b i) (b j)) *
        inner ℂ (v i) (v j) := by
  have hi (i j : ι) :=
    (((paid_mixed_kernel% two_integrable) advanced μ (b i) (b j) hμ).const_mul
      (k j + star (k i))).mul_const (inner ℂ (v i) (v j))
  simp_rw [finite_pair_pointwise]
  rw [integral_finsetSum Finset.univ
    (fun i _ => integrable_finsetSum Finset.univ (fun j _ => hi i j))]
  simp_rw [integral_finsetSum Finset.univ (fun j _ => hi _ j),integral_mul_const,
    integral_const_mul,(paid_mixed_kernel% two_integral) advanced μ _ _ hμ]

private theorem forcing_spectral (advanced : Bool) (F : Index) (μ : ℝ) (hμ : 0 < μ)
    (D : H →L[ℂ] H) (g : H) (w : ℝ) :
    D (finiteResolvent F (causalFrequency advanced μ w) g) =
      ∑ ij : Channel F × Channel F,
        pole (if advanced then -μ else μ) (channelValue F ij.2) w • spectralLeg F D g ij := by
  have hz : (causalFrequency advanced μ w).im ≠ 0 := by
    cases advanced <;> simpa [causalFrequency,line_im] using hμ.ne'
  rw [←(paid_mixed_source% leg_resolution) F D (finiteResolvent F _ g)]
  apply Finset.sum_congr rfl
  intro ij _
  unfold spectralLeg
  rw [(paid_mixed_source% channel_resolvent) F ij.2 _ hz,map_smul]
  rw [←projection_apply,map_smul,projection_apply]
  rfl

/-- The actual source smoothing, with its escape channel, is paired with the original forcing. -/
def frequencyPair (advanced : Bool) (F : Index) (μ : ℝ) (D : H →L[ℂ] H)
    (g : H) (w : ℝ) : ℂ :=
  inner ℂ (D (finiteResolvent F (causalFrequency advanced μ w) g))
    (sourceL advanced F μ D (finiteResolvent F (causalFrequency advanced μ w) g)) +
  inner ℂ (sourceL advanced F μ D (finiteResolvent F (causalFrequency advanced μ w) g))
    (D (finiteResolvent F (causalFrequency advanced μ w) g))

theorem actual_mixed_frequency_integrable (advanced : Bool) (F : Index) (μ : ℝ)
    (hμ : 0 < μ) (D : H →L[ℂ] H) (g : H) :
    Integrable (frequencyPair advanced F μ D g) := by
  unfold frequencyPair
  simp_rw [forcing_spectral advanced F μ hμ D g,
    actual_source_single_resolvent advanced F μ hμ D g]
  exact finite_pair_integrable advanced μ hμ _ _ _

private theorem actual_pair_spectral_integral (advanced : Bool) (F : Index) (μ : ℝ)
    (hμ : 0 < μ) (D : H →L[ℂ] H) (g : H) :
    (∫ w : ℝ,frequencyPair advanced F μ D g w) =
      (2*(μ : ℂ)) * (∑ ij : Channel F × Channel F,∑ kl : Channel F × Channel F,
        causalKernel advanced μ (channelValue F ij.1) (channelValue F ij.2)
          (channelValue F kl.1) (channelValue F kl.2) *
          inner ℂ (spectralLeg F D g ij) (spectralLeg F D g kl)) := by
  unfold frequencyPair
  simp_rw [forcing_spectral advanced F μ hμ D g,
    actual_source_single_resolvent advanced F μ hμ D g]
  rw [finite_pair_integral advanced μ hμ]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro ij _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro kl _
  by_cases h : ij.1 = kl.1
  · rw [←h]
    rw [actual_mixed_kernel advanced μ (channelValue F ij.1)
      (channelValue F ij.2) (channelValue F kl.2) hμ]
    ring
  · rw [leg_orthogonal F D g ij.1 ij.2 kl.1 kl.2 h]
    simp only [mul_zero]

private theorem pair_real {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    (x y : V) : (inner ℂ x y + inner ℂ y x).im = 0 := by
  have h := inner_conj_symm (𝕜 := ℂ) y x
  have hi := congrArg Complex.im h
  simp only [Complex.conj_im] at hi
  simp only [Complex.add_im]
  linarith

/-- Exact complex frequency balance; no PSD or residual-tail premise is supplied. -/
theorem actual_mixed_frequency_integral (advanced : Bool) (F : Index) (μ : ℝ)
    (hμ : 0 < μ) (D : H →L[ℂ] H) (g : H) :
    (∫ w : ℝ,frequencyPair advanced F μ D g w) =
      (2*(μ : ℂ)) * (vectorCost advanced F μ D g : ℂ) := by
  have he := actual_pair_spectral_integral advanced F μ hμ D g
  apply Complex.ext
  · have hr := congrArg Complex.re he
    norm_num only [Complex.mul_re,Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im,
      Complex.re_ofNat,Complex.im_ofNat,mul_zero,zero_mul,add_zero,sub_zero,vectorCost] at hr ⊢
    exact hr
  · have hi := actual_mixed_frequency_integrable advanced F μ hμ D g
    change RCLike.im (∫ w : ℝ,frequencyPair advanced F μ D g w) = _
    rw [←integral_im hi]
    have hz : (fun w : ℝ => RCLike.im (frequencyPair advanced F μ D g w)) = fun _ => 0 := by
      funext w
      exact pair_real _ _
    rw [hz,integral_zero]
    norm_num only [Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im,
      Complex.re_ofNat,Complex.im_ofNat,mul_zero,zero_mul,add_zero]

theorem actual_mixed_frequency_real (advanced : Bool) (F : Index) (μ : ℝ)
    (hμ : 0 < μ) (D : H →L[ℂ] H) (g : H) :
    Integrable (fun w : ℝ => 2*(inner ℂ
      (D (finiteResolvent F (causalFrequency advanced μ w) g))
      (sourceL advanced F μ D (finiteResolvent F (causalFrequency advanced μ w) g))).re) ∧
    (∫ w : ℝ,2*(inner ℂ
      (D (finiteResolvent F (causalFrequency advanced μ w) g))
      (sourceL advanced F μ D (finiteResolvent F (causalFrequency advanced μ w) g))).re) =
      2*μ*(∫ w : ℝ,‖finiteResolvent F (causalFrequency advanced μ w)
        (D (finiteResolvent F (causalFrequency advanced μ w) g))‖^2) := by
  have hp (w : ℝ) : (frequencyPair advanced F μ D g w).re = 2*(inner ℂ
      (D (finiteResolvent F (causalFrequency advanced μ w) g))
      (sourceL advanced F μ D (finiteResolvent F (causalFrequency advanced μ w) g))).re := by
    unfold frequencyPair
    rw [Complex.add_re]
    have hs := inner_re_symm (𝕜 := ℂ)
      (D (finiteResolvent F (causalFrequency advanced μ w) g))
      (sourceL advanced F μ D (finiteResolvent F (causalFrequency advanced μ w) g))
    change (inner ℂ _ _).re = (inner ℂ _ _).re at hs
    rw [hs]
    ring
  have hi := actual_mixed_frequency_integrable advanced F μ hμ D g
  refine ⟨hi.re.congr (Filter.Eventually.of_forall hp),?_⟩
  simp_rw [←hp]
  change (∫ w : ℝ,RCLike.re (frequencyPair advanced F μ D g w)) = _
  rw [integral_re hi,actual_mixed_frequency_integral advanced F μ hμ D g,
    actual_vector_causal_energy F advanced μ hμ D g]
  change (2*(μ : ℂ)*(vectorCost advanced F μ D g : ℂ)).re = _
  norm_num only [Complex.mul_re,Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im,
    Complex.re_ofNat,Complex.im_ofNat,mul_zero,zero_mul,add_zero,sub_zero]

end LowEnergy.ActualSylvesterMixedFrequency
