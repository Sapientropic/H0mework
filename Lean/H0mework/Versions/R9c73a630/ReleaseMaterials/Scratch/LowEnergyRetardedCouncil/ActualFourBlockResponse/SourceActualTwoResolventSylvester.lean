import H0mework.Versions.R9c73a630.ReleaseMaterials.Scratch.LowEnergyRetardedCouncil.ActualFourBlockResponse.SourceActualSylvesterChannels
import H0mework.Versions.R9c73a630.ReleaseMaterials.Scratch.LowEnergyRetardedCouncil.ActualFourBlockResponse.SourceActualSylvesterGram

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxRecDepth 4096
set_option maxHeartbeats 1800000
noncomputable section
namespace LowEnergy.ActualTwoResolventSylvester
open GaussCoreHilbert GaussDiagonalHistory GaussUnitaryHistory
open FullYSourceResolventGraphSplice SourceJointResidualEnergy SourceRetardedIncrement
open ActualSylvesterChannels ActualSylvesterKernels ActualSylvesterGram ActualVectorJointCost MeasureTheory
open SourceResolventBandLimit
open scoped BigOperators InnerProductSpace

/-- The actual finite Hamiltonian channels, including escape, generate the entire smoothing. -/
def sourceL (advanced : Bool) (F : Index) (μ : ℝ) (D : H →L[ℂ] H) : H →L[ℂ] H :=
  ∑ij : Channel F × Channel F,
    coefficient advanced μ (channelValue F ij.1) (channelValue F ij.2) •
      ((projection F ij.1 * D) * projection F ij.2)

theorem actual_source_L (advanced : Bool) (F : Index) (μ : ℝ) (D : H →L[ℂ] H) (g : H) :
    sourceL advanced F μ D g = ∑ij : Channel F × Channel F,
      coefficient advanced μ (channelValue F ij.1) (channelValue F ij.2) • spectralLeg F D g ij := by
  simp only [sourceL,sum_apply,smul_apply,
    mul_apply_eq_comp,projection_apply,spectralLeg]

private theorem coefficient_equation (advanced : Bool) (μ a b : ℝ) (hμ : 0 < μ) :
    (2*(μ : ℂ)-Complex.I*(if advanced then -1 else 1)*((a : ℂ)-(b : ℂ))) *
      coefficient advanced μ a b = 1 := by
  cases advanced with
  | false =>
    have hg := SourceFourPoleEnergyClosed.gap_ne μ a b hμ
    change (2*(μ : ℂ)-Complex.I*1*((a : ℂ)-(b : ℂ))) *
      (SourceFourPoleEnergyClosed.gap μ a b)⁻¹ = 1
    have he : 2*(μ : ℂ)-Complex.I*1*((a : ℂ)-(b : ℂ)) =
        SourceFourPoleEnergyClosed.gap μ a b := by unfold SourceFourPoleEnergyClosed.gap; ring
    rw [he,mul_inv_cancel₀ hg]
  | true =>
    have hg := SourceFourPoleEnergyClosed.gap_ne μ b a hμ
    have he : star (SourceFourPoleEnergyClosed.gap μ a b) =
        SourceFourPoleEnergyClosed.gap μ b a := by
      simp only [SourceFourPoleEnergyClosed.gap,map_add,map_mul,map_sub,Complex.star_def,
        Complex.conj_ofReal,Complex.conj_ofNat,Complex.conj_I]
      ring
    change (2*(μ : ℂ)-Complex.I*(-1)*((a : ℂ)-(b : ℂ))) *
      star ((SourceFourPoleEnergyClosed.gap μ a b)⁻¹) = 1
    rw [star_inv₀,he]
    have he' : 2*(μ : ℂ)-Complex.I*(-1)*((a : ℂ)-(b : ℂ)) =
        SourceFourPoleEnergyClosed.gap μ b a := by unfold SourceFourPoleEnergyClosed.gap; ring
    rw [he',mul_inv_cancel₀ hg]

private theorem leg_input (F : Index) (D : H →L[ℂ] H) (g : H) (ij : Channel F × Channel F) :
    spectralLeg F D (GaussGradedCompression.compression F g) ij =
      (channelValue F ij.2 : ℂ) • spectralLeg F D g ij := by
  change channel F ij.1 (D (channel F ij.2 (GaussGradedCompression.compression F g))) = _
  rw [channel_eigen_left,map_smul]
  rw [←projection_apply, map_smul, projection_apply]
  rfl

private theorem leg_output (F : Index) (D : H →L[ℂ] H) (g : H) (ij : Channel F × Channel F) :
    GaussGradedCompression.compression F (spectralLeg F D g ij) =
      (channelValue F ij.1 : ℂ) • spectralLeg F D g ij :=
  channel_eigen_right F ij.1 _

private theorem leg_resolution (F : Index) (D : H →L[ℂ] H) (g : H) :
    ∑ij : Channel F × Channel F, spectralLeg F D g ij = D g := by
  rw [Fintype.sum_prod_type]
  simp only [spectralLeg]
  rw [Finset.sum_comm]
  simp_rw [channel_resolution]
  rw [←map_sum,channel_resolution]

/-- The original compression itself supplies the Sylvester equation on the whole H. -/
theorem actual_source_sylvester (advanced : Bool) (F : Index) (μ : ℝ) (hμ : 0 < μ)
    (D : H →L[ℂ] H) :
    (2*(μ : ℂ)) • sourceL advanced F μ D -
      (Complex.I*(if advanced then -1 else 1)) •
        (GaussGradedCompression.compression F * sourceL advanced F μ D -
          sourceL advanced F μ D * GaussGradedCompression.compression F) = D := by
  apply ContinuousLinearMap.ext
  intro g
  simp only [sub_apply,smul_apply,mul_apply_eq_comp]
  simp_rw [actual_source_L,map_sum,map_smul,leg_output,leg_input,smul_smul]
  rw [Finset.smul_sum,←Finset.sum_sub_distrib,Finset.smul_sum,←Finset.sum_sub_distrib]
  rw [←leg_resolution F D g]
  apply Finset.sum_congr rfl
  intro ij _
  rw [←sub_smul]
  simp only [smul_smul]
  rw [←sub_smul]
  have hc := coefficient_equation advanced μ (channelValue F ij.1) (channelValue F ij.2) hμ
  have he : 2*(μ : ℂ)*coefficient advanced μ (channelValue F ij.1) (channelValue F ij.2) -
      (Complex.I*(if advanced then -1 else 1)) *
        (coefficient advanced μ (channelValue F ij.1) (channelValue F ij.2)*(channelValue F ij.1 : ℂ)-
         coefficient advanced μ (channelValue F ij.1) (channelValue F ij.2)*(channelValue F ij.2 : ℂ)) = 1 := by
    calc
      _ = (2*(μ : ℂ)-Complex.I*(if advanced then -1 else 1)*
          ((channelValue F ij.1 : ℂ)-(channelValue F ij.2 : ℂ))) *
          coefficient advanced μ (channelValue F ij.1) (channelValue F ij.2) := by ring
      _ = 1 := hc
  rw [he,one_smul]

private theorem channel_resolvent (F : Index) (i : Channel F) (z : ℂ) (hz : z.im ≠ 0) (g : H) :
    channel F i (finiteResolvent F z g) = ((channelValue F i : ℂ)-z)⁻¹ • channel F i g := by
  have hr := congrArg (fun T : H →L[ℂ] H => T g)
    (resolvent_right _ (GaussGradedCompression.compression_selfAdjoint F) z hz)
  change GaussGradedCompression.compression F (finiteResolvent F z g) -
    z • finiteResolvent F z g = g at hr
  have hp := congrArg (projection F i) hr
  simp only [map_sub,map_smul,projection_apply,channel_eigen_left] at hp
  rw [←sub_smul] at hp
  have hn : (channelValue F i : ℂ)-z ≠ 0 := by
    intro h
    have hi := congrArg Complex.im h
    simp only [Complex.sub_im,Complex.ofReal_im,Complex.zero_im,zero_sub,neg_eq_zero] at hi
    exact hz hi
  have h := congrArg (fun v : H => ((channelValue F i : ℂ)-z)⁻¹ • v) hp
  simpa only [smul_smul,inv_mul_cancel₀ hn,one_smul] using h

/-- The second positive term is the same smoothing acting on the original single resolvent. -/
theorem actual_source_single_resolvent (advanced : Bool) (F : Index) (μ : ℝ) (hμ : 0 < μ)
    (D : H →L[ℂ] H) (g : H) (w : ℝ) :
    sourceL advanced F μ D (finiteResolvent F (causalFrequency advanced μ w) g) =
      ∑ij : Channel F × Channel F,
        pole (if advanced then -μ else μ) (channelValue F ij.2) w •
          (coefficient advanced μ (channelValue F ij.1) (channelValue F ij.2) • spectralLeg F D g ij) := by
  have hz : (causalFrequency advanced μ w).im ≠ 0 := by
    cases advanced <;> simpa [causalFrequency,line_im] using hμ.ne'
  rw [actual_source_L]
  apply Finset.sum_congr rfl
  intro ij _
  unfold spectralLeg
  rw [channel_resolvent F ij.2 _ hz,map_smul]
  rw [←projection_apply,map_smul,projection_apply,smul_smul,smul_smul]
  congr 1
  exact mul_comm _ _

theorem actual_source_single_integrable (advanced : Bool) (F : Index) (μ : ℝ) (hμ : 0 < μ)
    (D : H →L[ℂ] H) (g : H) :
    Integrable (fun w : ℝ => ‖sourceL advanced F μ D
      (finiteResolvent F (causalFrequency advanced μ w) g)‖^2) := by
  simp_rw [actual_source_single_resolvent advanced F μ hμ D g]
  exact actual_single_gram_integrable advanced μ hμ _ _

/-- Exact two-R price: initial Sylvester energy plus the remaining single-R energy. -/
theorem actual_two_resolvent_price (advanced : Bool) (F : Index) (μ : ℝ) (hμ : 0 < μ)
    (D : H →L[ℂ] H) (g : H) :
    (∫w : ℝ,‖finiteResolvent F (causalFrequency advanced μ w)
      (D (finiteResolvent F (causalFrequency advanced μ w) g))‖^2) =
      Real.pi/μ * ‖sourceL advanced F μ D g‖^2 +
        ∫w : ℝ,‖sourceL advanced F μ D (finiteResolvent F (causalFrequency advanced μ w) g)‖^2 := by
  have h := actual_orthogonal_price advanced μ hμ (channelValue F) (spectralLeg F D g)
    (leg_orthogonal F D g)
  rw [←actual_source_L advanced F μ D g] at h
  have he : (fun w : ℝ => ‖∑ij : Channel F × Channel F,
      pole (if advanced then -μ else μ) (channelValue F ij.2) w •
        (coefficient advanced μ (channelValue F ij.1) (channelValue F ij.2) • spectralLeg F D g ij)‖^2) =
      (fun w : ℝ => ‖sourceL advanced F μ D (finiteResolvent F (causalFrequency advanced μ w) g)‖^2) := by
    funext w
    exact congrArg (fun x : H => ‖x‖^2) (actual_source_single_resolvent advanced F μ hμ D g w).symm
  rw [he] at h
  rw [actual_vector_causal_energy F advanced μ hμ D g]
  exact h

/-- Actual cutoff increments consume the source smoothing without a caller certificate. -/
theorem actual_increment_two_resolvent_price (advanced sharp : Bool) (m n : ℕ) (F : Index)
    (μ : ℝ) (hμ : 0 < μ) (g : H) :
    (∫w : ℝ,‖finiteResolvent F (causalFrequency advanced μ w)
      (SourceEscapeSeedTail.actualIncrement sharp m n (finiteResolvent F (causalFrequency advanced μ w) g))‖^2) =
      Real.pi/μ * ‖sourceL advanced F μ (SourceEscapeSeedTail.actualIncrement sharp m n) g‖^2 +
        ∫w : ℝ,‖sourceL advanced F μ (SourceEscapeSeedTail.actualIncrement sharp m n)
          (finiteResolvent F (causalFrequency advanced μ w) g)‖^2 :=
  actual_two_resolvent_price advanced F μ hμ _ g

end LowEnergy.ActualTwoResolventSylvester
