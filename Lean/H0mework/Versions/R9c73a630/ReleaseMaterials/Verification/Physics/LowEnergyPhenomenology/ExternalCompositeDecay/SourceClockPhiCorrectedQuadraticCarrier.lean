import H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceClockPhiQuadraticGaussianSource
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
noncomputable section
namespace LowEnergy.FirstCurrentPayerNext
open GaussCoreHilbert GaussCoreDifferential GaussFockPair GaussHistoryHilbert GaussNativeForm
open SourceQuantumConfigurationHilbert SourceClockPhiCoframeForwardCore
open ClockPhiHeatCorrectedCovarianceSource ClockPhiConservativeHeatSource ClockPhiCorrectedGaussianMeanSource
open MeasureTheory ProbabilityTheory Filter
open scoped InnerProductSpace
private abbrev γ := gaussianReal 0 1
private abbrev G (t : ℝ) := SourceClockPhiActualCovarianceStep.sourceGain (Real.sqrt t)

def correctedQuadraticColumn (t : ℝ) (ht : 0 < t) (v : QuadraticIndex → QuantumTest) (x : ℝ×ℝ) : H :=
  embed (correctedCompleteCore t ht x.1 x.2 (quadraticSource v x))
def correctedQuadraticMean (t : ℝ) (ht : 0 < t) (v : QuadraticIndex → QuantumTest) : H :=
  ∫ x : ℝ×ℝ, correctedQuadraticColumn t ht v x ∂γ.prod γ
def correctedQuadraticSquare (t : ℝ) (v : QuadraticIndex → QuantumTest) : ℝ :=
  (∑ a,∑ b,(quadraticMoment a b:ℂ)*sourcePair (G t (v a)) (G t (v b))).re
private theorem complete_pair (t : ℝ) (ht : 0 < t) (ξ η : ℝ) (f g : QuantumTest) :
    sourcePair (correctedCompleteCore t ht ξ η f) (correctedCompleteCore t ht ξ η g) =
      sourcePair (G t f) (G t g) := by
  change sourcePair (sourceForwardCore t ht.le (correctedProfileCore t ht ξ η (G t f)))
    (sourceForwardCore t ht.le (correctedProfileCore t ht ξ η (G t g))) = _
  rw [SourceClockPhiCoframeForwardPair.actual_forward_core_pair]
  exact clockProfileAction_pair _ _ _ _ _ _
private theorem carrier_measurable (t : ℝ) (ht : 0 < t) (v : QuadraticIndex → QuantumTest) :
    AEStronglyMeasurable (correctedQuadraticColumn t ht v) (γ.prod γ) := by
  have hm (a : QuadraticIndex) : AEStronglyMeasurable
      (fun x : ℝ×ℝ => (noiseQuadratic a x:ℂ) • embed (correctedCompleteCore t ht x.1 x.2 (v a))) (γ.prod γ) := by
    have hc : Continuous (fun x : ℝ×ℝ => (noiseQuadratic a x:ℂ)) := by
      unfold noiseQuadratic noiseLinear
      fun_prop
    exact hc.aestronglyMeasurable.smul (actual_corrected_complete_mean_source t ht (v a)).1.aestronglyMeasurable
  have he : correctedQuadraticColumn t ht v = fun x : ℝ×ℝ =>
      ∑ a,(noiseQuadratic a x:ℂ) • embed (correctedCompleteCore t ht x.1 x.2 (v a)) := by
    funext x
    simp only [correctedQuadraticColumn,quadraticSource,map_sum,map_smul]
  rw [he]
  simpa only [Finset.sum_apply] using! Finset.aestronglyMeasurable_sum Finset.univ (fun a _ => hm a)
private theorem carrier_square (t : ℝ) (ht : 0 < t) (v : QuadraticIndex → QuantumTest) :
    Integrable (fun x : ℝ×ℝ => ‖correctedQuadraticColumn t ht v x‖^2) (γ.prod γ) ∧
    (∫ x : ℝ×ℝ, ‖correctedQuadraticColumn t ht v x‖^2 ∂γ.prod γ) = correctedQuadraticSquare t v := by
  have h := quadratic_gaussian_pair (fun a => G t (v a)) (fun a => G t (v a))
    (1 : QuantumTest →ₗ[ℂ] QuantumTest)
  have he (x : ℝ×ℝ) : (sourcePair (quadraticSource (fun a => G t (v a)) x)
      (quadraticSource (fun a => G t (v a)) x)).re = ‖correctedQuadraticColumn t ht v x‖^2 := by
    have hp := complete_pair t ht x.1 x.2 (quadraticSource v x) (quadraticSource v x)
    have hG : G t (quadraticSource v x) = quadraticSource (fun a => G t (v a)) x := by
      simp only [quadraticSource,map_sum,map_smul]
    simp only [hG] at hp
    have hr := congrArg Complex.re hp
    have hself (q : QuantumTest) : (sourcePair q q).re = ‖embed q‖^2 :=
      (norm_sq_eq_re_inner (𝕜:=ℂ) (embed q)).symm
    rw [hself] at hr
    exact hr.symm
  have hi : Integrable (fun x : ℝ×ℝ => sourcePair (quadraticSource (fun a => G t (v a)) x)
      (quadraticSource (fun a => G t (v a)) x)) (γ.prod γ) := by
    simpa only [Module.End.one_apply] using h.1
  refine ⟨?_,?_⟩
  · simpa only [RCLike.re_eq_complex_re,he] using! hi.re
  · have hre := Complex.reCLM.integral_comp_comm hi
    change (∫ x : ℝ×ℝ, (sourcePair (quadraticSource (fun a => G t (v a)) x)
      (quadraticSource (fun a => G t (v a)) x)).re ∂γ.prod γ) = _ at hre
    simp only [he] at hre
    rw [show (∫ x : ℝ×ℝ, sourcePair (quadraticSource (fun a => G t (v a)) x)
      (quadraticSource (fun a => G t (v a)) x) ∂γ.prod γ) =
        ∑ a,∑ b,(quadraticMoment a b:ℂ)*sourcePair (G t (v a)) (G t (v b)) by
          simpa only [Module.End.one_apply] using h.2] at hre
    exact hre

private theorem variance_defect (F : (ℝ×ℝ) → H) (hi : Integrable F (γ.prod γ))
    (h2 : Integrable (fun x => ‖F x‖^2) (γ.prod γ)) :
    Integrable (fun x => ‖F x-(∫ y,F y ∂γ.prod γ)‖^2) (γ.prod γ) ∧
    (∫ x,‖F x-(∫ y,F y ∂γ.prod γ)‖^2 ∂γ.prod γ) =
      (∫ x,‖F x‖^2 ∂γ.prod γ)-‖∫ y,F y ∂γ.prod γ‖^2 ∧
    0 ≤ (∫ x,‖F x‖^2 ∂γ.prod γ)-‖∫ y,F y ∂γ.prod γ‖^2 := by
  let M : H := ∫ y,F y ∂γ.prod γ
  have hc : Integrable (fun x : ℝ×ℝ => inner ℂ M (F x)) (γ.prod γ) := hi.const_inner (𝕜:=ℂ) M
  have hr : Integrable (fun x : ℝ×ℝ => (inner ℂ M (F x)).re) (γ.prod γ) := hc.re (𝕜:=ℂ)
  have he (x : ℝ×ℝ) : ‖F x-M‖^2 = ‖F x‖^2-2*(inner ℂ M (F x)).re+‖M‖^2 := by
    rw [norm_sub_sq (𝕜:=ℂ),inner_re_symm (𝕜:=ℂ)]
    rfl
  have hb : Integrable (fun x : ℝ×ℝ => ‖F x‖^2-2*(inner ℂ M (F x)).re+‖M‖^2) (γ.prod γ) :=
    (h2.sub (hr.const_mul 2)).add (integrable_const _)
  have hd : Integrable (fun x : ℝ×ℝ => ‖F x-M‖^2) (γ.prod γ) :=
    hb.congr (Eventually.of_forall (fun x => (he x).symm))
  have hmean : (∫ x : ℝ×ℝ,(inner ℂ M (F x)).re ∂γ.prod γ) = ‖M‖^2 := by
    have hint : (∫ x : ℝ×ℝ,inner ℂ M (F x) ∂γ.prod γ) = inner ℂ M M := by
      simpa only [M] using! integral_inner hi M
    calc
      _ = (∫ x : ℝ×ℝ,inner ℂ M (F x) ∂γ.prod γ).re := Complex.reCLM.integral_comp_comm hc
      _ = (inner ℂ M M).re := by rw [hint]
      _ = ‖M‖^2 := by simpa only using! inner_self_eq_norm_sq (𝕜:=ℂ) M
  have hid : (∫ x : ℝ×ℝ,‖F x-M‖^2 ∂γ.prod γ) = (∫ x : ℝ×ℝ,‖F x‖^2 ∂γ.prod γ)-‖M‖^2 := by
    simp_rw [he]
    calc
      _ = (∫ x : ℝ×ℝ,‖F x‖^2-2*(inner ℂ M (F x)).re ∂γ.prod γ)+(∫ _ : ℝ×ℝ,‖M‖^2 ∂γ.prod γ) := by
        simpa only [Pi.sub_apply] using! integral_add (h2.sub (hr.const_mul 2)) (integrable_const (‖M‖^2))
      _ = (∫ x : ℝ×ℝ,‖F x‖^2 ∂γ.prod γ)-(∫ x : ℝ×ℝ,2*(inner ℂ M (F x)).re ∂γ.prod γ)+
          (∫ _ : ℝ×ℝ,‖M‖^2 ∂γ.prod γ) := by rw [integral_sub h2 (hr.const_mul 2)]
      _ = _ := by
        rw [integral_const_mul,hmean]
        simp only [integral_const,probReal_univ,smul_eq_mul,one_mul]
        ring
  refine ⟨hd,hid,?_⟩
  rw [←hid]
  exact integral_nonneg (fun _ => sq_nonneg _)

/-- The same corrected source internally generates the full quadratic carrier, mean, and centered loss. -/
theorem actual_corrected_quadratic_carrier (t : ℝ) (ht : 0 < t) (v : QuadraticIndex → QuantumTest) :
    Integrable (correctedQuadraticColumn t ht v) (γ.prod γ) ∧
    Integrable (fun x => ‖correctedQuadraticColumn t ht v x‖^2) (γ.prod γ) ∧
    (∫ x,‖correctedQuadraticColumn t ht v x‖^2 ∂γ.prod γ) = correctedQuadraticSquare t v ∧
    Integrable (fun x => ‖correctedQuadraticColumn t ht v x-correctedQuadraticMean t ht v‖^2) (γ.prod γ) ∧
    (∫ x,‖correctedQuadraticColumn t ht v x-correctedQuadraticMean t ht v‖^2 ∂γ.prod γ) =
      correctedQuadraticSquare t v-‖correctedQuadraticMean t ht v‖^2 ∧
    0 ≤ correctedQuadraticSquare t v-‖correctedQuadraticMean t ht v‖^2 := by
  have hs := carrier_square t ht v
  have hL : MemLp (correctedQuadraticColumn t ht v) 2 (γ.prod γ) :=
    (memLp_two_iff_integrable_sq_norm (carrier_measurable t ht v)).mpr hs.1
  have hi := hL.integrable (by norm_num : (1:ENNReal) ≤ 2)
  have hv := variance_defect (correctedQuadraticColumn t ht v) hi hs.1
  rw [hs.2] at hv
  exact ⟨hi,hs.1,hs.2,hv⟩
end LowEnergy.FirstCurrentPayerNext
