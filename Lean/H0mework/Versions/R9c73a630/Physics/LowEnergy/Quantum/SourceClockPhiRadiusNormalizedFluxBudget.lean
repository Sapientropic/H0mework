import H0mework.Versions.R9c73a630.Physics.LowEnergy.Quantum.SourceClockPhiRadiusNormalizedFlux
import H0mework.Versions.R9c73a630.Physics.LowEnergy.Quantum.SourceClockPhiRadiusResponseNativeBudget

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1600000
set_option maxRecDepth 2048
noncomputable section
namespace LowEnergy.SourceClockPhiRadiusNormalizedFluxBudget
open GaussCoreHilbert GaussCoreDifferential GaussFockPair GaussHistoryHilbert GaussNativeForm GaussNativeEnergy
open GaussLiveMomentum GaussDiagonalHistory GaussUnitaryHistory
open SourceClockPhiRadiusSourceCurrent SourceClockRadiusAffineCutoff SourceClockYukawaCubicCurrent
open SourceClockPhiRadiusResponsePositiveSource SourceClockPhiRadiusNormalizedFlux SourceClockPhiRadiusResponseNativeBudget
open SourceMixedNativeReturn SourceScalarPositiveBulkWard SourceScalarPairedTransport SourceLocalizedInverseFormPayment
open SourceQuantumConfigurationHilbert SourceQuantumScalarChart SourceQuantumGaugeSliceCoordinates SourceQuantumFockGauge
open FullYSourceResolventGraphSplice SourceResolventBandLimit MeasureTheory Filter
open scoped ContDiff InnerProductSpace Topology
abbrev End := QuantumTest →ₗ[ℂ] QuantumTest
private abbrev S : End := phiInverseAction
private abbrev r : End := phiRadiusAction
attribute [local irreducible] resolventCore state diagonalAction phiPositivePrice

private theorem frequency_nonreal (advanced : Bool) (μ : ℝ) (hμ : 0   <   μ) (w : ℝ) :
    (actualFrequency advanced μ w).im≠0 := by
  cases advanced <;> simpa only [actualFrequency,Bool.false_eq_true,ite_false,ite_true,
    Complex.star_def,Complex.conj_im,line_im,neg_ne_zero] using hμ.ne'
private theorem finite_star (F : Index) (z : ℂ) :
    finiteResolvent F (star z)=(finiteResolvent F z).adjoint := by
  unfold finiteResolvent
  change Ring.inverse (GaussGradedCompression.compression F-star z • 1)=
    (Ring.inverse (GaussGradedCompression.compression F-z • 1)).adjoint
  rw [←ContinuousLinearMap.star_eq_adjoint,←Ring.inverse_star]
  congr 1
  simp only [star_sub,star_smul,star_one,(GaussGradedCompression.compression_selfAdjoint F).star_eq]
private theorem frequency_continuous (advanced : Bool) (μ : ℝ) (hμ : 0   <   μ) (F : Index) :
    Continuous (fun w : ℝ=>finiteResolvent F (actualFrequency advanced μ w)) := by
  cases advanced
  · exact SourceRetardedBandCurrent.finite_frequency_continuous μ hμ F
  · have he:(fun w : ℝ=>finiteResolvent F (actualFrequency true μ w))=
        (fun w : ℝ=>(finiteResolvent F (line μ w)).adjoint) := by funext w;exact finite_star F _
    exact he ▸ (ContinuousLinearMap.adjoint.continuous.comp (SourceRetardedBandCurrent.finite_frequency_continuous μ hμ F))


def normalizedEnergy (m ell : ℕ) (F : Index) (z : ℂ) (hz : z.im≠0) (g : diagonal.domain) : ℝ :=
  ‖embed (S (phiResponseCore m ell F z hz g))‖^2

private theorem inverse_phi_core (f : QuantumTest) : phiInverseBounded (embed f)=embed (S f) :=
  GaussBoundedMultiplier.extension_core _ _ _ _ _ _ f
private theorem inverse_phi_norm : ‖phiInverseBounded‖ ≤ 1 := GaussBoundedMultiplier.extension_norm _ _ _ _ _ _
private theorem inverse_radius : S*r=(1:End) := by
  apply LinearMap.ext;intro f;apply DFunLike.ext;intro z
  change (phiReciprocal z:ℂ) • ((phiRadius z:ℂ) • f z)=f z
  rw [smul_smul,phiReciprocal,Complex.ofReal_inv,inv_mul_cancel₀,one_smul]
  exact Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.2 (by positivity)).ne'
private theorem inverse_theta (m ell : ℕ) : Commute S (phiThetaAction m ell) := by
  have hc : Commute S (1-S) := (Commute.one_right S).sub_right (Commute.refl S)
  exact (hc.pow_right (m+1)).sub_right (hc.pow_right (ell+1))
private theorem response_normalized (m ell : ℕ) (F : Index) (z : ℂ) (hz : z.im≠0)
    (g : diagonal.domain) :
    S (phiResponseCore m ell F z hz g)=
      phiThetaAction m ell (state F z hz g)-S (phiThetaAction m ell (state F z hz (phiRadiusSource g))) := by
  have hS (f : QuantumTest) : S (phiThetaAction m ell f)=phiThetaAction m ell (S f) :=
    LinearMap.congr_fun (inverse_theta m ell).eq f
  have hr (f : QuantumTest) : S (r f)=f := LinearMap.congr_fun inverse_radius f
  have hR : resolventCore F z hz (coreEquiv.symm g)=state F z hz g := by
    simp only [resolventCore,LinearMap.coe_mk,AddHom.coe_mk,coreEquiv.apply_symm_apply]
  have hρ : resolventCore F z hz (r (coreEquiv.symm g))=state F z hz (phiRadiusSource g) := by
    unfold resolventCore
    rfl
  unfold phiResponseCore SourceScalarDoubleCurrent.bracket
  simp only [LinearMap.sub_apply,Module.End.mul_apply,map_sub,hS,hr,hR,hρ]

private theorem normalized_bound (m ell : ℕ) (F : Index) (z : ℂ) (hz : z.im≠0)
    (g : diagonal.domain) : normalizedEnergy m ell F z hz g ≤
      2*‖embed (phiThetaAction m ell (state F z hz g))‖^2+
      2*‖embed (phiThetaAction m ell (state F z hz (phiRadiusSource g)))‖^2 := by
  unfold normalizedEnergy
  rw [response_normalized,map_sub,←inverse_phi_core]
  let x := embed (phiThetaAction m ell (state F z hz g))
  let y := embed (phiThetaAction m ell (state F z hz (phiRadiusSource g)))
  have hi : ‖phiInverseBounded y‖ ≤ ‖y‖ :=
    ((phiInverseBounded.le_opNorm y).trans (mul_le_mul_of_nonneg_right inverse_phi_norm (norm_nonneg y))).trans_eq (one_mul _)
  have h := norm_sub_le x (phiInverseBounded y)
  have hs := pow_le_pow_left₀ (norm_nonneg _) (h.trans (add_le_add (le_refl _) hi)) 2
  change ‖x-phiInverseBounded y‖^2 ≤ 2*‖x‖^2+2*‖y‖^2
  nlinarith only [hs,sq_nonneg (‖x‖-‖y‖)]

private theorem read_state (F : Index) (g : diagonal.domain) (A : End) (z : ℂ) (hz : z.im≠0) :
    sourceRead F g A (finiteResolvent F z (g:H))=embed (A (state F z hz g)) := by
  simpa only [state] using source_read_resolvent F g A z hz

private theorem theta_measurable (m ell : ℕ) (F : Index) (μ : ℝ) (hμ : 0<μ)
    (g : diagonal.domain) (advanced : Bool) :
    Measurable (fun w : ℝ => ENNReal.ofReal (‖embed (phiThetaAction m ell
      (state F (actualFrequency advanced μ w) (frequency_nonreal advanced μ hμ w) g))‖^2)) := by
  have h (w : ℝ) := read_state F g (phiThetaAction m ell)
    (actualFrequency advanced μ w) (frequency_nonreal advanced μ hμ w)
  simp_rw [←h]
  exact (((sourceRead F g (phiThetaAction m ell)).continuous.comp
    ((frequency_continuous advanced μ hμ F).clm_apply continuous_const)).norm.pow 2).measurable.ennreal_ofReal

private theorem energy_measurable (m ell : ℕ) (F : Index) (μ : ℝ) (hμ : 0<μ)
    (g : diagonal.domain) (advanced : Bool) :
    Measurable (fun w : ℝ => ENNReal.ofReal (normalizedEnergy m ell F (actualFrequency advanced μ w)
      (frequency_nonreal advanced μ hμ w) g)) := by
  have h1 (w : ℝ) := read_state F g (phiThetaAction m ell)
    (actualFrequency advanced μ w) (frequency_nonreal advanced μ hμ w)
  have h2 (w : ℝ) := read_state F (phiRadiusSource g) (phiThetaAction m ell)
    (actualFrequency advanced μ w) (frequency_nonreal advanced μ hμ w)
  simp only [normalizedEnergy,response_normalized,map_sub,←inverse_phi_core]
  simp_rw [←h1,←h2]
  have hr (h : H) : Continuous (fun w : ℝ => finiteResolvent F (actualFrequency advanced μ w) h) :=
    (frequency_continuous advanced μ hμ F).clm_apply continuous_const
  exact (((sourceRead F g (phiThetaAction m ell)).continuous.comp (hr (g:H))).sub
    (phiInverseBounded.continuous.comp ((sourceRead F (phiRadiusSource g) (phiThetaAction m ell)).continuous.comp
      (hr (phiRadiusSource g:H))))).norm.pow 2
    |>.measurable.ennreal_ofReal

/-- The normalized response is paid by precisely its two original fixed resolvent inputs. -/
theorem actual_normalized_response_common_tail (μ : ℝ) (hμ : 0<μ) (g : diagonal.domain) :
    ∀ ε : ℝ,0<ε → ∃ N : ℕ,∀ m,N ≤ m → ∀ ell,m ≤ ell → ∀ᶠ F in (sourceFilter:Filter Index),
      ∀ advanced : Bool,(∫⁻ w : ℝ,ENNReal.ofReal (normalizedEnergy m ell F (actualFrequency advanced μ w)
        (frequency_nonreal advanced μ hμ w) g)) ≤ ENNReal.ofReal ε := by
  intro ε hε
  obtain ⟨N1,h1⟩ := actual_phi_theta_common_tail μ hμ g (ε/4) (by positivity)
  obtain ⟨N2,h2⟩ := actual_phi_theta_common_tail μ hμ (phiRadiusSource g) (ε/4) (by positivity)
  refine ⟨max N1 N2,fun m hm ell hml => ?_⟩
  filter_upwards [h1 m (by omega) ell hml,h2 m (by omega) ell hml] with F hg hρ
  intro advanced
  let X := fun w : ℝ => ENNReal.ofReal (‖embed (phiThetaAction m ell
    (state F (actualFrequency advanced μ w) (frequency_nonreal advanced μ hμ w) g))‖^2)
  let Y := fun w : ℝ => ENNReal.ofReal (‖embed (phiThetaAction m ell
    (state F (actualFrequency advanced μ w) (frequency_nonreal advanced μ hμ w) (phiRadiusSource g)))‖^2)
  have my : Measurable Y := theta_measurable m ell F μ hμ (phiRadiusSource g) advanced
  calc
    _ ≤ ∫⁻ w : ℝ,ENNReal.ofReal 2*(X w+Y w) := by
      apply lintegral_mono
      intro w
      dsimp only [X,Y]
      rw [←ENNReal.ofReal_add (sq_nonneg _) (sq_nonneg _),←ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 2)]
      exact ENNReal.ofReal_le_ofReal ((normalized_bound m ell F _ _ g).trans_eq (by ring))
    _ = ENNReal.ofReal 2*((∫⁻ w : ℝ,X w)+(∫⁻ w : ℝ,Y w)) := by
      rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,lintegral_add_right _ my]
    _ ≤ ENNReal.ofReal 2*(ENNReal.ofReal (ε/4)+ENNReal.ofReal (ε/4)) :=
      mul_le_mul le_rfl (add_le_add (hg advanced) (hρ advanced)) zero_le zero_le
    _ = ENNReal.ofReal ε := by
      rw [←ENNReal.ofReal_add (by positivity) (by positivity),←ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 2)]
      congr 1
      ring

/-- Whole CF-plus-defect flux is absorbed with a freely small coefficient and an internal common tail. -/
theorem actual_joint_normalized_flux_common_budget (μ : ℝ) (hμ : 0<μ) (g : diagonal.domain)
    (η : ℝ) (hη : 0<η) :
    ∀ ε : ℝ,0<ε → ∃ N : ℕ,∀ m,N ≤ m → ∀ ell,m ≤ ell → ∀ᶠ F in (sourceFilter:Filter Index),
      (∫⁻ w : ℝ,ENNReal.ofReal (‖jointFlux F (phiResponseCore m ell F (line μ w)
        (by simpa only [line_im] using hμ.ne') g)‖)) ≤
        ENNReal.ofReal ε+ENNReal.ofReal η*phiPositiveBudget m ell F μ hμ g := by
  intro ε hε
  obtain ⟨N,hN⟩ := actual_normalized_response_common_tail μ hμ g (2*η*ε) (by positivity)
  refine ⟨N,fun m hm ell hml => ?_⟩
  filter_upwards [hN m hm ell hml] with F hF
  have hE := hF false
  have mE := energy_measurable m ell F μ hμ g false
  change (∫⁻ w : ℝ,ENNReal.ofReal (normalizedEnergy m ell F (line μ w) _ g)) ≤ _ at hE
  change Measurable (fun w : ℝ => ENNReal.ofReal (normalizedEnergy m ell F (line μ w) _ g)) at mE
  let E := fun w : ℝ => ENNReal.ofReal (normalizedEnergy m ell F (line μ w) (by simpa only [line_im] using hμ.ne') g)
  let P := fun w : ℝ => ENNReal.ofReal (phiPositivePrice m ell F (line μ w) (by simpa only [line_im] using hμ.ne') g)
  have hp (w : ℝ) : 0 ≤ phiPositivePrice m ell F (line μ w) (by simpa only [line_im] using hμ.ne') g := by
    have h := actual_phi_positive_slots m ell F (line μ w) (by simpa only [line_im] using hμ.ne') g
    have hc := SourceClockReflectedForm.original_coframe_gram_nonnegative
      (SourcePhysicalKineticSquare.inverseVolumeAction (phiResponseCore m ell F (line μ w) (by simpa only [line_im] using hμ.ne') g))
    have hs : 0 ≤ SourceClockReflectedForm.scalarForm
      (SourcePhysicalKineticSquare.inverseVolumeAction (phiResponseCore m ell F (line μ w) (by simpa only [line_im] using hμ.ne') g)) :=
      Finset.sum_nonneg (fun _ _ => sq_nonneg _)
    nlinarith only [h,mul_nonneg (by positivity : 0 ≤ (sourceTime 0)^2/4) hc,
      mul_nonneg (by positivity : 0 ≤ (sourceTime 0)^2/2) hs,
      mul_nonneg (by positivity : 0 ≤ 6*(sourceTime 0)^2)
        (sq_nonneg ‖embed (phiResponseCore m ell F (line μ w) (by simpa only [line_im] using hμ.ne') g)‖)]
  calc
    _ ≤ ∫⁻ w : ℝ,ENNReal.ofReal η*P w+ENNReal.ofReal (1/(2*η))*E w := by
      apply lintegral_mono
      intro w
      dsimp only [P,E]
      rw [←ENNReal.ofReal_mul hη.le,←ENNReal.ofReal_mul (by positivity : 0 ≤ 1/(2*η)),
        ←ENNReal.ofReal_add (mul_nonneg hη.le (hp w)) (by unfold normalizedEnergy;positivity)]
      apply ENNReal.ofReal_le_ofReal
      exact (actual_phi_normalized_flux_price m ell F _ _ g η hη).trans_eq (by unfold normalizedEnergy;ring)
    _ = ENNReal.ofReal η*phiPositiveBudget m ell F μ hμ g+
        ENNReal.ofReal (1/(2*η))*(∫⁻ w : ℝ,E w) := by
      have hm : Measurable (fun w : ℝ => ENNReal.ofReal (1/(2*η))*E w) := measurable_const.mul mE
      rw [lintegral_add_right _ hm,
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      rfl
    _ ≤ ENNReal.ofReal η*phiPositiveBudget m ell F μ hμ g+
        ENNReal.ofReal (1/(2*η))*ENNReal.ofReal (2*η*ε) :=
      add_le_add (le_refl _) (mul_le_mul le_rfl hE zero_le zero_le)
    _ = _ := by
      rw [←ENNReal.ofReal_mul (by positivity : 0 ≤ 1/(2*η))]
      have he : (1/(2*η))*(2*η*ε)=ε := by field_simp [hη.ne']
      rw [he,add_comm]

end LowEnergy.SourceClockPhiRadiusNormalizedFluxBudget
