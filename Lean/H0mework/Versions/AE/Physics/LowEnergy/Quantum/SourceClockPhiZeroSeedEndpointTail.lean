/-
The actual p=S*theta*v has zero fixed seed.
The one source-H step is used only on g and rho*g, never on a moving state.
-/
import H0mework.Versions.AE.Physics.LowEnergy.Quantum.SourceClockPhiRadiusNormalizedFluxBudget
import H0mework.Versions.AE.Physics.LowEnergy.Quantum.SourceInverseVolumeSourceJetEnergy
import H0mework.Versions.AE.Physics.LowEnergy.Quantum.SourceResolventLorentzian

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1500000
set_option maxRecDepth 2048
noncomputable section
namespace LowEnergy.SourceClockPhiZeroSeedEndpointTail
open GaussCoreHilbert GaussCoreDifferential GaussFockPair GaussHistoryHilbert GaussNativeForm
open GaussDiagonalHistory GaussUnitaryHistory SourceQuantumConfigurationHilbert
open SourceQuantumScalarChart SourceQuantumGaugeSliceCoordinates SourceQuantumFockGauge
open SourceClockPhiRadiusSourceCurrent SourceClockRadiusAffineCutoff SourceClockYukawaCubicCurrent
open SourceScalarDoubleCurrent SourceScalarPositiveBulkWard SourceClockPhiRadiusResponseNativeBudget
open SourceMixedNativeReturn SourceInverseJetEnergy SourceLocalizedInverseFormPayment
open FullYSourceResolventGraphSplice SourceResolventBandLimit SourceResolventLorentzian
open MeasureTheory Filter
open scoped InnerProductSpace Topology
abbrev End := QuantumTest →ₗ[ℂ] QuantumTest
private abbrev S : End := phiInverseAction
private abbrev r : End := phiRadiusAction
attribute [local irreducible] SourceClockYukawaCubicCurrent.resolventCore
  SourceScalarPositiveBulkWard.state GaussDiagonalHistory.diagonalAction GaussAdjointHistory.coreStep

private theorem frequency_nonreal (advanced : Bool) (μ : ℝ) (hμ : 0 < μ) (w : ℝ) :
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
private theorem frequency_continuous (advanced : Bool) (μ : ℝ) (hμ : 0 < μ) (F : Index) :
    Continuous (fun w : ℝ => finiteResolvent F (actualFrequency advanced μ w)) := by
  cases advanced
  · exact SourceRetardedBandCurrent.finite_frequency_continuous μ hμ F
  · have h : (fun w : ℝ => finiteResolvent F (actualFrequency true μ w))=
        fun w : ℝ => (finiteResolvent F (line μ w)).adjoint := by
      funext w;exact finite_star F _
    exact h ▸ (ContinuousLinearMap.adjoint.continuous.comp
      (SourceRetardedBandCurrent.finite_frequency_continuous μ hμ F))

private theorem inverse_core (f : QuantumTest) :
    phiInverseBounded (embed f)=embed (S f) :=
  GaussBoundedMultiplier.extension_core _ _ _ _ _ _ f
private theorem inverse_norm : ‖phiInverseBounded‖ ≤ 1 :=
  GaussBoundedMultiplier.extension_norm _ _ _ _ _ _
private theorem inverse_contraction (f : QuantumTest) : ‖embed (S f)‖ ≤ ‖embed f‖ := by
  rw [←inverse_core]
  exact ((phiInverseBounded.le_opNorm (embed f)).trans
    (mul_le_mul_of_nonneg_right inverse_norm (norm_nonneg _))).trans_eq (one_mul _)
private theorem inverse_radius : S*r=(1:End) := by
  apply LinearMap.ext;intro f;apply DFunLike.ext;intro x
  change (phiReciprocal x:ℂ) • ((phiRadius x:ℂ) • f x)=f x
  rw [smul_smul,phiReciprocal,Complex.ofReal_inv,inv_mul_cancel₀,one_smul]
  exact Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.2 (by positivity)).ne'
private theorem inverse_theta (m ell : ℕ) : Commute S (phiThetaAction m ell) :=
  (((Commute.one_right S).sub_right (Commute.refl S)).pow_right (m+1)).sub_right
    (((Commute.one_right S).sub_right (Commute.refl S)).pow_right (ell+1))

/-- This is exactly p=c(rho*q-h), c=S*theta^2, used in the scalar endpoint. -/
def endpointState (m ell : ℕ) (F : Index) (z : ℂ) (hz : z.im≠0)
    (g : diagonal.domain) : QuantumTest := S (phiThetaAction m ell (phiResponseCore m ell F z hz g))
private theorem endpoint_source (m ell : ℕ) (F : Index) (z : ℂ) (hz : z.im≠0)
    (g : diagonal.domain) : endpointState m ell F z hz g=
      ((phiThetaAction m ell)^2) (state F z hz g)-
        S (((phiThetaAction m ell)^2) (state F z hz (phiRadiusSource g))) := by
  have hS (f : QuantumTest) : S (phiThetaAction m ell f)=phiThetaAction m ell (S f) :=
    LinearMap.congr_fun (inverse_theta m ell).eq f
  have hr (f : QuantumTest) : S (r f)=f := LinearMap.congr_fun inverse_radius f
  have hR : resolventCore F z hz (coreEquiv.symm g)=state F z hz g := by
    simp only [resolventCore,LinearMap.coe_mk,AddHom.coe_mk,coreEquiv.apply_symm_apply]
  have hρ : resolventCore F z hz (r (coreEquiv.symm g))=state F z hz (phiRadiusSource g) := by
    unfold resolventCore;rfl
  unfold endpointState phiResponseCore bracket
  simp only [LinearMap.sub_apply,Module.End.mul_apply,map_sub,hS,hr,hR,hρ,pow_two]

private def shiftedEndpoint (m ell : ℕ) (F : Index) (z : ℂ) (hz : z.im≠0)
    (g : diagonal.domain) : QuantumTest :=
  ((phiThetaAction m ell)^2) (state F z hz (GaussAdjointHistory.coreStep g))-
    S (((phiThetaAction m ell)^2) (state F z hz (GaussAdjointHistory.coreStep (phiRadiusSource g))))

/-- One common source event precedes every cutoff and frequency; the fixed seed cancels. -/
theorem actual_endpoint_source_step (g : diagonal.domain) :
    ∀ᶠ F in (sourceFilter : Filter Index),∀ m ell : ℕ,∀ z : ℂ,∀ hz : z.im≠0,
      z • endpointState m ell F z hz g=shiftedEndpoint m ell F z hz g := by
  filter_upwards [actual_source_step g,actual_source_step (phiRadiusSource g)] with F hg hh
  intro m ell z hz
  have h1 := congrArg (fun f : QuantumTest => ((phiThetaAction m ell)^2) f) (hg z hz)
  have h2 := congrArg (fun f : QuantumTest => S (((phiThetaAction m ell)^2) f)) (hh z hz)
  have hS (f : QuantumTest) : S (((phiThetaAction m ell)^2) f)=
      ((phiThetaAction m ell)^2) (S f) := LinearMap.congr_fun ((inverse_theta m ell).pow_right 2).eq f
  have hf : S (coreEquiv.symm (phiRadiusSource g))=coreEquiv.symm g := by
    unfold phiRadiusSource
    rw [coreEquiv.symm_apply_apply]
    exact LinearMap.congr_fun inverse_radius _
  rw [endpoint_source]
  unfold shiftedEndpoint
  simp only [map_sub,map_smul,hS,hf] at h1 h2 ⊢
  linear_combination (norm := module) h1-h2

private theorem theta_square (m ell : ℕ) :
    (phiThetaAction m ell)^2=
      phiThetaAction (2*m+1) (m+ell+1)-phiThetaAction (m+ell+1) (2*ell+1) := by
  unfold phiThetaAction
  have h1 : (m+1)+(m+1)=2*m+1+1 := by omega
  have h2 : (m+1)+(ell+1)=m+ell+1+1 := by omega
  have h3 : (ell+1)+(m+1)=m+ell+1+1 := by omega
  have h4 : (ell+1)+(ell+1)=2*ell+1+1 := by omega
  simp only [pow_two,sub_mul,mul_sub,←pow_add,h1,h2,h3,h4]

private theorem shifted_bound (m ell : ℕ) (F : Index) (z : ℂ) (hz : z.im≠0)
    (g : diagonal.domain) :
    ‖embed (shiftedEndpoint m ell F z hz g)‖^2 ≤ 4*(
      ‖embed (phiThetaAction (2*m+1) (m+ell+1) (state F z hz (GaussAdjointHistory.coreStep g)))‖^2+
      ‖embed (phiThetaAction (m+ell+1) (2*ell+1) (state F z hz (GaussAdjointHistory.coreStep g)))‖^2+
      ‖embed (phiThetaAction (2*m+1) (m+ell+1)
        (state F z hz (GaussAdjointHistory.coreStep (phiRadiusSource g))))‖^2+
      ‖embed (phiThetaAction (m+ell+1) (2*ell+1)
        (state F z hz (GaussAdjointHistory.coreStep (phiRadiusSource g))))‖^2) := by
  let x := embed (phiThetaAction (2*m+1) (m+ell+1) (state F z hz (GaussAdjointHistory.coreStep g)))
  let y := embed (phiThetaAction (m+ell+1) (2*ell+1) (state F z hz (GaussAdjointHistory.coreStep g)))
  let u := phiThetaAction (2*m+1) (m+ell+1) (state F z hz (GaussAdjointHistory.coreStep (phiRadiusSource g)))
  let v := phiThetaAction (m+ell+1) (2*ell+1) (state F z hz (GaussAdjointHistory.coreStep (phiRadiusSource g)))
  have he : embed (shiftedEndpoint m ell F z hz g)=x-y-embed (S (u-v)) := by
    unfold shiftedEndpoint
    rw [theta_square]
    simp only [LinearMap.sub_apply,map_sub]
    rfl
  have huv : ‖embed (u-v)‖ ≤ ‖embed u‖+‖embed v‖ := by
    rw [map_sub]
    exact norm_sub_le _ _
  have h := (norm_sub_le (x-y) (embed (S (u-v)))).trans
    (add_le_add (norm_sub_le x y) ((inverse_contraction (u-v)).trans huv))
  have hs := pow_le_pow_left₀ (norm_nonneg _) h 2
  rw [he]
  change ‖x-y-embed (S (u-v))‖^2 ≤ 4*(‖x‖^2+‖y‖^2+‖embed u‖^2+‖embed v‖^2)
  nlinarith only [hs,sq_nonneg (‖x‖-‖y‖),sq_nonneg (‖x‖-‖embed u‖),
    sq_nonneg (‖x‖-‖embed v‖),sq_nonneg (‖y‖-‖embed u‖),
    sq_nonneg (‖y‖-‖embed v‖),sq_nonneg (‖embed u‖-‖embed v‖)]

private theorem read_state (F : Index) (g : diagonal.domain) (A : End) (z : ℂ) (hz : z.im≠0) :
    sourceRead F g A (finiteResolvent F z (g:H))=embed (A (state F z hz g)) := by
  simpa only [state] using source_read_resolvent F g A z hz
private theorem theta_measurable (m ell : ℕ) (F : Index) (μ : ℝ) (hμ : 0 < μ)
    (g : diagonal.domain) (advanced : Bool) :
    Measurable (fun w : ℝ => ENNReal.ofReal (‖embed (phiThetaAction m ell
      (state F (actualFrequency advanced μ w) (frequency_nonreal advanced μ hμ w) g))‖^2)) := by
  simp_rw [←read_state]
  exact (((sourceRead F g (phiThetaAction m ell)).continuous.comp
    ((frequency_continuous advanced μ hμ F).clm_apply continuous_const)).norm.pow 2).measurable.ennreal_ofReal
private theorem shifted_measurable (m ell : ℕ) (F : Index) (μ : ℝ) (hμ : 0 < μ)
    (g : diagonal.domain) (advanced : Bool) :
    Measurable (fun w : ℝ => ENNReal.ofReal (‖embed (shiftedEndpoint m ell F
      (actualFrequency advanced μ w) (frequency_nonreal advanced μ hμ w) g)‖^2)) := by
  let g1 : diagonal.domain := GaussAdjointHistory.coreStep g
  let g2 : diagonal.domain := GaussAdjointHistory.coreStep (phiRadiusSource g)
  let A : End := (phiThetaAction m ell)^2
  let B : End := S*(phiThetaAction m ell)^2
  let X : ℝ → H := fun w => sourceRead F g1 A (finiteResolvent F (actualFrequency advanced μ w) (g1:H))
  let Y : ℝ → H := fun w => sourceRead F g2 B (finiteResolvent F (actualFrequency advanced μ w) (g2:H))
  have hp (w : ℝ) : embed (shiftedEndpoint m ell F (actualFrequency advanced μ w)
      (frequency_nonreal advanced μ hμ w) g)=X w-Y w := by
    have h1 := read_state F g1 A (actualFrequency advanced μ w) (frequency_nonreal advanced μ hμ w)
    have h2 := read_state F g2 B (actualFrequency advanced μ w) (frequency_nonreal advanced μ hμ w)
    dsimp only [X,Y]
    rw [h1,h2]
    simp only [shiftedEndpoint,g1,g2,A,B,map_sub,Module.End.mul_apply]
  have hl : Continuous X := (sourceRead F g1 A).continuous.comp
    ((frequency_continuous advanced μ hμ F).clm_apply continuous_const)
  have hr : Continuous Y := (sourceRead F g2 B).continuous.comp
    ((frequency_continuous advanced μ hμ F).clm_apply continuous_const)
  simp_rw [hp]
  exact ((hl.sub hr).norm.pow 2).measurable.ennreal_ofReal

private theorem shifted_common_tail (μ : ℝ) (hμ : 0 < μ) (g : diagonal.domain) :
    ∀ ε : ℝ,0 < ε → ∃ N : ℕ,∀ m,N ≤ m → ∀ ell,m ≤ ell →
      ∀ᶠ F in (sourceFilter : Filter Index),∀ advanced : Bool,
        (∫⁻ w : ℝ,ENNReal.ofReal (‖embed (shiftedEndpoint m ell F (actualFrequency advanced μ w)
          (frequency_nonreal advanced μ hμ w) g)‖^2)) ≤ ENNReal.ofReal ε := by
  intro ε hε
  obtain ⟨N1,h1⟩ := actual_phi_theta_common_tail μ hμ (GaussAdjointHistory.coreStep g) (ε/16) (by positivity)
  obtain ⟨N2,h2⟩ := actual_phi_theta_common_tail μ hμ (GaussAdjointHistory.coreStep (phiRadiusSource g)) (ε/16) (by positivity)
  refine ⟨max N1 N2,fun m hm ell hml => ?_⟩
  filter_upwards [h1 (2*m+1) (by omega) (m+ell+1) (by omega),
    h1 (m+ell+1) (by omega) (2*ell+1) (by omega),
    h2 (2*m+1) (by omega) (m+ell+1) (by omega),
    h2 (m+ell+1) (by omega) (2*ell+1) (by omega)] with F hX hY hZ hW
  intro advanced
  let X := fun w : ℝ => ENNReal.ofReal (‖embed (phiThetaAction (2*m+1) (m+ell+1)
    (state F (actualFrequency advanced μ w) (frequency_nonreal advanced μ hμ w) (GaussAdjointHistory.coreStep g)))‖^2)
  let Y := fun w : ℝ => ENNReal.ofReal (‖embed (phiThetaAction (m+ell+1) (2*ell+1)
    (state F (actualFrequency advanced μ w) (frequency_nonreal advanced μ hμ w) (GaussAdjointHistory.coreStep g)))‖^2)
  let Z := fun w : ℝ => ENNReal.ofReal (‖embed (phiThetaAction (2*m+1) (m+ell+1)
    (state F (actualFrequency advanced μ w) (frequency_nonreal advanced μ hμ w) (GaussAdjointHistory.coreStep (phiRadiusSource g))))‖^2)
  let W := fun w : ℝ => ENNReal.ofReal (‖embed (phiThetaAction (m+ell+1) (2*ell+1)
    (state F (actualFrequency advanced μ w) (frequency_nonreal advanced μ hμ w) (GaussAdjointHistory.coreStep (phiRadiusSource g))))‖^2)
  have my : Measurable Y := theta_measurable (m+ell+1) (2*ell+1) F μ hμ (GaussAdjointHistory.coreStep g) advanced
  have mz : Measurable Z := theta_measurable (2*m+1) (m+ell+1) F μ hμ (GaussAdjointHistory.coreStep (phiRadiusSource g)) advanced
  have mw : Measurable W := theta_measurable (m+ell+1) (2*ell+1) F μ hμ (GaussAdjointHistory.coreStep (phiRadiusSource g)) advanced
  calc
    _ ≤ ∫⁻ w : ℝ,ENNReal.ofReal 4*(X w+Y w+Z w+W w) := by
      apply lintegral_mono
      intro w
      dsimp only [X,Y,Z,W]
      rw [←ENNReal.ofReal_add (by positivity) (by positivity),
        ←ENNReal.ofReal_add (by positivity) (by positivity),
        ←ENNReal.ofReal_add (by positivity) (by positivity),←ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 4)]
      exact ENNReal.ofReal_le_ofReal (shifted_bound m ell F _ _ g)
    _=ENNReal.ofReal 4*((∫⁻ w : ℝ,X w)+(∫⁻ w : ℝ,Y w)+(∫⁻ w : ℝ,Z w)+(∫⁻ w : ℝ,W w)) := by
      rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,lintegral_add_right _ mw,
        lintegral_add_right _ mz,lintegral_add_right _ my]
    _ ≤ ENNReal.ofReal 4*(ENNReal.ofReal (ε/16)+ENNReal.ofReal (ε/16)+
        ENNReal.ofReal (ε/16)+ENNReal.ofReal (ε/16)) := by
      gcongr
      · exact hX advanced
      · exact hY advanced
      · exact hZ advanced
      · exact hW advanced
    _=ENNReal.ofReal ε := by
      rw [←ENNReal.ofReal_add (by positivity) (by positivity),
        ←ENNReal.ofReal_add (by positivity) (by positivity),
        ←ENNReal.ofReal_add (by positivity) (by positivity),←ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 4)]
      congr 1
      ring

private theorem source_young (u x b η : ℝ) (hu : 0 < u) (hη : 0 < η)
    (hb : u*x=b) : x ≤ η/(u^2)+b^2/(4*η) := by
  subst b
  have hs := sq_nonneg (2*η-u^2*x)
  apply (mul_le_mul_iff_of_pos_left (show 0 < 4*η*u^2 by positivity)).mp
  field_simp [ne_of_gt hu,ne_of_gt hη]
  nlinarith only [hs]
private theorem frequency_kernel (advanced : Bool) (μ w : ℝ) :
    (‖actualFrequency advanced μ w‖^2)⁻¹=kernel μ 0 w := by
  have hb : (‖line μ w‖^2)⁻¹=kernel μ 0 w := by
    simpa only [Complex.ofReal_zero,zero_sub,norm_inv,norm_neg,inv_pow,line,
      mul_comm Complex.I (μ:ℂ)] using inverse_norm_square μ 0 w
  cases advanced
  · exact hb
  · change (‖star (line μ w)‖^2)⁻¹=kernel μ 0 w
    rw [norm_star]
    exact hb

/-- Zero input at time zero gains a true absolute L1 tail, including both causal legs. -/
theorem actual_endpoint_absolute_common_tail (μ : ℝ) (hμ : 0 < μ) (g : diagonal.domain) :
    ∀ ε : ℝ,0 < ε → ∃ N : ℕ,∀ m,N ≤ m → ∀ ell,m ≤ ell →
      ∀ᶠ F in (sourceFilter : Filter Index),∀ advanced : Bool,
        (∫⁻ w : ℝ,ENNReal.ofReal (‖embed (endpointState m ell F (actualFrequency advanced μ w)
          (frequency_nonreal advanced μ hμ w) g)‖)) ≤ ENNReal.ofReal ε := by
  intro ε hε
  let η : ℝ := ε*μ/(2*Real.pi)
  have hη : 0 < η := by dsimp only [η];positivity
  obtain ⟨N,hN⟩ := shifted_common_tail μ hμ g (2*η*ε) (by positivity)
  refine ⟨N,fun m hm ell hml => ?_⟩
  filter_upwards [hN m hm ell hml,actual_endpoint_source_step g] with F hF hstep
  intro advanced
  let energy := fun w : ℝ => ENNReal.ofReal (‖embed (shiftedEndpoint m ell F (actualFrequency advanced μ w)
    (frequency_nonreal advanced μ hμ w) g)‖^2)
  have me : Measurable energy := shifted_measurable m ell F μ hμ g advanced
  have hk : (∫⁻ w : ℝ,ENNReal.ofReal (kernel μ 0 w))=ENNReal.ofReal (Real.pi/μ) := by
    rw [←ofReal_integral_eq_lintegral_ofReal (kernel_integrable μ 0 hμ)
      (Eventually.of_forall (fun w => by unfold kernel;positivity)),kernel_integral μ 0 hμ]
  calc
    _ ≤ ∫⁻ w : ℝ,ENNReal.ofReal η*ENNReal.ofReal (kernel μ 0 w)+ENNReal.ofReal (1/(4*η))*energy w := by
      apply lintegral_mono
      intro w
      have hn := congrArg (fun f : QuantumTest => ‖embed f‖)
        (hstep m ell (actualFrequency advanced μ w) (frequency_nonreal advanced μ hμ w))
      simp only [map_smul,norm_smul] at hn
      have hz : 0 < ‖actualFrequency advanced μ w‖ := norm_pos_iff.mpr (by
        intro hz
        exact frequency_nonreal advanced μ hμ w (by rw [hz];rfl))
      have hp := source_young _ _ _ η hz hη hn
      rw [div_eq_mul_inv,frequency_kernel] at hp
      dsimp only [energy]
      rw [←ENNReal.ofReal_mul (by positivity),←ENNReal.ofReal_mul (by positivity),
        ←ENNReal.ofReal_add (by unfold kernel;positivity) (by positivity)]
      apply ENNReal.ofReal_le_ofReal
      exact hp.trans_eq (by ring)
    _=ENNReal.ofReal η*ENNReal.ofReal (Real.pi/μ)+
        ENNReal.ofReal (1/(4*η))*(∫⁻ w : ℝ,energy w) := by
      rw [lintegral_add_right _ (me.const_mul _),
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,hk]
    _ ≤ ENNReal.ofReal η*ENNReal.ofReal (Real.pi/μ)+
        ENNReal.ofReal (1/(4*η))*ENNReal.ofReal (2*η*ε) := by
      gcongr
      exact hF advanced
    _=ENNReal.ofReal ε := by
      rw [←ENNReal.ofReal_mul hη.le,←ENNReal.ofReal_mul (by positivity),
        ←ENNReal.ofReal_add (by positivity) (by positivity)]
      congr 1
      dsimp only [η]
      field_simp
      ring

private abbrev radiusSquareCurrent : End :=
  bracket diagonalAction SourceClockPhiRadiusAcceleration.phiSquare
private theorem radius_square_current_pair (f k : QuantumTest) :
    sourcePair f (radiusSquareCurrent k)= -sourcePair (radiusSquareCurrent f) k := by
  have hr (u v : QuantumTest) : sourcePair u (r v)=sourcePair (r u) v := multiply_pair _ _ _ _
  have hrr (u v : QuantumTest) : sourcePair u ((r^2) v)=sourcePair ((r^2) u) v := by
    simp only [pow_two,Module.End.mul_apply]
    rw [hr,hr]
  have hsR (u v w : QuantumTest) : sourcePair u (v-w)=sourcePair u v-sourcePair u w := by
    simp only [sourcePair,map_sub,inner_sub_right]
  have hsL (u v w : QuantumTest) : sourcePair (u-v) w=sourcePair u w-sourcePair v w := by
    simp only [sourcePair,map_sub,inner_sub_left]
  unfold radiusSquareCurrent bracket SourceClockPhiRadiusAcceleration.phiSquare
  simp only [LinearMap.sub_apply,Module.End.mul_apply,hsR,hsL]
  rw [diagonalAction_pair,hrr,←diagonalAction_pair,hrr]
  ring

/-- Direct payment of the actual fixed B*g endpoint created by acceleration lowering. -/
theorem actual_phi_acceleration_fixed_endpoint_tail (μ : ℝ) (hμ : 0 < μ) (g : diagonal.domain) :
    ∀ ε : ℝ,0 < ε → ∃ N : ℕ,∀ m,N ≤ m → ∀ ell,m ≤ ell →
      ∀ᶠ F in (sourceFilter : Filter Index),∀ advanced : Bool,
        (∫⁻ w : ℝ,ENNReal.ofReal (‖sourcePair (coreEquiv.symm g)
          (radiusSquareCurrent (endpointState m ell F (actualFrequency advanced μ w)
            (frequency_nonreal advanced μ hμ w) g))‖)) ≤ ENNReal.ofReal ε := by
  intro ε hε
  let C : ℝ := ‖embed (radiusSquareCurrent (coreEquiv.symm g))‖
  have hC : 0 ≤ C := norm_nonneg _
  obtain ⟨N,hN⟩ := actual_endpoint_absolute_common_tail μ hμ g (ε/(C+1)) (by positivity)
  refine ⟨N,fun m hm ell hml => ?_⟩
  filter_upwards [hN m hm ell hml] with F hF
  intro advanced
  calc
    _ ≤ ∫⁻ w : ℝ,ENNReal.ofReal C*ENNReal.ofReal
        (‖embed (endpointState m ell F (actualFrequency advanced μ w)
          (frequency_nonreal advanced μ hμ w) g)‖) := by
      apply lintegral_mono
      intro w
      dsimp only
      have hp := radius_square_current_pair (coreEquiv.symm g)
        (endpointState m ell F (actualFrequency advanced μ w) (frequency_nonreal advanced μ hμ w) g)
      rw [hp,norm_neg,←ENNReal.ofReal_mul hC]
      exact ENNReal.ofReal_le_ofReal (norm_inner_le_norm _ _)
    _=ENNReal.ofReal C*(∫⁻ w : ℝ,ENNReal.ofReal
        (‖embed (endpointState m ell F (actualFrequency advanced μ w)
          (frequency_nonreal advanced μ hμ w) g)‖)) := by
      rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    _ ≤ ENNReal.ofReal C*ENNReal.ofReal (ε/(C+1)) := by
      gcongr
      exact hF advanced
    _ ≤ ENNReal.ofReal ε := by
      rw [←ENNReal.ofReal_mul hC]
      apply ENNReal.ofReal_le_ofReal
      rw [←mul_div_assoc]
      apply (div_le_iff₀ (show 0 < C+1 by positivity)).mpr
      nlinarith

end LowEnergy.SourceClockPhiZeroSeedEndpointTail
