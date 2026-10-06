import H0mework.Versions.AD.Physics.LowEnergy.Quantum.SourceScalarPositiveBulkWard
import H0mework.Versions.AD.Physics.LowEnergy.Quantum.SourceFixedJetBudget

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 800000
set_option maxRecDepth 2048
noncomputable section
namespace LowEnergy.SourceScalarPositiveBulkEndpoint
open GaussCoreHilbert GaussCoreDifferential GaussFockPair GaussHistoryHilbert GaussNativeEnergy
open GaussDiagonalHistory GaussUnitaryHistory GaussNativeForm SourceCoframeVolume
open SourceCoframeVolumeCurrent SourceCoframeDilation SourceHamiltonianScaleJet SourceScalarGaugeScale
open SourceScalarVirialBulk SourceScalarPositiveBulkWard SourceGaugeCoframeJets
open FullYSourceResolventGraphSplice SourceResolventBandLimit SourceRelativePowerTail
open SourceHardyRetardedTail SourceRetardedBandCurrent MeasureTheory Filter
open scoped InnerProductSpace ENNReal
abbrev End := SourceScalarPositiveBulkWard.End

private theorem flow_pair_generator (flow : ℝ → End) (G : End)
    (hzero : ∀ f,flow 0 f=f)
    (hpair : ∀ t f g,sourcePair (flow t f) (flow t g)=sourcePair f g)
    (hderiv : ∀ f,HasDerivAt (fun t : ℝ => embed (flow t f)) (embed (G f)) 0)
    (f g : QuantumTest) : sourcePair f (G g)= -sourcePair (G f) g := by
  have h := (hderiv f).inner ℂ (hderiv g)
  simp only [hzero] at h
  have he : (fun t : ℝ => inner ℂ (embed (flow t f)) (embed (flow t g)))=
      fun _ => sourcePair f g := funext (fun t => hpair t f g)
  rw [he] at h
  have heq := h.unique (hasDerivAt_const (0 : ℝ) (sourcePair f g))
  exact eq_neg_of_add_eq_zero_left heq
private theorem phi_pair (f g : QuantumTest) : sourcePair f (Phi g)= -sourcePair (Phi f) g :=
  flow_pair_generator SourceScalarAffineScaleTransport.coreFlow Phi
    SourceScalarAffineScaleTransport.coreFlow_zero SourceScalarAffineScaleTransport.coreFlow_pair
    (fun q => by simpa only [SourceScalarAffineScaleTransport.coreFlow_zero] using!
      SourceScalarAffineScaleTransport.strong_core_derivative q 0) f g
private theorem gauge_pair (f g : QuantumTest) : sourcePair f (Gauge g)= -sourcePair (Gauge f) g :=
  flow_pair_generator SourceGaugeScaleTransport.coreFlow Gauge
    SourceGaugeScaleTransport.coreFlow_zero SourceGaugeScaleTransport.coreFlow_pair
    (fun q => by simpa only [SourceGaugeScaleTransport.coreFlow_zero] using!
      SourceGaugeScaleTransport.strong_core_derivative q 0) f g
private theorem coframe_pair (f g : QuantumTest) : sourcePair f (Coframe g)= -sourcePair (Coframe f) g := by
  have hc : star (3*Complex.I/2 : ℂ)= -(3*Complex.I/2 : ℂ) := by simp;ring
  have hd := dilation_pair f g
  change sourcePair f ((3*Complex.I/2 : ℂ) • dilation g)=
    -sourcePair ((3*Complex.I/2 : ℂ) • dilation f) g
  simp only [sourcePair,map_smul,inner_smul_left,inner_smul_right,starRingEnd_apply] at hd ⊢
  rw [hc,hd]
  ring

private def volumePair (f g : QuantumTest) : PairMatrix := fun A B => sourcePair (A f) (volumeAction (B g))
private theorem volume_pair_delta (G : End) (c : ℂ)
    (hG : ∀ f g,sourcePair f (G g)= -sourcePair (G f) g)
    (hc : G*volumeAction-volumeAction*G=c • volumeAction) (f g : QuantumTest) :
    pairDelta G (volumePair f g)=c • volumePair f g := by
  ext A B
  have h := congrArg (fun M : End => sourcePair (A f) (M (B g))) hc
  change sourcePair (A f) (G (volumeAction (B g))-volumeAction (G (B g)))=
    sourcePair (A f) (c • volumeAction (B g)) at h
  simp only [sourcePair,map_sub,map_smul,inner_sub_right,inner_smul_right] at h
  have hg := hG (A f) (volumeAction (B g))
  simp only [sourcePair] at hg
  rw [hg] at h
  exact h

private theorem volume_phi (f g : QuantumTest) : pairDelta Phi (volumePair f g)=0 := by
  have h : Phi*volumeAction-volumeAction*Phi=(0 : ℂ) • volumeAction := by
    rw [SourceScalarAffineScaleTransport.generator_commutator,original_volume_phi,zero_smul]
  simpa only [zero_smul] using! volume_pair_delta Phi 0 phi_pair h f g
private theorem volume_gauge (f g : QuantumTest) : pairDelta Gauge (volumePair f g)=0 := by
  have h : Gauge*volumeAction-volumeAction*Gauge=(0 : ℂ) • volumeAction := by
    rw [SourceGaugeScaleTransport.generator_commutator,original_volume_gauge,zero_smul]
  simpa only [zero_smul] using! volume_pair_delta Gauge 0 gauge_pair h f g
private theorem volume_coframe (f g : QuantumTest) : pairDelta Coframe (volumePair f g)=(3 : ℂ) • volumePair f g := by
  have h : Coframe*volumeAction-volumeAction*Coframe=(3 : ℂ) • volumeAction := by
    rw [K_commutator]
    change (3*Complex.I/2) • (dilation*volumeAction-volumeAction*dilation)=_
    rw [SourceDilationKinetic.volume_scale_current,smul_smul]
    congr 1
    calc (3*Complex.I/2)*(-2*Complex.I) = -3*(Complex.I*Complex.I) := by ring
         _ = 3 := by rw [Complex.I_mul_I];ring
  exact volume_pair_delta Coframe 3 coframe_pair h f g

private theorem fixed_pair_split (F : Index) (zl zr : ℂ) (hl : zl.im≠0) (hr : zr.im≠0)
    (g k : diagonal.domain) : fixedPair F zl zr hl hr g k=
      (1/2 : ℂ) • (volumePair (coreEquiv.symm k) (state F zr hr g)+
        volumePair (state F zl hl k) (coreEquiv.symm g)) := by
  ext A B
  change (1/2 : ℂ)*(_+sourcePair (volumeAction (A (state F zl hl k))) (B (coreEquiv.symm g)))=
    (1/2 : ℂ)*(_+sourcePair (A (state F zl hl k)) (volumeAction (B (coreEquiv.symm g))))
  have h : sourcePair (A (state F zl hl k)) (volumeAction (B (coreEquiv.symm g)))=
      sourcePair (volumeAction (A (state F zl hl k))) (B (coreEquiv.symm g)) := multiply_pair _ _ _ _
  rw [h]
  rfl

private theorem polynomial_eigen {V : Type*} [AddCommGroup V] [Module ℂ V]
    (dp dg dc : V →ₗ[ℂ] V) (x : V) (hp : dp x=0) (hg : dg x=0) (hc : dc x=(3 : ℂ) • x) :
    polynomial dp dg dc x=(-6*(vacuumJetCoefficient : ℂ)) • x := by
  simp only [polynomial,hp,hg,hc,map_smul,map_add,map_sub,map_zero,sub_self,smul_zero,zero_add,add_zero]
  module

private theorem eigen_combination {V : Type*} [AddCommGroup V] [Module ℂ V]
    (d : V →ₗ[ℂ] V) (x y z : V) (a c : ℂ) (hz : z=a • (x+y))
    (hx : d x=c • x) (hy : d y=c • y) : d z=c • z := by
  rw [hz,map_smul,map_add,hx,hy,←smul_add,smul_comm a c]

/-- The complete fixed-source polynomial collapses before estimating any mixed jet. -/
theorem actual_fixed_bulk_collapse (F : Index) (zl zr : ℂ) (hl : zl.im≠0) (hr : zr.im≠0)
    (g k : diagonal.domain) : fixedBulk F zl zr hl hr g k=
      (-6*(vacuumJetCoefficient : ℂ)) • fixedPair F zl zr hl hr g k := by
  unfold fixedBulk
  apply polynomial_eigen
  · have h := eigen_combination (pairDelta Phi) _ _ _ (1/2 : ℂ) 0
      (fixed_pair_split F zl zr hl hr g k)
      (by simpa only [zero_smul] using! volume_phi (coreEquiv.symm k) (state F zr hr g))
      (by simpa only [zero_smul] using! volume_phi (state F zl hl k) (coreEquiv.symm g))
    simpa only [zero_smul] using! h
  · have h := eigen_combination (pairDelta Gauge) _ _ _ (1/2 : ℂ) 0
      (fixed_pair_split F zl zr hl hr g k)
      (by simpa only [zero_smul] using! volume_gauge (coreEquiv.symm k) (state F zr hr g))
      (by simpa only [zero_smul] using! volume_gauge (state F zl hl k) (coreEquiv.symm g))
    simpa only [zero_smul] using! h
  · exact eigen_combination (pairDelta Coframe) _ _ _ (1/2 : ℂ) 3
      (fixed_pair_split F zl zr hl hr g k)
      (volume_coframe (coreEquiv.symm k) (state F zr hr g))
      (volume_coframe (state F zl hl k) (coreEquiv.symm g))

abbrev theta (m ell : ℕ) : End := SourceNativeCutoffContact.thetaAction m ell

def endpoint (m ell : ℕ) (f : QuantumTest) : QuantumTest := theta m ell (theta m ell (volumeAction f))
private theorem theta_volume (m ell : ℕ) : Commute (theta m ell) volumeAction := by
  apply LinearMap.ext
  intro f
  apply DFunLike.ext
  intro z
  exact smul_comm (SourceNativeCutoffContact.theta m ell z : ℂ) (volume z : ℂ) (f z)
private theorem theta_pair (m ell : ℕ) (f g : QuantumTest) :
    sourcePair f (theta m ell g)=sourcePair (theta m ell f) g := multiply_pair _ _ _ _
private theorem endpoint_pair (m ell : ℕ) (f g : QuantumTest) :
    sourcePair (theta m ell f) (volumeAction (theta m ell g))=sourcePair (endpoint m ell f) g := by
  have hU : sourcePair (theta m ell f) (volumeAction (theta m ell g))=
      sourcePair (volumeAction (theta m ell f)) (theta m ell g) := multiply_pair _ _ _ _
  rw [hU,theta_pair]
  exact congrArg (fun q : QuantumTest => sourcePair q g)
    (congrArg (theta m ell) (LinearMap.congr_fun (theta_volume m ell).eq f).symm)
private theorem endpoint_pair_right (m ell : ℕ) (f g : QuantumTest) :
    sourcePair (volumeAction (theta m ell f)) (theta m ell g)=sourcePair f (endpoint m ell g) := by
  have hU : sourcePair (volumeAction (theta m ell f)) (theta m ell g)=
      sourcePair (theta m ell f) (volumeAction (theta m ell g)) := (multiply_pair _ _ _ _).symm
  rw [hU,←theta_pair]
  exact congrArg (sourcePair f) (congrArg (theta m ell) (LinearMap.congr_fun (theta_volume m ell).eq g).symm)
private theorem core_embed (g : diagonal.domain) : embed (coreEquiv.symm g)=(g : H) :=
  congrArg Subtype.val (coreEquiv.apply_symm_apply g)
private theorem state_embed (F : Index) (z : ℂ) (hz : z.im≠0) (g : diagonal.domain) :
    embed (state F z hz g)=finiteResolvent F z (g : H) := core_embed _

private theorem core_fixed_pair (m ell : ℕ) (k g p q : QuantumTest) :
    (1/2 : ℂ)*(sourcePair (theta m ell k) (volumeAction (theta m ell q))+
      sourcePair (volumeAction (theta m ell p)) (theta m ell g))=
    (1/2 : ℂ)*(sourcePair (endpoint m ell k) q+sourcePair p (endpoint m ell g)) := by
  rw [endpoint_pair,endpoint_pair_right]

private theorem resolvent_pair {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    (C : E →L[ℂ] E) (hC : IsSelfAdjoint C) (z : ℂ) (hz : z.im≠0) (k f : E) :
    inner ℂ k (FullYSourceResolventGraphSplice.resolvent C z f)=
      inner ℂ (FullYSourceResolventGraphSplice.resolvent C (star z) k) f := by
  have hk := congrArg (fun A : E →L[ℂ] E => A k) (resolvent_right C hC (star z) (by simpa only [Complex.star_def,Complex.conj_im,neg_ne_zero] using hz))
  have hf := congrArg (fun A : E →L[ℂ] E => A f) (resolvent_right C hC z hz)
  change C (FullYSourceResolventGraphSplice.resolvent C (star z) k)-
    star z • FullYSourceResolventGraphSplice.resolvent C (star z) k=k at hk
  change C (FullYSourceResolventGraphSplice.resolvent C z f)-
    z • FullYSourceResolventGraphSplice.resolvent C z f=f at hf
  have hs : inner ℂ (C (FullYSourceResolventGraphSplice.resolvent C (star z) k))
      (FullYSourceResolventGraphSplice.resolvent C z f)=
      inner ℂ (FullYSourceResolventGraphSplice.resolvent C (star z) k)
        (C (FullYSourceResolventGraphSplice.resolvent C z f)) := hC.isSymmetric _ _
  calc
    _ = inner ℂ (C (FullYSourceResolventGraphSplice.resolvent C (star z) k)-
      star z • FullYSourceResolventGraphSplice.resolvent C (star z) k)
      (FullYSourceResolventGraphSplice.resolvent C z f) := congrArg (fun x => inner ℂ x _) hk.symm
    _ = inner ℂ (FullYSourceResolventGraphSplice.resolvent C (star z) k)
      (C (FullYSourceResolventGraphSplice.resolvent C z f)-z • FullYSourceResolventGraphSplice.resolvent C z f) := by
      rw [inner_sub_left,inner_smul_left,inner_sub_right,inner_smul_right,hs,
        starRingEnd_apply,star_star]
    _ = _ := congrArg (fun x => inner ℂ _ x) hf


/-- Both actual endpoints are fixed original tests carrying θ²U; no derivative of a varying RF state remains. -/
theorem actual_fixed_bulk_endpoints (m ell : ℕ) (F : Index) (z : ℂ) (hz : z.im≠0) (g k : diagonal.domain) :
    let hs : (star z).im≠0 := by simpa only [Complex.star_def,Complex.conj_im,neg_ne_zero] using hz
    fixedBulk F (star z) z hs hz g k (theta m ell) (theta m ell)=
      (-3*(vacuumJetCoefficient : ℂ))*(
        inner ℂ (embed (endpoint m ell (coreEquiv.symm k))) (finiteResolvent F z (g : H))+
        inner ℂ (k : H) (finiteResolvent F z (embed (endpoint m ell (coreEquiv.symm g))))) := by
  intro hs
  have h0 := congrArg (fun P : PairMatrix => P (theta m ell) (theta m ell))
    (actual_fixed_bulk_collapse F (star z) z hs hz g k)
  have h1 := core_fixed_pair m ell (coreEquiv.symm k) (coreEquiv.symm g)
    (state F (star z) hs k) (state F z hz g)
  change fixedPair F (star z) z hs hz g k (theta m ell) (theta m ell)=
    (1/2 : ℂ)*(sourcePair (endpoint m ell (coreEquiv.symm k)) (state F z hz g)+
      sourcePair (state F (star z) hs k) (endpoint m ell (coreEquiv.symm g))) at h1
  simp only [sourcePair,state_embed] at h1
  have hR := resolvent_pair (GaussGradedCompression.compression F)
    (GaussGradedCompression.compression_selfAdjoint F) z hz (k : H)
      (embed (endpoint m ell (coreEquiv.symm g)))
  change inner ℂ (k : H) (finiteResolvent F z (embed (endpoint m ell (coreEquiv.symm g))))=
    inner ℂ (finiteResolvent F (star z) (k : H)) (embed (endpoint m ell (coreEquiv.symm g))) at hR
  have h2 := congrArg (fun c : ℂ => (1/2 : ℂ)*(
    inner ℂ (embed (endpoint m ell (coreEquiv.symm k))) (finiteResolvent F z (g : H))+c)) hR.symm
  have h3 := h1.trans h2
  change fixedBulk F (star z) z hs hz g k (theta m ell) (theta m ell)=
    (-6*(vacuumJetCoefficient : ℂ))*fixedPair F (star z) z hs hz g k (theta m ell) (theta m ell) at h0
  exact h0.trans ((congrArg (fun c : ℂ => (-6*(vacuumJetCoefficient : ℂ))*c) h3).trans (by ring))

private theorem endpoint_bound (m ell : ℕ) (hell : m ≤ ell) (f : QuantumTest) :
    ‖embed (endpoint m ell f)‖ ≤ ‖relativeTail m ell (embed (volumeAction f))‖ := by
  rw [endpoint,SourceNativeCutoffContact.theta_core,SourceNativeCutoffContact.theta_core]
  exact relative_tail_contraction m ell hell _

private theorem endpoint_tail (f : QuantumTest) (C : ℝ) (hC : 0 ≤ C) :
    ∀ ε : ℝ,0<ε → ∃ N : ℕ,∀ m,N ≤ m → ∀ ell,m ≤ ell → C*‖embed (endpoint m ell f)‖^2 ≤ ε := by
  intro ε hε
  have hp : 0<C+1 := by linarith
  obtain ⟨N,hN⟩ := original_relative_tail (embed (volumeAction f))
    (Real.sqrt (ε/(C+1))) (Real.sqrt_pos.mpr (div_pos hε hp))
  refine ⟨N,fun m hm ell hell => ?_⟩
  have hb := (endpoint_bound m ell hell f).trans (hN m hm ell hell).le
  have hs := Real.sq_sqrt (div_pos hε hp).le
  have hb2 : ‖embed (endpoint m ell f)‖^2 ≤ ε/(C+1) := by
    nlinarith [norm_nonneg (embed (endpoint m ell f)),Real.sqrt_nonneg (ε/(C+1))]
  calc
    _ ≤ (C+1)*‖embed (endpoint m ell f)‖^2 := by nlinarith [sq_nonneg ‖embed (endpoint m ell f)‖]
    _ ≤ (C+1)*(ε/(C+1)) := mul_le_mul_of_nonneg_left hb2 hp.le
    _ = ε := mul_div_cancel₀ ε hp.ne'

private theorem response_energy (F : Index) (μ : ℝ) (hμ : 0<μ) (x y : H) :
    (∫⁻ w : ℝ,ENNReal.ofReal (‖inner ℂ x (finiteResolvent F (line μ w) y)‖^2)) ≤
      ENNReal.ofReal ((Real.pi/μ)*‖x‖^2*‖y‖^2) := by
  have he : (∫⁻ w : ℝ,ENNReal.ofReal (‖finiteResolvent F (line μ w) y‖^2))=
      ENNReal.ofReal ((Real.pi/μ)*‖y‖^2) := by
    simpa only [line,mul_comm (μ : ℂ) Complex.I] using! SourceActualResolventEnergy.actual_square_lintegral F μ hμ y
  calc
    _ ≤ ∫⁻ w : ℝ,ENNReal.ofReal (‖x‖^2)*ENNReal.ofReal (‖finiteResolvent F (line μ w) y‖^2) := by
      apply lintegral_mono
      intro w
      dsimp only
      rw [←ENNReal.ofReal_mul (sq_nonneg _)]
      exact ENNReal.ofReal_le_ofReal ((pow_le_pow_left₀ (norm_nonneg _)
        (norm_inner_le_norm x (finiteResolvent F (line μ w) y)) 2).trans_eq (mul_pow _ _ _))
    _=ENNReal.ofReal (‖x‖^2)*∫⁻ w : ℝ,ENNReal.ofReal (‖finiteResolvent F (line μ w) y‖^2) :=
      lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _=_ := by rw [he,←ENNReal.ofReal_mul (sq_nonneg _)];congr 1;ring

private theorem two_energy (F : Index) (μ : ℝ) (hμ : 0<μ) (c : ℂ) (x y u v : H) :
    (∫⁻ w : ℝ,ENNReal.ofReal (‖c*(inner ℂ x (finiteResolvent F (line μ w) y)+
      inner ℂ u (finiteResolvent F (line μ w) v))‖^2)) ≤
      ENNReal.ofReal ((2*‖c‖^2)*(Real.pi/μ)*(‖x‖^2*‖y‖^2+‖u‖^2*‖v‖^2)) := by
  let a := fun w => inner ℂ x (finiteResolvent F (line μ w) y)
  let b := fun w => inner ℂ u (finiteResolvent F (line μ w) v)
  have hm : Measurable (fun w : ℝ => ENNReal.ofReal (‖a w‖^2)) :=
    ((continuous_const.inner ((finite_frequency_continuous μ hμ F).clm_apply continuous_const)).norm.pow 2).measurable.ennreal_ofReal
  have hs (w : ℝ) : ‖c*(a w+b w)‖^2 ≤ (2*‖c‖^2)*(‖a w‖^2+‖b w‖^2) := by
    have ht := norm_add_le (a w) (b w)
    have hp : ‖a w+b w‖^2 ≤ 2*(‖a w‖^2+‖b w‖^2) := by
      nlinarith [norm_nonneg (a w+b w),norm_nonneg (a w),norm_nonneg (b w),sq_nonneg (‖a w‖-‖b w‖)]
    rw [norm_mul,mul_pow]
    nlinarith [mul_le_mul_of_nonneg_left hp (sq_nonneg ‖c‖)]
  calc
    _ ≤ ∫⁻ w : ℝ,ENNReal.ofReal (2*‖c‖^2)*(ENNReal.ofReal (‖a w‖^2)+ENNReal.ofReal (‖b w‖^2)) := by
      apply lintegral_mono
      intro w
      dsimp only
      rw [←ENNReal.ofReal_add (sq_nonneg _) (sq_nonneg _),←ENNReal.ofReal_mul (by positivity : 0 ≤ 2*‖c‖^2)]
      exact ENNReal.ofReal_le_ofReal (hs w)
    _ = ENNReal.ofReal (2*‖c‖^2)*((∫⁻ w : ℝ,ENNReal.ofReal (‖a w‖^2))+(∫⁻ w : ℝ,ENNReal.ofReal (‖b w‖^2))) := by
      rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,lintegral_add_left hm]
    _ ≤ ENNReal.ofReal (2*‖c‖^2)*(ENNReal.ofReal ((Real.pi/μ)*‖x‖^2*‖y‖^2)+
        ENNReal.ofReal ((Real.pi/μ)*‖u‖^2*‖v‖^2)) :=
      mul_le_mul le_rfl (add_le_add (response_energy F μ hμ x y) (response_energy F μ hμ u v)) (by positivity) (by positivity)
    _ = _ := by
      rw [←ENNReal.ofReal_add (by positivity) (by positivity),←ENNReal.ofReal_mul (by positivity : 0 ≤ 2*‖c‖^2)]
      congr 1
      ring

/-- This is the literal new fixedBulk, and the threshold is independent of F and the upper cutoff. -/
theorem actual_fixed_bulk_tail (μ : ℝ) (hμ : 0<μ) (g k : diagonal.domain) :
    ∀ ε : ℝ,0<ε → ∃ N : ℕ,∀ m,N ≤ m → ∀ ell,m ≤ ell → ∀ F : Index,
      (∫⁻ w : ℝ,ENNReal.ofReal (‖fixedBulk F (star (line μ w)) (line μ w)
        (by simpa only [Complex.star_def,Complex.conj_im,line_im,neg_ne_zero] using hμ.ne')
        (by simpa only [line_im] using hμ.ne') g k (theta m ell) (theta m ell)‖^2)) ≤
        ENNReal.ofReal ε := by
  intro ε hε
  let C := (2*‖-3*(vacuumJetCoefficient : ℂ)‖^2)*(Real.pi/μ)
  have hC : 0 ≤ C := by dsimp [C];positivity
  obtain ⟨N₁,h₁⟩ := endpoint_tail (coreEquiv.symm k) (C*‖(g : H)‖^2)
    (mul_nonneg hC (sq_nonneg _)) (ε/2) (by positivity)
  obtain ⟨N₂,h₂⟩ := endpoint_tail (coreEquiv.symm g) (C*‖(k : H)‖^2)
    (mul_nonneg hC (sq_nonneg _)) (ε/2) (by positivity)
  refine ⟨max N₁ N₂,fun m hm ell hell F => ?_⟩
  have hl := h₁ m (le_trans (Nat.le_max_left _ _) hm) ell hell
  have hr := h₂ m (le_trans (Nat.le_max_right _ _) hm) ell hell
  have hb := two_energy F μ hμ (-3*(vacuumJetCoefficient : ℂ))
    (embed (endpoint m ell (coreEquiv.symm k))) (g : H) (k : H) (embed (endpoint m ell (coreEquiv.symm g)))
  simp_rw [actual_fixed_bulk_endpoints] at ⊢
  apply hb.trans
  apply ENNReal.ofReal_le_ofReal
  change C*(_+_) ≤ ε
  nlinarith


/-- Literal localized positive source response minus its complete signed defect/frequency part. -/
def bulkDifference (m ell : ℕ) (F : Index) (z : ℂ) (hz : z.im≠0) (g k : diagonal.domain) : ℂ :=
  let hs : (star z).im≠0 := by simpa only [Complex.star_def,Complex.conj_im,neg_ne_zero] using hz
  let p := theta m ell (state F (star z) hs k)
  let q := theta m ell (state F z hz g)
  sourcePair p (volumeAction (positiveBulk q))-
    (defectBulk F (star z) z hs hz g k (theta m ell) (theta m ell)-
      (6*(vacuumJetCoefficient : ℂ)*z)*sourcePair p (volumeAction q))

private theorem bulk_difference_return (m ell : ℕ) (F : Index) (z : ℂ) (hz : z.im≠0) (g k : diagonal.domain) :
    let hs : (star z).im≠0 := by simpa only [Complex.star_def,Complex.conj_im,neg_ne_zero] using hz
    bulkDifference m ell F z hz g k=fixedBulk F (star z) z hs hz g k (theta m ell) (theta m ell) := by
  intro hs
  have h := actual_positive_bulk_normal F (star z) z hs hz g k (theta m ell) (theta m ell)
  simp only [star_star] at h
  dsimp only [bulkDifference]
  linear_combination h

/-- The original localized positive bulk differs from its full signed defect/frequency word by the paid all-F endpoint tail. -/
theorem actual_complete_bulk_difference_tail (μ : ℝ) (hμ : 0<μ) (g k : diagonal.domain) :
    ∀ ε : ℝ,0<ε → ∃ N : ℕ,∀ m,N ≤ m → ∀ ell,m ≤ ell → ∀ F : Index,
      (∫⁻ w : ℝ,ENNReal.ofReal (‖bulkDifference m ell F (line μ w)
        (by simpa only [line_im] using hμ.ne') g k‖^2)) ≤ ENNReal.ofReal ε := by
  simp_rw [bulk_difference_return]
  exact actual_fixed_bulk_tail μ hμ g k

end LowEnergy.SourceScalarPositiveBulkEndpoint
