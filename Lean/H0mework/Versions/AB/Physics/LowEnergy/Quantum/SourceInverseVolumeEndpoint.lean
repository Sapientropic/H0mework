import H0mework.Versions.AB.Physics.LowEnergy.Quantum.SourceInverseVolumeRetarded
import H0mework.Versions.AB.Physics.LowEnergy.Quantum.SourceScalarPositiveBulkEndpoint

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 1000000
set_option maxRecDepth 2048
noncomputable section
namespace LowEnergy.SourceScalarInverseEndpoint
open GaussCoreHilbert GaussCoreDifferential GaussFockPair GaussHistoryHilbert GaussNativeEnergy
open GaussDiagonalHistory GaussUnitaryHistory GaussNativeForm SourceCoframeVolume
open SourceCoframeVolumeCurrent SourcePhysicalKineticSquare SourceScalarVirialBulk
open SourceScalarPositiveBulkWard
open FullYSourceResolventGraphSplice SourceResolventBandLimit SourceRelativePowerTail
open SourceHardyRetardedTail SourceRetardedBandCurrent MeasureTheory Filter
open scoped InnerProductSpace ENNReal
abbrev End := SourceScalarPositiveBulkWard.End
abbrev theta (m ell : ℕ) : End := SourceNativeCutoffContact.thetaAction m ell

def endpoint (m ell : ℕ) (f : QuantumTest) : QuantumTest :=
  theta m ell (theta m ell (inverseVolumeAction f))

private theorem theta_inverse (m ell : ℕ) : Commute (theta m ell) inverseVolumeAction := by
  apply LinearMap.ext
  intro f
  apply DFunLike.ext
  intro z
  exact smul_comm (SourceNativeCutoffContact.theta m ell z : ℂ) (reciprocalVolume z : ℂ) (f z)

private theorem theta_pair (m ell : ℕ) (f g : QuantumTest) :
    sourcePair f (theta m ell g)=sourcePair (theta m ell f) g := multiply_pair _ _ _ _

private theorem endpoint_pair (m ell : ℕ) (f g : QuantumTest) :
    sourcePair (inverseVolumeAction (theta m ell f))
      (volumeAction (inverseVolumeAction (theta m ell g)))=sourcePair (endpoint m ell f) g := by
  rw [volume_inverse,theta_pair]
  exact congrArg (fun q : QuantumTest => sourcePair q g)
    (congrArg (theta m ell) (LinearMap.congr_fun (theta_inverse m ell).eq f).symm)

private theorem endpoint_pair_right (m ell : ℕ) (f g : QuantumTest) :
    sourcePair (volumeAction (inverseVolumeAction (theta m ell f)))
      (inverseVolumeAction (theta m ell g))=sourcePair f (endpoint m ell g) := by
  rw [volume_inverse,←theta_pair]
  exact congrArg (sourcePair f)
    (congrArg (theta m ell) (LinearMap.congr_fun (theta_inverse m ell).eq g).symm)

private theorem core_embed (g : diagonal.domain) : embed (coreEquiv.symm g)=(g : H) :=
  congrArg Subtype.val (coreEquiv.apply_symm_apply g)
private theorem state_embed (F : Index) (z : ℂ) (hz : z.im≠0) (g : diagonal.domain) :
    embed (state F z hz g)=finiteResolvent F z (g : H) := core_embed _

private theorem core_fixed_pair (m ell : ℕ) (k g p q : QuantumTest) :
    (1/2 : ℂ)*(sourcePair (inverseVolumeAction (theta m ell k))
      (volumeAction (inverseVolumeAction (theta m ell q)))+
      sourcePair (volumeAction (inverseVolumeAction (theta m ell p)))
        (inverseVolumeAction (theta m ell g)))=
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


theorem actual_fixed_bulk_endpoints (m ell : ℕ) (F : Index) (z : ℂ) (hz : z.im≠0) (g k : diagonal.domain) :
    let hs : (star z).im≠0 := by simpa only [Complex.star_def,Complex.conj_im,neg_ne_zero] using hz
    fixedBulk F (star z) z hs hz g k (inverseVolumeAction*theta m ell) (inverseVolumeAction*theta m ell)=
      (-3*(vacuumJetCoefficient : ℂ))*(
        inner ℂ (embed (endpoint m ell (coreEquiv.symm k))) (finiteResolvent F z (g : H))+
        inner ℂ (k : H) (finiteResolvent F z (embed (endpoint m ell (coreEquiv.symm g))))) := by
  intro hs
  have h0 := congrArg (fun P : PairMatrix => P (inverseVolumeAction*theta m ell) (inverseVolumeAction*theta m ell))
    (SourceScalarPositiveBulkEndpoint.actual_fixed_bulk_collapse F (star z) z hs hz g k)
  have h1 := core_fixed_pair m ell (coreEquiv.symm k) (coreEquiv.symm g)
    (state F (star z) hs k) (state F z hz g)
  change fixedPair F (star z) z hs hz g k (inverseVolumeAction*theta m ell) (inverseVolumeAction*theta m ell)=
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
  change fixedBulk F (star z) z hs hz g k (inverseVolumeAction*theta m ell) (inverseVolumeAction*theta m ell)=
    (-6*(vacuumJetCoefficient : ℂ))*fixedPair F (star z) z hs hz g k (inverseVolumeAction*theta m ell) (inverseVolumeAction*theta m ell) at h0
  exact h0.trans ((congrArg (fun c : ℂ => (-6*(vacuumJetCoefficient : ℂ))*c) h3).trans (by ring))

private theorem endpoint_bound (m ell : ℕ) (hell : m ≤ ell) (f : QuantumTest) :
    ‖embed (endpoint m ell f)‖ ≤ ‖relativeTail m ell (embed (inverseVolumeAction f))‖ := by
  rw [endpoint,SourceNativeCutoffContact.theta_core,SourceNativeCutoffContact.theta_core]
  exact relative_tail_contraction m ell hell _

private theorem endpoint_tail (f : QuantumTest) (C : ℝ) (hC : 0 ≤ C) :
    ∀ ε : ℝ,0<ε → ∃ N : ℕ,∀ m,N ≤ m → ∀ ell,m ≤ ell → C*‖embed (endpoint m ell f)‖^2 ≤ ε := by
  intro ε hε
  have hp : 0<C+1 := by linarith
  obtain ⟨N,hN⟩ := original_relative_tail (embed (inverseVolumeAction f))
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

/-- The inverse-volume fixed endpoints have a common full-frequency tail, and the threshold is independent of F and the upper cutoff. -/
theorem actual_fixed_bulk_tail (μ : ℝ) (hμ : 0<μ) (g k : diagonal.domain) :
    ∀ ε : ℝ,0<ε → ∃ N : ℕ,∀ m,N ≤ m → ∀ ell,m ≤ ell → ∀ F : Index,
      (∫⁻ w : ℝ,ENNReal.ofReal (‖fixedBulk F (star (line μ w)) (line μ w)
        (by simpa only [Complex.star_def,Complex.conj_im,line_im,neg_ne_zero] using hμ.ne')
        (by simpa only [line_im] using hμ.ne') g k (inverseVolumeAction*theta m ell) (inverseVolumeAction*theta m ell)‖^2)) ≤
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


/-- The fixed-source tail returns to the literal polynomial cutoff used by the Gamma consumer. -/
theorem actual_gamma_fixed_bulk_tail (μ : ℝ) (hμ : 0<μ) (g k : diagonal.domain) :
    ∀ ε : ℝ,0<ε → ∃ N : ℕ,∀ m,N ≤ m → ∀ ell,m ≤ ell → ∀ F : Index,
      (∫⁻ w : ℝ,ENNReal.ofReal (‖fixedBulk F (star (line μ w)) (line μ w)
        (by simpa only [Complex.star_def,Complex.conj_im,line_im,neg_ne_zero] using hμ.ne')
        (by simpa only [line_im] using hμ.ne') g k
        (inverseVolumeAction*SourceMixedNativeReturn.thetaAction m ell)
        (inverseVolumeAction*SourceMixedNativeReturn.thetaAction m ell)‖^2)) ≤
        ENNReal.ofReal ε := by
  simpa only [theta,SourceNativeCutoffContact.theta_action_polynomial,
    SourceMixedNativeReturn.thetaAction] using! actual_fixed_bulk_tail μ hμ g k

end LowEnergy.SourceScalarInverseEndpoint
