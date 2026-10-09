import H0mework.Versions.R3bbcbd59.ReleaseMaterials.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceInverseVolumeNeutralSpinTail
import H0mework.Versions.R71e.ReleaseMaterials.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceClockYukawaTail
import H0mework.Versions.R71e.ReleaseMaterials.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceClockYukawaHamiltonianCurrent

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1600000
set_option maxRecDepth 2048
noncomputable section
namespace LowEnergy.SourceClockYukawaCurrent
open GaussCoreHilbert GaussCoreDifferential GaussFockPair GaussNativeForm GaussDiagonalHistory
open GaussUnitaryHistory GaussHistoryHilbert SourceQuantumConfigurationHilbert SourceQuantumFockGauge
open SourceMixedNativeReturn SourceScalarDoubleCurrent SourceScalarPositiveBulkWard SourceScalarPairedTransport
open SourceInverseNeutralSpinCurrent SourceClockYukawaTail SourceCutoffDilationWard
open SourceRelativePowerTail SourceHardyRetardedTail SourceRetardedForcingTail
open SourceJointResidualEnergy SourceFourPoleEnergyClosed SourceScalarSignedInverseReturn
open SourceEscapeSeedTail FullYSourceResolventGraphSplice SourceResolventBandLimit
open MeasureTheory Filter
open scoped Topology InnerProductSpace
abbrev End := QuantumTest →ₗ[ℂ] QuantumTest
abbrev Op := H →L[ℂ] H
attribute [local irreducible] diagonalAction compressionCore defectAction state fullAction

/-- This is the original fixed Yukawa input on its own source core. -/
def yukawaSource (sharp : Bool) (g : diagonal.domain) : diagonal.domain :=
  coreEquiv (fullAction sharp (coreEquiv.symm g))

/-- The complete source current retains the actual compression defect. -/
abbrev correctedCurrent := SourceClockYukawaHamiltonianCurrent.correctedCurrent

theorem actual_corrected_current (sharp : Bool) (F : Index) :
    correctedCurrent sharp F=bracket (compressionCore F) (fullAction sharp) := by
  exact (SourceClockYukawaHamiltonianCurrent.original_compression_yukawa_current sharp F).symm

private theorem state_embed (F : Index) (z : ℂ) (hz : z.im≠0) (g : diagonal.domain) :
    embed (state F z hz g)=finiteResolvent F z (g:H) := by
  unfold state
  exact congrArg Subtype.val (coreEquiv.apply_symm_apply _)

private theorem compression_embed (F : Index) (q : QuantumTest) :
    embed (compressionCore F q)=GaussGradedCompression.compression F (embed q) := by
  unfold compressionCore
  exact congrArg Subtype.val (coreEquiv.apply_symm_apply _)

private theorem compression_equation (F : Index) (z : ℂ) (hz : z.im≠0) (g : diagonal.domain) :
    compressionCore F (state F z hz g)=coreEquiv.symm g+z • state F z hz g := by
  have h := actual_raised_source F z hz g (1:End)
  simp only [Module.End.one_apply,raisedDefect,mul_one,one_mul,sub_self,LinearMap.zero_apply,
    zero_add,defectAction,LinearMap.sub_apply] at h
  linear_combination (norm := module) h

def currentResponse (sharp : Bool) (F : Index) (z : ℂ) (hz : z.im≠0) (g : diagonal.domain) : H :=
  finiteResolvent F z (embed (correctedCurrent sharp F (state F z hz g)))

/-- The uncut Yukawa response returns to its fixed source and one complete
cutoff-independent current. No graph or moving-prefix hypothesis is supplied. -/
theorem actual_yukawa_resolvent_transport (sharp : Bool) (F : Index) (z : ℂ)
    (hz : z.im≠0) (g : diagonal.domain) :
    embed (fullAction sharp (state F z hz g))=
      finiteResolvent F z (yukawaSource sharp g:H)+currentResponse sharp F z hz g := by
  let q := state F z hz g
  have hc : compressionCore F (fullAction sharp q)-z • fullAction sharp q=
      fullAction sharp (coreEquiv.symm g)+correctedCurrent sharp F q := by
    rw [actual_corrected_current]
    simp only [bracket,LinearMap.sub_apply,Module.End.mul_apply,
      show compressionCore F q=coreEquiv.symm g+z • q from compression_equation F z hz g,
      map_add,map_smul]
    module
  have he := congrArg embed hc
  simp only [map_sub,map_smul,map_add,compression_embed] at he
  have hr := congrArg (fun T : Op => T (embed (fullAction sharp q)))
    (resolvent_left (GaussGradedCompression.compression F)
      (GaussGradedCompression.compression_selfAdjoint F) z hz)
  change finiteResolvent F z (GaussGradedCompression.compression F (embed (fullAction sharp q))-
    z • embed (fullAction sharp q))=embed (fullAction sharp q) at hr
  rw [he,map_add] at hr
  exact hr.symm

private theorem full_pair (sharp : Bool) (p q : QuantumTest) :
    sourcePair p (fullAction sharp q)=sourcePair (fullAction (!sharp) p) q := by
  unfold fullAction
  cases sharp
  · have h := congrArg (starRingEnd ℂ) (GaussFullHamiltonian.yukawa_pair q p)
    simpa only [sourcePair,inner_conj_symm,Bool.not_false] using! h.symm
  · exact GaussFullHamiltonian.yukawa_pair p q

def fixedAmplitude (sharp : Bool) (m ell : ℕ) (F : Index) (z : ℂ)
    (g k : diagonal.domain) : ℂ :=
  inner ℂ (finiteResolvent F (star z) (yukawaSource (!sharp) k:H))
    (relativeTail m ell (finiteResolvent F z (g:H)))

def currentAmplitude (sharp : Bool) (m ell : ℕ) (F : Index) (z : ℂ) (hz : z.im≠0)
    (g k : diagonal.domain) : ℂ :=
  inner ℂ (currentResponse (!sharp) F (star z)
    (by simpa only [Complex.star_def,Complex.conj_im,neg_ne_zero] using hz) k)
    (relativeTail m ell (finiteResolvent F z (g:H)))

/-- All radial growth leaves the insertion: both remaining source words pair
against the bounded original theta tail, at the same F and both sharp branches. -/
theorem actual_increment_current_split (sharp : Bool) (m ell : ℕ) (F : Index)
    (z : ℂ) (hz : z.im≠0) (g k : diagonal.domain) :
    inner ℂ (finiteResolvent F (star z) (k:H))
      (actualIncrement sharp m ell (finiteResolvent F z (g:H)))=
      fixedAmplitude sharp m ell F z g k+currentAmplitude sharp m ell F z hz g k := by
  let hs : (star z).im≠0 := by simpa only [Complex.star_def,Complex.conj_im,neg_ne_zero] using hz
  rw [←state_embed F z hz g,←state_embed F (star z) hs k,literal_increment_core,literal_full_return]
  change sourcePair (state F (star z) hs k) (fullAction sharp (thetaAction m ell (state F z hz g)))=_
  rw [full_pair]
  change inner ℂ (embed (fullAction (!sharp) (state F (star z) hs k)))
    (embed (thetaAction m ell (state F z hz g)))=_
  rw [←theta_core,actual_yukawa_resolvent_transport,inner_add_left,state_embed]
  rfl

private theorem fixed_amplitude_bound (sharp : Bool) (m ell : ℕ) (F : Index)
    (μ : ℝ) (hμ : 0<μ) (g k : diagonal.domain) (w : ℝ) :
    ‖fixedAmplitude sharp m ell F (line μ w) g k‖^2 ≤
      ((1/μ)*‖(yukawaSource (!sharp) k:H)‖)^2*
        ‖relativeTail m ell (finiteResolvent F (line μ w) (g:H))‖^2 := by
  have hs : (star (line μ w)).im≠0 := by
    simpa only [Complex.star_def,Complex.conj_im,line_im,neg_ne_zero] using hμ.ne'
  have hr : ‖finiteResolvent F (star (line μ w)) (yukawaSource (!sharp) k:H)‖ ≤
      (1/μ)*‖(yukawaSource (!sharp) k:H)‖ := by
    apply ((finiteResolvent F _).le_opNorm _).trans
    have hb := finite_resolvent_norm F (star (line μ w)) hs
    simp only [Complex.star_def,Complex.conj_im,line_im,abs_neg,abs_of_pos hμ] at hb
    exact mul_le_mul_of_nonneg_right hb (norm_nonneg _)
  have h := (norm_inner_le_norm (𝕜 := ℂ) _ _).trans
    (mul_le_mul_of_nonneg_right hr (norm_nonneg
      (relativeTail m ell (finiteResolvent F (line μ w) (g:H)))))
  have hh := pow_le_pow_left₀ (norm_nonneg _) h 2
  simpa only [fixedAmplitude,mul_pow] using hh

/-- The true Y-adjoint seed is paid internally by the original unweighted
resolvent bound and theta full-frequency tail on one common source cutoff. -/
theorem actual_fixed_yukawa_common_tail (sharp : Bool) (μ : ℝ) (hμ : 0<μ)
    (g k : diagonal.domain) :
    ∀ ε : ℝ,0<ε → ∃ N : ℕ,∀ m,N ≤ m → ∀ ell,m ≤ ell →
      ∀ᶠ F in (sourceFilter : Filter Index),
        (∫⁻ w : ℝ,ENNReal.ofReal (‖fixedAmplitude sharp m ell F (line μ w) g k‖^2)) ≤ ENNReal.ofReal ε := by
  intro ε hε
  let C : ℝ := ((1/μ)*‖(yukawaSource (!sharp) k:H)‖)^2
  have hC : 0 ≤ C := sq_nonneg _
  obtain ⟨N,hN⟩ := actual_theta_full_frequency_tail μ hμ g (ε/(C+1)) (by positivity)
  refine ⟨N,fun m hm ell hml => ?_⟩
  filter_upwards [hN m hm ell hml] with F hF
  calc
    _ ≤ ∫⁻ w : ℝ,ENNReal.ofReal C*
        ENNReal.ofReal (‖relativeTail m ell (finiteResolvent F (line μ w) (g:H))‖^2) := by
      apply lintegral_mono
      intro w
      dsimp only
      rw [←ENNReal.ofReal_mul hC]
      exact ENNReal.ofReal_le_ofReal (fixed_amplitude_bound sharp m ell F μ hμ g k w)
    _ = ENNReal.ofReal C*(∫⁻ w : ℝ,
        ENNReal.ofReal (‖relativeTail m ell (finiteResolvent F (line μ w) (g:H))‖^2)) :=
      lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ ≤ ENNReal.ofReal C*ENNReal.ofReal (ε/(C+1)) := mul_le_mul (le_refl _) hF bot_le bot_le
    _ ≤ ENNReal.ofReal ε := by
      rw [←ENNReal.ofReal_mul hC]
      apply ENNReal.ofReal_le_ofReal
      have hp : 0<C+1 := by positivity
      exact (mul_le_mul_of_nonneg_right (by linarith : C ≤ C+1) (div_pos hε hp).le).trans_eq
        (mul_div_cancel₀ ε hp.ne')

private theorem resolvent_pair {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] [CompleteSpace E]
    (C : E →L[ℂ] E) (hC : IsSelfAdjoint C) (z : ℂ) (hz : z.im≠0) (k f : E) :
    inner ℂ k (FullYSourceResolventGraphSplice.resolvent C z f) =
      inner ℂ (FullYSourceResolventGraphSplice.resolvent C (star z) k) f := by
  have hs : (star z).im≠0 := by simpa only [Complex.star_def,Complex.conj_im,neg_ne_zero] using hz
  have hk := congrArg (fun A : E →L[ℂ] E => A k) (resolvent_right C hC (star z) hs)
  have hf := congrArg (fun A : E →L[ℂ] E => A f) (resolvent_right C hC z hz)
  change C (FullYSourceResolventGraphSplice.resolvent C (star z) k) -
    star z • FullYSourceResolventGraphSplice.resolvent C (star z) k = k at hk
  change C (FullYSourceResolventGraphSplice.resolvent C z f) -
    z • FullYSourceResolventGraphSplice.resolvent C z f = f at hf
  have hsym : inner ℂ (C (FullYSourceResolventGraphSplice.resolvent C (star z) k))
      (FullYSourceResolventGraphSplice.resolvent C z f)=
      inner ℂ (FullYSourceResolventGraphSplice.resolvent C (star z) k)
        (C (FullYSourceResolventGraphSplice.resolvent C z f)) := hC.isSymmetric _ _
  calc
    _ = inner ℂ (C (FullYSourceResolventGraphSplice.resolvent C (star z) k) -
        star z • FullYSourceResolventGraphSplice.resolvent C (star z) k)
        (FullYSourceResolventGraphSplice.resolvent C z f) := congrArg (fun v => inner ℂ v _) hk.symm
    _ = inner ℂ (FullYSourceResolventGraphSplice.resolvent C (star z) k)
        (C (FullYSourceResolventGraphSplice.resolvent C z f) -
          z • FullYSourceResolventGraphSplice.resolvent C z f) := by
      rw [inner_sub_left,inner_smul_left,inner_sub_right,inner_smul_right,
        hsym,starRingEnd_apply,star_star]
    _ = _ := congrArg (fun v => inner ℂ _ v) hf

/-- The complete original Gamma decomposition now contains one paid fixed source,
one cutoff-independent corrected Y current, and the already-paid Hardy word. -/
theorem actual_joint_current_split (sharp : Bool) (m ell : ℕ) (F : Index)
    (z : ℂ) (hz : z.im≠0) (g k : diagonal.domain) :
    jointResidual sharp m ell F z hz g k=
      fixedAmplitude sharp m ell F z g k+currentAmplitude sharp m ell F z hz g k-
        inner ℂ (k:H) (hardyVector sharp m ell F z (g:H)) := by
  have hi := SourceCornerPartition.actual_full_increment_splice sharp m ell F z hz g k
  have hp := resolvent_pair (GaussGradedCompression.compression F)
    (GaussGradedCompression.compression_selfAdjoint F) z hz (k:H)
    (actualIncrement sharp m ell (finiteResolvent F z (g:H)))
  have he : fixedAmplitude sharp m ell F z g k+currentAmplitude sharp m ell F z hz g k=
      inner ℂ (k:H) (hardyVector sharp m ell F z (g:H))+jointResidual sharp m ell F z hz g k := by
    rw [←actual_increment_current_split]
    simpa only [jointResidual,hardyVector,add_assoc] using! hp.symm.trans hi
  linear_combination -he

private theorem three_square (a b c : ℂ) :
    ‖a+b-c‖^2 ≤ 3*‖a‖^2+3*‖b‖^2+3*‖c‖^2 := by
  have hn := (norm_sub_le (a+b) c).trans (add_le_add (norm_add_le a b) (le_refl _))
  have h := pow_le_pow_left₀ (norm_nonneg _) hn 2
  nlinarith only [h,sq_nonneg (‖a‖-‖b‖),sq_nonneg (‖a‖-‖c‖),sq_nonneg (‖b‖-‖c‖)]

private theorem fixed_amplitude_continuous (sharp : Bool) (m ell : ℕ) (F : Index)
    (μ : ℝ) (hμ : 0<μ) (g k : diagonal.domain) :
    Continuous (fun w : ℝ => fixedAmplitude sharp m ell F (line μ w) g k) := by
  have hr := SourceRetardedBandCurrent.finite_frequency_continuous μ hμ F
  have he (w : ℝ) : fixedAmplitude sharp m ell F (line μ w) g k=
      inner ℂ (yukawaSource (!sharp) k:H) (finiteResolvent F (line μ w)
        (relativeTail m ell (finiteResolvent F (line μ w) (g:H)))) :=
    (resolvent_pair (GaussGradedCompression.compression F)
      (GaussGradedCompression.compression_selfAdjoint F) (line μ w)
      (by simpa only [line_im] using hμ.ne') _ _).symm
  simp_rw [he]
  exact continuous_const.inner (hr.clm_apply ((relativeTail m ell).continuous.comp (hr.clm_apply continuous_const)))

def currentCost (sharp : Bool) (m ell : ℕ) (F : Index) (μ : ℝ) (hμ : 0<μ)
    (g k : diagonal.domain) : ENNReal :=
  ∫⁻ w : ℝ,ENNReal.ofReal (‖currentAmplitude sharp m ell F (line μ w)
    (by simpa only [line_im] using hμ.ne') g k‖^2)

private theorem joint_current_integral_upper (sharp : Bool) (m ell : ℕ) (F : Index)
    (μ : ℝ) (hμ : 0<μ) (g k : diagonal.domain) :
    ENNReal.ofReal (closedJointCost sharp m ell F μ (g:H) (k:H)) ≤
      ENNReal.ofReal (3:ℝ)*(∫⁻ w : ℝ,ENNReal.ofReal (‖fixedAmplitude sharp m ell F (line μ w) g k‖^2))+
      ENNReal.ofReal (3:ℝ)*currentCost sharp m ell F μ hμ g k+
      ENNReal.ofReal (3*‖(k:H)‖^2)*(∫⁻ w : ℝ,ENNReal.ofReal (‖hardyVector sharp m ell F (line μ w) (g:H)‖^2)) := by
  rw [←actual_joint_closed_lintegral sharp m ell F μ hμ g k]
  have hr := SourceRetardedBandCurrent.finite_frequency_continuous μ hμ F
  have hp : Continuous (fun w => particular sharp m ell F (line μ w) (g:H)) :=
    (cutoffSolver sharp m ell).continuous.comp (hr.clm_apply continuous_const)
  have hh : Continuous (fun w : ℝ => hardyVector sharp m ell F (line μ w) (g:H)) :=
    hp.add ((show Continuous (fun w : ℝ => line μ w) by unfold line;fun_prop).smul (hr.clm_apply hp))
  have hfixed : Measurable (fun w : ℝ => ENNReal.ofReal (3:ℝ)*
      ENNReal.ofReal (‖fixedAmplitude sharp m ell F (line μ w) g k‖^2)) := by
    simpa only [Pi.pow_apply] using
      (((fixed_amplitude_continuous sharp m ell F μ hμ g k).norm.pow 2).measurable.ennreal_ofReal).const_mul _
  have hhardy : Measurable (fun w : ℝ => ENNReal.ofReal (3*‖(k:H)‖^2)*
      ENNReal.ofReal (‖hardyVector sharp m ell F (line μ w) (g:H)‖^2)) := by
    simpa only [Pi.pow_apply] using ((hh.norm.pow 2).measurable.ennreal_ofReal).const_mul _
  calc
    _ ≤ ∫⁻ w : ℝ,ENNReal.ofReal (3:ℝ)*ENNReal.ofReal (‖fixedAmplitude sharp m ell F (line μ w) g k‖^2)+
        ENNReal.ofReal (3:ℝ)*ENNReal.ofReal (‖currentAmplitude sharp m ell F (line μ w)
          (by simpa only [line_im] using hμ.ne') g k‖^2)+
        ENNReal.ofReal (3*‖(k:H)‖^2)*ENNReal.ofReal (‖hardyVector sharp m ell F (line μ w) (g:H)‖^2) := by
      apply lintegral_mono
      intro w
      dsimp only
      have h := three_square (fixedAmplitude sharp m ell F (line μ w) g k)
        (currentAmplitude sharp m ell F (line μ w) (by simpa only [line_im] using hμ.ne') g k)
        (inner ℂ (k:H) (hardyVector sharp m ell F (line μ w) (g:H)))
      have hb := pow_le_pow_left₀ (norm_nonneg _) (norm_inner_le_norm (𝕜 := ℂ)
        (k:H) (hardyVector sharp m ell F (line μ w) (g:H))) 2
      rw [mul_pow] at hb
      rw [←actual_joint_current_split] at h
      have hj : ‖jointResidual sharp m ell F (line μ w) (by simpa only [line_im] using hμ.ne') g k‖^2 ≤
          3*‖fixedAmplitude sharp m ell F (line μ w) g k‖^2+
          3*‖currentAmplitude sharp m ell F (line μ w) (by simpa only [line_im] using hμ.ne') g k‖^2+
          (3*‖(k:H)‖^2)*‖hardyVector sharp m ell F (line μ w) (g:H)‖^2 := by nlinarith only [h,hb]
      apply (ENNReal.ofReal_le_ofReal hj).trans
      rw [←ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 3),
        ←ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 3),←ENNReal.ofReal_mul (by positivity : 0 ≤ 3*‖(k:H)‖^2)]
      exact ENNReal.ofReal_add_le.trans (add_le_add ENNReal.ofReal_add_le (le_refl _))
    _ = _ := by
      rw [lintegral_add_right _ hhardy,lintegral_add_left hfixed,
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      rfl

/-- Fixed Y source and Hardy endpoints are paid on one common cutoff. The
original Gamma now asks only for the full corrected-current/theta pairing. -/
theorem actual_original_yukawa_current_budget (sharp : Bool) (μ : ℝ) (hμ : 0<μ)
    (g k : diagonal.domain) :
    ∀ ε : ℝ,0<ε → ∃ N : ℕ,∀ m,N ≤ m → ∀ ell,m ≤ ell →
      ∀ᶠ F in (sourceFilter : Filter Index),
        ENNReal.ofReal (closedJointCost sharp m ell F μ (g:H) (k:H)) ≤
          ENNReal.ofReal ε+ENNReal.ofReal (3:ℝ)*currentCost sharp m ell F μ hμ g k := by
  intro ε hε
  let C : ℝ := ‖(k:H)‖^2
  have hC : 0 ≤ C := sq_nonneg _
  obtain ⟨N₁,h₁⟩ := actual_fixed_yukawa_common_tail sharp μ hμ g k (ε/6) (by positivity)
  obtain ⟨N₂,h₂⟩ := actual_hardy_retarded_tail μ hμ sharp g (ε/(6*(C+1))) (by positivity)
  refine ⟨max N₁ N₂,fun m hm ell hml => ?_⟩
  filter_upwards [h₁ m ((le_max_left _ _).trans hm) ell hml,
    h₂ m ((le_max_right _ _).trans hm) ell hml] with F hf hh
  have hbound := joint_current_integral_upper sharp m ell F μ hμ g k
  have hb : ENNReal.ofReal (3:ℝ)*ENNReal.ofReal (ε/6)+
      ENNReal.ofReal (3*C)*ENNReal.ofReal (ε/(6*(C+1))) ≤ ENNReal.ofReal ε := by
    rw [←ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 3),
      ←ENNReal.ofReal_mul (by positivity : 0 ≤ 3*C),←ENNReal.ofReal_add (by positivity) (by positivity)]
    apply ENNReal.ofReal_le_ofReal
    have hp : 0<C+1 := by positivity
    have hc : C/(C+1) ≤ 1 := (div_le_one hp).mpr (by linarith)
    have he : 3*(ε/6)+3*C*(ε/(6*(C+1)))=ε/2+(ε/2)*(C/(C+1)) := by
      simp only [div_eq_mul_inv,mul_inv_rev]
      ring
    rw [he]
    nlinarith only [mul_le_mul_of_nonneg_left hc (by positivity : 0 ≤ ε/2)]
  calc
    _ ≤ ENNReal.ofReal (3:ℝ)*ENNReal.ofReal (ε/6)+
        ENNReal.ofReal (3:ℝ)*currentCost sharp m ell F μ hμ g k+
        ENNReal.ofReal (3*C)*ENNReal.ofReal (ε/(6*(C+1))) := by
      apply hbound.trans
      exact add_le_add (add_le_add (mul_le_mul (le_refl _) hf bot_le bot_le) (le_refl _))
        (mul_le_mul (le_refl _) hh bot_le bot_le)
    _ = (ENNReal.ofReal (3:ℝ)*ENNReal.ofReal (ε/6)+
        ENNReal.ofReal (3*C)*ENNReal.ofReal (ε/(6*(C+1))))+
        ENNReal.ofReal (3:ℝ)*currentCost sharp m ell F μ hμ g k := by ac_rfl
    _ ≤ _ := add_le_add hb (le_refl _)

end LowEnergy.SourceClockYukawaCurrent
