import H0mework.Versions.AD.Physics.LowEnergy.Quantum.SourceClockYukawaGradedInverse
import H0mework.Versions.AD.Physics.LowEnergy.Quantum.SourceClockYukawaCurrent

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1800000
set_option maxRecDepth 2048
noncomputable section
namespace LowEnergy.SourceClockYukawaGradedGamma
open GaussCoreHilbert GaussCoreDifferential GaussFockPair GaussHistoryHilbert GaussNativeForm
open GaussDiagonalHistory GaussUnitaryHistory GaussRadialDomain GaussYukawaOperator NativeHistoryGrade
open SourceQuantumConfigurationHilbert SourceMixedNativeReturn SourceScalarDoubleCurrent
open SourceScalarPairedTransport SourceScalarPositiveBulkWard SourceClockYukawaTail
open SourceClockYukawaGradedRadial SourceClockYukawaGradedInverse SourceClockYukawaNormalizedCurrent
open SourceRelativePowerTail SourceHardyRetardedTail SourceRetardedForcingTail
open SourceJointResidualEnergy SourceFourPoleEnergyClosed SourceScalarSignedInverseReturn
open SourceCutoffDilationWard
open SourceEscapeSeedTail FullYSourceResolventGraphSplice SourceResolventBandLimit
open MeasureTheory Filter
open scoped Topology InnerProductSpace
abbrev End := QuantumTest →ₗ[ℂ] QuantumTest
abbrev Op := H →L[ℂ] H
local instance labelFintype : Fintype Label := Fintype.ofFinite _
attribute [local irreducible] state fullAction radialWeight radialWeightCore inverseWeightCore
  compressionCore defectAction correctedGradedCurrent

def liftedSource (sharp : Bool) (k : diagonal.domain) : diagonal.domain :=
  coreEquiv (inverseWeightCore sharp (coreEquiv.symm k))

private theorem state_embed (F : Index) (z : ℂ) (hz : z.im≠0) (g : diagonal.domain) :
    embed (state F z hz g)=finiteResolvent F z (g:H) := by
  unfold state
  exact congrArg Subtype.val (coreEquiv.apply_symm_apply _)

private theorem compression_embed (F : Index) (f : QuantumTest) :
    embed (compressionCore F f)=GaussGradedCompression.compression F (embed f) := by
  unfold compressionCore
  exact congrArg Subtype.val (coreEquiv.apply_symm_apply _)

private theorem compression_equation (F : Index) (z : ℂ) (hz : z.im≠0) (g : diagonal.domain) :
    compressionCore F (state F z hz g)=coreEquiv.symm g+z • state F z hz g := by
  have h := actual_raised_source F z hz g (1:End)
  simp only [Module.End.one_apply,raisedDefect,mul_one,one_mul,sub_self,LinearMap.zero_apply,
    zero_add,defectAction,LinearMap.sub_apply] at h
  linear_combination (norm := module) h

def radialResponse (sharp : Bool) (F : Index) (z : ℂ) (hz : z.im≠0) (k : diagonal.domain) : H :=
  finiteResolvent F z (embed (correctedGradedCurrent sharp F (state F z hz (liftedSource sharp k))))

/-- The inverse weight acts on the original fixed core source only. The dynamic
return retains the complete scalar radial current and the actual compression defect. -/
theorem actual_graded_radial_transport (sharp : Bool) (F : Index) (z : ℂ) (hz : z.im≠0)
    (k : diagonal.domain) :
    radialWeight sharp (finiteResolvent F z (liftedSource sharp k:H))=
      finiteResolvent F z (k:H)+radialResponse sharp F z hz k := by
  let u := liftedSource sharp k
  let q := state F z hz u
  have hk : radialWeightCore sharp (coreEquiv.symm u)=coreEquiv.symm k := by
    dsimp only [u,liftedSource]
    rw [coreEquiv.symm_apply_apply]
    exact LinearMap.congr_fun (original_inverse_radial_weight sharp) (coreEquiv.symm k)
  have hc : compressionCore F (radialWeightCore sharp q)-z • radialWeightCore sharp q=
      coreEquiv.symm k+correctedGradedCurrent sharp F q := by
    rw [←actual_graded_compression_current]
    simp only [bracket,LinearMap.sub_apply,Module.End.mul_apply,
      show compressionCore F q=coreEquiv.symm u+z • q from compression_equation F z hz u,
      map_add,map_smul,hk]
    module
  have he := congrArg embed hc
  simp only [map_sub,map_smul,map_add,compression_embed] at he
  have hr := congrArg (fun T : Op => T (embed (radialWeightCore sharp q)))
    (resolvent_left (GaussGradedCompression.compression F)
      (GaussGradedCompression.compression_selfAdjoint F) z hz)
  change finiteResolvent F z (GaussGradedCompression.compression F (embed (radialWeightCore sharp q))-
    z • embed (radialWeightCore sharp q))=embed (radialWeightCore sharp q) at hr
  rw [he,map_add,←original_radial_weight_core] at hr
  have hseed : embed (coreEquiv.symm k)=(k:H) := congrArg Subtype.val (coreEquiv.apply_symm_apply k)
  dsimp only [q] at hr
  rw [hseed,state_embed] at hr
  exact hr.symm

private theorem inverse_weight (sharp : Bool) : Commute inverseRadius (radialWeight sharp) := by
  unfold radialWeight
  apply Commute.sum_right
  intro g _
  exact ((Commute.refl inverseRadius).pow_right _).mul_right
    (show Commute inverseRadius (projection g) from (GaussYukawaGrade.inverse_blocks g).symm)

private theorem tail_commute (A : Op) (hA : Commute inverseRadius A) (m ell : ℕ) :
    Commute (relativeTail m ell) A := by
  have hc : Commute sourceComplement A := (Commute.one_left A).sub_left hA
  exact (hc.pow_left _).sub_left (hc.pow_left _)

private theorem weight_theta (sharp : Bool) (m ell : ℕ) (f : QuantumTest) :
    radialWeightCore sharp (thetaAction m ell f)=thetaAction m ell (radialWeightCore sharp f) := by
  apply embed_injective
  rw [←original_radial_weight_core,←SourceMixedNativeReturn.theta_core,
    ←SourceMixedNativeReturn.theta_core,←original_radial_weight_core]
  exact congrArg (fun A : Op => A (embed f)) (tail_commute _ (inverse_weight sharp) m ell).eq.symm

def fixedAmplitude (sharp : Bool) (m ell : ℕ) (F : Index) (z : ℂ)
    (g k : diagonal.domain) : ℂ :=
  inner ℂ (finiteResolvent F (star z) (liftedSource sharp k:H))
    ((sourceB sharp*radialWeight sharp) (relativeTail m ell (finiteResolvent F z (g:H))))

def radialAmplitude (sharp : Bool) (m ell : ℕ) (F : Index) (z : ℂ) (hz : z.im≠0)
    (g k : diagonal.domain) : ℂ :=
  inner ℂ (radialResponse sharp F (star z)
    (by simpa only [Complex.star_def,Complex.conj_im,neg_ne_zero] using hz) k)
    (actualIncrement sharp m ell (finiteResolvent F z (g:H)))

/-- The original Gamma insertion has only one dynamic remainder: the actual
graded scalar radial current. Spin, matter and gauge leave by source intertwinement. -/
theorem actual_increment_graded_split (sharp : Bool) (m ell : ℕ) (F : Index)
    (z : ℂ) (hz : z.im≠0) (g k : diagonal.domain) :
    inner ℂ (finiteResolvent F (star z) (k:H))
      (actualIncrement sharp m ell (finiteResolvent F z (g:H)))=
      fixedAmplitude sharp m ell F z g k-radialAmplitude sharp m ell F z hz g k := by
  let hs : (star z).im≠0 := by simpa only [Complex.star_def,Complex.conj_im,neg_ne_zero] using hz
  have ht := actual_graded_radial_transport sharp F (star z) hs k
  have he : finiteResolvent F (star z) (k:H)=
      radialWeight sharp (finiteResolvent F (star z) (liftedSource sharp k:H))-radialResponse sharp F (star z) hs k := by
    rw [ht]
    module
  rw [he,inner_sub_left]
  unfold radialAmplitude
  congr 1
  rw [←state_embed F z hz g,←state_embed F (star z) hs (liftedSource sharp k),
    original_radial_weight_core,literal_increment_core,literal_full_return]
  change sourcePair (radialWeightCore sharp (state F (star z) hs (liftedSource sharp k)))
    (fullAction sharp (thetaAction m ell (state F z hz g)))=_
  rw [←original_radial_weight_pair]
  have hy := LinearMap.congr_fun (original_graded_yukawa_return sharp) (thetaAction m ell (state F z hz g))
  change radialWeightCore sharp (fullAction sharp (thetaAction m ell (state F z hz g)))=
    normalizedAction sharp (radialWeightCore sharp (thetaAction m ell (state F z hz g))) at hy
  rw [hy,weight_theta]
  change inner ℂ (embed (state F (star z) hs (liftedSource sharp k)))
    (embed (normalizedAction sharp (thetaAction m ell (radialWeightCore sharp (state F z hz g)))))=_
  rw [←original_normalized_core,←SourceMixedNativeReturn.theta_core,←original_radial_weight_core]
  rw [show relativeTail m ell (radialWeight sharp (embed (state F z hz g)))=
    radialWeight sharp (relativeTail m ell (embed (state F z hz g))) from
      congrArg (fun A : Op => A (embed (state F z hz g))) (tail_commute _ (inverse_weight sharp) m ell).eq]
  simp only [state_embed,fixedAmplitude,mul_apply_eq_comp]


private theorem fixed_amplitude_bound (sharp : Bool) (m ell : ℕ) (F : Index)
    (μ : ℝ) (hμ : 0<μ) (g k : diagonal.domain) (w : ℝ) :
    ‖fixedAmplitude sharp m ell F (line μ w) g k‖^2 ≤
      ((1/μ)*‖(liftedSource sharp k:H)‖)^2*
        ‖(sourceB sharp*radialWeight sharp) (relativeTail m ell (finiteResolvent F (line μ w) (g:H)))‖^2 := by
  have hs : (star (line μ w)).im≠0 := by
    simpa only [Complex.star_def,Complex.conj_im,line_im,neg_ne_zero] using hμ.ne'
  have hr : ‖finiteResolvent F (star (line μ w)) (liftedSource sharp k:H)‖ ≤
      (1/μ)*‖(liftedSource sharp k:H)‖ := by
    apply ((finiteResolvent F _).le_opNorm _).trans
    have hb := finite_resolvent_norm F (star (line μ w)) hs
    simp only [Complex.star_def,Complex.conj_im,line_im,abs_neg,abs_of_pos hμ] at hb
    exact mul_le_mul_of_nonneg_right hb (norm_nonneg _)
  have h := (norm_inner_le_norm (𝕜 := ℂ) _ _).trans
    (mul_le_mul_of_nonneg_right hr (norm_nonneg
      ((sourceB sharp*radialWeight sharp) (relativeTail m ell (finiteResolvent F (line μ w) (g:H))))))
  have hh := pow_le_pow_left₀ (norm_nonneg _) h 2
  simpa only [fixedAmplitude,mul_pow] using hh

private theorem fixed_common_tail (sharp : Bool) (μ : ℝ) (hμ : 0<μ) (g k : diagonal.domain) :
    ∀ ε : ℝ,0<ε → ∃ N : ℕ,∀ m,N ≤ m → ∀ ell,m ≤ ell →
      ∀ᶠ F in (sourceFilter : Filter Index),
        (∫⁻ w : ℝ,ENNReal.ofReal (‖fixedAmplitude sharp m ell F (line μ w) g k‖^2)) ≤ ENNReal.ofReal ε := by
  intro ε hε
  let C : ℝ := ((1/μ)*‖(liftedSource sharp k:H)‖)^2
  have hC : 0≤C := sq_nonneg _
  obtain ⟨N,hN⟩ := bounded_forcing_full_frequency_tail μ hμ (sourceB sharp*radialWeight sharp) g
    (ε/(C+1)) (by positivity)
  refine ⟨N,fun m hm ell hell => ?_⟩
  filter_upwards [hN m hm ell hell] with F hF
  calc
    _ ≤ ∫⁻ w : ℝ,ENNReal.ofReal C*ENNReal.ofReal
        (‖(sourceB sharp*radialWeight sharp) (relativeTail m ell (finiteResolvent F (line μ w) (g:H)))‖^2) := by
      apply lintegral_mono
      intro w
      dsimp only
      rw [←ENNReal.ofReal_mul hC]
      exact ENNReal.ofReal_le_ofReal (fixed_amplitude_bound sharp m ell F μ hμ g k w)
    _ = ENNReal.ofReal C*(∫⁻ w : ℝ,ENNReal.ofReal
        (‖(sourceB sharp*radialWeight sharp) (relativeTail m ell (finiteResolvent F (line μ w) (g:H)))‖^2)) :=
      lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ ≤ ENNReal.ofReal C*ENNReal.ofReal (ε/(C+1)) := by gcongr
    _ ≤ ENNReal.ofReal ε := by
      rw [←ENNReal.ofReal_mul hC]
      apply ENNReal.ofReal_le_ofReal
      rw [←mul_div_assoc]
      apply (div_le_iff₀ (by positivity : 0<C+1)).mpr
      nlinarith

private theorem joint_graded_split (sharp : Bool) (m ell : ℕ) (F : Index)
    (z : ℂ) (hz : z.im≠0) (g k : diagonal.domain) :
    jointResidual sharp m ell F z hz g k=
      fixedAmplitude sharp m ell F z g k-radialAmplitude sharp m ell F z hz g k-
        inner ℂ (k:H) (hardyVector sharp m ell F z (g:H)) := by
  have h := SourceClockYukawaCurrent.actual_increment_current_split sharp m ell F z hz g k
  rw [actual_increment_graded_split sharp m ell F z hz g k] at h
  rw [SourceClockYukawaCurrent.actual_joint_current_split sharp m ell F z hz g k]
  linear_combination -h

private theorem three_square (a b c : ℂ) :
    ‖a-b-c‖^2 ≤ 3*‖a‖^2+3*‖b‖^2+3*‖c‖^2 := by
  have hn := (norm_sub_le (a-b) c).trans (add_le_add (norm_sub_le a b) (le_refl _))
  have h := pow_le_pow_left₀ (norm_nonneg _) hn 2
  nlinarith only [h,sq_nonneg (‖a‖-‖b‖),sq_nonneg (‖a‖-‖c‖),sq_nonneg (‖b‖-‖c‖)]

private theorem finite_adjoint (F : Index) (z : ℂ) :
    (finiteResolvent F z).adjoint=finiteResolvent F (star z) := by
  change star (finiteResolvent F z)=_
  unfold finiteResolvent FullYSourceResolventGraphSplice.resolvent
  rw [←Ring.inverse_star,star_sub,star_smul,star_one,
    (GaussGradedCompression.compression_selfAdjoint F).star_eq]

private theorem fixed_amplitude_continuous (sharp : Bool) (m ell : ℕ) (F : Index)
    (μ : ℝ) (hμ : 0<μ) (g k : diagonal.domain) :
    Continuous (fun w : ℝ => fixedAmplitude sharp m ell F (line μ w) g k) := by
  have hr := SourceRetardedBandCurrent.finite_frequency_continuous μ hμ F
  have he (w : ℝ) : fixedAmplitude sharp m ell F (line μ w) g k=
      inner ℂ (liftedSource sharp k:H) (finiteResolvent F (line μ w)
        ((sourceB sharp*radialWeight sharp) (relativeTail m ell (finiteResolvent F (line μ w) (g:H))))) := by
    rw [fixedAmplitude,←finite_adjoint,ContinuousLinearMap.adjoint_inner_left]
  simp_rw [he]
  exact continuous_const.inner (hr.clm_apply ((sourceB sharp*radialWeight sharp).continuous.comp
    ((relativeTail m ell).continuous.comp (hr.clm_apply continuous_const))))

def radialCurrentCost (sharp : Bool) (m ell : ℕ) (F : Index) (μ : ℝ) (hμ : 0<μ)
    (g k : diagonal.domain) : ENNReal :=
  ∫⁻ w : ℝ,ENNReal.ofReal (‖radialAmplitude sharp m ell F (line μ w)
    (by simpa only [line_im] using hμ.ne') g k‖^2)

private theorem joint_radial_integral_upper (sharp : Bool) (m ell : ℕ) (F : Index)
    (μ : ℝ) (hμ : 0<μ) (g k : diagonal.domain) :
    ENNReal.ofReal (closedJointCost sharp m ell F μ (g:H) (k:H)) ≤
      ENNReal.ofReal (3:ℝ)*(∫⁻ w : ℝ,ENNReal.ofReal (‖fixedAmplitude sharp m ell F (line μ w) g k‖^2))+
      ENNReal.ofReal (3:ℝ)*radialCurrentCost sharp m ell F μ hμ g k+
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
        ENNReal.ofReal (3:ℝ)*ENNReal.ofReal (‖radialAmplitude sharp m ell F (line μ w)
          (by simpa only [line_im] using hμ.ne') g k‖^2)+
        ENNReal.ofReal (3*‖(k:H)‖^2)*ENNReal.ofReal (‖hardyVector sharp m ell F (line μ w) (g:H)‖^2) := by
      apply lintegral_mono
      intro w
      dsimp only
      have h := three_square (fixedAmplitude sharp m ell F (line μ w) g k)
        (radialAmplitude sharp m ell F (line μ w) (by simpa only [line_im] using hμ.ne') g k)
        (inner ℂ (k:H) (hardyVector sharp m ell F (line μ w) (g:H)))
      have hb := pow_le_pow_left₀ (norm_nonneg _) (norm_inner_le_norm (𝕜 := ℂ)
        (k:H) (hardyVector sharp m ell F (line μ w) (g:H))) 2
      rw [mul_pow] at hb
      rw [←joint_graded_split] at h
      have hj : ‖jointResidual sharp m ell F (line μ w) (by simpa only [line_im] using hμ.ne') g k‖^2 ≤
          3*‖fixedAmplitude sharp m ell F (line μ w) g k‖^2+
          3*‖radialAmplitude sharp m ell F (line μ w) (by simpa only [line_im] using hμ.ne') g k‖^2+
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

/-- The original whole Gamma now spends only its graded scalar radial current
and full compression defect; fixed inverse-weight sources and Hardy tails are paid internally. -/
theorem actual_original_graded_radial_budget (sharp : Bool) (μ : ℝ) (hμ : 0<μ)
    (g k : diagonal.domain) :
    ∀ ε : ℝ,0<ε → ∃ N : ℕ,∀ m,N ≤ m → ∀ ell,m ≤ ell →
      ∀ᶠ F in (sourceFilter : Filter Index),
        ENNReal.ofReal (closedJointCost sharp m ell F μ (g:H) (k:H)) ≤
          ENNReal.ofReal ε+ENNReal.ofReal (3:ℝ)*radialCurrentCost sharp m ell F μ hμ g k := by
  intro ε hε
  let C : ℝ := ‖(k:H)‖^2
  have hC : 0 ≤ C := sq_nonneg _
  obtain ⟨N₁,h₁⟩ := fixed_common_tail sharp μ hμ g k (ε/6) (by positivity)
  obtain ⟨N₂,h₂⟩ := actual_hardy_retarded_tail μ hμ sharp g (ε/(6*(C+1))) (by positivity)
  refine ⟨max N₁ N₂,fun m hm ell hml => ?_⟩
  filter_upwards [h₁ m ((le_max_left _ _).trans hm) ell hml,
    h₂ m ((le_max_right _ _).trans hm) ell hml] with F hf hh
  have hbound := joint_radial_integral_upper sharp m ell F μ hμ g k
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
        ENNReal.ofReal (3:ℝ)*radialCurrentCost sharp m ell F μ hμ g k+
        ENNReal.ofReal (3*C)*ENNReal.ofReal (ε/(6*(C+1))) := by
      apply hbound.trans
      exact add_le_add (add_le_add (mul_le_mul (le_refl _) hf bot_le bot_le) (le_refl _))
        (mul_le_mul (le_refl _) hh bot_le bot_le)
    _ = (ENNReal.ofReal (3:ℝ)*ENNReal.ofReal (ε/6)+
        ENNReal.ofReal (3*C)*ENNReal.ofReal (ε/(6*(C+1))))+
        ENNReal.ofReal (3:ℝ)*radialCurrentCost sharp m ell F μ hμ g k := by ac_rfl
    _ ≤ _ := add_le_add hb (le_refl _)

end LowEnergy.SourceClockYukawaGradedGamma
