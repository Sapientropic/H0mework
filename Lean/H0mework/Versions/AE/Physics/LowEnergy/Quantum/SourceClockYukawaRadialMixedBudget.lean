import H0mework.Versions.AE.Physics.LowEnergy.Quantum.SourceClockYukawaRadialMixedGamma

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1800000
set_option maxRecDepth 2048
noncomputable section
namespace LowEnergy.SourceClockYukawaRadialMixedBudget
open GaussCoreHilbert GaussCoreDifferential GaussFockPair GaussHistoryHilbert GaussNativeForm
open GaussDiagonalHistory GaussUnitaryHistory GaussRadialDomain GaussYukawaOperator
open SourceQuantumConfigurationHilbert SourceMixedNativeReturn SourceScalarDoubleCurrent
open SourceScalarPairedTransport SourceScalarPositiveBulkWard SourceClockYukawaTail
open SourceClockYukawaRadialMixedGamma SourceRelativePowerTail SourceHardyRetardedTail SourceRetardedForcingTail
open SourceJointResidualEnergy SourceFourPoleEnergyClosed SourceScalarSignedInverseReturn
open SourceCutoffDilationWard SourceEscapeSeedTail FullYSourceResolventGraphSplice SourceResolventBandLimit
open MeasureTheory Filter
open scoped Topology InnerProductSpace
abbrev End := QuantumTest →ₗ[ℂ] QuantumTest
abbrev Op := H →L[ℂ] H
attribute [local irreducible] fullAction state compressionCore defectAction inverseRadius sourceB
  SourceClockYukawaRadialMixedGamma.mixedResponse

def radiusSource (g : diagonal.domain) : diagonal.domain :=
  coreEquiv (radiusAction (coreEquiv.symm g))

private theorem radius_source_inverse (g : diagonal.domain) : inverseRadius (radiusSource g:H)=(g:H) := by
  change inverseRadius (embed (radiusAction (coreEquiv.symm g)))=_
  rw [inverse_core,inverse_radius_action]
  exact congrArg Subtype.val (coreEquiv.apply_symm_apply g)

private theorem increment_fixed (sharp : Bool) (m ell : ℕ) (h : diagonal.domain) :
    actualIncrement sharp m ell (h:H)=relativeTail m ell (SourceClockYukawaCurrent.yukawaSource sharp h:H) := by
  have hy : Commute (fullAction sharp) inverseAction := by
    unfold fullAction
    cases sharp
    · exact GaussRadialHamiltonian.original_commutes
    · exact GaussRadialHamiltonian.adjoint_commutes
  have ht : Commute (fullAction sharp) (thetaAction m ell) := by
    unfold thetaAction
    exact (((Commute.one_right (fullAction sharp)).sub_right hy).pow_right _).sub_right
      (((Commute.one_right (fullAction sharp)).sub_right hy).pow_right _)
  have he : embed (coreEquiv.symm h)=(h:H) := congrArg Subtype.val (coreEquiv.apply_symm_apply h)
  have hc := LinearMap.congr_fun ht.eq (coreEquiv.symm h)
  change fullAction sharp (thetaAction m ell (coreEquiv.symm h))=
    thetaAction m ell (fullAction sharp (coreEquiv.symm h)) at hc
  rw [←he,literal_increment_core,literal_full_return,Module.End.mul_apply,hc,←SourceMixedNativeReturn.theta_core]
  rfl

def fixedVector (sharp : Bool) (m ell : ℕ) (F : Index) (z : ℂ) (g : diagonal.domain) : H :=
  finiteResolvent F z (sourceB sharp (relativeTail m ell (radiusSource g:H)))-
    inverseRadius (finiteResolvent F z (relativeTail m ell (SourceClockYukawaCurrent.yukawaSource sharp (radiusSource g):H)))+
    sourceB sharp (relativeTail m ell (finiteResolvent F z (radiusSource g:H)))

def fixedAmplitude (sharp : Bool) (m ell : ℕ) (F : Index) (z : ℂ) (g k : diagonal.domain) : ℂ :=
  inner ℂ (k:H) (finiteResolvent F z (fixedVector sharp m ell F z g))

def mixedAmplitude (sharp : Bool) (m ell : ℕ) (F : Index) (z : ℂ) (g k : diagonal.domain) : ℂ :=
  inner ℂ (k:H) (finiteResolvent F z (mixedResponse sharp m ell F z (radiusSource g:H)))

private theorem finite_adjoint (F : Index) (z : ℂ) :
    (finiteResolvent F z).adjoint=finiteResolvent F (star z) := by
  change star (finiteResolvent F z)=_
  unfold finiteResolvent FullYSourceResolventGraphSplice.resolvent
  rw [←Ring.inverse_star,star_sub,star_smul,star_one,
    (GaussGradedCompression.compression_selfAdjoint F).star_eq]

theorem actual_increment_mixed_split (sharp : Bool) (m ell : ℕ) (F : Index)
    (z : ℂ) (hz : z.im≠0) (g k : diagonal.domain) :
    inner ℂ (finiteResolvent F (star z) (k:H))
      (actualIncrement sharp m ell (finiteResolvent F z (g:H)))=
      fixedAmplitude sharp m ell F z g k-mixedAmplitude sharp m ell F z g k := by
  have h := congrArg (fun A : Op => A (radiusSource g:H))
    (actual_mixed_gamma_operator sharp m ell F z hz)
  simp only [mul_apply_eq_comp,sub_apply,add_apply,pow_two,radius_source_inverse,increment_fixed] at h
  rw [←finite_adjoint,ContinuousLinearMap.adjoint_inner_left,h]
  simp only [fixedAmplitude,mixedAmplitude,fixedVector,map_add,map_sub,inner_add_right,inner_sub_right]

private def fixedPrice (μ : ℝ) (k : diagonal.domain) : ℝ := 3*((1/μ)*‖(k:H)‖)^2

private theorem fixed_bound (sharp : Bool) (m ell : ℕ) (F : Index)
    (μ : ℝ) (hμ : 0<μ) (g k : diagonal.domain) (w : ℝ) :
    ‖fixedAmplitude sharp m ell F (line μ w) g k‖^2 ≤
      fixedPrice μ k*‖finiteResolvent F (line μ w) (sourceB sharp (relativeTail m ell (radiusSource g:H)))‖^2+
      (fixedPrice μ k*‖inverseRadius‖^2)*‖finiteResolvent F (line μ w)
        (relativeTail m ell (SourceClockYukawaCurrent.yukawaSource sharp (radiusSource g):H))‖^2+
      fixedPrice μ k*‖sourceB sharp (relativeTail m ell (finiteResolvent F (line μ w) (radiusSource g:H)))‖^2 := by
  let X := finiteResolvent F (line μ w) (sourceB sharp (relativeTail m ell (radiusSource g:H)))
  let Y := finiteResolvent F (line μ w) (relativeTail m ell (SourceClockYukawaCurrent.yukawaSource sharp (radiusSource g):H))
  let Z := sourceB sharp (relativeTail m ell (finiteResolvent F (line μ w) (radiusSource g:H)))
  have hr : ‖finiteResolvent F (line μ w) (X-inverseRadius Y+Z)‖ ≤
      (1/μ)*‖X-inverseRadius Y+Z‖ := by
    apply ((finiteResolvent F _).le_opNorm _).trans
    have hR := finite_resolvent_norm F (line μ w) (by simpa only [line_im] using hμ.ne')
    have hRn : ‖finiteResolvent F (line μ w)‖ ≤ 1/μ := by
      simpa only [line_im,abs_of_pos hμ] using hR
    exact mul_le_mul_of_nonneg_right hRn (norm_nonneg _)
  have hi := pow_le_pow_left₀ (norm_nonneg _) ((norm_inner_le_norm (𝕜 := ℂ) (k:H) _).trans
    (mul_le_mul_of_nonneg_left hr (norm_nonneg (k:H)))) 2
  have ht := (norm_add_le (X-inverseRadius Y) Z).trans
    (add_le_add (norm_sub_le X (inverseRadius Y)) (le_refl _))
  have hts := pow_le_pow_left₀ (norm_nonneg _) ht 2
  have hp : ‖X-inverseRadius Y+Z‖^2 ≤ 3*‖X‖^2+3*‖inverseRadius Y‖^2+3*‖Z‖^2 := by
    nlinarith only [hts,sq_nonneg (‖X‖-‖inverseRadius Y‖),sq_nonneg (‖X‖-‖Z‖),sq_nonneg (‖inverseRadius Y‖-‖Z‖)]
  have hS := pow_le_pow_left₀ (norm_nonneg _) (inverseRadius.le_opNorm Y) 2
  rw [mul_pow] at hS
  have hv : ‖X-inverseRadius Y+Z‖^2 ≤ 3*‖X‖^2+3*‖inverseRadius‖^2*‖Y‖^2+3*‖Z‖^2 := by
    nlinarith only [hp,hS]
  have hb := mul_le_mul_of_nonneg_left hv (sq_nonneg ((1/μ)*‖(k:H)‖))
  simp only [mul_pow] at hi
  change ‖inner ℂ (k:H) (finiteResolvent F (line μ w) (X-inverseRadius Y+Z))‖^2 ≤ _
  dsimp only [fixedPrice]
  nlinarith only [hi,hb]

private theorem fixed_continuous (sharp : Bool) (m ell : ℕ) (F : Index)
    (μ : ℝ) (hμ : 0<μ) (g k : diagonal.domain) :
    Continuous (fun w : ℝ => fixedAmplitude sharp m ell F (line μ w) g k) := by
  have hr := SourceRetardedBandCurrent.finite_frequency_continuous μ hμ F
  unfold fixedAmplitude fixedVector
  exact continuous_const.inner (hr.clm_apply
    (((hr.clm_apply continuous_const).sub (inverseRadius.continuous.comp (hr.clm_apply continuous_const))).add
      ((sourceB sharp).continuous.comp ((relativeTail m ell).continuous.comp (hr.clm_apply continuous_const)))))

private theorem fixed_common_tail (sharp : Bool) (μ : ℝ) (hμ : 0<μ) (g k : diagonal.domain) :
    ∀ ε : ℝ,0<ε → ∃ N : ℕ,∀ m,N ≤ m → ∀ ell,m ≤ ell →
      ∀ᶠ F in (sourceFilter : Filter Index),
        (∫⁻ w : ℝ,ENNReal.ofReal (‖fixedAmplitude sharp m ell F (line μ w) g k‖^2)) ≤ ENNReal.ofReal ε := by
  intro ε hε
  let P := fixedPrice μ k
  let Q := P*‖inverseRadius‖^2
  let C := 2*P+Q
  have hP : 0≤P := by dsimp [P,fixedPrice];positivity
  have hQ : 0≤Q := mul_nonneg hP (sq_nonneg _)
  have hC : 0≤C := by dsimp [C];positivity
  let δ := ε/(C+1)
  have hδ : 0<δ := by dsimp [δ];positivity
  obtain ⟨N₁,h₁⟩ := fixed_forcing_uniform_energy_tail μ hμ (sourceB sharp) (radiusSource g:H) δ hδ
  obtain ⟨N₂,h₂⟩ := fixed_forcing_uniform_energy_tail μ hμ (1:Op)
    (SourceClockYukawaCurrent.yukawaSource sharp (radiusSource g):H) δ hδ
  obtain ⟨N₃,h₃⟩ := bounded_forcing_full_frequency_tail μ hμ (sourceB sharp) (radiusSource g) δ hδ
  refine ⟨max N₁ (max N₂ N₃),fun m hm ell hml => ?_⟩
  filter_upwards [h₃ m ((le_max_right _ _).trans ((le_max_right _ _).trans hm)) ell hml] with F hz
  have hx := h₁ m ((le_max_left _ _).trans hm) ell hml F
  have hy := h₂ m ((le_max_left _ _).trans ((le_max_right _ _).trans hm)) ell hml F
  simp only [one_apply_eq_self] at hy
  let X (w : ℝ) := ENNReal.ofReal (‖finiteResolvent F (line μ w) (sourceB sharp (relativeTail m ell (radiusSource g:H)))‖^2)
  let Y (w : ℝ) := ENNReal.ofReal (‖finiteResolvent F (line μ w)
    (relativeTail m ell (SourceClockYukawaCurrent.yukawaSource sharp (radiusSource g):H))‖^2)
  let Z (w : ℝ) := ENNReal.ofReal (‖sourceB sharp (relativeTail m ell (finiteResolvent F (line μ w) (radiusSource g:H)))‖^2)
  have hr := SourceRetardedBandCurrent.finite_frequency_continuous μ hμ F
  have hymeas : Measurable (fun w => ENNReal.ofReal Q*Y w) :=
    ((((hr.clm_apply continuous_const).norm.pow 2).measurable).ennreal_ofReal).const_mul _
  have hzmeas : Measurable (fun w => ENNReal.ofReal P*Z w) :=
    (((((sourceB sharp).continuous.comp ((relativeTail m ell).continuous.comp
      (hr.clm_apply continuous_const))).norm.pow 2).measurable).ennreal_ofReal).const_mul _
  calc
    _ ≤ ∫⁻ w : ℝ,ENNReal.ofReal P*X w+ENNReal.ofReal Q*Y w+ENNReal.ofReal P*Z w := by
      apply lintegral_mono
      intro w
      dsimp only [X,Y,Z]
      apply (ENNReal.ofReal_le_ofReal (fixed_bound sharp m ell F μ hμ g k w)).trans
      rw [←ENNReal.ofReal_mul hP,←ENNReal.ofReal_mul hQ,←ENNReal.ofReal_mul hP]
      exact ENNReal.ofReal_add_le.trans (add_le_add ENNReal.ofReal_add_le (le_refl _))
    _ = ENNReal.ofReal P*(∫⁻ w : ℝ,X w)+ENNReal.ofReal Q*(∫⁻ w : ℝ,Y w)+
        ENNReal.ofReal P*(∫⁻ w : ℝ,Z w) := by
      rw [lintegral_add_right _ hzmeas,lintegral_add_right _ hymeas,
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    _ ≤ ENNReal.ofReal P*ENNReal.ofReal δ+ENNReal.ofReal Q*ENNReal.ofReal δ+
        ENNReal.ofReal P*ENNReal.ofReal δ := by gcongr
    _ ≤ ENNReal.ofReal ε := by
      rw [←ENNReal.ofReal_mul hP,←ENNReal.ofReal_mul hQ,
        ←ENNReal.ofReal_add (by positivity) (by positivity),←ENNReal.ofReal_add (by positivity) (by positivity)]
      apply ENNReal.ofReal_le_ofReal
      have he : P*δ+Q*δ+P*δ=C*(ε/(C+1)) := by dsimp [C,δ];ring
      rw [he,←mul_div_assoc]
      apply (div_le_iff₀ (by positivity : 0<C+1)).mpr
      nlinarith

private theorem joint_mixed_split (sharp : Bool) (m ell : ℕ) (F : Index)
    (z : ℂ) (hz : z.im≠0) (g k : diagonal.domain) :
    jointResidual sharp m ell F z hz g k=
      fixedAmplitude sharp m ell F z g k-mixedAmplitude sharp m ell F z g k-
        inner ℂ (k:H) (hardyVector sharp m ell F z (g:H)) := by
  have h := SourceClockYukawaCurrent.actual_increment_current_split sharp m ell F z hz g k
  rw [actual_increment_mixed_split sharp m ell F z hz g k] at h
  rw [SourceClockYukawaCurrent.actual_joint_current_split sharp m ell F z hz g k]
  linear_combination -h

private theorem three_square (a b c : ℂ) :
    ‖a-b-c‖^2 ≤ 3*‖a‖^2+3*‖b‖^2+3*‖c‖^2 := by
  have hn := (norm_sub_le (a-b) c).trans (add_le_add (norm_sub_le a b) (le_refl _))
  have h := pow_le_pow_left₀ (norm_nonneg _) hn 2
  nlinarith only [h,sq_nonneg (‖a‖-‖b‖),sq_nonneg (‖a‖-‖c‖),sq_nonneg (‖b‖-‖c‖)]

def mixedResponseCost (sharp : Bool) (m ell : ℕ) (F : Index) (μ : ℝ) (_hμ : 0<μ)
    (g k : diagonal.domain) : ENNReal :=
  ∫⁻ w : ℝ,ENNReal.ofReal (‖mixedAmplitude sharp m ell F (line μ w) g k‖^2)

private theorem joint_mixed_integral_upper (sharp : Bool) (m ell : ℕ) (F : Index)
    (μ : ℝ) (hμ : 0<μ) (g k : diagonal.domain) :
    ENNReal.ofReal (closedJointCost sharp m ell F μ (g:H) (k:H)) ≤
      ENNReal.ofReal (3:ℝ)*(∫⁻ w : ℝ,ENNReal.ofReal (‖fixedAmplitude sharp m ell F (line μ w) g k‖^2))+
      ENNReal.ofReal (3:ℝ)*mixedResponseCost sharp m ell F μ hμ g k+
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
      (((fixed_continuous sharp m ell F μ hμ g k).norm.pow 2).measurable.ennreal_ofReal).const_mul _
  have hhardy : Measurable (fun w : ℝ => ENNReal.ofReal (3*‖(k:H)‖^2)*
      ENNReal.ofReal (‖hardyVector sharp m ell F (line μ w) (g:H)‖^2)) := by
    simpa only [Pi.pow_apply] using ((hh.norm.pow 2).measurable.ennreal_ofReal).const_mul _
  calc
    _ ≤ ∫⁻ w : ℝ,ENNReal.ofReal (3:ℝ)*ENNReal.ofReal (‖fixedAmplitude sharp m ell F (line μ w) g k‖^2)+
        ENNReal.ofReal (3:ℝ)*ENNReal.ofReal (‖mixedAmplitude sharp m ell F (line μ w) g k‖^2)+
        ENNReal.ofReal (3*‖(k:H)‖^2)*ENNReal.ofReal (‖hardyVector sharp m ell F (line μ w) (g:H)‖^2) := by
      apply lintegral_mono
      intro w
      dsimp only
      have h := three_square (fixedAmplitude sharp m ell F (line μ w) g k)
        (mixedAmplitude sharp m ell F (line μ w) g k)
        (inner ℂ (k:H) (hardyVector sharp m ell F (line μ w) (g:H)))
      have hb := pow_le_pow_left₀ (norm_nonneg _) (norm_inner_le_norm (𝕜 := ℂ)
        (k:H) (hardyVector sharp m ell F (line μ w) (g:H))) 2
      rw [mul_pow] at hb
      rw [←joint_mixed_split sharp m ell F (line μ w)
        (by simpa only [line_im] using hμ.ne') g k] at h
      have hj : ‖jointResidual sharp m ell F (line μ w) (by simpa only [line_im] using hμ.ne') g k‖^2 ≤
          3*‖fixedAmplitude sharp m ell F (line μ w) g k‖^2+
          3*‖mixedAmplitude sharp m ell F (line μ w) g k‖^2+
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

/-- The original Gamma consumes one complete mixed response. The three fixed
source endpoints and the original Hardy tail are paid internally at one cutoff. -/
theorem actual_original_mixed_response_budget (sharp : Bool) (μ : ℝ) (hμ : 0<μ)
    (g k : diagonal.domain) :
    ∀ ε : ℝ,0<ε → ∃ N : ℕ,∀ m,N ≤ m → ∀ ell,m ≤ ell →
      ∀ᶠ F in (sourceFilter : Filter Index),
        ENNReal.ofReal (closedJointCost sharp m ell F μ (g:H) (k:H)) ≤
          ENNReal.ofReal ε+ENNReal.ofReal (3:ℝ)*mixedResponseCost sharp m ell F μ hμ g k := by
  intro ε hε
  let C : ℝ := ‖(k:H)‖^2
  have hC : 0 ≤ C := sq_nonneg _
  obtain ⟨N₁,h₁⟩ := fixed_common_tail sharp μ hμ g k (ε/6) (by positivity)
  obtain ⟨N₂,h₂⟩ := actual_hardy_retarded_tail μ hμ sharp g (ε/(6*(C+1))) (by positivity)
  refine ⟨max N₁ N₂,fun m hm ell hml => ?_⟩
  filter_upwards [h₁ m ((le_max_left _ _).trans hm) ell hml,
    h₂ m ((le_max_right _ _).trans hm) ell hml] with F hf hh
  have hbound := joint_mixed_integral_upper sharp m ell F μ hμ g k
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
        ENNReal.ofReal (3:ℝ)*mixedResponseCost sharp m ell F μ hμ g k+
        ENNReal.ofReal (3*C)*ENNReal.ofReal (ε/(6*(C+1))) := by
      apply hbound.trans
      exact add_le_add (add_le_add (mul_le_mul (le_refl _) hf bot_le bot_le) (le_refl _))
        (mul_le_mul (le_refl _) hh bot_le bot_le)
    _ = (ENNReal.ofReal (3:ℝ)*ENNReal.ofReal (ε/6)+
        ENNReal.ofReal (3*C)*ENNReal.ofReal (ε/(6*(C+1))))+
        ENNReal.ofReal (3:ℝ)*mixedResponseCost sharp m ell F μ hμ g k := by ac_rfl
    _ ≤ _ := add_le_add hb (le_refl _)

end LowEnergy.SourceClockYukawaRadialMixedBudget
