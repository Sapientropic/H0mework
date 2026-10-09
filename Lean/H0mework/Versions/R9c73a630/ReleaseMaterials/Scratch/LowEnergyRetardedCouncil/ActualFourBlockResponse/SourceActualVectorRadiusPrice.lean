import H0mework.Versions.R9c73a630.ReleaseMaterials.Scratch.LowEnergyRetardedCouncil.ActualFourBlockResponse.SourceActualVectorJointTail
import H0mework.Versions.R9c73a630.Physics.LowEnergy.Quantum.SourceClockYukawaQ8RadiusBudget
import H0mework.Versions.R9c73a630.Physics.LowEnergy.Quantum.SourceClockYukawaNormalizedCurrent

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 1800000
noncomputable section
namespace LowEnergy.ActualVectorJointCost
open GaussCoreHilbert GaussCoreDifferential GaussFockPair GaussHistoryHilbert GaussNativeForm
open GaussDiagonalHistory GaussUnitaryHistory GaussRadialDomain GaussYukawaCoefficient GaussYukawaOperator
open SourceClockYukawaCubicCurrent
open SourceMixedNativeReturn SourceScalarDoubleCurrent SourceScalarPositiveBulkWard
open SourceClockYukawaTail SourceClockYukawaNormalizedCurrent SourceClockYukawaRadialMixedBudget
open SourceClockYukawaQ8RadiusBudget SourceRelativePowerTail SourceCutoffDilationWard
open SourceEscapeSeedTail FullYSourceResolventGraphSplice SourceResolventBandLimit
open MeasureTheory Filter
open scoped BigOperators InnerProductSpace Topology ENNReal

private abbrev End := QuantumTest →ₗ[ℂ] QuantumTest
private theorem core_embed (g : diagonal.domain) : embed (coreEquiv.symm g)=(g:H) :=
  congrArg Subtype.val (coreEquiv.apply_symm_apply g)
private theorem resolvent_embed (F : Index) (z : ℂ) (hz : z.im≠0) (f : QuantumTest) :
    embed (resolventCore F z hz f)=finiteResolvent F z (embed f) := by
  unfold resolventCore state
  exact core_embed _
private theorem radius_inverse (f : QuantumTest) : radiusAction (inverseAction f)=f := by
  apply DFunLike.ext
  intro z
  apply PiLp.ext
  intro word
  change radius z • ((reciprocal z:ℂ)*f z word)=f z word
  rw [Complex.real_smul]
  have hr : (radius z:ℂ)≠0 := by exact_mod_cast (radius_pos z).ne'
  simp only [reciprocal,Complex.ofReal_inv,←mul_assoc,mul_inv_cancel₀ hr,one_mul]
private theorem radius_theta (m ell : ℕ) : Commute radiusAction (thetaAction m ell) := by
  let Q : End := 1-inverseAction
  have hQ (f:QuantumTest) : radiusAction (Q f)=Q (radiusAction f) := by
    change radiusAction (f-inverseAction f)=radiusAction f-inverseAction (radiusAction f)
    rw [map_sub,radius_inverse,inverse_radius_action]
  have hp (k:ℕ) (f:QuantumTest) : radiusAction ((Q^k) f)=(Q^k) (radiusAction f) := by
    induction k generalizing f with
    | zero => rfl
    | succ k ih =>
      rw [pow_succ']
      change radiusAction (Q ((Q^k) f))=Q ((Q^k) (radiusAction f))
      rw [hQ,ih]
  change radiusAction*thetaAction m ell=thetaAction m ell*radiusAction
  apply LinearMap.ext
  intro f
  change radiusAction ((Q^(m+1)) f-(Q^(ell+1)) f)=
    (Q^(m+1)) (radiusAction f)-(Q^(ell+1)) (radiusAction f)
  rw [map_sub,hp,hp]
private theorem full_inverse (sharp : Bool) : Commute (fullAction sharp) inverseAction := by
  cases sharp
  · exact GaussRadialHamiltonian.original_commutes
  · exact GaussRadialHamiltonian.adjoint_commutes
private theorem full_normalized_radius (sharp : Bool) (f : QuantumTest) :
    fullAction sharp f=normalizedAction sharp (radiusAction f) := by
  unfold normalizedAction
  change _=inverseAction (fullAction sharp (radiusAction f))
  have hc := LinearMap.congr_fun (full_inverse sharp).eq (radiusAction f)
  change fullAction sharp (inverseAction (radiusAction f))=inverseAction (fullAction sharp (radiusAction f)) at hc
  rw [inverse_radius_action] at hc
  exact hc

attribute [local irreducible] embed resolventCore radiusAction relativeTail sourceB finiteResolvent

/-- The original full cutoff increment splits into a fixed-radius seed and its
same-compression radius commutator. Both Yukawa branches retain their actual B. -/
theorem actual_increment_radius_split (sharp : Bool) (m ell : ℕ) (F : Index)
    (z : ℂ) (hz : z.im≠0) (g : diagonal.domain) :
    finiteResolvent F z (actualIncrement sharp m ell (finiteResolvent F z (g:H)))=
      finiteResolvent F z (sourceB sharp (relativeTail m ell
        (finiteResolvent F z (radiusSource g:H))))+
      finiteResolvent F z (sourceB sharp (embed (radiusResponseCore m ell F z hz g))) := by
  have he := resolvent_embed F z hz (coreEquiv.symm g)
  rw [core_embed] at he
  rw [←he,literal_increment_core,literal_full_return]
  change finiteResolvent F z (embed (fullAction sharp
    (thetaAction m ell (resolventCore F z hz (coreEquiv.symm g)))))=_
  have ht (f:QuantumTest) : radiusAction (thetaAction m ell f)=thetaAction m ell (radiusAction f) :=
    LinearMap.congr_fun (radius_theta m ell).eq f
  rw [full_normalized_radius,ht,←original_normalized_core]
  have hd : embed (radiusResponseCore m ell F z hz g)=
      relativeTail m ell (embed (radiusAction (resolventCore F z hz (coreEquiv.symm g))))-
      relativeTail m ell (finiteResolvent F z (radiusSource g:H)) := by
    let f:=coreEquiv.symm g
    let R:=resolventCore F z hz
    have h0:= (theta_core m ell (radiusAction (R f)-R (radiusAction f))).symm
    have h1:=congrArg (relativeTail m ell)
      (map_sub embed (radiusAction (R f)) (R (radiusAction f)))
    have h2:=congrArg (fun v:H=>relativeTail m ell (embed (radiusAction (R f))-v))
      (resolvent_embed F z hz (radiusAction f))
    have h3:=map_sub (relativeTail m ell) (embed (radiusAction (R f)))
      (finiteResolvent F z (embed (radiusAction f)))
    exact h0.trans (h1.trans (h2.trans h3))
  have hs := (sub_eq_iff_eq_add.mp hd.symm).trans (add_comm _ _)
  have ht := (theta_core m ell (radiusAction (resolventCore F z hz (coreEquiv.symm g)))).symm.trans hs
  exact (congrArg (fun v:H=>finiteResolvent F z (sourceB sharp v)) ht).trans
    ((congrArg (finiteResolvent F z) (map_add (sourceB sharp) _ _)).trans
      (map_add (finiteResolvent F z) _ _))

private theorem causal_nonreal' (advanced : Bool) (μ w : ℝ) (hμ : 0<μ) :
    (causalFrequency advanced μ w).im≠0 := by
  cases advanced <;> simpa only [causalFrequency,Bool.false_eq_true,ite_false,ite_true,
    line_im,neg_ne_zero] using hμ.ne'
private theorem causal_resolvent_bound (advanced : Bool) (μ : ℝ) (hμ : 0<μ)
    (F : Index) (w : ℝ) (v : H) :
    ‖finiteResolvent F (causalFrequency advanced μ w) v‖≤(1/μ)*‖v‖ := by
  have hb:=finite_resolvent_norm F _ (causal_nonreal' advanced μ w hμ)
  have he: |(causalFrequency advanced μ w).im|=μ := by
    cases advanced <;> simp [causalFrequency,line_im,abs_of_pos hμ]
  rw [he] at hb
  exact ((finiteResolvent F _).le_opNorm v).trans
    (mul_le_mul_of_nonneg_right hb (norm_nonneg v))
private theorem two_norm (a b : H) : ‖a+b‖^2≤2*‖a‖^2+2*‖b‖^2 := by
  have h:=pow_le_pow_left₀ (norm_nonneg _) (norm_add_le a b) 2
  nlinarith only [h,sq_nonneg (‖a‖-‖b‖)]

/-- No output reader is selected: this is the actual radius commutator's complete
Hilbert norm on each of the original causal lines. -/
def causalRadiusBudget (advanced : Bool) (m ell : ℕ) (F : Index)
    (μ : ℝ) (hμ : 0<μ) (g : diagonal.domain) : ENNReal :=
  ∫⁻w:ℝ,ENNReal.ofReal (‖embed (radiusResponseCore m ell F
    (causalFrequency advanced μ w) (causal_nonreal' advanced μ w hμ) g)‖^2)

theorem actual_original_radius_budget (m ell : ℕ) (F : Index)
    (μ : ℝ) (hμ : 0<μ) (g : diagonal.domain) :
    radiusResponseBudget m ell F μ hμ g=
      ENNReal.ofReal μ*causalRadiusBudget false m ell F μ hμ g := by
  unfold radiusResponseBudget causalRadiusBudget
  simp only [causalFrequency,Bool.false_eq_true,ite_false]
  simp_rw [ENNReal.ofReal_mul hμ.le]
  exact lintegral_const_mul' _ _ ENNReal.ofReal_ne_top

private theorem increment_radius_bound (advanced sharp : Bool) (m ell : ℕ) (F : Index)
    (μ : ℝ) (hμ : 0<μ) (g : diagonal.domain) (w : ℝ) :
    ‖finiteResolvent F (causalFrequency advanced μ w) (actualIncrement sharp m ell
      (finiteResolvent F (causalFrequency advanced μ w) (g:H)))‖^2≤
      (2*(1/μ)^2)*‖sourceB sharp (relativeTail m ell
        (finiteResolvent F (causalFrequency advanced μ w) (radiusSource g:H)))‖^2+
      (2*(1/μ)^2*‖sourceB sharp‖^2)*‖embed (radiusResponseCore m ell F
        (causalFrequency advanced μ w) (causal_nonreal' advanced μ w hμ) g)‖^2 := by
  rw [actual_increment_radius_split sharp m ell F _ (causal_nonreal' advanced μ w hμ) g]
  have ht:=two_norm
    (finiteResolvent F (causalFrequency advanced μ w) (sourceB sharp (relativeTail m ell
      (finiteResolvent F (causalFrequency advanced μ w) (radiusSource g:H)))))
    (finiteResolvent F (causalFrequency advanced μ w) (sourceB sharp (embed
      (radiusResponseCore m ell F _ (causal_nonreal' advanced μ w hμ) g))))
  have h1:=pow_le_pow_left₀ (norm_nonneg _) (causal_resolvent_bound advanced μ hμ F w
    (sourceB sharp (relativeTail m ell
      (finiteResolvent F (causalFrequency advanced μ w) (radiusSource g:H))))) 2
  have h2:=pow_le_pow_left₀ (norm_nonneg _) ((causal_resolvent_bound advanced μ hμ F w
    (sourceB sharp (embed (radiusResponseCore m ell F _ (causal_nonreal' advanced μ w hμ) g)))).trans
      (mul_le_mul_of_nonneg_left ((sourceB sharp).le_opNorm _) (by positivity))) 2
  simp only [mul_pow] at h1 h2
  nlinarith only [ht,h1,h2]

/-- The fixed-radius term is paid in the original whole-input TimeSpace. The
remaining price is the same source radius response, without fixed-k reduction. -/
theorem actual_first_leg_radius_paid_price (sharp : Bool) (μ : ℝ) (hμ : 0<μ)
    (g : diagonal.domain) :
    ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ m, N ≤ m → ∀ ell, m ≤ ell →
      ∀ᶠ F in (sourceFilter : Filter Index),
      ∀advanced:Bool,
        (∫⁻w:ℝ,ENNReal.ofReal (‖finiteResolvent F (causalFrequency advanced μ w)
          (actualIncrement sharp m ell (finiteResolvent F (causalFrequency advanced μ w) (g:H)))‖^2))≤
        ENNReal.ofReal ε+ENNReal.ofReal (2*(1/μ)^2*‖sourceB sharp‖^2)*
          causalRadiusBudget advanced m ell F μ hμ g := by
  intro ε hε
  let C:ℝ:=2*(1/μ)^2
  have hC:0≤C:=by dsimp only [C]; positivity
  obtain ⟨N,hN⟩:=actual_bounded_theta_causal_tail μ hμ (sourceB sharp) (radiusSource g:H)
    (ε/(C+1)) (by positivity)
  refine ⟨N,fun m hm ell hml=>?_⟩
  filter_upwards [hN m hm ell hml] with F hF
  intro advanced
  let X:ℝ→ℝ:=fun w=>‖sourceB sharp (relativeTail m ell
    (finiteResolvent F (causalFrequency advanced μ w) (radiusSource g:H)))‖^2
  have hc:Continuous X := by
    have he: (fun w:ℝ=>causalFrequency advanced μ w)=
        (fun w:ℝ=>SourceLocalizedInverseFormPayment.actualFrequency advanced μ w) := by
      funext w
      cases advanced
      · rfl
      · apply Complex.ext <;> simp [causalFrequency,SourceLocalizedInverseFormPayment.actualFrequency,line]
    dsimp only [X]
    simp_rw [congrFun he]
    exact ((sourceB sharp).continuous.comp ((relativeTail m ell).continuous.comp
      (((paid_clock_tail% frequency_continuous) advanced μ hμ F).clm_apply continuous_const))).norm.pow 2
  have hb := lintegral_mono (μ := volume) (fun w:ℝ=>ENNReal.ofReal_le_ofReal
    (increment_radius_bound advanced sharp m ell F μ hμ g w))
  have hnon:0≤2*(1/μ)^2*‖sourceB sharp‖^2:=by positivity
  have hadd (u v:ℝ) (hu:0≤u) (hv:0≤v) :
      ENNReal.ofReal (C*u+(C*‖sourceB sharp‖^2)*v)=
        ENNReal.ofReal C*ENNReal.ofReal u+
        ENNReal.ofReal (C*‖sourceB sharp‖^2)*ENNReal.ofReal v := by
    rw [ENNReal.ofReal_add (mul_nonneg hC hu) (mul_nonneg hnon hv),
      ENNReal.ofReal_mul hC,ENNReal.ofReal_mul hnon]
  have hb := hb.trans_eq (lintegral_congr (μ := volume) (fun w:ℝ=>
    hadd (X w) (‖embed (radiusResponseCore m ell F (causalFrequency advanced μ w)
      (causal_nonreal' advanced μ w hμ) g)‖^2) (sq_nonneg _) (sq_nonneg _)))
  have hmX : Measurable (fun w:ℝ=>ENNReal.ofReal C*ENNReal.ofReal (X w)) :=
    measurable_const.mul (ENNReal.measurable_ofReal.comp hc.measurable)
  rw [lintegral_add_left hmX,
    lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
    lintegral_const_mul' _ _ ENNReal.ofReal_ne_top] at hb
  change _≤ENNReal.ofReal C*(∫⁻w,ENNReal.ofReal (X w))+
    ENNReal.ofReal (C*‖sourceB sharp‖^2)*causalRadiusBudget advanced m ell F μ hμ g at hb
  apply hb.trans
  refine add_le_add ?_ le_rfl
  calc
    _≤ENNReal.ofReal C*ENNReal.ofReal (ε/(C+1)) :=
      mul_le_mul le_rfl (hF advanced) zero_le zero_le
    _≤ENNReal.ofReal ε := by
      rw [←ENNReal.ofReal_mul hC]
      apply ENNReal.ofReal_le_ofReal
      rw [←mul_div_assoc]
      apply (div_le_iff₀ (show 0<C+1 by positivity)).mpr
      nlinarith only [hε]
private theorem joint_reverse_price (advanced sharp : Bool) (m ell : ℕ) (F : Index)
    (μ : ℝ) (hμ : 0<μ) (g : H) :
    vectorJointCost advanced sharp m ell F μ g≤
      2*(∫w:ℝ,‖finiteResolvent F (causalFrequency advanced μ w)
        (actualIncrement sharp m ell (finiteResolvent F (causalFrequency advanced μ w) g))‖^2)+
      2*hardyPrice advanced sharp m ell F μ g := by
  let X:ℝ→H:=fun w=>finiteResolvent F (causalFrequency advanced μ w)
    (actualIncrement sharp m ell (finiteResolvent F (causalFrequency advanced μ w) g))
  have hi:=actual_vector_causal_integrable F advanced μ hμ (actualIncrement sharp m ell) g
  have hj:=actual_vector_causal_integrable F advanced μ hμ
    (SourceJointResidualEnergy.jointInsertion sharp m ell F) g
  have hh:=actual_hardy_vector_integrable advanced sharp m ell F μ hμ g
  have hp(w:ℝ):‖jointVector advanced sharp m ell F μ g w‖^2≤
      2*‖X w‖^2+2*‖hardyVector advanced sharp m ell F μ g w‖^2 := by
    have he:=actual_increment_vector_split advanced sharp m ell F μ hμ g w
    have he':jointVector advanced sharp m ell F μ g w=
        X w+(-hardyVector advanced sharp m ell F μ g w) := by
      change X w=_ at he
      rw [he]
      abel
    rw [he']
    simpa only [norm_neg] using two_norm (X w) (-hardyVector advanced sharp m ell F μ g w)
  have h:=integral_mono hj ((hi.const_mul 2).add (hh.const_mul 2)) hp
  simp only [Pi.add_apply] at h
  rw [integral_add (hi.const_mul 2) (hh.const_mul 2),integral_const_mul,integral_const_mul,
    actual_hardy_vector_energy advanced sharp m ell F μ hμ g] at h
  exact (actual_vector_joint_energy advanced sharp m ell F μ hμ g).symm ▸ h

/-- The reader-free closed four-pole joint Gram now consumes the actual radius
commutator price. All fixed-source and Hardy pieces are paid internally. -/
theorem actual_vector_joint_radius_paid_price (sharp : Bool) (μ : ℝ) (hμ : 0<μ)
    (g : diagonal.domain) :
    ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ m, N ≤ m → ∀ ell, m ≤ ell →
      ∀ᶠ F in (sourceFilter:Filter Index), ∀ advanced:Bool,
        ENNReal.ofReal (vectorJointCost advanced sharp m ell F μ (g:H))≤
          ENNReal.ofReal ε+ENNReal.ofReal (4*(1/μ)^2*‖sourceB sharp‖^2)*
            causalRadiusBudget advanced m ell F μ hμ g := by
  intro ε hε
  obtain ⟨N1,h1⟩:=actual_first_leg_radius_paid_price sharp μ hμ g (ε/4) (by positivity)
  obtain ⟨N2,h2⟩:=actual_hardy_price_causal_tail sharp μ hμ g (ε/4) (by positivity)
  refine ⟨max N1 N2,fun m hm ell hml=>?_⟩
  filter_upwards [h1 m (by omega) ell hml,h2 m (by omega) ell hml] with F hF hG
  intro advanced
  let J:ℝ:=∫w:ℝ,‖finiteResolvent F (causalFrequency advanced μ w)
    (actualIncrement sharp m ell (finiteResolvent F (causalFrequency advanced μ w) (g:H)))‖^2
  have hJ:0≤J:=integral_nonneg (fun _=>sq_nonneg _)
  have hH:0≤hardyPrice advanced sharp m ell F μ (g:H) := by
    rw [←actual_hardy_vector_energy advanced sharp m ell F μ hμ (g:H)]
    exact integral_nonneg (fun _=>sq_nonneg _)
  have hi:=actual_vector_causal_integrable F advanced μ hμ (actualIncrement sharp m ell) (g:H)
  have he:=ofReal_integral_eq_lintegral_ofReal hi (Eventually.of_forall (fun _=>sq_nonneg _))
  change ENNReal.ofReal J=_ at he
  have hb:=ENNReal.ofReal_le_ofReal (joint_reverse_price advanced sharp m ell F μ hμ (g:H))
  change _≤ENNReal.ofReal (2*J+2*hardyPrice advanced sharp m ell F μ (g:H)) at hb
  rw [ENNReal.ofReal_add (mul_nonneg (by norm_num) hJ) (mul_nonneg (by norm_num) hH),
    ENNReal.ofReal_mul (by norm_num: (0:ℝ)≤2),ENNReal.ofReal_mul (by norm_num: (0:ℝ)≤2),he] at hb
  have h:=hb.trans (add_le_add (mul_le_mul le_rfl (hF advanced) zero_le zero_le)
    (mul_le_mul le_rfl (ENNReal.ofReal_le_ofReal (hG advanced)) zero_le zero_le))
  have hfour:ENNReal.ofReal (2:ℝ)*ENNReal.ofReal (2*(1/μ)^2*‖sourceB sharp‖^2)=
      ENNReal.ofReal (4*(1/μ)^2*‖sourceB sharp‖^2) := by
    rw [←ENNReal.ofReal_mul (by norm_num)]
    congr 1
    ring
  have heps:ENNReal.ofReal (2:ℝ)*ENNReal.ofReal (ε/4)+
      ENNReal.ofReal (2:ℝ)*ENNReal.ofReal (ε/4)=ENNReal.ofReal ε := by
    rw [←ENNReal.ofReal_mul (by norm_num),←ENNReal.ofReal_add (by positivity) (by positivity)]
    congr 1
    ring
  exact h.trans_eq (by rw [mul_add,←mul_assoc,hfour];rw [add_right_comm,heps])

end LowEnergy.ActualVectorJointCost
