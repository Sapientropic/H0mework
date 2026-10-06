import H0mework.Versions.AD.Physics.LowEnergy.Quantum.SourceRadiusPairedScalarPrice

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1500000
set_option maxRecDepth 2048
noncomputable section
namespace LowEnergy.SourceRadiusClosedJointCost
open GaussCoreHilbert GaussDiagonalHistory GaussUnitaryHistory
open SourceRadiusPairedScalarPrice SourceScalarSignedInverseReturn SourceJointResidualEnergy
open SourceHardyRetardedTail SourceRetardedIncrement SourceFourPoleEnergyClosed
open FullYSourceResolventGraphSplice SourceResolventBandLimit
open MeasureTheory Filter
open scoped Topology InnerProductSpace
attribute [local irreducible] closedJointCost jointResidual radiusMoment radiusBand

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

private theorem two_square (a b : ℂ) : ‖a-b‖^2 ≤ 2*‖a‖^2+2*‖b‖^2 := by
  have h := pow_le_pow_left₀ (norm_nonneg _) (norm_sub_le a b) 2
  nlinarith [sq_nonneg (‖a‖-‖b‖)]

/-- Original full joint remainder, before any scalar/coframe current decomposition. -/
theorem actual_joint_paired_radius_bound (sharp : Bool) (m ell : ℕ) (hm : m≤ell) (F : Index)
    (z : ℂ) (hz : z.im≠0) (g k : diagonal.domain) :
    ‖jointResidual sharp m ell F z hz g k‖^2 ≤
      2*‖GaussYukawaOperator.bounded‖^2*
        (radiusMoment m ell (finiteResolvent F (star z) (k : H))*
          radiusMoment m ell (finiteResolvent F z (g : H)))+
      2*‖(k : H)‖^2*‖hardyVector sharp m ell F z (g : H)‖^2 := by
  let a := inner ℂ (finiteResolvent F (star z) (k : H))
    (SourceEscapeSeedTail.actualIncrement sharp m ell (finiteResolvent F z (g : H)))
  let b := inner ℂ (k : H) (hardyVector sharp m ell F z (g : H))
  have hi := SourceCornerPartition.actual_full_increment_splice sharp m ell F z hz g k
  have hp := resolvent_pair (GaussGradedCompression.compression F)
    (GaussGradedCompression.compression_selfAdjoint F) z hz (k : H)
    (SourceEscapeSeedTail.actualIncrement sharp m ell (finiteResolvent F z (g : H)))
  have hj : jointResidual sharp m ell F z hz g k=a-b := by
    have he : a=b+jointResidual sharp m ell F z hz g k := by
      simpa only [a,b,jointResidual,hardyVector,add_assoc] using! hp.symm.trans hi
    exact (eq_sub_iff_add_eq.mpr (by rw [he];ring))
  have ha := original_paired_radius_price sharp m ell hm
    (finiteResolvent F (star z) (k : H)) (finiteResolvent F z (g : H))
  have hb := (pow_le_pow_left₀ (norm_nonneg _) (norm_inner_le_norm (𝕜 := ℂ) (k : H)
    (hardyVector sharp m ell F z (g : H))) 2).trans_eq (mul_pow _ _ _)
  rw [hj]
  have ht := (two_square a b).trans (add_le_add (mul_le_mul_of_nonneg_left ha (by norm_num))
    (mul_le_mul_of_nonneg_left hb (by norm_num)))
  exact ht.trans_eq (by ring)

/-- Both radius moments refer to the same original F and the original advanced/retarded legs. -/
def pairedRadiusCost (m ell : ℕ) (F : Index) (μ : ℝ) (g k : diagonal.domain) : ENNReal :=
  ∫⁻ w : ℝ,ENNReal.ofReal (radiusMoment m ell (finiteResolvent F (star (line μ w)) (k : H))*
    radiusMoment m ell (finiteResolvent F (line μ w) (g : H)))

private theorem joint_integral_upper (sharp : Bool) (m ell : ℕ) (hm : m≤ell) (F : Index)
    (μ : ℝ) (hμ : 0<μ) (g k : diagonal.domain) :
    ENNReal.ofReal (closedJointCost sharp m ell F μ (g : H) (k : H)) ≤
      ENNReal.ofReal (2*‖GaussYukawaOperator.bounded‖^2)*pairedRadiusCost m ell F μ g k+
      ENNReal.ofReal (2*‖(k : H)‖^2)*(∫⁻ w : ℝ,
        ENNReal.ofReal (‖hardyVector sharp m ell F (line μ w) (g : H)‖^2)) := by
  rw [←actual_joint_closed_lintegral sharp m ell F μ hμ g k]
  have hr := SourceRetardedBandCurrent.finite_frequency_continuous μ hμ F
  have hp : Continuous (fun w => particular sharp m ell F (line μ w) (g : H)) :=
    (cutoffSolver sharp m ell).continuous.comp (hr.clm_apply continuous_const)
  have hh : Continuous (fun w : ℝ => hardyVector sharp m ell F (line μ w) (g : H)) :=
    hp.add ((show Continuous (fun w : ℝ => line μ w) by unfold line;fun_prop).smul (hr.clm_apply hp))
  have hmeas : Measurable (fun w : ℝ => ENNReal.ofReal (2*‖(k : H)‖^2)*
      ENNReal.ofReal (‖hardyVector sharp m ell F (line μ w) (g : H)‖^2)) := by
    simpa only [Pi.pow_apply] using
      ((hh.norm.pow 2).measurable.ennreal_ofReal).const_mul (ENNReal.ofReal (2*‖(k : H)‖^2))
  calc
    _ ≤ ∫⁻ w : ℝ,ENNReal.ofReal (2*‖GaussYukawaOperator.bounded‖^2)*
        ENNReal.ofReal (radiusMoment m ell (finiteResolvent F (star (line μ w)) (k : H))*
          radiusMoment m ell (finiteResolvent F (line μ w) (g : H)))+
        ENNReal.ofReal (2*‖(k : H)‖^2)*ENNReal.ofReal (‖hardyVector sharp m ell F (line μ w) (g : H)‖^2) := by
      apply lintegral_mono
      intro w
      dsimp only
      have h := actual_joint_paired_radius_bound sharp m ell hm F (line μ w)
        (by simpa only [line_im] using hμ.ne') g k
      calc
        _ ≤ ENNReal.ofReal (2*‖GaussYukawaOperator.bounded‖^2*
            (radiusMoment m ell (finiteResolvent F (star (line μ w)) (k : H))*
              radiusMoment m ell (finiteResolvent F (line μ w) (g : H)))+
            2*‖(k : H)‖^2*‖hardyVector sharp m ell F (line μ w) (g : H)‖^2) := ENNReal.ofReal_le_ofReal h
        _ ≤ _ := by
          rw [←ENNReal.ofReal_mul (by positivity : 0≤2*‖GaussYukawaOperator.bounded‖^2),
            ←ENNReal.ofReal_mul (by positivity : 0≤2*‖(k : H)‖^2)]
          exact ENNReal.ofReal_add_le
    _ = _ := by
      rw [lintegral_add_right _ hmeas,lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      rfl

/-- The paid Hardy endpoint leaves only the paired first-radius price in the complete original cost. -/
theorem actual_original_paired_radius_budget (sharp : Bool) (μ : ℝ) (hμ : 0<μ) (g k : diagonal.domain) :
    ∀ ε : ℝ,0<ε → ∃ N : ℕ,∀ m,N ≤ m → ∀ ell,m ≤ ell →
      ∀ᶠ F in (sourceFilter : Filter Index),
        ENNReal.ofReal (closedJointCost sharp m ell F μ (g : H) (k : H)) ≤ ENNReal.ofReal ε+
          ENNReal.ofReal (2*‖GaussYukawaOperator.bounded‖^2)*pairedRadiusCost m ell F μ g k := by
  intro ε hε
  let C : ℝ := 2*‖(k : H)‖^2
  have hC : 0≤C := by dsimp only [C];positivity
  obtain ⟨N,hN⟩ := actual_hardy_retarded_tail μ hμ sharp g (ε/(C+1)) (by positivity)
  refine ⟨N,fun m hm ell hell => ?_⟩
  filter_upwards [hN m hm ell hell] with F hF
  have he : ENNReal.ofReal C*ENNReal.ofReal (ε/(C+1)) ≤ ENNReal.ofReal ε := by
    rw [←ENNReal.ofReal_mul hC]
    apply ENNReal.ofReal_le_ofReal
    have hp : 0<C+1 := by linarith
    exact (mul_le_mul_of_nonneg_right (by linarith : C≤C+1) (div_pos hε hp).le).trans_eq
      (mul_div_cancel₀ ε hp.ne')
  have hi := (joint_integral_upper sharp m ell hell F μ hμ g k).trans
    (add_le_add le_rfl ((mul_le_mul' le_rfl hF).trans he))
  exact hi.trans_eq (add_comm _ _)

end LowEnergy.SourceRadiusClosedJointCost
