import H0mework.Versions.AD.Physics.LowEnergy.AlphaSource.CanonicalPreparationMomentumTargetJets

set_option autoImplicit false
set_option maxHeartbeats 240000
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationVacuumMomentumFirst
open PreparationVacuumWeyl PreparationVacuumWeylDecay PreparationVacuumFourierJets
open CanonicalPreparationSquareCutoff MeasureTheory Filter Set
open scoped ContDiff Topology SchwartzMap

local instance targetNormSMul (j n : ℕ) : NormSMulClass ℝ
    (ContinuousMultilinearMap ℝ (fun _ : Fin j => PhysicalMomentum) (MomentumJet n)) := by
  with_unfolding_all
    exact @NormedSpace.toNormSMulClass ℝ
      (ContinuousMultilinearMap ℝ (fun _ : Fin j => PhysicalMomentum) (MomentumJet n))
      inferInstance inferInstance inferInstance

def sourceTargetCompact : Set (PhysicalMomentum × PhysicalMomentum) :=
  positionCompact ×ˢ Metric.closedBall 0 3

theorem sourceTargetCompact_compact : IsCompact sourceTargetCompact :=
  positionCompact_compact.prod (isCompact_closedBall _ _)

theorem sourceTargetBound_exists (j n : ℕ) :
    ∃ bound : ℝ, 0 ≤ bound ∧ ∀ xp∈sourceTargetCompact, ‖momentumFirstJet j n xp‖ ≤ bound := by
  have normContinuous : Continuous (fun f :
      ContinuousMultilinearMap ℝ (fun _ : Fin j => PhysicalMomentum) (MomentumJet n) => ‖f‖) := by
    with_unfolding_all
      exact continuous_norm (E := ContinuousMultilinearMap ℝ (fun _ : Fin j => PhysicalMomentum) (MomentumJet n))
  have cont : Continuous (fun xp => ‖momentumFirstJet j n xp‖) :=
    normContinuous.comp (momentumFirstJet_smooth j n).continuous
  obtain ⟨bound,hbound⟩ := sourceTargetCompact_compact.bddAbove_image cont.continuousOn
  refine ⟨max bound 0,le_max_right _ _,?_⟩
  intro xp hx
  exact (hbound (mem_image_of_mem _ hx)).trans (le_max_left _ _)

def sourceTargetBound (j n : ℕ) : ℝ := Classical.choose (sourceTargetBound_exists j n)

theorem sourceTargetBound_nonnegative (j n : ℕ) : 0 ≤ sourceTargetBound j n :=
  (Classical.choose_spec (sourceTargetBound_exists j n)).1

theorem momentumFirstJet_low_bound (j n : ℕ) (x p : PhysicalMomentum) (low : ‖p‖≤3) :
    ‖momentumFirstJet j n (x,p)‖ ≤ sourceTargetBound j n := by
  by_cases position : x∈positionCompact
  · exact (Classical.choose_spec (sourceTargetBound_exists j n)).2 (x,p)
      ⟨position,by simpa only [Metric.mem_closedBall,dist_zero_right] using low⟩
  · rw [momentumFirstJet_zero_outside j n x p position]
    have zeroNorm := @norm_zero
      (ContinuousMultilinearMap ℝ (fun _ : Fin j => PhysicalMomentum) (MomentumJet n)) inferInstance
    simpa only [zeroNorm] using sourceTargetBound_nonnegative j n

theorem momentumFirstJet_high_bound (j n : ℕ) (x p : PhysicalMomentum) (high : 3<‖p‖) :
    (‖p‖/2)^n*‖momentumFirstJet j n (x,p)‖ ≤ (‖p‖/2)*sourceTargetBound j n := by
  let a : ℝ := ‖p‖/2
  let u : PhysicalMomentum := a⁻¹ • p
  have positive : 0<a := by dsimp [a]; linarith
  have radius : ‖u‖=2 := by
    dsimp only [u]
    rw [norm_smul,Real.norm_eq_abs,abs_inv,abs_of_pos positive]
    dsimp only [a]
    field_simp
  have scale : a • u=p := by
    dsimp only [u]
    rw [smul_smul,mul_inv_cancel₀ positive.ne',one_smul]
  have homothety := congrArg norm (momentumFirstJet_homothety j n x u a positive
    (by rw [radius]; norm_num) (by rw [scale]; linarith))
  have normLeft : ‖a^n • momentumFirstJet j n (x,a • u)‖=
      ‖a^n‖*‖momentumFirstJet j n (x,a • u)‖ := by
    with_unfolding_all
      exact norm_smul (a^n) (momentumFirstJet j n (x,a • u))
  have normRight : ‖a • momentumFirstJet j n (x,u)‖=‖a‖*‖momentumFirstJet j n (x,u)‖ := by
    with_unfolding_all
      exact norm_smul a (momentumFirstJet j n (x,u))
  rw [normLeft,normRight] at homothety
  simp only [Real.norm_eq_abs,abs_of_nonneg (pow_nonneg positive.le n),
    abs_of_pos positive,scale] at homothety
  calc
    a^n*‖momentumFirstJet j n (x,p)‖ = a*‖momentumFirstJet j n (x,u)‖ := homothety
    _ ≤ a*sourceTargetBound j n := mul_le_mul_of_nonneg_left
      (momentumFirstJet_low_bound j n x u (by rw [radius]; norm_num)) positive.le

theorem momentumFirstJet_order_zero_bound (j : ℕ) (x p : PhysicalMomentum) :
    ‖momentumFirstJet j 0 (x,p)‖ ≤ sourceTargetBound j 0*(1+‖p‖) := by
  have nonnegative := sourceTargetBound_nonnegative j 0
  by_cases low : ‖p‖≤3
  · exact (momentumFirstJet_low_bound j 0 x p low).trans (by nlinarith [norm_nonneg p])
  · have scaled := momentumFirstJet_high_bound j 0 x p (lt_of_not_ge low)
    simp only [pow_zero,one_mul] at scaled
    exact scaled.trans (by nlinarith [norm_nonneg p])

theorem momentumFirstJet_order_one_bound (j : ℕ) (x p : PhysicalMomentum) :
    ‖momentumFirstJet j 1 (x,p)‖ ≤ sourceTargetBound j 1 := by
  by_cases low : ‖p‖≤3
  · exact momentumFirstJet_low_bound j 1 x p low
  · have positive : 0<‖p‖/2 := by linarith [norm_nonneg p]
    have scaled := momentumFirstJet_high_bound j 1 x p (lt_of_not_ge low)
    simp only [pow_one] at scaled
    exact (mul_le_mul_iff_right₀ positive).mp (by simpa only [mul_comm] using scaled)

theorem momentumFirstJet_order_two_bound (j : ℕ) (x p : PhysicalMomentum) :
    ‖momentumFirstJet j 2 (x,p)‖ ≤ 4*sourceTargetBound j 2/(1+‖p‖) := by
  have nonnegative := sourceTargetBound_nonnegative j 2
  have denominator : 0<1+‖p‖ := by linarith [norm_nonneg p]
  apply (le_div_iff₀ denominator).mpr
  by_cases low : ‖p‖≤3
  · have bound := momentumFirstJet_low_bound j 2 x p low
    nlinarith [norm_nonneg (momentumFirstJet j 2 (x,p))]
  · have high : 3<‖p‖ := lt_of_not_ge low
    have positive : 0<‖p‖/2 := by linarith
    have scaled := momentumFirstJet_high_bound j 2 x p high
    have reduced : (‖p‖/2)*‖momentumFirstJet j 2 (x,p)‖ ≤ sourceTargetBound j 2 :=
      (mul_le_mul_iff_right₀ positive).mp (by nlinarith [scaled])
    nlinarith [norm_nonneg (momentumFirstJet j 2 (x,p))]

theorem momentumFirstJet_order_succ_bound (j n : ℕ) (x p : PhysicalMomentum) :
    ‖momentumFirstJet j (n+1) (x,p)‖ ≤ 4^n*sourceTargetBound j (n+1)/(1+‖p‖)^n := by
  have nonnegative := sourceTargetBound_nonnegative j (n+1)
  have denominator : 0<(1+‖p‖)^n := by positivity
  apply (le_div_iff₀ denominator).mpr
  by_cases low : ‖p‖≤3
  · have power : (1+‖p‖)^n≤(4 : ℝ)^n :=
      pow_le_pow_left₀ (by positivity) (by linarith) n
    calc
      _ ≤ sourceTargetBound j (n+1)*(1+‖p‖)^n :=
        mul_le_mul_of_nonneg_right (momentumFirstJet_low_bound j (n+1) x p low) (by positivity)
      _ ≤ sourceTargetBound j (n+1)*4^n := mul_le_mul_of_nonneg_left power nonnegative
      _ = _ := mul_comm _ _
  · have high : 3<‖p‖ := lt_of_not_ge low
    have positive : 0<‖p‖/2 := by linarith
    have scaled := momentumFirstJet_high_bound j (n+1) x p high
    have reduced : (‖p‖/2)^n*‖momentumFirstJet j (n+1) (x,p)‖ ≤ sourceTargetBound j (n+1) := by
      apply (mul_le_mul_iff_right₀ positive).mp
      calc
        _ = (‖p‖/2)^(n+1)*‖momentumFirstJet j (n+1) (x,p)‖ := by
          rw [pow_succ]
          ac_rfl
        _ ≤ _ := scaled
    have power : (1+‖p‖)^n≤(4*(‖p‖/2))^n :=
      pow_le_pow_left₀ (by positivity) (by linarith) n
    calc
      _ ≤ ‖momentumFirstJet j (n+1) (x,p)‖*(4*(‖p‖/2))^n :=
        mul_le_mul_of_nonneg_left power (norm_nonneg (momentumFirstJet j (n+1) (x,p)))
      _ = 4^n*((‖p‖/2)^n*‖momentumFirstJet j (n+1) (x,p)‖) := by
        rw [mul_pow]
        ac_rfl
      _ ≤ _ := mul_le_mul_of_nonneg_left reduced (by positivity)

end LowEnergy.PreparationVacuumMomentumFirst
