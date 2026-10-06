import H0mework.Versions.AD.Checks.Physics.IndependentBell.NistReal.NominalReplay.ObservableClosure.FullStatisticalFiber.Phasefiber

/-! Actual local means recover one covariance chart over their complete error intervals. -/

set_option autoImplicit false

namespace P23.ObservableClosure.TrainingChart

open PhaseFiber

noncomputable section

def cosDouble (a : ℝ) : ℝ := Real.cos (2*a)
def sinDouble (a : ℝ) : ℝ := Real.sin (2*a)

def covarianceMean (s : Snapshot) (a : ℝ) : ℝ :=
  covarianceM s-covarianceZ s*cosDouble a-covarianceX s*sinDouble a

theorem native_mean_A_covariance (s : Snapshot) (a : ℝ) :
    meanA s a=covarianceMean s a := by
  have ht := Real.cos_two_mul' (a-s.delta)
  have hn := Real.sin_sq_add_cos_sq (a-s.delta)
  have ha : 2*(a-s.delta)=2*a-2*s.delta := by ring
  rw [ha,Real.cos_sub] at ht
  dsimp [meanA,covarianceMean,covarianceM,covarianceZ,covarianceX,covarianceC,
    cosDouble,sinDouble,h,v]
  linear_combination (s.etaA*(s.nH+s.nV)/2)*hn+(s.etaA*(s.nH-s.nV)/2)*ht

theorem ratio_mean_B (s : Snapshot) (b : ℝ) : ratio s*meanB s b=meanA s b := by
  dsimp [ratio,meanA,meanB]
  field_simp [ne_of_gt s.etaB_pos]

theorem native_mean_B_covariance (s : Snapshot) (b : ℝ) :
    meanB s b=covarianceMean s b/ratio s := by
  apply (eq_div_iff (ne_of_gt (ratio_pos s))).2
  rw [mul_comm,ratio_mean_B,native_mean_A_covariance]

theorem native_mirror_means (s : Snapshot) (a : ℝ) :
    meanA s a=covarianceM s-covarianceZ s*cosDouble a-covarianceX s*sinDouble a ∧
    ratio s*meanB s (-a)=covarianceM s-covarianceZ s*cosDouble a+
      covarianceX s*sinDouble a := by
  constructor
  · exact native_mean_A_covariance s a
  · rw [ratio_mean_B,native_mean_A_covariance]
    simp only [covarianceMean,cosDouble,sinDouble,mul_neg,Real.cos_neg,Real.sin_neg]
    ring

structure MeanSeed where
  alpha0 : ℝ
  alpha1 : ℝ
  beta0 : ℝ
  beta1 : ℝ

def actualSeed (s : Snapshot) (a0 a1 : ℝ) : MeanSeed where
  alpha0 := meanA s a0
  alpha1 := meanA s a1
  beta0 := meanB s (-a0)
  beta1 := meanB s (-a1)

def ratioDenominator (seed : MeanSeed) (a0 a1 : ℝ) : ℝ :=
  sinDouble a1*seed.beta0-sinDouble a0*seed.beta1

def recoveredRatio (seed : MeanSeed) (a0 a1 : ℝ) : ℝ :=
  (sinDouble a1*seed.alpha0-sinDouble a0*seed.alpha1)/ratioDenominator seed a0 a1

def recoveredU0 (seed : MeanSeed) (a0 a1 : ℝ) : ℝ :=
  (seed.alpha0+recoveredRatio seed a0 a1*seed.beta0)/2

def recoveredU1 (seed : MeanSeed) (a0 a1 : ℝ) : ℝ :=
  (seed.alpha1+recoveredRatio seed a0 a1*seed.beta1)/2

def recoveredZ (seed : MeanSeed) (a0 a1 : ℝ) : ℝ :=
  (recoveredU1 seed a0 a1-recoveredU0 seed a0 a1)/(cosDouble a0-cosDouble a1)

def recoveredM (seed : MeanSeed) (a0 a1 : ℝ) : ℝ :=
  recoveredU0 seed a0 a1+recoveredZ seed a0 a1*cosDouble a0

def recoveredX (seed : MeanSeed) (a0 a1 : ℝ) : ℝ :=
  -(seed.alpha0-recoveredRatio seed a0 a1*seed.beta0)/(2*sinDouble a0)

theorem ratio_denominator_negative (seed : MeanSeed) (a0 a1 : ℝ)
    (hs0 : 0 < sinDouble a0) (hs1 : sinDouble a1 < 0)
    (hb0 : 0 < seed.beta0) (hb1 : 0 < seed.beta1) :
    ratioDenominator seed a0 a1 < 0 := by
  have hm0 := mul_neg_of_neg_of_pos hs1 hb0
  have hm1 := mul_pos hs0 hb1
  dsimp [ratioDenominator]
  linarith

theorem source_ratio_relation (s : Snapshot) (a0 a1 : ℝ) :
    sinDouble a1*(actualSeed s a0 a1).alpha0-
      sinDouble a0*(actualSeed s a0 a1).alpha1=
    ratio s*ratioDenominator (actualSeed s a0 a1) a0 a1 := by
  have h0 := native_mirror_means s a0
  have h1 := native_mirror_means s a1
  dsimp [actualSeed,ratioDenominator]
  linear_combination sinDouble a1*h0.1-sinDouble a0*h1.1-
    sinDouble a1*h0.2+sinDouble a0*h1.2

theorem recovered_ratio_readback (s : Snapshot) (a0 a1 : ℝ)
    (hs0 : 0 < sinDouble a0) (hs1 : sinDouble a1 < 0)
    (hb0 : 0 < meanB s (-a0)) (hb1 : 0 < meanB s (-a1)) :
    recoveredRatio (actualSeed s a0 a1) a0 a1=ratio s := by
  have hd := ratio_denominator_negative (actualSeed s a0 a1) a0 a1 hs0 hs1 hb0 hb1
  apply (div_eq_iff (ne_of_lt hd)).2
  exact source_ratio_relation s a0 a1

theorem recovered_U_readback (s : Snapshot) (a0 a1 : ℝ)
    (hr : recoveredRatio (actualSeed s a0 a1) a0 a1=ratio s) :
    recoveredU0 (actualSeed s a0 a1) a0 a1=
      covarianceM s-covarianceZ s*cosDouble a0 ∧
    recoveredU1 (actualSeed s a0 a1) a0 a1=
      covarianceM s-covarianceZ s*cosDouble a1 := by
  have h0 := native_mirror_means s a0
  have h1 := native_mirror_means s a1
  dsimp only [recoveredU0,recoveredU1]
  rw [hr]
  dsimp only [actualSeed]
  constructor <;> nlinarith [h0.1,h0.2,h1.1,h1.2]

structure ChartReadback (s : Snapshot) (a0 a1 : ℝ) : Prop where
  ratio_eq : recoveredRatio (actualSeed s a0 a1) a0 a1=ratio s
  z_eq : recoveredZ (actualSeed s a0 a1) a0 a1=covarianceZ s
  m_eq : recoveredM (actualSeed s a0 a1) a0 a1=covarianceM s
  x_eq : recoveredX (actualSeed s a0 a1) a0 a1=covarianceX s

/-- Four actual means recover the source coordinates without supplied coordinate endpoints. -/
theorem actual_means_recover_chart (s : Snapshot) (a0 a1 : ℝ)
    (hs0 : 0 < sinDouble a0) (hs1 : sinDouble a1 < 0)
    (hb0 : 0 < meanB s (-a0)) (hb1 : 0 < meanB s (-a1))
    (hc : cosDouble a1 < cosDouble a0) : ChartReadback s a0 a1 := by
  have hr := recovered_ratio_readback s a0 a1 hs0 hs1 hb0 hb1
  have hu := recovered_U_readback s a0 a1 hr
  have hcd : cosDouble a0-cosDouble a1 ≠ 0 := ne_of_gt (sub_pos.mpr hc)
  have hz : recoveredZ (actualSeed s a0 a1) a0 a1=covarianceZ s := by
    dsimp only [recoveredZ]
    rw [hu.1,hu.2]
    apply (div_eq_iff hcd).2
    ring
  have hm : recoveredM (actualSeed s a0 a1) a0 a1=covarianceM s := by
    dsimp only [recoveredM]
    rw [hu.1,hz]
    ring
  have hx : recoveredX (actualSeed s a0 a1) a0 a1=covarianceX s := by
    dsimp only [recoveredX]
    rw [hr]
    have h0 := native_mirror_means s a0
    apply (div_eq_iff (mul_ne_zero (by norm_num) (ne_of_gt hs0))).2
    dsimp only [actualSeed]
    linear_combination -h0.1+h0.2
  exact ⟨hr,hz,hm,hx⟩

theorem both_mean_increases_force_z (s : Snapshot) (a0 a1 : ℝ)
    (hA : meanA s a0 < meanA s a1) (hB : meanB s (-a0) < meanB s (-a1))
    (hc : cosDouble a1 < cosDouble a0) : 0 < covarianceZ s := by
  have h0 := native_mirror_means s a0
  have h1 := native_mirror_means s a1
  have hsum : (meanA s a1-meanA s a0)+ratio s*(meanB s (-a1)-meanB s (-a0))=
      2*covarianceZ s*(cosDouble a0-cosDouble a1) := by
    linear_combination h1.1-h0.1+h1.2-h0.2
  have hprod := mul_pos (ratio_pos s) (sub_pos.mpr hB)
  have hzprod : 0 < 2*covarianceZ s*(cosDouble a0-cosDouble a1) := by
    linarith
  by_contra hz
  have hz0 : covarianceZ s ≤ 0 := le_of_not_gt hz
  have hn := mul_nonpos_of_nonpos_of_nonneg (by nlinarith : 2*covarianceZ s ≤ 0)
    (sub_pos.mpr hc).le
  linarith

theorem both_mean_increases_force_radius (s : Snapshot) (a0 a1 : ℝ)
    (hA : meanA s a0 < meanA s a1) (hB : meanB s (-a0) < meanB s (-a1))
    (hc : cosDouble a1 < cosDouble a0) : 0 < covarianceR2 s := by
  have hz := both_mean_increases_force_z s a0 a1 hA hB hc
  dsimp [covarianceR2]
  nlinarith [sq_pos_of_pos hz,sq_nonneg (covarianceX s)]

structure MeanIntervals where
  alpha0lo : ℝ
  alpha0hi : ℝ
  alpha1lo : ℝ
  alpha1hi : ℝ
  beta0lo : ℝ
  beta0hi : ℝ
  beta1lo : ℝ
  beta1hi : ℝ

structure SingleMembership (s : Snapshot) (a0 a1 : ℝ) (bounds : MeanIntervals) : Prop where
  alpha0 : bounds.alpha0lo ≤ meanA s a0 ∧ meanA s a0 ≤ bounds.alpha0hi
  alpha1 : bounds.alpha1lo ≤ meanA s a1 ∧ meanA s a1 ≤ bounds.alpha1hi
  beta0 : bounds.beta0lo ≤ meanB s (-a0) ∧ meanB s (-a0) ≤ bounds.beta0hi
  beta1 : bounds.beta1lo ≤ meanB s (-a1) ∧ meanB s (-a1) ≤ bounds.beta1hi

def mirrorCovarianceMean (s : Snapshot) (a : ℝ) : ℝ :=
  covarianceM s-covarianceZ s*cosDouble a+covarianceX s*sinDouble a

structure SourcePolytope (s : Snapshot) (a0 a1 : ℝ) (bounds : MeanIntervals) : Prop where
  alpha0 : bounds.alpha0lo ≤ covarianceMean s a0 ∧ covarianceMean s a0 ≤ bounds.alpha0hi
  alpha1 : bounds.alpha1lo ≤ covarianceMean s a1 ∧ covarianceMean s a1 ≤ bounds.alpha1hi
  beta0 : bounds.beta0lo*ratio s ≤ mirrorCovarianceMean s a0 ∧
    mirrorCovarianceMean s a0 ≤ bounds.beta0hi*ratio s
  beta1 : bounds.beta1lo*ratio s ≤ mirrorCovarianceMean s a1 ∧
    mirrorCovarianceMean s a1 ≤ bounds.beta1hi*ratio s

theorem mirror_beta_interval_iff (s : Snapshot) (a lo hi : ℝ) :
    (lo ≤ meanB s (-a) ∧ meanB s (-a) ≤ hi) ↔
    (lo*ratio s ≤ mirrorCovarianceMean s a ∧ mirrorCovarianceMean s a ≤ hi*ratio s) := by
  have hm := (native_mirror_means s a).2
  have hr := ratio_pos s
  have hb : meanB s (-a)=mirrorCovarianceMean s a/ratio s := by
    apply (eq_div_iff (ne_of_gt hr)).2
    simpa [mirrorCovarianceMean,mul_comm] using hm
  rw [hb,le_div_iff₀ hr,div_le_iff₀ hr]

/-- Membership of all four local mean intervals equals the complete linear source polytope. -/
theorem single_membership_iff_polytope (s : Snapshot) (a0 a1 : ℝ) (bounds : MeanIntervals) :
    SingleMembership s a0 a1 bounds ↔ SourcePolytope s a0 a1 bounds := by
  constructor
  · intro hs
    exact ⟨by simpa [native_mean_A_covariance] using hs.alpha0,
      by simpa [native_mean_A_covariance] using hs.alpha1,
      (mirror_beta_interval_iff s a0 _ _).1 hs.beta0,
      (mirror_beta_interval_iff s a1 _ _).1 hs.beta1⟩
  · intro hp
    exact ⟨by simpa [native_mean_A_covariance] using hp.alpha0,
      by simpa [native_mean_A_covariance] using hp.alpha1,
      (mirror_beta_interval_iff s a0 _ _).2 hp.beta0,
      (mirror_beta_interval_iff s a1 _ _).2 hp.beta1⟩

structure PhysicalCovariance (s : Snapshot) : Prop where
  m_nonneg : 0 ≤ covarianceM s
  r2_nonneg : 0 ≤ covarianceR2 s
  psd : covarianceR2 s ≤ covarianceM s^2
  ratio_pos : 0 < ratio s
  loss_pos : 0 < e s
  loss_le_one : e s ≤ 1
  loss_le_ratio : e s ≤ ratio s
  native_T2 : T2 s (e s)=(covarianceM s^2-covarianceR2 s)*
    ((covarianceM s+e s)^2-covarianceR2 s)

theorem source_physical_covariance (s : Snapshot) : PhysicalCovariance s := by
  have hh : 0 ≤ h s := mul_nonneg s.etaA_pos.le s.nH_nonneg
  have hv : 0 ≤ v s := mul_nonneg s.etaA_pos.le s.nV_nonneg
  have hs := snapshot_scaled_readback s
  refine ⟨?_,?_,?_,ratio_pos s,hs.2.2.2.1,hs.2.2.2.2.1,hs.2.2.2.2.2.1,
    covariance_T2 s⟩
  · dsimp [covarianceM]
    linarith
  · dsimp [covarianceR2]
    positivity
  · rw [covariance_radius]
    dsimp [covarianceC,covarianceM]
    nlinarith [mul_nonneg hh hv]

theorem training_intervals_exclude_equal_modes (s : Snapshot) (a0 a1 : ℝ)
    (bounds : MeanIntervals) (hs : SingleMembership s a0 a1 bounds)
    (hA : bounds.alpha0hi < bounds.alpha1lo) (hB : bounds.beta0hi < bounds.beta1lo)
    (hc : cosDouble a1 < cosDouble a0) :
    0 < covarianceZ s ∧ 0 < covarianceR2 s := by
  have hAi : meanA s a0 < meanA s a1 := lt_of_le_of_lt hs.alpha0.2
    (lt_of_lt_of_le hA hs.alpha1.1)
  have hBi : meanB s (-a0) < meanB s (-a1) := lt_of_le_of_lt hs.beta0.2
    (lt_of_lt_of_le hB hs.beta1.1)
  exact ⟨both_mean_increases_force_z s a0 a1 hAi hBi hc,
    both_mean_increases_force_radius s a0 a1 hAi hBi hc⟩

/-- Every member of the complete four-single intervals has the same inverse chart. -/
theorem interval_members_recover_chart (s : Snapshot) (a0 a1 : ℝ)
    (bounds : MeanIntervals) (hm : SingleMembership s a0 a1 bounds)
    (hs0 : 0 < sinDouble a0) (hs1 : sinDouble a1 < 0)
    (hb0 : 0 < bounds.beta0lo) (hb1 : 0 < bounds.beta1lo)
    (hc : cosDouble a1 < cosDouble a0) : ChartReadback s a0 a1 :=
  actual_means_recover_chart s a0 a1 hs0 hs1
    (lt_of_lt_of_le hb0 hm.beta0.1) (lt_of_lt_of_le hb1 hm.beta1.1) hc

end
end P23.ObservableClosure.TrainingChart
