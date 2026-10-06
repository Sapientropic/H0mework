import H0mework.Versions.AD.Checks.Physics.IndependentBell.NistReal.NominalReplay.PublicReview.ContrastSource.Contrastconsumer

/-! The same source law generates the exact nuisance-setting support and full-trial bet. -/

set_option autoImplicit false

namespace P23.ObservableClosure.SourceCompression

open P23.ObservableClosure.ContrastSource
open P23.ObservableClosure.ContrastSource.Consumer

noncomputable section

def loss01 (q : ProbabilityLaw) : ℝ := (q.cells 1).onlyA
def loss10 (q : ProbabilityLaw) : ℝ := (q.cells 2).onlyB
def loss11 (q : ProbabilityLaw) : ℝ := (q.cells 3).both
def minimumLoss (q : ProbabilityLaw) : ℝ := min (loss01 q) (min (loss10 q) (loss11 q))
def settingExcess (eps : ℝ) : ℝ := eps*(1-eps)
def settingRatio (eps : ℝ) : ℝ := pLower eps/pUpper eps
def support (eps : ℝ) (q : ProbabilityLaw) : ℝ :=
  pLower eps*CH q-settingExcess eps*minimumLoss q
def drift {eps : ℝ} (settings : Settings eps) (q : ProbabilityLaw) : ℝ :=
  settingRatio eps*weightedWin settings q-weightedLoss settings q

theorem CH_loss_readback (q : ProbabilityLaw) :
    CH q=win q-(loss01 q+loss10 q+loss11 q) := by
  rw [← contrast_CH_readback,loss_outcome_readback]
  rfl

theorem losses_nonnegative (q : ProbabilityLaw) :
    0 ≤ loss01 q ∧ 0 ≤ loss10 q ∧ 0 ≤ loss11 q :=
  ⟨(q.positive 1).onlyA,(q.positive 2).onlyB,(q.positive 3).both⟩

theorem minimum_loss_bounds (q : ProbabilityLaw) :
    0 ≤ minimumLoss q ∧ minimumLoss q ≤ loss01 q ∧
      minimumLoss q ≤ loss10 q ∧ minimumLoss q ≤ loss11 q := by
  have h := losses_nonnegative q
  exact ⟨le_min h.1 (le_min h.2.1 h.2.2),min_le_left _ _,
    (min_le_right _ _).trans (min_le_left _ _),
    (min_le_right _ _).trans (min_le_right _ _)⟩

theorem minimum_loss_choice (q : ProbabilityLaw) :
    minimumLoss q=loss01 q ∨ minimumLoss q=loss10 q ∨ minimumLoss q=loss11 q := by
  by_cases h01 : loss01 q ≤ min (loss10 q) (loss11 q)
  · exact Or.inl (min_eq_left h01)
  · have hr : minimumLoss q=min (loss10 q) (loss11 q) := min_eq_right (le_of_not_ge h01)
    by_cases h10 : loss10 q ≤ loss11 q
    · exact Or.inr (Or.inl (hr.trans (min_eq_left h10)))
    · exact Or.inr (Or.inr (hr.trans (min_eq_right (le_of_not_ge h10))))

theorem setting_geometry {eps : ℝ} (h0 : 0 ≤ eps) (h1 : eps < 1) :
    0 ≤ settingExcess eps ∧ pLower eps ≤ pUpper eps ∧
      pLower eps+settingExcess eps ≤ pUpper eps ∧
      1-pUpper eps-3*pLower eps=settingExcess eps := by
  dsimp [settingExcess,pLower,pUpper]
  constructor
  · positivity
  constructor
  · nlinarith
  constructor
  · nlinarith [sq_nonneg eps]
  · ring

theorem ratio_mul_upper {eps : ℝ} (h0 : 0 ≤ eps) :
    settingRatio eps*pUpper eps=pLower eps := by
  dsimp [settingRatio]
  exact div_mul_cancel₀ _ (ne_of_gt (upper_pos h0))

/-- No empirical setting estimate is needed: all normalized settings in the original box obey this. -/
theorem drift_le_support {eps : ℝ} (settings : Settings eps) (q : ProbabilityLaw) :
    drift settings q ≤ support eps q := by
  have geo := setting_geometry settings.eps_nonneg settings.eps_lt_one
  have hm := minimum_loss_bounds q
  have hl := (lower_pos settings.eps_lt_one).le
  have hr : 0 ≤ settingRatio eps := div_nonneg hl (upper_pos settings.eps_nonneg).le
  have hw : weightedWin settings q ≤ pUpper eps*win q :=
    mul_le_mul_of_nonneg_right (settings.bounds 0).2 (q.positive 0).both
  have hw' := mul_le_mul_of_nonneg_left hw hr
  rw [← mul_assoc,ratio_mul_upper settings.eps_nonneg] at hw'
  have h01 := mul_le_mul_of_nonneg_left hm.2.1 (sub_nonneg.mpr (settings.bounds 1).1)
  have h10 := mul_le_mul_of_nonneg_left hm.2.2.1 (sub_nonneg.mpr (settings.bounds 2).1)
  have h11 := mul_le_mul_of_nonneg_left hm.2.2.2 (sub_nonneg.mpr (settings.bounds 3).1)
  have he : settingExcess eps ≤ 1-settings.probabilities 0-3*pLower eps := by
    rw [← geo.2.2.2]
    linarith [(settings.bounds 0).2]
  have he' := mul_le_mul_of_nonneg_right he hm.1
  have hn := settings.normalized
  have hnm := congrArg (fun x : ℝ => x*minimumLoss q) hn
  have hc := CH_loss_readback q
  dsimp [weightedLoss,loss01,loss10,loss11] at *
  dsimp [drift,support,weightedLoss]
  rw [hc]
  nlinarith

def corner (eps : ℝ) (h0 : 0 ≤ eps) (h1 : eps < 1) (picked : Fin 3) : Settings eps where
  probabilities := fun i => if i=0 then pUpper eps else
    pLower eps+(if i.val=picked.val+1 then settingExcess eps else 0)
  eps_nonneg := h0
  eps_lt_one := h1
  bounds := by
    intro i
    have geo := setting_geometry h0 h1
    fin_cases picked <;> fin_cases i <;> norm_num [Fin.ext_iff] <;> aesop
  normalized := by
    fin_cases picked <;> norm_num [Fin.ext_iff,pLower,pUpper,settingExcess] <;> ring

theorem corner_drift {eps : ℝ} (h0 : 0 ≤ eps) (h1 : eps < 1)
    (q : ProbabilityLaw) (picked : Fin 3) :
    drift (corner eps h0 h1 picked) q=
      pLower eps*CH q-settingExcess eps*
        (if picked=0 then loss01 q else if picked=1 then loss10 q else loss11 q) := by
  have hc := CH_loss_readback q
  have hu := ne_of_gt (upper_pos h0)
  dsimp only [drift,weightedWin,weightedLoss,corner]
  fin_cases picked <;>
    norm_num [Fin.ext_iff] <;>
    rw [hc] <;> dsimp only [settingRatio,loss01,loss10,loss11,win] <;>
    field_simp [hu] <;> ring

/-- A legal original setting vertex realizes the bound; this is the exact support, not a loose hull. -/
theorem support_attained {eps : ℝ} (h0 : 0 ≤ eps) (h1 : eps < 1)
    (q : ProbabilityLaw) : ∃ settings : Settings eps, drift settings q=support eps q := by
  rcases minimum_loss_choice q with h|h|h
  · refine ⟨corner eps h0 h1 0,?_⟩
    rw [corner_drift]
    simp [support,h]
  · refine ⟨corner eps h0 h1 1,?_⟩
    rw [corner_drift]
    simp [support,h]
  · refine ⟨corner eps h0 h1 2,?_⟩
    rw [corner_drift]
    simp [support,h]

theorem nonpositive_CH_support {eps : ℝ} (h0 : 0 ≤ eps) (h1 : eps < 1)
    (q : ProbabilityLaw) (hCH : CH q ≤ 0) : support eps q ≤ 0 := by
  have hl := (lower_pos h1).le
  have he := (setting_geometry h0 h1).1
  have hm := (minimum_loss_bounds q).1
  exact sub_nonpos.mpr ((mul_nonpos_of_nonneg_of_nonpos hl hCH).trans (mul_nonneg he hm))

theorem weighted_loss_le_one {eps : ℝ} (settings : Settings eps) (q : ProbabilityLaw) :
    weightedLoss settings q ≤ 1 := by
  have h01 : loss01 q ≤ 1 := by
    have h := q.positive 1
    have hn := q.normalized 1
    dsimp [loss01]
    linarith [h.both,h.onlyB,h.neither]
  have h10 : loss10 q ≤ 1 := by
    have h := q.positive 2
    have hn := q.normalized 2
    dsimp [loss10]
    linarith [h.both,h.onlyA,h.neither]
  have h11 : loss11 q ≤ 1 := by
    have h := q.positive 3
    have hn := q.normalized 3
    dsimp [loss11]
    linarith [h.onlyA,h.onlyB,h.neither]
  have hp : ∀ i, 0 ≤ settings.probabilities i :=
    fun i => (lower_pos settings.eps_lt_one).le.trans (settings.bounds i).1
  have a := mul_le_mul_of_nonneg_left h01 (hp 1)
  have b := mul_le_mul_of_nonneg_left h10 (hp 2)
  have c := mul_le_mul_of_nonneg_left h11 (hp 3)
  have hn := settings.normalized
  dsimp [loss01,loss10,loss11,weightedLoss] at *
  nlinarith [hp 0]

theorem support_lower_bound {eps : ℝ} (h0 : 0 ≤ eps) (h1 : eps < 1)
    (q : ProbabilityLaw) : -1 ≤ support eps q := by
  rcases support_attained h0 h1 q with ⟨settings,hs⟩
  have hr : 0 ≤ settingRatio eps := div_nonneg (lower_pos h1).le (upper_pos h0).le
  have hw : 0 ≤ weightedWin settings q :=
    mul_nonneg ((lower_pos h1).le.trans (settings.bounds 0).1) (q.positive 0).both
  have hp := mul_nonneg hr hw
  have hl := weighted_loss_le_one settings q
  rw [← hs]
  dsimp [drift]
  linarith

def winFactor (eps t : ℝ) : ℝ := 1+settingRatio eps*t
def lossFactor (t : ℝ) : ℝ := 1-t
def normalizer (eps : ℝ) (q : ProbabilityLaw) (t : ℝ) : ℝ := 1+t*support eps q

theorem factor_expectation {eps : ℝ} (settings : Settings eps) (q : ProbabilityLaw) (t : ℝ) :
    expectation settings q (winFactor eps t) (lossFactor t)=1+t*drift settings q := by
  rw [expectation_readback]
  dsimp [winFactor,lossFactor,drift]
  ring

theorem normalizer_positive {eps : ℝ} (h0 : 0 ≤ eps) (h1 : eps < 1)
    (q : ProbabilityLaw) (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t < 1) :
    0 < normalizer eps q t := by
  have hm := mul_le_mul_of_nonneg_left (support_lower_bound h0 h1 q) ht0
  dsimp [normalizer]
  nlinarith

/-- Every outcome, including the twelve neutral outcomes, is divided by this same normalizer. -/
theorem normalized_one_step {eps : ℝ} (settings : Settings eps) (q : ProbabilityLaw)
    (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t < 1) :
    0 ≤ expectation settings q (winFactor eps t) (lossFactor t)/normalizer eps q t ∧
      expectation settings q (winFactor eps t) (lossFactor t)/normalizer eps q t ≤ 1 := by
  have hd := normalizer_positive settings.eps_nonneg settings.eps_lt_one q t ht0 ht1
  have hr : 0 ≤ settingRatio eps :=
    div_nonneg (lower_pos settings.eps_lt_one).le (upper_pos settings.eps_nonneg).le
  have ha : 0 ≤ winFactor eps t := by dsimp [winFactor]; positivity
  have hb : 0 ≤ lossFactor t := by dsimp [lossFactor]; linarith
  have hn := expectation_nonneg settings q _ _ ha hb
  have he := mul_le_mul_of_nonneg_left (drift_le_support settings q) ht0
  constructor
  · exact div_nonneg hn hd.le
  · apply (div_le_one hd).2
    rw [factor_expectation]
    dsimp [normalizer]
    linarith

def fixedScale (k : ℕ) : ℝ := 1/(2:ℝ)^(k+1)
def originalFixedP (eps : ℝ) (k : ℕ) : ℝ :=
  qThreshold eps+(1-qThreshold eps)*fixedScale k

theorem fixed_scale_bounds (k : ℕ) : 0 < fixedScale k ∧ fixedScale k < 1 := by
  have hp : (1:ℝ) ≤ 2^k := one_le_pow₀ (by norm_num)
  have hpos : (0:ℝ) < 2^k := by positivity
  dsimp [fixedScale]
  rw [pow_succ]
  constructor
  · positivity
  · apply (div_lt_one (by positivity)).2
    nlinarith

theorem original_fixed_factors {eps : ℝ} (settings : Settings eps) (k : ℕ) :
    originalFixedP eps k/qThreshold eps=winFactor eps (fixedScale k) ∧
      (1-originalFixedP eps k)/(1-qThreshold eps)=lossFactor (fixedScale k) := by
  have hl := ne_of_gt (lower_pos settings.eps_lt_one)
  have hu := ne_of_gt (upper_pos settings.eps_nonneg)
  have hs : pUpper eps+pLower eps ≠ 0 :=
    ne_of_gt (add_pos (upper_pos settings.eps_nonneg) (lower_pos settings.eps_lt_one))
  dsimp [originalFixedP,winFactor,lossFactor,settingRatio,qThreshold]
  constructor <;> field_simp [hl,hu,hs] <;> ring

theorem source_normalized_fixed_bet (s : P23.ObservableClosure.Snapshot)
    (N : ℕ) (bg : Background) (a0 a1 b0 b1 eps : ℝ)
    (settings : Settings eps) (k : ℕ) :
    let q := sourceLaw s N bg a0 a1 b0 b1
    0 < normalizer eps q (fixedScale k) ∧
      0 ≤ expectation settings q (winFactor eps (fixedScale k)) (lossFactor (fixedScale k))/
        normalizer eps q (fixedScale k) ∧
      expectation settings q (winFactor eps (fixedScale k)) (lossFactor (fixedScale k))/
        normalizer eps q (fixedScale k) ≤ 1 := by
  dsimp only
  have ht := fixed_scale_bounds k
  exact ⟨normalizer_positive settings.eps_nonneg settings.eps_lt_one _ _ ht.1.le ht.2,
    normalized_one_step settings _ _ ht.1.le ht.2⟩

def conditionalFeature (q : ProbabilityLaw) (i : Fin 4) (feature : Fin 6) : ℝ :=
  if feature=0 then (q.cells i).both else if feature=1 then (q.cells i).onlyA
  else if feature=2 then (q.cells i).onlyB else if feature=3 then (q.cells i).neither
  else if feature=4 then (q.cells i).both+(q.cells i).onlyA
  else (q.cells i).both+(q.cells i).onlyB

theorem conditional_feature_bounds (q : ProbabilityLaw) (i : Fin 4) (feature : Fin 6) :
    0 ≤ conditionalFeature q i feature ∧ conditionalFeature q i feature ≤ 1 := by
  have hp := q.positive i
  have hn := q.normalized i
  fin_cases feature <;> norm_num [conditionalFeature,Fin.ext_iff] <;>
    constructor <;> linarith [hp.both,hp.onlyA,hp.onlyB,hp.neither]

def conditionalPoissonStep (q : ProbabilityLaw) (i : Fin 4) (feature : Fin 6)
    (lambda : ℝ) : ℝ :=
  (1+conditionalFeature q i feature*(Real.exp lambda-1))/
    Real.exp (conditionalFeature q i feature*(Real.exp lambda-1))

/-- The probability is the source's current-setting conditional law, supplied before selection. -/
theorem conditional_poisson_one_step (q : ProbabilityLaw) (i : Fin 4)
    (feature : Fin 6) (lambda : ℝ) :
    0 ≤ conditionalPoissonStep q i feature lambda ∧
      conditionalPoissonStep q i feature lambda ≤ 1 := by
  have hp := conditional_feature_bounds q i feature
  have he := Real.exp_pos lambda
  have hn : 0 ≤ 1+conditionalFeature q i feature*(Real.exp lambda-1) := by
    nlinarith [mul_nonneg hp.1 he.le]
  have hd := Real.exp_pos (conditionalFeature q i feature*(Real.exp lambda-1))
  constructor
  · exact div_nonneg hn hd.le
  · apply (div_le_one hd).2
    simpa [add_comm] using Real.add_one_le_exp
      (conditionalFeature q i feature*(Real.exp lambda-1))

def selectedSettingStep {eps : ℝ} (settings : Settings eps) (q : ProbabilityLaw)
    (i : Fin 4) (feature : Fin 6) (lambda : ℝ) : ℝ :=
  1-settings.probabilities i+
    settings.probabilities i*conditionalPoissonStep q i feature lambda

theorem selected_setting_one_step {eps : ℝ} (settings : Settings eps)
    (q : ProbabilityLaw) (i : Fin 4) (feature : Fin 6) (lambda : ℝ) :
    0 ≤ selectedSettingStep settings q i feature lambda ∧
      selectedSettingStep settings q i feature lambda ≤ 1 := by
  have hp : ∀ j, 0 ≤ settings.probabilities j :=
    fun j => (lower_pos settings.eps_lt_one).le.trans (settings.bounds j).1
  have hi : settings.probabilities i ≤ 1 := by
    have hu : pUpper eps ≤ 1 := by
      dsimp [pUpper]
      nlinarith [settings.eps_nonneg,settings.eps_lt_one,
        mul_nonneg settings.eps_nonneg (sub_nonneg.mpr settings.eps_lt_one.le)]
    exact (settings.bounds i).2.trans hu
  have hc := conditional_poisson_one_step q i feature lambda
  have hm0 := mul_nonneg (hp i) hc.1
  have hm1 := mul_le_mul_of_nonneg_left hc.2 (hp i)
  dsimp [selectedSettingStep]
  constructor <;> linarith

theorem source_selected_setting_one_step (s : P23.ObservableClosure.Snapshot)
    (N : ℕ) (bg : Background) (a0 a1 b0 b1 eps : ℝ)
    (settings : Settings eps) (i : Fin 4) (feature : Fin 6) (lambda : ℝ) :
    0 ≤ selectedSettingStep settings (sourceLaw s N bg a0 a1 b0 b1) i feature lambda ∧
      selectedSettingStep settings (sourceLaw s N bg a0 a1 b0 b1) i feature lambda ≤ 1 :=
  selected_setting_one_step settings _ i feature lambda

end
end P23.ObservableClosure.SourceCompression
