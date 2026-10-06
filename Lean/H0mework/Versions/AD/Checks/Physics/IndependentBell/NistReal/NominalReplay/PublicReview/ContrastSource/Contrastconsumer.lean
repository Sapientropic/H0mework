import H0mework.Versions.AD.Checks.Physics.IndependentBell.NistReal.NominalReplay.PublicReview.ContrastSource.Contrastsource

/-! Same-source CH null laws generate the setting-corrected one-step test inequality. -/

set_option autoImplicit false

namespace P23.ObservableClosure.ContrastSource.Consumer

noncomputable section

def pLower (eps : ℝ) : ℝ := (1-eps)^2/4
def pUpper (eps : ℝ) : ℝ := (1+eps)^2/4
def qThreshold (eps : ℝ) : ℝ := pUpper eps/(pUpper eps+pLower eps)

theorem threshold_closed_form (eps : ℝ) :
    qThreshold eps=(1+eps)^2/(2*(1+eps^2)) := by
  have hs : pUpper eps+pLower eps=(1+eps^2)/2 := by dsimp [pUpper,pLower]; ring
  have hd : 0 < 1+eps^2 := by positivity
  rw [qThreshold,hs]
  dsimp [pUpper]
  field_simp [ne_of_gt hd]
  ring

structure Settings (eps : ℝ) where
  probabilities : Fin 4 → ℝ
  eps_nonneg : 0 ≤ eps
  eps_lt_one : eps < 1
  bounds : ∀ i, pLower eps ≤ probabilities i ∧ probabilities i ≤ pUpper eps
  normalized : probabilities 0+probabilities 1+probabilities 2+probabilities 3=1

theorem lower_pos {eps : ℝ} (h : eps < 1) : 0 < pLower eps := by
  dsimp [pLower]
  positivity

theorem upper_pos {eps : ℝ} (h : 0 ≤ eps) : 0 < pUpper eps := by
  dsimp [pUpper]
  positivity

theorem threshold_bounds {eps : ℝ} (settings : Settings eps) :
    0 < qThreshold eps ∧ qThreshold eps < 1 := by
  have hl := lower_pos settings.eps_lt_one
  have hu := upper_pos settings.eps_nonneg
  dsimp [qThreshold]
  exact ⟨div_pos hu (by linarith),(div_lt_one (by linarith)).2 (by linarith)⟩

def weightedWin {eps : ℝ} (settings : Settings eps) (q : ProbabilityLaw) : ℝ :=
  settings.probabilities 0*(q.cells 0).both

def weightedLoss {eps : ℝ} (settings : Settings eps) (q : ProbabilityLaw) : ℝ :=
  settings.probabilities 1*(q.cells 1).onlyA+
    settings.probabilities 2*(q.cells 2).onlyB+settings.probabilities 3*(q.cells 3).both

theorem null_win_le_loss (q : ProbabilityLaw) (hCH : CH q ≤ 0) : win q ≤ loss q := by
  rw [← contrast_CH_readback] at hCH
  linarith

theorem weighted_null_bound {eps : ℝ} (settings : Settings eps) (q : ProbabilityLaw)
    (hCH : CH q ≤ 0) : pLower eps*weightedWin settings q ≤ pUpper eps*weightedLoss settings q := by
  have hl := (lower_pos settings.eps_lt_one).le
  have hu := (upper_pos settings.eps_nonneg).le
  have hwin : weightedWin settings q ≤ pUpper eps*win q :=
    mul_le_mul_of_nonneg_right (settings.bounds 0).2 (q.positive 0).both
  have hloss : pLower eps*loss q ≤ weightedLoss settings q := by
    rw [loss_outcome_readback]
    have h1 := mul_le_mul_of_nonneg_right (settings.bounds 1).1 (q.positive 1).onlyA
    have h2 := mul_le_mul_of_nonneg_right (settings.bounds 2).1 (q.positive 2).onlyB
    have h3 := mul_le_mul_of_nonneg_right (settings.bounds 3).1 (q.positive 3).both
    dsimp [weightedLoss]
    nlinarith [h1,h2,h3]
  calc
    pLower eps*weightedWin settings q ≤ pLower eps*(pUpper eps*win q) :=
      mul_le_mul_of_nonneg_left hwin hl
    _ ≤ pLower eps*(pUpper eps*loss q) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (null_win_le_loss q hCH) hu) hl
    _ = pUpper eps*(pLower eps*loss q) := by ring
    _ ≤ pUpper eps*weightedLoss settings q := mul_le_mul_of_nonneg_left hloss hu

theorem weighted_ratio_bound {eps : ℝ} (settings : Settings eps) (q : ProbabilityLaw)
    (hCH : CH q ≤ 0) :
    weightedWin settings q ≤ (pUpper eps/pLower eps)*weightedLoss settings q := by
  have h := weighted_null_bound settings q hCH
  have hl := lower_pos settings.eps_lt_one
  have heq : (pUpper eps/pLower eps)*weightedLoss settings q=
      (pUpper eps*weightedLoss settings q)/pLower eps := by ring
  rw [heq]
  apply (le_div_iff₀ hl).2
  nlinarith

def cellExpectation (q : ProbabilityLaw) (i : Fin 4) (winFactor lossFactor : ℝ) : ℝ :=
  if i=0 then (q.cells i).both*winFactor+(q.cells i).onlyA+(q.cells i).onlyB+(q.cells i).neither
  else if i=1 then (q.cells i).both+(q.cells i).onlyA*lossFactor+(q.cells i).onlyB+(q.cells i).neither
  else if i=2 then (q.cells i).both+(q.cells i).onlyA+(q.cells i).onlyB*lossFactor+(q.cells i).neither
  else (q.cells i).both*lossFactor+(q.cells i).onlyA+(q.cells i).onlyB+(q.cells i).neither

def expectation {eps : ℝ} (settings : Settings eps) (q : ProbabilityLaw)
    (winFactor lossFactor : ℝ) : ℝ :=
  settings.probabilities 0*cellExpectation q 0 winFactor lossFactor+
    settings.probabilities 1*cellExpectation q 1 winFactor lossFactor+
    settings.probabilities 2*cellExpectation q 2 winFactor lossFactor+
    settings.probabilities 3*cellExpectation q 3 winFactor lossFactor

theorem expectation_readback {eps : ℝ} (settings : Settings eps) (q : ProbabilityLaw)
    (winFactor lossFactor : ℝ) :
    expectation settings q winFactor lossFactor=
      1+(winFactor-1)*weightedWin settings q+(lossFactor-1)*weightedLoss settings q := by
  dsimp [expectation,cellExpectation,weightedWin,weightedLoss]
  linear_combination settings.probabilities 0*q.normalized 0+
    settings.probabilities 1*q.normalized 1+settings.probabilities 2*q.normalized 2+
    settings.probabilities 3*q.normalized 3+settings.normalized

theorem cell_expectation_nonneg (q : ProbabilityLaw) (i : Fin 4)
    (winFactor lossFactor : ℝ) (hwin : 0 ≤ winFactor) (hloss : 0 ≤ lossFactor) :
    0 ≤ cellExpectation q i winFactor lossFactor := by
  have h := q.positive i
  rcases h with ⟨hb,ha,hb',hn⟩
  fin_cases i <;> norm_num [cellExpectation] <;> positivity

theorem expectation_nonneg {eps : ℝ} (settings : Settings eps) (q : ProbabilityLaw)
    (winFactor lossFactor : ℝ) (hwin : 0 ≤ winFactor) (hloss : 0 ≤ lossFactor) :
    0 ≤ expectation settings q winFactor lossFactor := by
  have hp : ∀ i, 0 ≤ settings.probabilities i :=
    fun i => (lower_pos settings.eps_lt_one).le.trans (settings.bounds i).1
  have hc := fun i => cell_expectation_nonneg q i winFactor lossFactor hwin hloss
  dsimp [expectation]
  exact add_nonneg (add_nonneg (add_nonneg (mul_nonneg (hp 0) (hc 0))
    (mul_nonneg (hp 1) (hc 1))) (mul_nonneg (hp 2) (hc 2)))
    (mul_nonneg (hp 3) (hc 3))

theorem weighted_threshold_gap {eps : ℝ} (settings : Settings eps) (q : ProbabilityLaw)
    (hCH : CH q ≤ 0) :
    (1-qThreshold eps)*weightedWin settings q-qThreshold eps*weightedLoss settings q ≤ 0 := by
  have h := weighted_null_bound settings q hCH
  have hl := lower_pos settings.eps_lt_one
  have hu := upper_pos settings.eps_nonneg
  have hs : 0 < pUpper eps+pLower eps := by linarith
  have heq : (1-qThreshold eps)*weightedWin settings q-qThreshold eps*weightedLoss settings q=
      (pLower eps*weightedWin settings q-pUpper eps*weightedLoss settings q)/
        (pUpper eps+pLower eps) := by
    dsimp [qThreshold]
    field_simp [ne_of_gt hs]
    ring
  rw [heq]
  exact div_nonpos_of_nonpos_of_nonneg (by linarith) hs.le

/-- The original fixed-relevant-count test consumes this source-generated success bound. -/
theorem relevant_success_bound {eps : ℝ} (settings : Settings eps) (q : ProbabilityLaw)
    (hCH : CH q ≤ 0) (hrelevant : 0 < weightedWin settings q+weightedLoss settings q) :
    weightedWin settings q/(weightedWin settings q+weightedLoss settings q) ≤
      qThreshold eps := by
  have h := weighted_threshold_gap settings q hCH
  apply (div_le_iff₀ hrelevant).2
  nlinarith

def oneStep {eps : ℝ} (settings : Settings eps) (q : ProbabilityLaw) (p : ℝ) : ℝ :=
  expectation settings q (p/qThreshold eps) ((1-p)/(1-qThreshold eps))

/-- Any constant source with nonpositive CH, including a quantum source, satisfies this step. -/
theorem nonpositive_CH_one_step {eps : ℝ} (settings : Settings eps) (q : ProbabilityLaw)
    (p : ℝ) (hp0 : qThreshold eps ≤ p) (hp1 : p ≤ 1) (hCH : CH q ≤ 0) :
    0 ≤ oneStep settings q p ∧ oneStep settings q p ≤ 1 := by
  have ht := threshold_bounds settings
  have h1 : 0 < 1-qThreshold eps := by linarith
  have hp : 0 ≤ p := ht.1.le.trans hp0
  have hg := weighted_threshold_gap settings q hCH
  have hcoef : 0 ≤ (p-qThreshold eps)/(qThreshold eps*(1-qThreshold eps)) :=
    div_nonneg (sub_nonneg.mpr hp0) (mul_pos ht.1 h1).le
  have heq : oneStep settings q p-1=
      ((p-qThreshold eps)/(qThreshold eps*(1-qThreshold eps)))*
        ((1-qThreshold eps)*weightedWin settings q-qThreshold eps*weightedLoss settings q) := by
    rw [oneStep,expectation_readback]
    field_simp [ne_of_gt ht.1,ne_of_gt h1]
    ring
  constructor
  · exact expectation_nonneg settings q _ _ (div_nonneg hp ht.1.le)
      (div_nonneg (by linarith) h1.le)
  · have hprod := mul_nonpos_of_nonneg_of_nonpos hcoef hg
    linarith

/-- The EF physical source internally pays all probability-law requirements before the statistic. -/
theorem source_nonpositive_CH_one_step (s : Snapshot) (N : ℕ) (bg : Background)
    (a0 a1 b0 b1 eps p : ℝ) (settings : Settings eps)
    (hp0 : qThreshold eps ≤ p) (hp1 : p ≤ 1)
    (hCH : nativeCH s N bg a0 a1 b0 b1 ≤ 0) :
    0 ≤ oneStep settings (sourceLaw s N bg a0 a1 b0 b1) p ∧
      oneStep settings (sourceLaw s N bg a0 a1 b0 b1) p ≤ 1 := by
  apply nonpositive_CH_one_step settings _ p hp0 hp1
  rwa [source_CH_readback]

/-- This local deterministic mouth does not replace the stronger source-CH null mouth. -/
theorem local_assignment_one_step {eps : ℝ} (settings : Settings eps)
    (assignment : Assignment) (p : ℝ) (hp0 : qThreshold eps ≤ p) (hp1 : p ≤ 1) :
    0 ≤ oneStep settings (assignmentLaw assignment) p ∧
      oneStep settings (assignmentLaw assignment) p ≤ 1 :=
  nonpositive_CH_one_step settings _ p hp0 hp1 (sixteen_assignments_CH_nonpositive assignment)

end
end P23.ObservableClosure.ContrastSource.Consumer
