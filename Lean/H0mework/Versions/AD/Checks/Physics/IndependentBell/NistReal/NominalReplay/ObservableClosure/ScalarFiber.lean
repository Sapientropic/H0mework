import H0mework.Versions.AD.Checks.Physics.IndependentBell.NistReal.NominalReplay.ObservableClosure.Observableclosure

set_option autoImplicit false

namespace P23.ObservableClosure.ScalarFiber

noncomputable section

structure ScaledSource where
  h : ℝ
  v : ℝ
  r : ℝ
  delta : ℝ
  v_pos : 0 < v
  v_lt_h : v < h
  r_pos : 0 < r

theorem ScaledSource.h_pos (s : ScaledSource) : 0 < s.h := lt_trans s.v_pos s.v_lt_h

structure LegalLoss (s : ScaledSource) (loss : ℝ) : Prop where
  positive : 0 < loss
  le_one : loss ≤ 1
  le_ratio : loss ≤ s.r

def lossSnapshot (s : ScaledSource) (loss : ℝ) (hl : LegalLoss s loss)
    (lam : ℝ) (h0 : 0 ≤ lam) (h1 : lam ≤ 1) : Snapshot where
  nH := s.h/loss
  nV := s.v/loss
  etaA := loss
  etaB := loss/s.r
  delta := s.delta
  lam := lam
  nH_nonneg := (div_pos s.h_pos hl.positive).le
  nV_nonneg := (div_pos s.v_pos hl.positive).le
  nV_le_nH := div_le_div_of_nonneg_right s.v_lt_h.le hl.positive.le
  etaA_pos := hl.positive
  etaA_le_one := hl.le_one
  etaB_pos := div_pos hl.positive s.r_pos
  etaB_le_one := (div_le_one s.r_pos).2 hl.le_ratio
  lam_nonneg := h0
  lam_le_one := h1

def baseline (s : ScaledSource) (loss : ℝ) (hl : LegalLoss s loss) : Snapshot :=
  lossSnapshot s loss hl 0 (by norm_num) (by norm_num)

theorem lossSnapshot_scaled (s : ScaledSource) (loss : ℝ) (hl : LegalLoss s loss)
    (lam : ℝ) (h0 : 0 ≤ lam) (h1 : lam ≤ 1) :
    let snap := lossSnapshot s loss hl lam h0 h1
    h snap=s.h ∧ v snap=s.v ∧ ratio snap=s.r ∧ e snap=loss := by
  dsimp [lossSnapshot,h,v,ratio,e]
  constructor
  · field_simp [ne_of_gt hl.positive]
  constructor
  · field_simp [ne_of_gt hl.positive]
  constructor
  · field_simp [ne_of_gt hl.positive,ne_of_gt s.r_pos]
  · rfl

def scaledMeanA (s : ScaledSource) (a : ℝ) : ℝ :=
  s.h*Real.sin (a-s.delta)^2+s.v*Real.cos (a-s.delta)^2
def scaledMeanB (s : ScaledSource) (b : ℝ) : ℝ :=
  (s.h*Real.sin (b-s.delta)^2+s.v*Real.cos (b-s.delta)^2)/s.r

theorem lossSnapshot_means (s : ScaledSource) (loss : ℝ) (hl : LegalLoss s loss)
    (lam : ℝ) (h0 : 0 ≤ lam) (h1 : lam ≤ 1) (a b : ℝ) :
    meanA (lossSnapshot s loss hl lam h0 h1) a=scaledMeanA s a ∧
    meanB (lossSnapshot s loss hl lam h0 h1) b=scaledMeanB s b := by
  constructor <;> dsimp [meanA,meanB,lossSnapshot,scaledMeanA,scaledMeanB] <;>
    field_simp [ne_of_gt hl.positive,ne_of_gt s.r_pos]

theorem baseline_T_pos (s : ScaledSource) (loss : ℝ) (hl : LegalLoss s loss) :
    0 < T (baseline s loss hl) := by
  have hnH : 0 < (baseline s loss hl).nH := div_pos s.h_pos hl.positive
  have hnV : 0 < (baseline s loss hl).nV := div_pos s.v_pos hl.positive
  dsimp only [T]
  apply mul_pos
  · apply mul_pos (ratio_pos _)
    dsimp only [kH]
    exact mul_pos (Real.sqrt_pos.mpr (mul_pos (baseline s loss hl).etaA_pos hnH))
      (Real.sqrt_pos.mpr (mul_pos (baseline s loss hl).etaB_pos (by linarith)))
  · dsimp only [kV]
    exact mul_pos (Real.sqrt_pos.mpr (mul_pos (baseline s loss hl).etaA_pos hnV))
      (Real.sqrt_pos.mpr (mul_pos (baseline s loss hl).etaB_pos (by linarith)))

def observedH (s : ScaledSource) (loss : ℝ) (hl : LegalLoss s loss) (seed : Cell) (w : ℝ) : ℝ :=
  w*E (baseline s loss hl) seed loss-L (baseline s loss hl) seed loss

def inferredCoherence (s : ScaledSource) (loss : ℝ) (hl : LegalLoss s loss)
    (seed : Cell) (w : ℝ) : ℝ :=
  observedH s loss hl seed w/(g (baseline s loss hl) seed*T (baseline s loss hl))

def PhaseDomain (s : ScaledSource) (loss : ℝ) (hl : LegalLoss s loss) (seed : Cell) (w : ℝ) : Prop :=
  observedH s loss hl seed w^2 ≤ g (baseline s loss hl) seed^2*T (baseline s loss hl)^2

theorem inferred_coherence_bounds (s : ScaledSource) (loss : ℝ) (hl : LegalLoss s loss)
    (seed : Cell) (w : ℝ) (hg : g (baseline s loss hl) seed ≠ 0)
    (hp : PhaseDomain s loss hl seed w) :
    -1 ≤ inferredCoherence s loss hl seed w ∧ inferredCoherence s loss hl seed w ≤ 1 := by
  have hd := mul_ne_zero hg (ne_of_gt (baseline_T_pos s loss hl))
  have hdsq : 0 < (g (baseline s loss hl) seed*T (baseline s loss hl))^2 := sq_pos_of_ne_zero hd
  have hc : inferredCoherence s loss hl seed w^2 ≤ 1 := by
    rw [inferredCoherence,div_pow]
    apply (div_le_one hdsq).2
    simpa [PhaseDomain,mul_pow] using hp
  exact abs_le.mp ((sq_le_one_iff_abs_le_one _).mp hc)

def inferredLambda (s : ScaledSource) (loss : ℝ) (hl : LegalLoss s loss) (seed : Cell) (w : ℝ) : ℝ :=
  (1-inferredCoherence s loss hl seed w)/2

theorem inferred_lambda_bounds (s : ScaledSource) (loss : ℝ) (hl : LegalLoss s loss)
    (seed : Cell) (w : ℝ) (hg : g (baseline s loss hl) seed ≠ 0)
    (hp : PhaseDomain s loss hl seed w) :
    0 ≤ inferredLambda s loss hl seed w ∧ inferredLambda s loss hl seed w ≤ 1 := by
  have hc := inferred_coherence_bounds s loss hl seed w hg hp
  dsimp [inferredLambda]
  constructor <;> linarith

def generatedSnapshot (s : ScaledSource) (loss : ℝ) (hl : LegalLoss s loss)
    (seed : Cell) (w : ℝ) (hg : g (baseline s loss hl) seed ≠ 0)
    (hp : PhaseDomain s loss hl seed w) : Snapshot :=
  lossSnapshot s loss hl (inferredLambda s loss hl seed w)
    (inferred_lambda_bounds s loss hl seed w hg hp).1
    (inferred_lambda_bounds s loss hl seed w hg hp).2

theorem generated_coherence (s : ScaledSource) (loss : ℝ) (hl : LegalLoss s loss)
    (seed : Cell) (w : ℝ) (hg : g (baseline s loss hl) seed ≠ 0)
    (hp : PhaseDomain s loss hl seed w) :
    coherence (generatedSnapshot s loss hl seed w hg hp)=inferredCoherence s loss hl seed w := by
  dsimp [coherence,generatedSnapshot,lossSnapshot,inferredLambda]
  ring

theorem generated_seed_readback (s : ScaledSource) (loss : ℝ) (hl : LegalLoss s loss)
    (seed : Cell) (w : ℝ) (hg : g (baseline s loss hl) seed ≠ 0)
    (hp : PhaseDomain s loss hl seed w) :
    pulse00 (generatedSnapshot s loss hl seed w hg hp) seed=w := by
  have hs := source_H (generatedSnapshot s loss hl seed w hg hp) seed
  rw [generated_coherence] at hs
  change pulse00 (generatedSnapshot s loss hl seed w hg hp) seed*
    E (baseline s loss hl) seed loss-L (baseline s loss hl) seed loss =
    inferredCoherence s loss hl seed w*g (baseline s loss hl) seed*T (baseline s loss hl) at hs
  have hd := mul_ne_zero hg (ne_of_gt (baseline_T_pos s loss hl))
  have hc : inferredCoherence s loss hl seed w*
      (g (baseline s loss hl) seed*T (baseline s loss hl))=observedH s loss hl seed w :=
    div_mul_cancel₀ _ hd
  rw [← mul_assoc] at hc
  rw [hc] at hs
  have he : 0 < E (baseline s loss hl) seed loss := E_pos (baseline s loss hl) seed
  dsimp [observedH] at hs
  apply (mul_right_cancel₀ (ne_of_gt he))
  linarith

def observedClosure (s : ScaledSource) (loss : ℝ) (hl : LegalLoss s loss)
    (seed cell : Cell) (w : ℝ) : ℝ :=
  (L (baseline s loss hl) cell loss+
    (g (baseline s loss hl) cell/g (baseline s loss hl) seed)*observedH s loss hl seed w)/
    E (baseline s loss hl) cell loss

theorem generated_cell_readback (s : ScaledSource) (loss : ℝ) (hl : LegalLoss s loss)
    (seed cell : Cell) (w : ℝ) (hg : g (baseline s loss hl) seed ≠ 0)
    (hp : PhaseDomain s loss hl seed w) :
    pulse00 (generatedSnapshot s loss hl seed w hg hp) cell=observedClosure s loss hl seed cell w := by
  have hga : g (generatedSnapshot s loss hl seed w hg hp) seed ≠ 0 := hg
  rw [← same_source_cell_closure (generatedSnapshot s loss hl seed w hg hp) seed cell hga]
  change (L (baseline s loss hl) cell loss+(g (baseline s loss hl) cell/g (baseline s loss hl) seed)*
      (pulse00 (generatedSnapshot s loss hl seed w hg hp) seed*E (baseline s loss hl) seed loss-
        L (baseline s loss hl) seed loss))/E (baseline s loss hl) cell loss=observedClosure s loss hl seed cell w
  rw [generated_seed_readback]
  rfl

theorem generated_interval_readback (s : ScaledSource) (loss : ℝ) (hl : LegalLoss s loss)
    (seed cell : Cell) (w lo hi : ℝ) (hg : g (baseline s loss hl) seed ≠ 0)
    (hp : PhaseDomain s loss hl seed w)
    (hlo : 0 ≤ L (baseline s loss hl) cell loss+
      (g (baseline s loss hl) cell/g (baseline s loss hl) seed)*observedH s loss hl seed w-
        lo*E (baseline s loss hl) cell loss)
    (hhi : 0 ≤ hi*E (baseline s loss hl) cell loss-
      (L (baseline s loss hl) cell loss+
        (g (baseline s loss hl) cell/g (baseline s loss hl) seed)*observedH s loss hl seed w)) :
    lo ≤ pulse00 (generatedSnapshot s loss hl seed w hg hp) cell ∧
      pulse00 (generatedSnapshot s loss hl seed w hg hp) cell ≤ hi := by
  have he : 0 < E (baseline s loss hl) cell loss := E_pos (baseline s loss hl) cell
  rw [generated_cell_readback]
  exact ⟨(le_div_iff₀ he).2 (by linarith),(div_le_iff₀ he).2 (by linarith)⟩

end
end P23.ObservableClosure.ScalarFiber
