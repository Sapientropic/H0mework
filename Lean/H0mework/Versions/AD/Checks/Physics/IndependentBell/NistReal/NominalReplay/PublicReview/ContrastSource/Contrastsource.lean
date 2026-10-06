import H0mework.Versions.AD.Checks.Physics.IndependentBell.NistReal.NominalReplay.ObservableClosure.Closureconsumer

/-! The original Gaussian source generates a positive no-signaling N-pulse law. -/

set_option autoImplicit false

namespace P23.ObservableClosure.ContrastSource

open P23.ObservableClosure.Consumer

noncomputable section

def marginalA (o : Outcomes) : ℝ := o.both+o.onlyA
def marginalB (o : Outcomes) : ℝ := o.both+o.onlyB

structure PositiveOutcomes (o : Outcomes) : Prop where
  both : 0 ≤ o.both
  onlyA : 0 ≤ o.onlyA
  onlyB : 0 ≤ o.onlyB
  neither : 0 ≤ o.neither

structure Background where
  alice : ℝ
  bob : ℝ
  alice_nonneg : 0 ≤ alice
  alice_le_one : alice ≤ 1
  bob_nonneg : 0 ≤ bob
  bob_le_one : bob ≤ 1

theorem root_pair_swap (a b n : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hn : 0 ≤ n) :
    Real.sqrt (a*n)*Real.sqrt (b*(1+n))=
      Real.sqrt (b*n)*Real.sqrt (a*(1+n)) := by
  rw [← Real.sqrt_mul (mul_nonneg ha hn),← Real.sqrt_mul (mul_nonneg hb hn)]
  congr 1
  ring

theorem phase_cauchy_left (s : Snapshot) (cell : Cell) (phase : ℝ) (hp : phase^2=1) :
    kappa s cell phase^2 ≤ meanB s cell.b*(s.etaA+meanA s cell.a) := by
  let x := Real.sqrt (s.etaB*s.nH)*Real.sin (cell.b-s.delta)
  let y := Real.sqrt (s.etaB*s.nV)*Real.cos (cell.b-s.delta)
  let z := Real.sqrt (s.etaA*(1+s.nH))*Real.sin (cell.a-s.delta)
  let w := phase*Real.sqrt (s.etaA*(1+s.nV))*Real.cos (cell.a-s.delta)
  have hB : x^2+y^2=meanB s cell.b := by
    dsimp [x,y,meanB]
    simp only [mul_pow,Real.sq_sqrt (mul_nonneg s.etaB_pos.le s.nH_nonneg),
      Real.sq_sqrt (mul_nonneg s.etaB_pos.le s.nV_nonneg)]
    ring
  have hA : z^2+w^2=s.etaA+meanA s cell.a := by
    dsimp [z,w,meanA]
    simp only [mul_pow,hp,one_mul,
      Real.sq_sqrt (mul_nonneg s.etaA_pos.le (by linarith [s.nH_nonneg] : 0 ≤ 1+s.nH)),
      Real.sq_sqrt (mul_nonneg s.etaA_pos.le (by linarith [s.nV_nonneg] : 0 ≤ 1+s.nV))]
    linear_combination s.etaA*(Real.sin_sq_add_cos_sq (cell.a-s.delta))
  have hH := root_pair_swap s.etaB s.etaA s.nH s.etaB_pos.le s.etaA_pos.le s.nH_nonneg
  have hV := root_pair_swap s.etaB s.etaA s.nV s.etaB_pos.le s.etaA_pos.le s.nV_nonneg
  have hk : x*z+y*w=kappa s cell phase := by
    dsimp [x,y,z,w,kappa,kH,kV,U,V]
    calc
      _ = (Real.sqrt (s.etaB*s.nH)*Real.sqrt (s.etaA*(1+s.nH)))*
          (Real.sin (cell.a-s.delta)*Real.sin (cell.b-s.delta))+
        phase*(Real.sqrt (s.etaB*s.nV)*Real.sqrt (s.etaA*(1+s.nV)))*
          (Real.cos (cell.a-s.delta)*Real.cos (cell.b-s.delta)) := by ring
      _ = _ := by rw [hH,hV]
  simpa [hA,hB,hk] using two_term_cauchy x y z w

theorem denominator_edge_bounds (s : Snapshot) (cell : Cell) (phase : ℝ)
    (hp : phase^2=1) :
    1+meanA s cell.a ≤ phaseDen s cell phase ∧
      1+meanB s cell.b ≤ phaseDen s cell phase := by
  have hA := phase_cauchy_left s cell phase hp
  have hB := phase_cauchy s cell phase hp
  have ha := meanA_nonneg s cell.a
  have hb := meanB_nonneg s cell.b
  have hma := mul_le_mul_of_nonneg_left s.etaA_le_one hb
  have hmb := mul_le_mul_of_nonneg_left s.etaB_le_one ha
  dsimp [phaseDen,D]
  constructor <;> nlinarith

theorem pulse_mixture_upper (s : Snapshot) (cell : Cell) (bound : ℝ)
    (hplus : 1/phaseDen s cell 1 ≤ bound)
    (hminus : 1/phaseDen s cell (-1) ≤ bound) : pulse00 s cell ≤ bound := by
  have hl : 0 ≤ 1-s.lam := by linarith [s.lam_le_one]
  calc
    pulse00 s cell=(1-s.lam)*(1/phaseDen s cell 1)+
      s.lam*(1/phaseDen s cell (-1)) := by dsimp [pulse00]; ring
    _ ≤ (1-s.lam)*bound+s.lam*bound :=
      add_le_add (mul_le_mul_of_nonneg_left hplus hl)
        (mul_le_mul_of_nonneg_left hminus s.lam_nonneg)
    _ = bound := by ring

theorem pulse_mixture_lower (s : Snapshot) (cell : Cell) (bound : ℝ)
    (hplus : bound ≤ 1/phaseDen s cell 1)
    (hminus : bound ≤ 1/phaseDen s cell (-1)) : bound ≤ pulse00 s cell := by
  have hl : 0 ≤ 1-s.lam := by linarith [s.lam_le_one]
  calc
    bound=(1-s.lam)*bound+s.lam*bound := by ring
    _ ≤ (1-s.lam)*(1/phaseDen s cell 1)+s.lam*(1/phaseDen s cell (-1)) :=
      add_le_add (mul_le_mul_of_nonneg_left hplus hl)
        (mul_le_mul_of_nonneg_left hminus s.lam_nonneg)
    _ = pulse00 s cell := by dsimp [pulse00]; ring

theorem pulse_bounds (s : Snapshot) (cell : Cell) :
    1/D s cell ≤ pulse00 s cell ∧
      pulse00 s cell ≤ 1/(1+meanA s cell.a) ∧
      pulse00 s cell ≤ 1/(1+meanB s cell.b) := by
  have ha : 0 < 1+meanA s cell.a := by linarith [meanA_nonneg s cell.a]
  have hb : 0 < 1+meanB s cell.b := by linarith [meanB_nonneg s cell.b]
  have hle : ∀ phase, phase^2=1 → phaseDen s cell phase ≤ D s cell := by
    intro phase _
    dsimp [phaseDen]
    nlinarith [sq_nonneg (kappa s cell phase)]
  refine ⟨pulse_mixture_lower s cell _ ?_ ?_,
    pulse_mixture_upper s cell _ ?_ ?_,pulse_mixture_upper s cell _ ?_ ?_⟩
  · exact one_div_le_one_div_of_le (phaseDen_pos s cell 1 (by norm_num)) (hle 1 (by norm_num))
  · exact one_div_le_one_div_of_le (phaseDen_pos s cell (-1) (by norm_num)) (hle (-1) (by norm_num))
  · exact one_div_le_one_div_of_le ha (denominator_edge_bounds s cell 1 (by norm_num)).1
  · exact one_div_le_one_div_of_le ha (denominator_edge_bounds s cell (-1) (by norm_num)).1
  · exact one_div_le_one_div_of_le hb (denominator_edge_bounds s cell 1 (by norm_num)).2
  · exact one_div_le_one_div_of_le hb (denominator_edge_bounds s cell (-1) (by norm_num)).2

def perPulseA (s : Snapshot) (bg : Background) (a : ℝ) : ℝ :=
  (1-bg.alice)/(1+meanA s a)
def perPulseB (s : Snapshot) (bg : Background) (b : ℝ) : ℝ :=
  (1-bg.bob)/(1+meanB s b)
def perPulsePair (s : Snapshot) (bg : Background) (cell : Cell) : ℝ :=
  (1-bg.alice)*(1-bg.bob)*pulse00 s cell

structure PerPulseBounds (s : Snapshot) (bg : Background) (cell : Cell) : Prop where
  alice_nonneg : 0 ≤ perPulseA s bg cell.a
  alice_le_one : perPulseA s bg cell.a ≤ 1
  bob_nonneg : 0 ≤ perPulseB s bg cell.b
  bob_le_one : perPulseB s bg cell.b ≤ 1
  pair_nonneg : 0 ≤ perPulsePair s bg cell
  pair_ge_product : perPulseA s bg cell.a*perPulseB s bg cell.b ≤ perPulsePair s bg cell
  pair_le_alice : perPulsePair s bg cell ≤ perPulseA s bg cell.a
  pair_le_bob : perPulsePair s bg cell ≤ perPulseB s bg cell.b

theorem source_per_pulse_bounds (s : Snapshot) (bg : Background) (cell : Cell) :
    PerPulseBounds s bg cell := by
  have hma := meanA_nonneg s cell.a
  have hmb := meanB_nonneg s cell.b
  have ha : 0 < 1+meanA s cell.a := by linarith
  have hb : 0 < 1+meanB s cell.b := by linarith
  have hga : 0 ≤ 1-bg.alice := by linarith [bg.alice_le_one]
  have hgb : 0 ≤ 1-bg.bob := by linarith [bg.bob_le_one]
  have hA0 : 0 ≤ perPulseA s bg cell.a := div_nonneg hga ha.le
  have hB0 : 0 ≤ perPulseB s bg cell.b := div_nonneg hgb hb.le
  have hd : 0 < D s cell := mul_pos ha hb
  have hp := pulse_bounds s cell
  have hp0 : 0 ≤ pulse00 s cell := (by positivity : 0 ≤ 1/D s cell).trans hp.1
  refine ⟨hA0,?_,hB0,?_,mul_nonneg (mul_nonneg hga hgb) hp0,?_,?_,?_⟩
  · apply (div_le_one ha).2
    linarith [bg.alice_nonneg]
  · apply (div_le_one hb).2
    linarith [bg.bob_nonneg]
  · calc
      perPulseA s bg cell.a*perPulseB s bg cell.b=
          (1-bg.alice)*(1-bg.bob)*(1/D s cell) := by
        dsimp [perPulseA,perPulseB,D]
        field_simp [ne_of_gt ha,ne_of_gt hb]
      _ ≤ perPulsePair s bg cell := mul_le_mul_of_nonneg_left hp.1 (mul_nonneg hga hgb)
  · calc
      perPulsePair s bg cell=(1-bg.bob)*((1-bg.alice)*pulse00 s cell) := by
        dsimp [perPulsePair]; ring
      _ ≤ (1-bg.bob)*((1-bg.alice)*(1/(1+meanA s cell.a))) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hp.2.1 hga) hgb
      _ ≤ 1*((1-bg.alice)*(1/(1+meanA s cell.a))) :=
        mul_le_mul_of_nonneg_right (by linarith [bg.bob_nonneg]) (by positivity)
      _ = perPulseA s bg cell.a := by dsimp [perPulseA]; ring
  · calc
      perPulsePair s bg cell=(1-bg.alice)*((1-bg.bob)*pulse00 s cell) := by
        dsimp [perPulsePair]; ring
      _ ≤ (1-bg.alice)*((1-bg.bob)*(1/(1+meanB s cell.b))) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hp.2.2 hgb) hga
      _ ≤ 1*((1-bg.bob)*(1/(1+meanB s cell.b))) :=
        mul_le_mul_of_nonneg_right (by linarith [bg.alice_nonneg]) (by positivity)
      _ = perPulseB s bg cell.b := by dsimp [perPulseB]; ring

def window (s : Snapshot) (N : ℕ) (bg : Background) (cell : Cell) : Outcomes :=
  let qa := perPulseA s bg cell.a^N
  let qb := perPulseB s bg cell.b^N
  let qab := perPulsePair s bg cell^N
  ⟨1-qa-qb+qab,qb-qab,qa-qab,qab⟩

theorem window_positive (s : Snapshot) (N : ℕ) (bg : Background) (cell : Cell) :
    PositiveOutcomes (window s N bg cell) := by
  have h := source_per_pulse_bounds s bg cell
  have hA := pow_le_one₀ (n := N) h.alice_nonneg h.alice_le_one
  have hB := pow_le_one₀ (n := N) h.bob_nonneg h.bob_le_one
  have hAB := pow_le_pow_left₀ (mul_nonneg h.alice_nonneg h.bob_nonneg) h.pair_ge_product N
  rw [mul_pow] at hAB
  have hPA := pow_le_pow_left₀ h.pair_nonneg h.pair_le_alice N
  have hPB := pow_le_pow_left₀ h.pair_nonneg h.pair_le_bob N
  have hprod := mul_nonneg (sub_nonneg.mpr hA) (sub_nonneg.mpr hB)
  dsimp [window]
  constructor
  · nlinarith [hAB,hprod]
  · linarith [hPB]
  · linarith [hPA]
  · exact pow_nonneg h.pair_nonneg N

theorem window_normalized (s : Snapshot) (N : ℕ) (bg : Background) (cell : Cell) :
    let o := window s N bg cell
    o.both+o.onlyA+o.onlyB+o.neither=1 := by dsimp [window]; ring

theorem window_marginal_A (s : Snapshot) (N : ℕ) (bg : Background) (cell : Cell) :
    marginalA (window s N bg cell)=1-perPulseA s bg cell.a^N := by
  dsimp [marginalA,window]
  ring

theorem window_marginal_B (s : Snapshot) (N : ℕ) (bg : Background) (cell : Cell) :
    marginalB (window s N bg cell)=1-perPulseB s bg cell.b^N := by
  dsimp [marginalB,window]
  ring

theorem window_five_readback (s : Snapshot) (bg : Background) (cell : Cell) :
    window s 5 bg cell=generatedWindow s cell bg.alice bg.bob := rfl

structure ProbabilityLaw where
  cells : Fin 4 → Outcomes
  positive : ∀ i, PositiveOutcomes (cells i)
  normalized : ∀ i, (cells i).both+(cells i).onlyA+(cells i).onlyB+(cells i).neither=1
  alice0 : marginalA (cells 0)=marginalA (cells 1)
  alice1 : marginalA (cells 2)=marginalA (cells 3)
  bob0 : marginalB (cells 0)=marginalB (cells 2)
  bob1 : marginalB (cells 1)=marginalB (cells 3)

def fourCells (a0 a1 b0 b1 : ℝ) (i : Fin 4) : Cell :=
  if i=0 then ⟨a0,b0⟩ else if i=1 then ⟨a0,b1⟩ else if i=2 then ⟨a1,b0⟩ else ⟨a1,b1⟩

/-- Positivity, normalization and both local restrictions come from the original source itself. -/
def sourceLaw (s : Snapshot) (N : ℕ) (bg : Background) (a0 a1 b0 b1 : ℝ) : ProbabilityLaw where
  cells := fun i => window s N bg (fourCells a0 a1 b0 b1 i)
  positive := fun i => window_positive s N bg _
  normalized := fun i => window_normalized s N bg _
  alice0 := by simp [window_marginal_A,fourCells]
  alice1 := by simp [window_marginal_A,fourCells]
  bob0 := by simp [window_marginal_B,fourCells]
  bob1 := by simp [window_marginal_B,fourCells]

def CH (q : ProbabilityLaw) : ℝ :=
  (q.cells 0).both+(q.cells 1).both+(q.cells 2).both-(q.cells 3).both-
    marginalA (q.cells 0)-marginalB (q.cells 0)

def win (q : ProbabilityLaw) : ℝ := (q.cells 0).both

def loss (q : ProbabilityLaw) : ℝ :=
  (marginalA (q.cells 0)-(q.cells 1).both)+
    (marginalB (q.cells 0)-(q.cells 2).both)+(q.cells 3).both

theorem contrast_CH_readback (q : ProbabilityLaw) : win q-loss q=CH q := by
  dsimp [win,loss,CH]
  ring

theorem loss_outcome_readback (q : ProbabilityLaw) :
    loss q=(q.cells 1).onlyA+(q.cells 2).onlyB+(q.cells 3).both := by
  rw [loss,q.alice0,q.bob0]
  dsimp [marginalA,marginalB]
  ring

theorem win_loss_nonnegative (q : ProbabilityLaw) : 0 ≤ win q ∧ 0 ≤ loss q := by
  rw [loss_outcome_readback]
  exact ⟨(q.positive 0).both,add_nonneg (add_nonneg (q.positive 1).onlyA
    (q.positive 2).onlyB) (q.positive 3).both⟩

def nativeCH (s : Snapshot) (N : ℕ) (bg : Background) (a0 a1 b0 b1 : ℝ) : ℝ :=
  (window s N bg ⟨a0,b0⟩).both+(window s N bg ⟨a0,b1⟩).both+
    (window s N bg ⟨a1,b0⟩).both-(window s N bg ⟨a1,b1⟩).both-
    (1-perPulseA s bg a0^N)-(1-perPulseB s bg b0^N)

theorem source_CH_readback (s : Snapshot) (N : ℕ) (bg : Background)
    (a0 a1 b0 b1 : ℝ) : CH (sourceLaw s N bg a0 a1 b0 b1)=nativeCH s N bg a0 a1 b0 b1 := by
  dsimp [CH,sourceLaw]
  rw [window_marginal_A,window_marginal_B]
  simp only [fourCells]
  norm_num
  rfl

structure Assignment where
  a0 : Bool
  a1 : Bool
  b0 : Bool
  b1 : Bool

def deterministicOutcomes (a b : Bool) : Outcomes :=
  if a then if b then ⟨1,0,0,0⟩ else ⟨0,1,0,0⟩
  else if b then ⟨0,0,1,0⟩ else ⟨0,0,0,1⟩

def assignmentCell (a : Assignment) (i : Fin 4) : Outcomes :=
  if i=0 then deterministicOutcomes a.a0 a.b0
  else if i=1 then deterministicOutcomes a.a0 a.b1
  else if i=2 then deterministicOutcomes a.a1 a.b0 else deterministicOutcomes a.a1 a.b1

private theorem deterministic_positive (a b : Bool) : PositiveOutcomes (deterministicOutcomes a b) := by
  cases a <;> cases b <;> constructor <;> norm_num [deterministicOutcomes]

private theorem deterministic_normalized (a b : Bool) :
    let o := deterministicOutcomes a b
    o.both+o.onlyA+o.onlyB+o.neither=1 := by
  cases a <;> cases b <;> norm_num [deterministicOutcomes]

private theorem deterministic_A (a b : Bool) :
    marginalA (deterministicOutcomes a b)=if a then 1 else 0 := by
  cases a <;> cases b <;> norm_num [deterministicOutcomes,marginalA]

private theorem deterministic_B (a b : Bool) :
    marginalB (deterministicOutcomes a b)=if b then 1 else 0 := by
  cases a <;> cases b <;> norm_num [deterministicOutcomes,marginalB]

def assignmentLaw (a : Assignment) : ProbabilityLaw where
  cells := assignmentCell a
  positive := by intro i; fin_cases i <;> simp [assignmentCell,deterministic_positive]
  normalized := by intro i; fin_cases i <;> simp [assignmentCell,deterministic_normalized]
  alice0 := by simp [assignmentCell,deterministic_A]
  alice1 := by simp [assignmentCell,deterministic_A]
  bob0 := by simp [assignmentCell,deterministic_B]
  bob1 := by simp [assignmentCell,deterministic_B]

/-- All sixteen local assignments satisfy the null; this is separate from the constant-source mouth. -/
theorem sixteen_assignments_CH_nonpositive (a : Assignment) : CH (assignmentLaw a) ≤ 0 := by
  rcases a with ⟨a0,a1,b0,b1⟩
  cases a0 <;> cases a1 <;> cases b0 <;> cases b1 <;>
    norm_num [CH,assignmentLaw,assignmentCell,deterministicOutcomes,marginalA,marginalB,
      Fin.ext_iff]

end
end P23.ObservableClosure.ContrastSource
