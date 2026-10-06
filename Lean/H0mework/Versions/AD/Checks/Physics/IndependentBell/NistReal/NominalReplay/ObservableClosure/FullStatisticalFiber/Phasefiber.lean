import H0mework.Versions.AD.Checks.Physics.IndependentBell.NistReal.NominalReplay.ObservableClosure.Observableclosure

/-! Complete same-source phase fibre for the named Gaussian vacuum law. -/

set_option autoImplicit false

namespace P23.ObservableClosure.PhaseFiber

noncomputable section

structure RawSource where
  nH : ℝ
  nV : ℝ
  etaA : ℝ
  etaB : ℝ
  delta : ℝ
  nH_nonneg : 0 ≤ nH
  nV_nonneg : 0 ≤ nV
  nV_le_nH : nV ≤ nH
  etaA_pos : 0 < etaA
  etaA_le_one : etaA ≤ 1
  etaB_pos : 0 < etaB
  etaB_le_one : etaB ≤ 1

def RawSource.withPhase (raw : RawSource) (lam : ℝ) (h0 : 0 ≤ lam) (h1 : lam ≤ 1) :
    Snapshot where
  nH := raw.nH
  nV := raw.nV
  etaA := raw.etaA
  etaB := raw.etaB
  delta := raw.delta
  lam := lam
  nH_nonneg := raw.nH_nonneg
  nV_nonneg := raw.nV_nonneg
  nV_le_nH := raw.nV_le_nH
  etaA_pos := raw.etaA_pos
  etaA_le_one := raw.etaA_le_one
  etaB_pos := raw.etaB_pos
  etaB_le_one := raw.etaB_le_one
  lam_nonneg := h0
  lam_le_one := h1

def RawSource.baseline (raw : RawSource) : Snapshot :=
  raw.withPhase 0 (by norm_num) (by norm_num)

def forgetPhase (s : Snapshot) : RawSource where
  nH := s.nH
  nV := s.nV
  etaA := s.etaA
  etaB := s.etaB
  delta := s.delta
  nH_nonneg := s.nH_nonneg
  nV_nonneg := s.nV_nonneg
  nV_le_nH := s.nV_le_nH
  etaA_pos := s.etaA_pos
  etaA_le_one := s.etaA_le_one
  etaB_pos := s.etaB_pos
  etaB_le_one := s.etaB_le_one

theorem forget_phase_readback (s : Snapshot) :
    (forgetPhase s).withPhase s.lam s.lam_nonneg s.lam_le_one = s := by
  cases s
  rfl

def interference (s : Snapshot) : ℝ := coherence s*T s

def PhysicalPhase (raw : RawSource) (k : ℝ) : Prop :=
  -T raw.baseline ≤ k ∧ k ≤ T raw.baseline

def affinePulse (raw : RawSource) (cell : Cell) (k : ℝ) : ℝ :=
  (L raw.baseline cell (e raw.baseline)+g raw.baseline cell*k)/
    E raw.baseline cell (e raw.baseline)

theorem with_phase_means (raw : RawSource) (lam : ℝ) (h0 : 0 ≤ lam) (h1 : lam ≤ 1)
    (a b : ℝ) :
    meanA (raw.withPhase lam h0 h1) a=meanA raw.baseline a ∧
    meanB (raw.withPhase lam h0 h1) b=meanB raw.baseline b := ⟨rfl,rfl⟩

theorem with_phase_interference (raw : RawSource) (lam : ℝ)
    (h0 : 0 ≤ lam) (h1 : lam ≤ 1) :
    interference (raw.withPhase lam h0 h1)=(1-2*lam)*T raw.baseline := rfl

theorem interference_physical (raw : RawSource) (lam : ℝ)
    (h0 : 0 ≤ lam) (h1 : lam ≤ 1) :
    PhysicalPhase raw (interference (raw.withPhase lam h0 h1)) := by
  have ht := T_nonneg raw.baseline
  have hc0 : -1 ≤ 1-2*lam := by linarith
  have hc1 : 1-2*lam ≤ 1 := by linarith
  have hlo := mul_le_mul_of_nonneg_right hc0 ht
  have hhi := mul_le_mul_of_nonneg_right hc1 ht
  rw [with_phase_interference]
  exact ⟨by nlinarith,by nlinarith⟩

theorem physical_phase_iff_square (raw : RawSource) (k : ℝ) :
    PhysicalPhase raw k ↔ k^2 ≤ T2 raw.baseline (e raw.baseline) := by
  rw [← T_sq]
  have ht := T_nonneg raw.baseline
  constructor
  · rintro ⟨hlo,hhi⟩
    nlinarith
  · intro hk
    constructor <;> nlinarith [sq_nonneg (k+T raw.baseline),sq_nonneg (k-T raw.baseline)]

theorem zero_T_physical_iff (raw : RawSource) (hT : T raw.baseline=0) (k : ℝ) :
    PhysicalPhase raw k ↔ k=0 := by
  simp only [PhysicalPhase,hT,neg_zero]
  constructor
  · rintro ⟨hlo,hhi⟩
    exact le_antisymm hhi hlo
  · rintro rfl
    exact ⟨le_rfl,le_rfl⟩

/-- The phase recipe uses only the raw source and its legal signed interference. -/
def phaseRecipe (raw : RawSource) (k : ℝ) : ℝ :=
  if T raw.baseline=0 then 0 else (1-k/T raw.baseline)/2

theorem phase_recipe_bounds (raw : RawSource) (k : ℝ) (hk : PhysicalPhase raw k) :
    0 ≤ phaseRecipe raw k ∧ phaseRecipe raw k ≤ 1 := by
  by_cases hz : T raw.baseline=0
  · simp [phaseRecipe,hz]
  · have ht : 0 < T raw.baseline := lt_of_le_of_ne (T_nonneg _) (Ne.symm hz)
    have hlo : -1 ≤ k/T raw.baseline := (le_div_iff₀ ht).2 (by nlinarith [hk.1])
    have hhi : k/T raw.baseline ≤ 1 := (div_le_iff₀ ht).2 (by nlinarith [hk.2])
    simp only [phaseRecipe,hz,if_false]
    constructor <;> linarith

def generatedSnapshot (raw : RawSource) (k : ℝ) (hk : PhysicalPhase raw k) : Snapshot :=
  raw.withPhase (phaseRecipe raw k) (phase_recipe_bounds raw k hk).1
    (phase_recipe_bounds raw k hk).2

theorem generated_interference (raw : RawSource) (k : ℝ) (hk : PhysicalPhase raw k) :
    interference (generatedSnapshot raw k hk)=k := by
  rw [generatedSnapshot,with_phase_interference]
  by_cases hz : T raw.baseline=0
  · have hk0 := (zero_T_physical_iff raw hz k).1 hk
    simp [phaseRecipe,hz,hk0]
  · simp only [phaseRecipe,hz,if_false]
    field_simp [hz]
    ring

theorem with_phase_affine_readback (raw : RawSource) (lam : ℝ)
    (h0 : 0 ≤ lam) (h1 : lam ≤ 1) (cell : Cell) :
    pulse00 (raw.withPhase lam h0 h1) cell=
      affinePulse raw cell (interference (raw.withPhase lam h0 h1)) := by
  have hs := source_H (raw.withPhase lam h0 h1) cell
  change pulse00 (raw.withPhase lam h0 h1) cell*E raw.baseline cell (e raw.baseline)-
    L raw.baseline cell (e raw.baseline)=
    coherence (raw.withPhase lam h0 h1)*g raw.baseline cell*T raw.baseline at hs
  have he := ne_of_gt (E_pos raw.baseline cell)
  dsimp [affinePulse,interference]
  apply (eq_div_iff he).2
  change pulse00 (raw.withPhase lam h0 h1) cell*E raw.baseline cell (e raw.baseline)=
    L raw.baseline cell (e raw.baseline)+
      g raw.baseline cell*(coherence (raw.withPhase lam h0 h1)*T raw.baseline)
  linear_combination hs

/-- A legal signed phase generates one source and every cell of its original law. -/
theorem generated_all_cells (raw : RawSource) (k : ℝ) (hk : PhysicalPhase raw k) :
    ∀ cell, pulse00 (generatedSnapshot raw k hk) cell=affinePulse raw cell k := by
  intro cell
  have hf := with_phase_affine_readback raw (phaseRecipe raw k)
    (phase_recipe_bounds raw k hk).1 (phase_recipe_bounds raw k hk).2 cell
  change pulse00 (generatedSnapshot raw k hk) cell=
    affinePulse raw cell (interference (generatedSnapshot raw k hk)) at hf
  simpa [generated_interference] using hf

def Slab (raw : RawSource) (cell : Cell) (lo hi k : ℝ) : Prop :=
  lo*E raw.baseline cell (e raw.baseline)-L raw.baseline cell (e raw.baseline) ≤
      g raw.baseline cell*k ∧
    g raw.baseline cell*k ≤
      hi*E raw.baseline cell (e raw.baseline)-L raw.baseline cell (e raw.baseline)

def TrainingQualified (raw : RawSource) (lam : ℝ) (h0 : 0 ≤ lam) (h1 : lam ≤ 1)
    (cell0 cell1 : Cell) (lo0 hi0 lo1 hi1 : ℝ) : Prop :=
  (lo0 ≤ pulse00 (raw.withPhase lam h0 h1) cell0 ∧
    pulse00 (raw.withPhase lam h0 h1) cell0 ≤ hi0) ∧
  (lo1 ≤ pulse00 (raw.withPhase lam h0 h1) cell1 ∧
    pulse00 (raw.withPhase lam h0 h1) cell1 ≤ hi1)

structure PhaseQualified (raw : RawSource) (cell0 cell1 : Cell)
    (lo0 hi0 lo1 hi1 k : ℝ) : Prop where
  physical : PhysicalPhase raw k
  first : Slab raw cell0 lo0 hi0 k
  second : Slab raw cell1 lo1 hi1 k

theorem affine_interval_iff_slab (raw : RawSource) (cell : Cell) (lo hi k : ℝ) :
    (lo ≤ affinePulse raw cell k ∧ affinePulse raw cell k ≤ hi) ↔
      Slab raw cell lo hi k := by
  have he := E_pos raw.baseline cell
  dsimp [affinePulse,Slab]
  rw [le_div_iff₀ he,div_le_iff₀ he]
  constructor <;> rintro ⟨hlo,hhi⟩ <;> constructor <;> linarith

theorem training_qualified_iff_phase (raw : RawSource) (lam : ℝ)
    (h0 : 0 ≤ lam) (h1 : lam ≤ 1) (cell0 cell1 : Cell) (lo0 hi0 lo1 hi1 : ℝ) :
    TrainingQualified raw lam h0 h1 cell0 cell1 lo0 hi0 lo1 hi1 ↔
      PhaseQualified raw cell0 cell1 lo0 hi0 lo1 hi1
        (interference (raw.withPhase lam h0 h1)) := by
  unfold TrainingQualified
  rw [with_phase_affine_readback,with_phase_affine_readback,
    affine_interval_iff_slab,affine_interval_iff_slab]
  constructor
  · rintro ⟨ha,hb⟩
    exact ⟨interference_physical raw lam h0 h1,ha,hb⟩
  · intro hq
    exact ⟨hq.first,hq.second⟩

/-- No phase endpoint or training readback is supplied to this complete fibre characterization. -/
theorem complete_phase_fiber (raw : RawSource) (cell0 cell1 : Cell)
    (lo0 hi0 lo1 hi1 k : ℝ) :
    (∃ (lam : ℝ) (h0 : 0 ≤ lam) (h1 : lam ≤ 1),
      interference (raw.withPhase lam h0 h1)=k ∧
      TrainingQualified raw lam h0 h1 cell0 cell1 lo0 hi0 lo1 hi1) ↔
    PhaseQualified raw cell0 cell1 lo0 hi0 lo1 hi1 k := by
  constructor
  · rintro ⟨lam,h0,h1,hk,hq⟩
    have hp := (training_qualified_iff_phase raw lam h0 h1 cell0 cell1 lo0 hi0 lo1 hi1).1 hq
    rwa [hk] at hp
  · intro hq
    refine ⟨phaseRecipe raw k,(phase_recipe_bounds raw k hq.physical).1,
      (phase_recipe_bounds raw k hq.physical).2,generated_interference raw k hq.physical,?_⟩
    apply (training_qualified_iff_phase raw _ _ _ cell0 cell1 lo0 hi0 lo1 hi1).2
    change PhaseQualified raw cell0 cell1 lo0 hi0 lo1 hi1
      (interference (generatedSnapshot raw k hq.physical))
    simpa [generated_interference] using hq

theorem zero_g_slab (raw : RawSource) (cell : Cell) (lo hi k : ℝ)
    (hg : g raw.baseline cell=0) :
    Slab raw cell lo hi k ↔
      lo*E raw.baseline cell (e raw.baseline) ≤ L raw.baseline cell (e raw.baseline) ∧
      L raw.baseline cell (e raw.baseline) ≤ hi*E raw.baseline cell (e raw.baseline) := by
  simp only [Slab,hg,zero_mul]
  constructor <;> rintro ⟨hlo,hhi⟩ <;> constructor <;> linarith

theorem zero_T_all_phases (raw : RawSource) (hT : T raw.baseline=0)
    (lam mu : ℝ) (hl0 : 0 ≤ lam) (hl1 : lam ≤ 1) (hm0 : 0 ≤ mu) (hm1 : mu ≤ 1) :
    ∀ cell, pulse00 (raw.withPhase lam hl0 hl1) cell=
      pulse00 (raw.withPhase mu hm0 hm1) cell := by
  intro cell
  rw [with_phase_affine_readback,with_phase_affine_readback,
    with_phase_interference,with_phase_interference,hT]
  simp

theorem pure_mode_zero_T (raw : RawSource) (hv : raw.nV=0) : T raw.baseline=0 := by
  simp [T,kV,RawSource.baseline,RawSource.withPhase,hv]

def covarianceM (s : Snapshot) : ℝ := (h s+v s)/2
def covarianceC (s : Snapshot) : ℝ := (h s-v s)/2
def covarianceZ (s : Snapshot) : ℝ := covarianceC s*Real.cos (2*s.delta)
def covarianceX (s : Snapshot) : ℝ := covarianceC s*Real.sin (2*s.delta)
def covarianceR2 (s : Snapshot) : ℝ := covarianceZ s^2+covarianceX s^2

theorem covariance_radius (s : Snapshot) : covarianceR2 s=covarianceC s^2 := by
  dsimp [covarianceR2,covarianceZ,covarianceX]
  nlinarith [Real.sin_sq_add_cos_sq (2*s.delta)]

theorem covariance_T2 (s : Snapshot) :
    T2 s (e s)=(covarianceM s^2-covarianceR2 s)*
      ((covarianceM s+e s)^2-covarianceR2 s) := by
  rw [covariance_radius]
  dsimp [T2,covarianceM,covarianceC]
  ring

def cellD (cell : Cell) : ℝ := Real.cos (cell.a-cell.b)
def cellY (s : Snapshot) (cell : Cell) : ℝ :=
  covarianceZ s*Real.cos (cell.a+cell.b)+covarianceX s*Real.sin (cell.a+cell.b)
def cellQ (s : Snapshot) (cell : Cell) : ℝ := Real.cos (cell.a+cell.b-2*s.delta)

theorem cell_Y_readback (s : Snapshot) (cell : Cell) :
    cellY s cell=covarianceC s*cellQ s cell := by
  dsimp [cellY,covarianceZ,covarianceX,cellQ]
  rw [Real.cos_sub]
  ring

theorem cell_UV_readback (s : Snapshot) (cell : Cell) :
    U s cell=(cellD cell-cellQ s cell)/2 ∧
    V s cell=(cellD cell+cellQ s cell)/2 := by
  have hu := Real.two_mul_sin_mul_sin (cell.a-s.delta) (cell.b-s.delta)
  have hv := Real.two_mul_cos_mul_cos (cell.a-s.delta) (cell.b-s.delta)
  have hd : (cell.a-s.delta)-(cell.b-s.delta)=cell.a-cell.b := by ring
  have hs : (cell.a-s.delta)+(cell.b-s.delta)=cell.a+cell.b-2*s.delta := by ring
  rw [hd,hs] at hu hv
  dsimp [U,V,cellD,cellQ]
  constructor <;> linarith

def covarianceGamma (s : Snapshot) (cell : Cell) : ℝ :=
  covarianceR2 s*cellD cell^2-cellY s cell^2

def covarianceEll (s : Snapshot) (cell : Cell) : ℝ :=
  2*covarianceR2 s*(1+meanA s cell.a)*(ratio s+ratio s*meanB s cell.b)-
    (covarianceM s^2+covarianceR2 s+e s*covarianceM s)*
      (covarianceR2 s*cellD cell^2+cellY s cell^2)+
    2*covarianceR2 s*(2*covarianceM s+e s)*cellD cell*cellY s cell

theorem covariance_gamma_readback (s : Snapshot) (cell : Cell) :
    covarianceGamma s cell=2*ratio s*covarianceR2 s*g s cell := by
  rw [covarianceGamma,cell_Y_readback]
  have huv := cell_UV_readback s cell
  dsimp [g]
  rw [huv.1,huv.2,covariance_radius]
  field_simp [ne_of_gt (ratio_pos s)]
  ring

theorem covariance_ell_readback (s : Snapshot) (cell : Cell) :
    covarianceEll s cell=2*ratio s*covarianceR2 s*L s cell (e s) := by
  rw [covarianceEll,cell_Y_readback]
  have huv := cell_UV_readback s cell
  dsimp [L,D]
  rw [huv.1,huv.2,covariance_radius]
  dsimp [covarianceM,covarianceC]
  field_simp [ne_of_gt (ratio_pos s)]
  ring

def covariancePulse (s : Snapshot) (cell : Cell) : ℝ :=
  2*ratio s*covarianceR2 s*(covarianceEll s cell+covarianceGamma s cell*interference s)/
    (covarianceEll s cell^2-covarianceGamma s cell^2*T2 s (e s))

theorem covariance_pulse_readback (s : Snapshot) (cell : Cell)
    (hR : covarianceR2 s ≠ 0) : covariancePulse s cell=pulse00 s cell := by
  have he := ne_of_gt (E_pos s cell)
  have hr := ne_of_gt (ratio_pos s)
  have hscale : 2*ratio s*covarianceR2 s ≠ 0 := mul_ne_zero (mul_ne_zero (by norm_num) hr) hR
  have hden : covarianceEll s cell^2-covarianceGamma s cell^2*T2 s (e s) ≠ 0 := by
    rw [covariance_ell_readback,covariance_gamma_readback]
    have hid : (2*ratio s*covarianceR2 s*L s cell (e s))^2-
        (2*ratio s*covarianceR2 s*g s cell)^2*T2 s (e s)=
        (2*ratio s*covarianceR2 s)^2*E s cell (e s) := by dsimp [E]; ring
    rw [hid]
    exact mul_ne_zero (pow_ne_zero 2 hscale) he
  have hs := source_H s cell
  dsimp [H] at hs
  unfold covariancePulse
  rw [covariance_ell_readback,covariance_gamma_readback]
  dsimp [interference,E] at *
  field_simp [hden,he,hr,hR]
  nlinarith [hs]

end
end P23.ObservableClosure.PhaseFiber
