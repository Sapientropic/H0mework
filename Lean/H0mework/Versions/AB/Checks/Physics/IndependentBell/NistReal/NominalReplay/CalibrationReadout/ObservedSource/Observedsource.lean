import H0mework.Versions.AB.Checks.Physics.IndependentBell.NistReal.NominalReplay.CalibrationReadout.Calibrationlaw
import Mathlib.Analysis.SpecialFunctions.Artanh

set_option autoImplicit false

namespace P23.GaussianWindow.Calibration.Observed

noncomputable section

@[ext] structure Counts where
  a : ℝ
  b : ℝ
  j : ℝ

def delta (o : Counts) : ℝ := o.j-o.a*o.b
def vacuum (o : Counts) : ℝ := 1-o.a-o.b+o.j

structure Domain (o : Counts) : Prop where
  a_pos : 0 < o.a
  a_lt_one : o.a < 1
  b_pos : 0 < o.b
  b_lt_one : o.b < 1
  j_le_a : o.j ≤ o.a
  j_le_b : o.j ≤ o.b
  delta_pos : 0 < delta o
  finite_gap : 0 < delta o-o.a*o.b*vacuum o

def recoveredT (o : Counts) : ℝ := o.a*o.b*vacuum o/delta o
def recoveredTA (o : Counts) : ℝ := o.a*(1-recoveredT o)/(recoveredT o*(1-o.a))
def recoveredTB (o : Counts) : ℝ := o.b*(1-recoveredT o)/(recoveredT o*(1-o.b))
def recoveredGain (o : Counts) : ℝ := Real.artanh (Real.sqrt (recoveredT o))

theorem outcome_bounds {o : Counts} (h : Domain o) :
    0 < o.j ∧ 0 ≤ o.a-o.j ∧ 0 ≤ o.b-o.j ∧ 0 < vacuum o := by
  have hab : 0 < o.a*o.b := mul_pos h.a_pos h.b_pos
  have hp : 0 < (1-o.a)*(1-o.b) := mul_pos (by linarith [h.a_lt_one])
    (by linarith [h.b_lt_one])
  refine ⟨by linarith [show 0 < o.j-o.a*o.b from h.delta_pos],sub_nonneg.mpr h.j_le_a,
    sub_nonneg.mpr h.j_le_b,?_⟩
  dsimp [vacuum]
  nlinarith [show 0 < o.j-o.a*o.b from h.delta_pos]

theorem recoveredT_bounds {o : Counts} (h : Domain o) :
    0 < recoveredT o ∧ recoveredT o < 1 := by
  refine ⟨div_pos (mul_pos (mul_pos h.a_pos h.b_pos) (outcome_bounds h).2.2.2)
    h.delta_pos, (div_lt_one h.delta_pos).2 ?_⟩
  linarith [h.finite_gap]

theorem recoveredT_equation {o : Counts} (h : Domain o) :
    recoveredT o*delta o = o.a*o.b*vacuum o :=
  div_mul_cancel₀ _ (ne_of_gt h.delta_pos)

theorem singles_le_recoveredT {o : Counts} (h : Domain o) :
    o.a ≤ recoveredT o ∧ o.b ≤ recoveredT o := by
  constructor
  · apply (le_div_iff₀ h.delta_pos).2
    have hx : 0 ≤ (1-o.b)*(o.b-o.j) :=
      mul_nonneg (by linarith [h.b_lt_one]) (sub_nonneg.mpr h.j_le_b)
    have hy := mul_nonneg h.a_pos.le hx
    dsimp [delta,vacuum] at *
    nlinarith
  · apply (le_div_iff₀ h.delta_pos).2
    have hx : 0 ≤ (1-o.a)*(o.a-o.j) :=
      mul_nonneg (by linarith [h.a_lt_one]) (sub_nonneg.mpr h.j_le_a)
    have hy := mul_nonneg h.b_pos.le hx
    dsimp [delta,vacuum] at *
    nlinarith

theorem recoveredLoss_bounds {o : Counts} (h : Domain o) :
    0 < recoveredTA o ∧ recoveredTA o ≤ 1 ∧
    0 < recoveredTB o ∧ recoveredTB o ≤ 1 := by
  have ht := recoveredT_bounds h
  have ha : 0 < recoveredT o*(1-o.a) := mul_pos ht.1 (by linarith [h.a_lt_one])
  have hb : 0 < recoveredT o*(1-o.b) := mul_pos ht.1 (by linarith [h.b_lt_one])
  have hab := singles_le_recoveredT h
  refine ⟨div_pos (mul_pos h.a_pos (by linarith)) ha,
    (div_le_one ha).2 (by nlinarith),div_pos (mul_pos h.b_pos (by linarith)) hb,
    (div_le_one hb).2 (by nlinarith)⟩

def inferredSource (o : Counts) (h : Domain o) : RawKernel :=
  onePolSource (recoveredT o) (recoveredT_bounds h).1.le (recoveredT_bounds h).2
def inferredLossA (o : Counts) (h : Domain o) : RawLoss :=
  onePolLoss (recoveredTA o) (recoveredLoss_bounds h).1.le (recoveredLoss_bounds h).2.1
def inferredLossB (o : Counts) (h : Domain o) : RawLoss :=
  onePolLoss (recoveredTB o) (recoveredLoss_bounds h).2.2.1.le (recoveredLoss_bounds h).2.2.2

def sourceCounts (s : RawKernel) (a b : RawLoss) : Counts :=
  ⟨bucketSingle s a,bucketSingle s b,bucketJoint s a b⟩

def singleDen (t a : ℝ) : ℝ := 1-t*(1-a)
def jointDen (t a b : ℝ) : ℝ := 1-t*((1-a)*(1-b))

theorem singleDen_pos {t a : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1) (ha : 0 ≤ a) :
    0 < singleDen t a := by
  have := mul_le_mul_of_nonneg_left (show 1-a ≤ 1 by linarith) ht0
  dsimp [singleDen]
  linarith

theorem jointDen_pos {t a b : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1)
    (ha : 0 ≤ a) (_ha1 : a ≤ 1) (hb : 0 ≤ b) (hb1 : b ≤ 1) :
    0 < jointDen t a b := by
  have hx : (1-a)*(1-b) ≤ 1 := by
    nlinarith [mul_nonneg ha (show 0 ≤ 1-b by linarith)]
  have := mul_le_mul_of_nonneg_left hx ht0
  dsimp [jointDen]
  linarith

def scalarCounts (t a b : ℝ) : Counts :=
  ⟨t*a/singleDen t a,t*b/singleDen t b,
    1-(1-t)/singleDen t a-(1-t)/singleDen t b+(1-t)/jointDen t a b⟩

theorem onePol_counts {t a b : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1)
    (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (hb0 : 0 ≤ b) (hb1 : b ≤ 1) :
    sourceCounts (onePolSource t ht0 ht1) (onePolLoss a ha0 ha1)
      (onePolLoss b hb0 hb1) = scalarCounts t a b := by
  have hda := ne_of_gt (singleDen_pos ht0 ht1 ha0)
  have hdb := ne_of_gt (singleDen_pos ht0 ht1 hb0)
  ext <;> dsimp [sourceCounts,scalarCounts,bucketSingle,bucketJoint]
  · rw [noClickA_eq]
    simp only [onePolSource,onePolLoss,sub_zero,div_one,mul_one]
    dsimp [singleDen] at *
    field_simp
    ring
  · rw [noClickA_eq]
    simp only [onePolSource,onePolLoss,sub_zero,div_one,mul_one]
    dsimp [singleDen] at *
    field_simp
    ring
  · rw [noClickA_eq,noClickA_eq,noClickAB_eq]
    simp only [onePolSource,onePolLoss,sub_zero,div_one,mul_one]
    rfl

theorem scalar_vacuum {t a b : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1)
    (ha0 : 0 ≤ a) (hb0 : 0 ≤ b) :
    vacuum (scalarCounts t a b) = (1-t)/jointDen t a b := by
  have hda := ne_of_gt (singleDen_pos ht0 ht1 ha0)
  have hdb := ne_of_gt (singleDen_pos ht0 ht1 hb0)
  dsimp [vacuum,scalarCounts,singleDen] at *
  field_simp
  ring

theorem scalar_delta {t a b : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1)
    (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (hb0 : 0 ≤ b) (hb1 : b ≤ 1) :
    delta (scalarCounts t a b) =
      t*(1-t)*a*b/(singleDen t a*singleDen t b*jointDen t a b) := by
  have hda := ne_of_gt (singleDen_pos ht0 ht1 ha0)
  have hdb := ne_of_gt (singleDen_pos ht0 ht1 hb0)
  have hdu := ne_of_gt (jointDen_pos ht0 ht1 ha0 ha1 hb0 hb1)
  have hdu' : 1-t+t*a-t*a*b+t*b ≠ 0 := by
    convert hdu using 1
    dsimp [jointDen]
    ring
  dsimp [delta,scalarCounts,singleDen,jointDen] at *
  field_simp
  ring_nf
  field_simp [hdu']
  ring

theorem scalar_finite_gap {t a b : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1)
    (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (hb0 : 0 ≤ b) (hb1 : b ≤ 1) :
    delta (scalarCounts t a b)-(scalarCounts t a b).a*(scalarCounts t a b).b*
      vacuum (scalarCounts t a b) = (1-t)*delta (scalarCounts t a b) := by
  rw [scalar_vacuum ht0 ht1 ha0 hb0,scalar_delta ht0 ht1 ha0 ha1 hb0 hb1]
  dsimp [scalarCounts]
  field_simp

theorem scalar_domain {t a b : ℝ} (ht0 : 0 < t) (ht1 : t < 1)
    (ha0 : 0 < a) (ha1 : a ≤ 1) (hb0 : 0 < b) (hb1 : b ≤ 1) :
    Domain (scalarCounts t a b) := by
  have hda := singleDen_pos ht0.le ht1 ha0.le
  have hdb := singleDen_pos ht0.le ht1 hb0.le
  have hdu := jointDen_pos ht0.le ht1 ha0.le ha1 hb0.le hb1
  have hd : 0 < delta (scalarCounts t a b) := by
    rw [scalar_delta ht0.le ht1 ha0.le ha1 hb0.le hb1]
    positivity
  have hau : singleDen t a ≤ jointDen t a b := by
    dsimp [singleDen,jointDen]
    nlinarith [mul_nonneg ht0.le (mul_nonneg (show 0 ≤ 1-a by linarith) hb0.le)]
  have hbu : singleDen t b ≤ jointDen t a b := by
    dsimp [singleDen,jointDen]
    nlinarith [mul_nonneg ht0.le (mul_nonneg (show 0 ≤ 1-b by linarith) ha0.le)]
  have hratioA : (1-t)/jointDen t a b ≤ (1-t)/singleDen t a :=
    div_le_div_of_nonneg_left (by linarith) hda hau
  have hratioB : (1-t)/jointDen t a b ≤ (1-t)/singleDen t b :=
    div_le_div_of_nonneg_left (by linarith) hdb hbu
  have hae : (scalarCounts t a b).a = 1-(1-t)/singleDen t a := by
    dsimp [scalarCounts,singleDen] at *
    field_simp
    ring
  have hbe : (scalarCounts t a b).b = 1-(1-t)/singleDen t b := by
    dsimp [scalarCounts,singleDen] at *
    field_simp
    ring
  refine ⟨div_pos (mul_pos ht0 ha0) hda,?_,div_pos (mul_pos ht0 hb0) hdb,?_,?_,?_,hd,?_⟩
  · apply (div_lt_one hda).2
    dsimp [singleDen]
    linarith
  · apply (div_lt_one hdb).2
    dsimp [singleDen]
    linarith
  · rw [hae]
    dsimp [scalarCounts]
    linarith
  · rw [hbe]
    dsimp [scalarCounts]
    linarith
  · rw [scalar_finite_gap ht0.le ht1 ha0.le ha1 hb0.le hb1]
    exact mul_pos (by linarith) hd

theorem scalar_recovery {t a b : ℝ} (ht0 : 0 < t) (ht1 : t < 1)
    (ha0 : 0 < a) (ha1 : a ≤ 1) (hb0 : 0 < b) (hb1 : b ≤ 1) :
    recoveredT (scalarCounts t a b) = t ∧
    recoveredTA (scalarCounts t a b) = a ∧ recoveredTB (scalarCounts t a b) = b := by
  have hda := ne_of_gt (singleDen_pos ht0.le ht1 ha0.le)
  have hdb := ne_of_gt (singleDen_pos ht0.le ht1 hb0.le)
  have hdu := ne_of_gt (jointDen_pos ht0.le ht1 ha0.le ha1 hb0.le hb1)
  have ht : 1-t ≠ 0 := by linarith
  have ht_eq : recoveredT (scalarCounts t a b) = t := by
    rw [recoveredT,scalar_vacuum ht0.le ht1 ha0.le hb0.le,
      scalar_delta ht0.le ht1 ha0.le ha1 hb0.le hb1]
    dsimp [scalarCounts]
    field_simp [ne_of_gt ht0,ne_of_gt ha0,ne_of_gt hb0,hda,hdb,hdu,ht]
  refine ⟨ht_eq,?_,?_⟩
  · rw [recoveredTA,ht_eq]
    dsimp [scalarCounts,singleDen] at *
    field_simp [ne_of_gt ht0,ht,hda]
    ring_nf
    field_simp [ht]
    ring
  · rw [recoveredTB,ht_eq]
    dsimp [scalarCounts,singleDen] at *
    field_simp [ne_of_gt ht0,ht,hdb]
    ring_nf
    field_simp [ht]
    ring

theorem inverse_denominators {o : Counts} (h : Domain o) :
    singleDen (recoveredT o) (recoveredTA o) = (1-recoveredT o)/(1-o.a) ∧
    singleDen (recoveredT o) (recoveredTB o) = (1-recoveredT o)/(1-o.b) ∧
    jointDen (recoveredT o) (recoveredTA o) (recoveredTB o) =
      (1-recoveredT o)/vacuum o := by
  have ht := ne_of_gt (recoveredT_bounds h).1
  have ha : 1-o.a ≠ 0 := by linarith [h.a_lt_one]
  have hb : 1-o.b ≠ 0 := by linarith [h.b_lt_one]
  have hp := ne_of_gt (outcome_bounds h).2.2.2
  have he : vacuum o*(recoveredT o-o.a*o.b) = recoveredT o*(1-o.a)*(1-o.b) := by
    have hte := recoveredT_equation h
    dsimp [delta,vacuum] at *
    linear_combination hte
  refine ⟨?_,?_,?_⟩
  · dsimp [singleDen,recoveredTA]
    field_simp [ht,ha]
    ring
  · dsimp [singleDen,recoveredTB]
    field_simp [ht,hb]
    ring
  · dsimp [jointDen,recoveredTA,recoveredTB]
    field_simp [ht,ha,hb,hp]
    linear_combination (1-recoveredT o)*he

theorem inverse_scalar_readback {o : Counts} (h : Domain o) :
    scalarCounts (recoveredT o) (recoveredTA o) (recoveredTB o) = o := by
  have ht := recoveredT_bounds h
  have ha : 1-o.a ≠ 0 := by linarith [h.a_lt_one]
  have hb : 1-o.b ≠ 0 := by linarith [h.b_lt_one]
  have htm : 1-recoveredT o ≠ 0 := by linarith
  have hden := inverse_denominators h
  ext
  · change recoveredT o*recoveredTA o/singleDen (recoveredT o) (recoveredTA o) = o.a
    rw [hden.1]
    dsimp [recoveredTA]
    field_simp [ne_of_gt ht.1,ha,htm]
  · change recoveredT o*recoveredTB o/singleDen (recoveredT o) (recoveredTB o) = o.b
    rw [hden.2.1]
    dsimp [recoveredTB]
    field_simp [ne_of_gt ht.1,hb,htm]
  · change 1-(1-recoveredT o)/singleDen (recoveredT o) (recoveredTA o)-
      (1-recoveredT o)/singleDen (recoveredT o) (recoveredTB o)+
      (1-recoveredT o)/jointDen (recoveredT o) (recoveredTA o) (recoveredTB o) = o.j
    rw [hden.1,hden.2.1,hden.2.2]
    field_simp [htm]
    dsimp [vacuum]
    ring

theorem inverse_PGF_readback {o : Counts} (h : Domain o) :
    sourceCounts (inferredSource o h) (inferredLossA o h) (inferredLossB o h) = o ∧
    klyshko (inferredSource o h) (inferredLossA o h) (inferredLossB o h) = some (o.j/o.b) ∧
    klyshko (inferredSource o h) (inferredLossB o h) (inferredLossA o h) = some (o.j/o.a) := by
  have hc : sourceCounts (inferredSource o h) (inferredLossA o h) (inferredLossB o h) = o := by
    rw [inferredSource,inferredLossA,inferredLossB,onePol_counts]
    exact inverse_scalar_readback h
  have hca := congrArg Counts.a hc
  have hcb := congrArg Counts.b hc
  have hcj := congrArg Counts.j hc
  dsimp [sourceCounts] at hca hcb hcj
  have hswap : bucketJoint (inferredSource o h) (inferredLossB o h) (inferredLossA o h) = o.j := by
    rw [bucketJoint]
    have he : noClickAB (inferredSource o h) (inferredLossB o h) (inferredLossA o h) =
        noClickAB (inferredSource o h) (inferredLossA o h) (inferredLossB o h) := by
      simp only [noClickAB,mul_comm]
    rw [he]
    dsimp [bucketJoint] at hcj
    linarith
  refine ⟨hc,?_,?_⟩
  · rw [klyshko,hcb,if_pos h.b_pos,hcj]
  · rw [klyshko,hca,if_pos h.a_pos,hswap]

theorem source_roundtrip {t a b : ℝ} (ht0 : 0 < t) (ht1 : t < 1)
    (ha0 : 0 < a) (ha1 : a ≤ 1) (hb0 : 0 < b) (hb1 : b ≤ 1) :
    let o := sourceCounts (onePolSource t ht0.le ht1) (onePolLoss a ha0.le ha1)
      (onePolLoss b hb0.le hb1)
    Domain o ∧ recoveredT o = t ∧ recoveredTA o = a ∧ recoveredTB o = b := by
  dsimp only
  rw [onePol_counts]
  exact ⟨scalar_domain ht0 ht1 ha0 ha1 hb0 hb1,scalar_recovery ht0 ht1 ha0 ha1 hb0 hb1⟩

theorem nonempty_observed_domain : Domain ⟨(1/3 : ℝ),(1/3 : ℝ),(5/21 : ℝ)⟩ := by
  constructor <;> norm_num [delta,vacuum]

theorem recovered_gain_law {o : Counts} (h : Domain o) :
    0 < recoveredGain o ∧ Real.tanh (recoveredGain o)^2 = recoveredT o := by
  have ht := recoveredT_bounds h
  have hs0 : 0 < Real.sqrt (recoveredT o) := Real.sqrt_pos.mpr ht.1
  have hs1 : Real.sqrt (recoveredT o) < 1 := by
    have hs := Real.sq_sqrt ht.1.le
    have hn := Real.sqrt_nonneg (recoveredT o)
    nlinarith
  refine ⟨Real.artanh_pos ⟨hs0,hs1⟩,?_⟩
  rw [recoveredGain,Real.tanh_artanh ⟨by linarith,hs1⟩,Real.sq_sqrt ht.1.le]

end
end P23.GaussianWindow.Calibration.Observed
