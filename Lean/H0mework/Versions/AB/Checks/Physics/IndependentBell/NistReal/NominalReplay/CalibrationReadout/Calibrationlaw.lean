import H0mework.Versions.AB.Checks.Physics.IndependentBell.NistReal.NominalReplay.GaussianWindow.Gaussiansource

/-! Pair counts and named inclusive-loss calibration from the same raw source. -/

set_option autoImplicit false

namespace P23.GaussianWindow.Calibration

open scoped BigOperators
noncomputable section

def pairAtLeastOne (s : RawKernel) : ℝ := sourceTail s 0
def pairExactlyOne (s : RawKernel) : ℝ := sectorMass s 1
def pairMean (s : RawKernel) : ℝ :=
  mixedFactorialMoment s 1 0 + mixedFactorialMoment s 0 1

theorem pairAtLeastOne_eq (s : RawKernel) :
    pairAtLeastOne s = s.tH + s.tV - s.tH*s.tV := by
  rw [pairAtLeastOne,sourceTail_raw]
  norm_num [Finset.sum_range_succ]
  ring

theorem pairExactlyOne_eq (s : RawKernel) :
    pairExactlyOne s = (1-s.tH)*(1-s.tV)*(s.tH+s.tV) := by
  norm_num [pairExactlyOne,sectorMass,numberMass_raw,Finset.sum_range_succ]
  ring

theorem pairMean_eq (s : RawKernel) :
    pairMean s = s.tH/(1-s.tH) + s.tV/(1-s.tV) := by
  rw [pairMean,mixedFactorialMoment_eq s 1 0,mixedFactorialMoment_eq s 0 1]
  norm_num [meanNumber]

theorem source_pair_quantities (s : RawKernel) :
    pairAtLeastOne s = s.tH+s.tV-s.tH*s.tV ∧
    pairExactlyOne s = (1-s.tH)*(1-s.tV)*(s.tH+s.tV) ∧
    pairMean s = s.tH/(1-s.tH)+s.tV/(1-s.tV) :=
  ⟨pairAtLeastOne_eq s,pairExactlyOne_eq s,pairMean_eq s⟩

structure RawLoss where
  h : ℝ
  v : ℝ
  h_nonneg : 0 ≤ h
  h_le_one : h ≤ 1
  v_nonneg : 0 ≤ v
  v_le_one : v ≤ 1

def noClickA (s : RawKernel) (a : RawLoss) : ℝ := countPGF s (1-a.h) (1-a.v)
def noClickAB (s : RawKernel) (a b : RawLoss) : ℝ :=
  countPGF s ((1-a.h)*(1-b.h)) ((1-a.v)*(1-b.v))
def bucketSingle (s : RawKernel) (a : RawLoss) : ℝ := 1-noClickA s a
def bucketJoint (s : RawKernel) (a b : RawLoss) : ℝ :=
  1-noClickA s a-noClickA s b+noClickAB s a b
def klyshko (s : RawKernel) (a b : RawLoss) : Option ℝ :=
  if 0 < bucketSingle s b then some (bucketJoint s a b / bucketSingle s b) else none

private theorem tz_lt_one {t z : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1) (hz1 : z ≤ 1) :
    t*z < 1 := lt_of_le_of_lt (by nlinarith) ht1

theorem noClickA_eq (s : RawKernel) (a : RawLoss) :
    noClickA s a = ((1-s.tH)/(1-s.tH*(1-a.h))) *
      ((1-s.tV)/(1-s.tV*(1-a.v))) := by
  exact countPGF_eq s (by linarith [a.h_le_one]) (by linarith [a.v_le_one])
    (tz_lt_one s.tH_nonneg s.tH_lt_one (by linarith [a.h_nonneg]))
    (tz_lt_one s.tV_nonneg s.tV_lt_one (by linarith [a.v_nonneg]))

theorem noClickAB_eq (s : RawKernel) (a b : RawLoss) :
    noClickAB s a b = ((1-s.tH)/(1-s.tH*((1-a.h)*(1-b.h)))) *
      ((1-s.tV)/(1-s.tV*((1-a.v)*(1-b.v)))) := by
  have hH0 : 0 ≤ (1-a.h)*(1-b.h) := mul_nonneg
    (by linarith [a.h_le_one]) (by linarith [b.h_le_one])
  have hV0 : 0 ≤ (1-a.v)*(1-b.v) := mul_nonneg
    (by linarith [a.v_le_one]) (by linarith [b.v_le_one])
  have hH1 : (1-a.h)*(1-b.h) ≤ 1 := by
    nlinarith [b.h_nonneg,mul_nonneg a.h_nonneg b.h_nonneg,
      mul_nonneg a.h_nonneg (by linarith [b.h_le_one] : 0 ≤ 1-b.h)]
  have hV1 : (1-a.v)*(1-b.v) ≤ 1 := by
    nlinarith [b.v_nonneg,mul_nonneg a.v_nonneg b.v_nonneg,
      mul_nonneg a.v_nonneg (by linarith [b.v_le_one] : 0 ≤ 1-b.v)]
  exact countPGF_eq s hH0 hV0 (tz_lt_one s.tH_nonneg s.tH_lt_one hH1)
    (tz_lt_one s.tV_nonneg s.tV_lt_one hV1)

def onePolSource (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t < 1) : RawKernel where
  tH := t
  tV := 0
  phase := 1
  tH_nonneg := ht0
  tH_lt_one := ht1
  tV_nonneg := by norm_num
  tV_lt_one := by norm_num
  phase_unit := by norm_num

def onePolLoss (a : ℝ) (ha0 : 0 ≤ a) (ha1 : a ≤ 1) : RawLoss where
  h := a
  v := 0
  h_nonneg := ha0
  h_le_one := ha1
  v_nonneg := by norm_num
  v_le_one := by norm_num

def lossUnion (a b : ℝ) : ℝ := a+b-a*b
def bucketEfficiency (n a b : ℝ) : ℝ :=
  1-(1-a)*(1+n*b)/((1+n*a)*(1+n*lossUnion a b))

private theorem union_nonneg {a b : ℝ} (ha0 : 0 ≤ a) (hb0 : 0 ≤ b) (hb1 : b ≤ 1) :
    0 ≤ lossUnion a b := by
  dsimp [lossUnion]
  nlinarith [mul_nonneg ha0 (by linarith : 0 ≤ 1-b)]

private theorem union_le_one {a b : ℝ} (ha1 : a ≤ 1) (hb1 : b ≤ 1) :
    lossUnion a b ≤ 1 := by
  dsimp [lossUnion]
  nlinarith [mul_nonneg (by linarith : 0 ≤ 1-a) (by linarith : 0 ≤ 1-b)]

theorem efficiency_minus_loss {n a b : ℝ} (hn : 0 ≤ n) (ha0 : 0 ≤ a)
    (hb0 : 0 ≤ b) (hb1 : b ≤ 1) :
    bucketEfficiency n a b-a =
      n*(1-a)*a*(2-b+n*lossUnion a b)/((1+n*a)*(1+n*lossUnion a b)) := by
  have hu := union_nonneg ha0 hb0 hb1
  have ha : 1+n*a ≠ 0 := ne_of_gt (by positivity)
  have hb : 1+n*lossUnion a b ≠ 0 := ne_of_gt (by positivity)
  dsimp [bucketEfficiency,lossUnion] at *
  field_simp
  ring

theorem matched_bucket_increase_bound {n a b : ℝ} (hn : 0 ≤ n) (ha0 : 0 ≤ a)
    (ha1 : a ≤ 1) (hb0 : 0 ≤ b) (hb1 : b ≤ 1) :
    0 ≤ bucketEfficiency n a b-a ∧ bucketEfficiency n a b-a ≤ 2*n := by
  have hu := union_nonneg ha0 hb0 hb1
  have hna : 0 ≤ n*a := mul_nonneg hn ha0
  have hnu : 0 ≤ n*lossUnion a b := mul_nonneg hn hu
  have hD : 0 < (1+n*a)*(1+n*lossUnion a b) := by positivity
  have hf0 : 0 ≤ (1-a)*a := mul_nonneg (by linarith) ha0
  have hf1 : (1-a)*a ≤ 1+n*a := by nlinarith [sq_nonneg a]
  have hbracket : 0 ≤ 2-b+n*lossUnion a b := by linarith
  have hbracket2 : 2-b+n*lossUnion a b ≤ 2*(1+n*lossUnion a b) := by linarith
  rw [efficiency_minus_loss hn ha0 hb0 hb1]
  constructor
  · positivity
  · apply (div_le_iff₀ hD).2
    calc
      n*(1-a)*a*(2-b+n*lossUnion a b) = n*((1-a)*a)*(2-b+n*lossUnion a b) := by ring
      _ ≤ n*((1-a)*a)*(2*(1+n*lossUnion a b)) := by gcongr
      _ ≤ n*(1+n*a)*(2*(1+n*lossUnion a b)) := by gcongr
      _ = 2*n*((1+n*a)*(1+n*lossUnion a b)) := by ring

theorem source_single_pol_no_click {t a : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1)
    (ha0 : 0 ≤ a) (ha1 : a ≤ 1) :
    noClickA (onePolSource t ht0 ht1) (onePolLoss a ha0 ha1) =
      1/(1+meanNumber t*a) := by
  rw [noClickA_eq]
  simp only [onePolSource,onePolLoss,sub_zero,div_one,mul_one]
  have ht : 1-t ≠ 0 := by linarith
  have hd : 1-t*(1-a) ≠ 0 := ne_of_gt (by
    have := tz_lt_one ht0 ht1 (by linarith : 1-a ≤ 1)
    linarith)
  dsimp [meanNumber]
  have hd' : 1-t+t*a ≠ 0 := by convert hd using 1; ring
  field_simp [ht,hd,hd']
  ring

theorem source_single_pol_joint_no_click {t a b : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1)
    (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (hb0 : 0 ≤ b) (hb1 : b ≤ 1) :
    noClickAB (onePolSource t ht0 ht1) (onePolLoss a ha0 ha1) (onePolLoss b hb0 hb1) =
      1/(1+meanNumber t*lossUnion a b) := by
  rw [noClickAB_eq]
  simp only [onePolSource,onePolLoss,sub_zero,div_one,mul_one]
  have hu0 := union_nonneg ha0 hb0 hb1
  have hu1 := union_le_one ha1 hb1
  have ht : 1-t ≠ 0 := by linarith
  have hd : 1-t*(1-lossUnion a b) ≠ 0 := ne_of_gt (by
    have := tz_lt_one ht0 ht1 (by linarith : 1-lossUnion a b ≤ 1)
    linarith)
  have hh : (1-a)*(1-b) = 1-lossUnion a b := by dsimp [lossUnion]; ring
  rw [hh]
  dsimp [meanNumber]
  have hd' : 1-t+t*lossUnion a b ≠ 0 := by convert hd using 1; ring
  field_simp [ht,hd,hd']
  ring

theorem source_matched_klyshko {t a b : ℝ} (ht0 : 0 < t) (ht1 : t < 1)
    (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (hb0 : 0 < b) (hb1 : b ≤ 1) :
    klyshko (onePolSource t (le_of_lt ht0) ht1)
      (onePolLoss a ha0 ha1) (onePolLoss b (le_of_lt hb0) hb1) =
      some (bucketEfficiency (meanNumber t) a b) := by
  have hn : 0 < meanNumber t := div_pos ht0 (by linarith)
  have hu : 0 ≤ lossUnion a b := union_nonneg ha0 (le_of_lt hb0) hb1
  have hA : 0 < 1+meanNumber t*a := by positivity
  have hB : 0 < 1+meanNumber t*b := by positivity
  have hU : 0 < 1+meanNumber t*lossUnion a b := by positivity
  have hsingle : 0 < bucketSingle (onePolSource t (le_of_lt ht0) ht1)
      (onePolLoss b (le_of_lt hb0) hb1) := by
    rw [bucketSingle,source_single_pol_no_click]
    apply sub_pos.mpr
    exact (div_lt_one hB).2 (by nlinarith)
  rw [klyshko,if_pos hsingle]
  congr 1
  rw [bucketJoint,bucketSingle,source_single_pol_no_click,source_single_pol_no_click,
    source_single_pol_joint_no_click]
  have hden : 1-1/(1+meanNumber t*b) ≠ 0 := ne_of_gt (by
    apply sub_pos.mpr
    exact (div_lt_one hB).2 (by nlinarith))
  dsimp [bucketEfficiency]
  field_simp [ne_of_gt hA,ne_of_gt hB,ne_of_gt hU,hden]
  dsimp [lossUnion]
  ring

theorem source_matched_calibration_contract {t a b : ℝ} (ht0 : 0 < t) (ht1 : t < 1)
    (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (hb0 : 0 < b) (hb1 : b ≤ 1) :
    klyshko (onePolSource t (le_of_lt ht0) ht1)
      (onePolLoss a ha0 ha1) (onePolLoss b (le_of_lt hb0) hb1) =
        some (bucketEfficiency (meanNumber t) a b) ∧
    0 ≤ bucketEfficiency (meanNumber t) a b-a ∧
    bucketEfficiency (meanNumber t) a b-a ≤ 2*meanNumber t := by
  exact ⟨source_matched_klyshko ht0 ht1 ha0 ha1 hb0 hb1,
    matched_bucket_increase_bound (le_of_lt (div_pos ht0 (by linarith)))
      ha0 ha1 (le_of_lt hb0) hb1⟩

end
end P23.GaussianWindow.Calibration
