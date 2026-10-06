import H0mework.Versions.AB.Checks.Physics.IndependentBell.NistReal.NominalReplay.CalibrationReadout.ObservedSource.Observedconsumer
import Mathlib.Algebra.Order.Floor.Defs

set_option autoImplicit false

namespace P23.GaussianWindow.Calibration.Observed.FiniteCount

open P23.FrameWindow.ControlIdentity
noncomputable section

structure Bounds where
  lo : ℝ
  hi : ℝ
  ordered : lo ≤ hi

def InBounds (b : Bounds) (x : ℝ) : Prop := b.lo ≤ x ∧ x ≤ b.hi

structure ObservationBox where
  a : Bounds
  b : Bounds
  j : Bounds

def InObservation (b : ObservationBox) (o : Counts) : Prop :=
  InBounds b.a o.a ∧ InBounds b.b o.b ∧ InBounds b.j o.j

def vacuumLo (b : ObservationBox) : ℝ := 1-b.a.hi-b.b.hi+b.j.lo
def vacuumHi (b : ObservationBox) : ℝ := 1-b.a.lo-b.b.lo+b.j.hi
def deltaLo (b : ObservationBox) : ℝ := b.j.lo-b.a.hi*b.b.hi
def deltaHi (b : ObservationBox) : ℝ := b.j.hi-b.a.lo*b.b.lo

structure WholeDomain (b : ObservationBox) : Prop where
  a_lo_pos : 0 < b.a.lo
  a_hi_lt_one : b.a.hi < 1
  b_lo_pos : 0 < b.b.lo
  b_hi_lt_one : b.b.hi < 1
  j_hi_le_a_lo : b.j.hi ≤ b.a.lo
  j_hi_le_b_lo : b.j.hi ≤ b.b.lo
  delta_lo_pos : 0 < deltaLo b
  finite_gap_lo : 0 < deltaLo b-b.a.hi*b.b.hi*vacuumHi b

theorem vacuumLo_pos {b : ObservationBox} (h : WholeDomain b) : 0 < vacuumLo b := by
  have hp : 0 < (1-b.a.hi)*(1-b.b.hi) :=
    mul_pos (by linarith [h.a_hi_lt_one]) (by linarith [h.b_hi_lt_one])
  have hd := h.delta_lo_pos
  dsimp [vacuumLo,deltaLo] at *
  nlinarith

theorem vacuum_bounds {b : ObservationBox} {o : Counts} (ho : InObservation b o) :
    vacuumLo b ≤ vacuum o ∧ vacuum o ≤ vacuumHi b := by
  rcases ho with ⟨⟨ha0,ha1⟩,⟨hb0,hb1⟩,⟨hj0,hj1⟩⟩
  dsimp [vacuumLo,vacuumHi,vacuum]
  constructor <;> linarith

theorem product_bounds {b : ObservationBox} (h : WholeDomain b) {o : Counts}
    (ho : InObservation b o) :
    b.a.lo*b.b.lo ≤ o.a*o.b ∧ o.a*o.b ≤ b.a.hi*b.b.hi := by
  have ha : 0 ≤ o.a := le_trans h.a_lo_pos.le ho.1.1
  have hb : 0 ≤ o.b := le_trans h.b_lo_pos.le ho.2.1.1
  constructor
  · exact mul_le_mul ho.1.1 ho.2.1.1 h.b_lo_pos.le ha
  · exact mul_le_mul ho.1.2 ho.2.1.2 hb (le_trans h.a_lo_pos.le b.a.ordered)

theorem delta_bounds {b : ObservationBox} (h : WholeDomain b) {o : Counts}
    (ho : InObservation b o) : deltaLo b ≤ delta o ∧ delta o ≤ deltaHi b := by
  have hab := product_bounds h ho
  dsimp [deltaLo,deltaHi,delta]
  constructor <;> linarith [ho.2.2.1,ho.2.2.2,hab.1,hab.2]

theorem whole_box_domain {b : ObservationBox} (h : WholeDomain b) {o : Counts}
    (ho : InObservation b o) : Domain o := by
  have hp := vacuum_bounds ho
  have hd := delta_bounds h ho
  have hab := product_bounds h ho
  have hpa : 0 ≤ vacuum o := le_trans (vacuumLo_pos h).le hp.1
  have hAB : 0 ≤ b.a.hi*b.b.hi := mul_nonneg
    (le_trans h.a_lo_pos.le b.a.ordered) (le_trans h.b_lo_pos.le b.b.ordered)
  have hn : o.a*o.b*vacuum o ≤ b.a.hi*b.b.hi*vacuumHi b :=
    mul_le_mul hab.2 hp.2 hpa hAB
  refine ⟨lt_of_lt_of_le h.a_lo_pos ho.1.1,lt_of_le_of_lt ho.1.2 h.a_hi_lt_one,
    lt_of_lt_of_le h.b_lo_pos ho.2.1.1,lt_of_le_of_lt ho.2.1.2 h.b_hi_lt_one,
    le_trans ho.2.2.2 (le_trans h.j_hi_le_a_lo ho.1.1),
    le_trans ho.2.2.2 (le_trans h.j_hi_le_b_lo ho.2.1.1),
    lt_of_lt_of_le h.delta_lo_pos hd.1,?_⟩
  linarith [h.finite_gap_lo]

def boxCenter (b : ObservationBox) : Counts :=
  ⟨(b.a.lo+b.a.hi)/2,(b.b.lo+b.b.hi)/2,(b.j.lo+b.j.hi)/2⟩

theorem boxCenter_mem (b : ObservationBox) : InObservation b (boxCenter b) := by
  dsimp [InObservation,InBounds,boxCenter]
  exact ⟨⟨by linarith [b.a.ordered],by linarith [b.a.ordered]⟩,
    ⟨by linarith [b.b.ordered],by linarith [b.b.ordered]⟩,
    ⟨by linarith [b.j.ordered],by linarith [b.j.ordered]⟩⟩

def tLo (b : ObservationBox) : ℝ := b.a.lo*b.b.lo*vacuumLo b/deltaHi b
def tHi (b : ObservationBox) : ℝ := b.a.hi*b.b.hi*vacuumHi b/deltaLo b

theorem inverse_t_bounds {b : ObservationBox} (h : WholeDomain b) {o : Counts}
    (ho : InObservation b o) : tLo b ≤ recoveredT o ∧ recoveredT o ≤ tHi b := by
  have hm := whole_box_domain h ho
  have hp := vacuum_bounds ho
  have hd := delta_bounds h ho
  have hab := product_bounds h ho
  have hplo := (vacuumLo_pos h).le
  have hpactual := (outcome_bounds hm).2.2.2.le
  have hAB := mul_pos hm.a_pos hm.b_pos
  have hABhi := mul_pos (lt_of_lt_of_le h.a_lo_pos b.a.ordered)
    (lt_of_lt_of_le h.b_lo_pos b.b.ordered)
  have hnlo : b.a.lo*b.b.lo*vacuumLo b ≤ o.a*o.b*vacuum o :=
    mul_le_mul hab.1 hp.1 hplo hAB.le
  have hnhi : o.a*o.b*vacuum o ≤ b.a.hi*b.b.hi*vacuumHi b :=
    mul_le_mul hab.2 hp.2 hpactual hABhi.le
  constructor
  · exact div_le_div₀ (mul_nonneg hAB.le hpactual) hnlo hm.delta_pos hd.2
  · exact div_le_div₀ (mul_nonneg hABhi.le (le_trans hpactual hp.2))
      hnhi h.delta_lo_pos hd.1

theorem t_envelope_legal {b : ObservationBox} (h : WholeDomain b) :
    0 < tLo b ∧ tLo b ≤ tHi b ∧ tHi b < 1 := by
  have hc := boxCenter_mem b
  have hm := whole_box_domain h hc
  have hd := delta_bounds h hc
  have hb := inverse_t_bounds h hc
  refine ⟨div_pos (mul_pos (mul_pos h.a_lo_pos h.b_lo_pos) (vacuumLo_pos h))
    (lt_of_lt_of_le hm.delta_pos hd.2),le_trans hb.1 hb.2,?_⟩
  apply (div_lt_one h.delta_lo_pos).2
  linarith [h.finite_gap_lo]

def gainOf (t : ℝ) : ℝ := Real.artanh (Real.sqrt t)

theorem gainOf_pos {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) : 0 < gainOf t := by
  have hs0 := Real.sqrt_pos.mpr ht0
  have hs1 : Real.sqrt t < 1 := by
    nlinarith [Real.sq_sqrt ht0.le,Real.sqrt_nonneg t]
  exact Real.artanh_pos ⟨hs0,hs1⟩

theorem gainOf_mono {x y : ℝ} (hy : y < 1) (hxy : x ≤ y) : gainOf x ≤ gainOf y := by
  have hsy : Real.sqrt y < 1 := by
    by_cases hy0 : 0 ≤ y
    · nlinarith [Real.sq_sqrt hy0,Real.sqrt_nonneg y]
    · rw [Real.sqrt_eq_zero_of_nonpos (le_of_not_ge hy0)]
      norm_num
  exact Real.artanh_le_artanh (by linarith [Real.sqrt_nonneg x]) hsy (Real.sqrt_le_sqrt hxy)

theorem inverse_gain_bounds {b : ObservationBox} (h : WholeDomain b) {o : Counts}
    (ho : InObservation b o) : gainOf (tLo b) ≤ recoveredGain o ∧
      recoveredGain o ≤ gainOf (tHi b) := by
  have ht := inverse_t_bounds h ho
  have hr := recoveredT_bounds (whole_box_domain h ho)
  have he := t_envelope_legal h
  exact ⟨gainOf_mono hr.2 ht.1,gainOf_mono he.2.2 ht.2⟩

def dyadicLo (m : ℕ) (x : ℝ) : ℝ := (⌊(2:ℝ)^m*x⌋ : ℝ)/(2:ℝ)^m
def dyadicHi (m : ℕ) (x : ℝ) : ℝ := (⌈(2:ℝ)^m*x⌉ : ℝ)/(2:ℝ)^m

theorem dyadicLo_le (m : ℕ) (x : ℝ) : dyadicLo m x ≤ x := by
  apply (div_le_iff₀ (show 0 < (2:ℝ)^m by positivity)).2
  simpa [mul_comm] using Int.floor_le ((2:ℝ)^m*x)

theorem le_dyadicHi (m : ℕ) (x : ℝ) : x ≤ dyadicHi m x := by
  apply (le_div_iff₀ (show 0 < (2:ℝ)^m by positivity)).2
  simpa [mul_comm] using Int.le_ceil ((2:ℝ)^m*x)

theorem dyadicLo_nonneg (m : ℕ) {x : ℝ} (hx : 0 ≤ x) : 0 ≤ dyadicLo m x := by
  apply div_nonneg ?_ (by positivity)
  exact_mod_cast (Int.floor_nonneg.mpr (mul_nonneg (by positivity : 0 ≤ (2:ℝ)^m) hx))

def gainEnvelope (b : ObservationBox) (h : WholeDomain b) (m : ℕ) : Bounds where
  lo := dyadicLo m (gainOf (tLo b))
  hi := dyadicHi m (gainOf (tHi b))
  ordered := le_trans (dyadicLo_le _ _) (le_trans
    (gainOf_mono (t_envelope_legal h).2.2 (t_envelope_legal h).2.1) (le_dyadicHi _ _))

def midpoint (b : Bounds) : ℝ := (b.lo+b.hi)/2

theorem gainEnvelope_legality {b : ObservationBox} (h : WholeDomain b) (m : ℕ) :
    0 ≤ (gainEnvelope b h m).lo ∧ 0 < (gainEnvelope b h m).hi ∧
      0 < midpoint (gainEnvelope b h m) := by
  have ht := t_envelope_legal h
  have hlo := dyadicLo_nonneg m (gainOf_pos ht.1 (lt_of_le_of_lt ht.2.1 ht.2.2)).le
  have hhi := lt_of_lt_of_le (gainOf_pos (lt_of_lt_of_le ht.1 ht.2.1) ht.2.2)
    (le_dyadicHi m (gainOf (tHi b)))
  exact ⟨hlo,hhi,by dsimp [midpoint,gainEnvelope]; linarith⟩

theorem gain_midpoint_rational (b : ObservationBox) (h : WholeDomain b) (m : ℕ) :
    ∃ q : ℚ, (q : ℝ) = midpoint (gainEnvelope b h m) := by
  refine ⟨((⌊(2:ℝ)^m*gainOf (tLo b)⌋ : ℚ)/(2:ℚ)^m+
    (⌈(2:ℝ)^m*gainOf (tHi b)⌉ : ℚ)/(2:ℚ)^m)/2,?_⟩
  dsimp [midpoint,gainEnvelope,dyadicLo,dyadicHi]
  push_cast
  rfl

theorem inverse_gain_enclosed {b : ObservationBox} (h : WholeDomain b) (m : ℕ)
    {o : Counts} (ho : InObservation b o) : InBounds (gainEnvelope b h m) (recoveredGain o) := by
  have hg := inverse_gain_bounds h ho
  exact ⟨le_trans (dyadicLo_le _ _) hg.1,le_trans hg.2 (le_dyadicHi _ _)⟩

theorem same_kernel_box_readback (g : Gain) (hh : 0 < g.h) (hv : 0 < g.v)
    (aH bH aV bV : Transmission) (boxH boxV : ObservationBox)
    (hH : WholeDomain boxH) (hV : WholeDomain boxV) (m : ℕ)
    (coverH : InObservation boxH (matchedCounts (gainKernel g) aH bH aV bV).h)
    (coverV : InObservation boxV (matchedCounts (gainKernel g) aH bH aV bV).v) :
    Domain (matchedCounts (gainKernel g) aH bH aV bV).h ∧
    Domain (matchedCounts (gainKernel g) aH bH aV bV).v ∧
    (tLo boxH ≤ (gainKernel g).tH ∧ (gainKernel g).tH ≤ tHi boxH) ∧
    (tLo boxV ≤ (gainKernel g).tV ∧ (gainKernel g).tV ≤ tHi boxV) ∧
    InBounds (gainEnvelope boxH hH m) g.h ∧ InBounds (gainEnvelope boxV hV m) g.v := by
  have hs := same_kernel_gain_recovery g hh hv aH bH aV bV
  have hth := inverse_t_bounds hH coverH
  have htv := inverse_t_bounds hV coverV
  have hhg := inverse_gain_enclosed hH m coverH
  have hvg := inverse_gain_enclosed hV m coverV
  have htrH : recoveredT (matchedCounts (gainKernel g) aH bH aV bV).h = (gainKernel g).tH := by
    change recoveredT (horizontalCounts (gainKernel g) aH bH) = squeezingRatio g.h
    rw [horizontal_counts_eq]
    exact (scalar_recovery (squeezingRatio_pos hh) (Real.tanh_sq_lt_one _)
      aH.positive aH.le_one bH.positive bH.le_one).1
  have htrV : recoveredT (matchedCounts (gainKernel g) aH bH aV bV).v = (gainKernel g).tV := by
    change recoveredT (verticalCounts (gainKernel g) aV bV) = squeezingRatio g.v
    rw [vertical_counts_eq]
    exact (scalar_recovery (squeezingRatio_pos hv) (Real.tanh_sq_lt_one _)
      aV.positive aV.le_one bV.positive bV.le_one).1
  rw [htrH] at hth
  rw [htrV] at htv
  have hgrH := congrArg Gain.h hs.2.2
  have hgrV := congrArg Gain.v hs.2.2
  change recoveredGain (matchedCounts (gainKernel g) aH bH aV bV).h = g.h at hgrH
  change recoveredGain (matchedCounts (gainKernel g) aH bH aV bV).v = g.v at hgrV
  rw [hgrH] at hhg
  rw [hgrV] at hvg
  exact ⟨hs.1,hs.2.1,hth,htv,hhg,hvg⟩

def estimatedGain (boxH boxV : ObservationBox) (hH : WholeDomain boxH)
    (hV : WholeDomain boxV) (m : ℕ) : Gain :=
  ⟨midpoint (gainEnvelope boxH hH m),midpoint (gainEnvelope boxV hV m)⟩

theorem feedback_gain_formula (p : Plant) (current : Drive) (estimate desired : Gain) :
    generatedGain p (feedbackDrive current estimate desired) =
      ⟨(generatedGain p current).h*desired.h/estimate.h,
        (generatedGain p current).v*desired.v/estimate.v⟩ := by
  ext <;> dsimp [generatedGain,feedbackDrive] <;> ring

theorem same_plant_bounded_count_feedback (p : Plant) (current : Drive)
    (hu : 0 < current.u) (hv : 0 < current.v) (desired : Gain)
    (hh : 0 < desired.h) (hV : 0 < desired.v) (aH bH aV bV : Transmission)
    (boxH boxV : ObservationBox) (hboxH : WholeDomain boxH) (hboxV : WholeDomain boxV) (m : ℕ)
    (coverH : InObservation boxH
      (matchedCounts (gainKernel (generatedGain p current)) aH bH aV bV).h)
    (coverV : InObservation boxV
      (matchedCounts (gainKernel (generatedGain p current)) aH bH aV bV).v) :
    let rangeH := gainEnvelope boxH hboxH m
    let rangeV := gainEnvelope boxV hboxV m
    let estimate := estimatedGain boxH boxV hboxH hboxV m
    let update := feedbackDrive current estimate desired
    InBounds rangeH (generatedGain p current).h ∧
    InBounds rangeV (generatedGain p current).v ∧
    (rangeH.lo/current.u ≤ p.kH ∧ p.kH ≤ rangeH.hi/current.u) ∧
    (rangeV.lo/current.v ≤ p.kV ∧ p.kV ≤ rangeV.hi/current.v) ∧
    0 < estimate.h ∧ 0 < estimate.v ∧ 0 < update.u ∧ 0 < update.v ∧
    (desired.h*rangeH.lo/estimate.h ≤ (generatedGain p update).h ∧
      (generatedGain p update).h ≤ desired.h*rangeH.hi/estimate.h) ∧
    (desired.v*rangeV.lo/estimate.v ≤ (generatedGain p update).v ∧
      (generatedGain p update).v ≤ desired.v*rangeV.hi/estimate.v) ∧
    power update = (current.u*desired.h/estimate.h)^2+(current.v*desired.v/estimate.v)^2 ∧
    hwpRatio update = current.v*desired.v*estimate.h/(current.u*desired.h*estimate.v) := by
  have hgH : 0 < (generatedGain p current).h := mul_pos p.kH_pos hu
  have hgV : 0 < (generatedGain p current).v := mul_pos p.kV_pos hv
  have hs := same_kernel_box_readback (generatedGain p current) hgH hgV aH bH aV bV
    boxH boxV hboxH hboxV m coverH coverV
  have hboundH := hs.2.2.2.2.1
  have hboundV := hs.2.2.2.2.2
  have heH : 0 < (estimatedGain boxH boxV hboxH hboxV m).h := (gainEnvelope_legality hboxH m).2.2
  have heV : 0 < (estimatedGain boxH boxV hboxH hboxV m).v := (gainEnvelope_legality hboxV m).2.2
  have hkH : (gainEnvelope boxH hboxH m).lo/current.u ≤ p.kH ∧
      p.kH ≤ (gainEnvelope boxH hboxH m).hi/current.u := by
    dsimp [InBounds,generatedGain] at hboundH
    exact ⟨(div_le_iff₀ hu).2 hboundH.1,(le_div_iff₀ hu).2 hboundH.2⟩
  have hkV : (gainEnvelope boxV hboxV m).lo/current.v ≤ p.kV ∧
      p.kV ≤ (gainEnvelope boxV hboxV m).hi/current.v := by
    dsimp [InBounds,generatedGain] at hboundV
    exact ⟨(div_le_iff₀ hv).2 hboundV.1,(le_div_iff₀ hv).2 hboundV.2⟩
  dsimp only
  refine ⟨hboundH,hboundV,hkH,hkV,heH,heV,
    div_pos (mul_pos hu hh) heH,div_pos (mul_pos hv hV) heV,?_,?_,rfl,?_⟩
  · rw [feedback_gain_formula]
    dsimp only
    constructor
    · apply div_le_div_of_nonneg_right ?_ heH.le
      nlinarith [hboundH.1]
    · apply div_le_div_of_nonneg_right ?_ heH.le
      nlinarith [hboundH.2]
  · rw [feedback_gain_formula]
    dsimp only
    constructor
    · apply div_le_div_of_nonneg_right ?_ heV.le
      nlinarith [hboundV.1]
    · apply div_le_div_of_nonneg_right ?_ heV.le
      nlinarith [hboundV.2]
  · dsimp [hwpRatio,feedbackDrive]
    field_simp [ne_of_gt hu,ne_of_gt hh,ne_of_gt heH,ne_of_gt heV]

end
end P23.GaussianWindow.Calibration.Observed.FiniteCount
