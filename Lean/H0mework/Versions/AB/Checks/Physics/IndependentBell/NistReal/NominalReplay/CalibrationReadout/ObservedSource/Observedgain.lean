import H0mework.Versions.AB.Checks.Physics.IndependentBell.NistReal.NominalReplay.CalibrationReadout.ObservedSource.Observedsource
import H0mework.Versions.AB.Checks.Physics.IndependentBell.NistReal.NominalReplay.FrameWindow.ControlIdentity.Controlsource

set_option autoImplicit false

namespace P23.GaussianWindow.Calibration.Observed

open P23.FrameWindow.ControlIdentity
noncomputable section

structure Transmission where
  value : ℝ
  positive : 0 < value
  le_one : value ≤ 1

def horizontalLoss (a : Transmission) : RawLoss :=
  onePolLoss a.value a.positive.le a.le_one

def verticalLoss (a : Transmission) : RawLoss where
  h := 0
  v := a.value
  h_nonneg := by norm_num
  h_le_one := by norm_num
  v_nonneg := a.positive.le
  v_le_one := a.le_one

def horizontalCounts (s : RawKernel) (a b : Transmission) : Counts :=
  sourceCounts s (horizontalLoss a) (horizontalLoss b)
def verticalCounts (s : RawKernel) (a b : Transmission) : Counts :=
  sourceCounts s (verticalLoss a) (verticalLoss b)

theorem horizontal_no_click (s : RawKernel) (a : Transmission) :
    noClickA s (horizontalLoss a) = (1-s.tH)/singleDen s.tH a.value := by
  rw [noClickA_eq]
  simp [horizontalLoss,onePolLoss,singleDen,ne_of_gt (sub_pos.mpr s.tV_lt_one)]

theorem horizontal_joint_no_click (s : RawKernel) (a b : Transmission) :
    noClickAB s (horizontalLoss a) (horizontalLoss b) =
      (1-s.tH)/jointDen s.tH a.value b.value := by
  rw [noClickAB_eq]
  simp [horizontalLoss,onePolLoss,jointDen,ne_of_gt (sub_pos.mpr s.tV_lt_one)]

theorem vertical_no_click (s : RawKernel) (a : Transmission) :
    noClickA s (verticalLoss a) = (1-s.tV)/singleDen s.tV a.value := by
  rw [noClickA_eq]
  simp [verticalLoss,singleDen,ne_of_gt (sub_pos.mpr s.tH_lt_one)]

theorem vertical_joint_no_click (s : RawKernel) (a b : Transmission) :
    noClickAB s (verticalLoss a) (verticalLoss b) =
      (1-s.tV)/jointDen s.tV a.value b.value := by
  rw [noClickAB_eq]
  simp [verticalLoss,jointDen,ne_of_gt (sub_pos.mpr s.tH_lt_one)]

theorem horizontal_counts_eq (s : RawKernel) (a b : Transmission) :
    horizontalCounts s a b = scalarCounts s.tH a.value b.value := by
  have hda := ne_of_gt (singleDen_pos s.tH_nonneg s.tH_lt_one a.positive.le)
  have hdb := ne_of_gt (singleDen_pos s.tH_nonneg s.tH_lt_one b.positive.le)
  ext <;> dsimp [horizontalCounts,sourceCounts,scalarCounts,bucketSingle,bucketJoint]
  · rw [horizontal_no_click]
    dsimp [singleDen] at *
    field_simp
    ring
  · rw [horizontal_no_click]
    dsimp [singleDen] at *
    field_simp
    ring
  · rw [horizontal_no_click,horizontal_no_click,horizontal_joint_no_click]

theorem vertical_counts_eq (s : RawKernel) (a b : Transmission) :
    verticalCounts s a b = scalarCounts s.tV a.value b.value := by
  have hda := ne_of_gt (singleDen_pos s.tV_nonneg s.tV_lt_one a.positive.le)
  have hdb := ne_of_gt (singleDen_pos s.tV_nonneg s.tV_lt_one b.positive.le)
  ext <;> dsimp [verticalCounts,sourceCounts,scalarCounts,bucketSingle,bucketJoint]
  · rw [vertical_no_click]
    dsimp [singleDen] at *
    field_simp
    ring
  · rw [vertical_no_click]
    dsimp [singleDen] at *
    field_simp
    ring
  · rw [vertical_no_click,vertical_no_click,vertical_joint_no_click]

def squeezingRatio (g : ℝ) : ℝ := Real.tanh g^2

theorem positive_tanh {g : ℝ} (hg : 0 < g) : 0 < Real.tanh g := by
  rw [Real.tanh_eq]
  exact div_pos (sub_pos.mpr (Real.exp_lt_exp.mpr (by linarith)))
    (add_pos (Real.exp_pos _) (Real.exp_pos _))

theorem squeezingRatio_pos {g : ℝ} (hg : 0 < g) : 0 < squeezingRatio g :=
  sq_pos_of_pos (positive_tanh hg)

def gainKernel (g : Gain) : RawKernel where
  tH := squeezingRatio g.h
  tV := squeezingRatio g.v
  phase := 1
  tH_nonneg := sq_nonneg _
  tH_lt_one := Real.tanh_sq_lt_one _
  tV_nonneg := sq_nonneg _
  tV_lt_one := Real.tanh_sq_lt_one _
  phase_unit := by norm_num

@[ext] structure MatchedCounts where
  h : Counts
  v : Counts

def matchedCounts (s : RawKernel) (aH bH aV bV : Transmission) : MatchedCounts :=
  ⟨horizontalCounts s aH bH,verticalCounts s aV bV⟩

def inverseGain (o : MatchedCounts) : Gain := ⟨recoveredGain o.h,recoveredGain o.v⟩

theorem positive_gain_roundtrip {g : ℝ} (hg : 0 < g) (a b : Transmission) :
    recoveredGain (scalarCounts (squeezingRatio g) a.value b.value) = g := by
  rw [recoveredGain,(scalar_recovery (squeezingRatio_pos hg) (Real.tanh_sq_lt_one _)
    a.positive a.le_one b.positive b.le_one).1]
  rw [squeezingRatio,Real.sqrt_sq (positive_tanh hg).le,Real.artanh_tanh]

theorem same_kernel_gain_recovery (g : Gain) (hh : 0 < g.h) (hv : 0 < g.v)
    (aH bH aV bV : Transmission) :
    Domain (matchedCounts (gainKernel g) aH bH aV bV).h ∧
    Domain (matchedCounts (gainKernel g) aH bH aV bV).v ∧
    inverseGain (matchedCounts (gainKernel g) aH bH aV bV) = g := by
  have hcH := horizontal_counts_eq (gainKernel g) aH bH
  have hcV := vertical_counts_eq (gainKernel g) aV bV
  change horizontalCounts (gainKernel g) aH bH =
    scalarCounts (squeezingRatio g.h) aH.value bH.value at hcH
  change verticalCounts (gainKernel g) aV bV =
    scalarCounts (squeezingRatio g.v) aV.value bV.value at hcV
  refine ⟨?_,?_,?_⟩
  · change Domain (horizontalCounts (gainKernel g) aH bH)
    rw [hcH]
    exact scalar_domain (squeezingRatio_pos hh) (Real.tanh_sq_lt_one _)
      aH.positive aH.le_one bH.positive bH.le_one
  · change Domain (verticalCounts (gainKernel g) aV bV)
    rw [hcV]
    exact scalar_domain (squeezingRatio_pos hv) (Real.tanh_sq_lt_one _)
      aV.positive aV.le_one bV.positive bV.le_one
  · ext
    · change recoveredGain (horizontalCounts (gainKernel g) aH bH) = g.h
      rw [hcH]
      exact positive_gain_roundtrip hh aH bH
    · change recoveredGain (verticalCounts (gainKernel g) aV bV) = g.v
      rw [hcV]
      exact positive_gain_roundtrip hv aV bV

end
end P23.GaussianWindow.Calibration.Observed
