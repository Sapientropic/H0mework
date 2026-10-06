import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic

/-!
A fixed linear branch conversion generates gains from the actual pump input.
State-only readouts forget that input; feedback uses its recorded value and the
same plant's observed gains. The two snapshot realizations are different plants,
not alternative presentations of a single actual control occurrence.
-/

set_option autoImplicit false

namespace P23.FrameWindow.ControlIdentity

noncomputable section

@[ext] structure Gain where
  h : ℝ
  v : ℝ

@[ext] structure Drive where
  u : ℝ
  v : ℝ

structure Plant where
  kH : ℝ
  kV : ℝ
  kH_pos : 0 < kH
  kV_pos : 0 < kV

def generatedGain (p : Plant) (d : Drive) : Gain := ⟨p.kH*d.u, p.kV*d.v⟩
def power (d : Drive) : ℝ := d.u^2+d.v^2
def gainNormSq (g : Gain) : ℝ := g.h^2+g.v^2
def inverseDrive (p : Plant) (g : Gain) : Drive := ⟨g.h/p.kH, g.v/p.kV⟩

theorem inverseDrive_generated (p : Plant) (g : Gain) :
    generatedGain p (inverseDrive p g) = g := by
  ext <;> dsimp [generatedGain, inverseDrive] <;>
    field_simp [ne_of_gt p.kH_pos, ne_of_gt p.kV_pos]

def circleRadius (h v : ℝ) : ℝ := Real.sqrt (h^2+v^2)
def ellipseRadius (h v : ℝ) : ℝ := Real.sqrt (h^2/4+v^2)

theorem circleRadius_pos {h v : ℝ} (hh : 0 < h) : 0 < circleRadius h v := by
  apply Real.sqrt_pos.mpr
  nlinarith [sq_pos_of_pos hh, sq_nonneg v]

theorem ellipseRadius_pos {h v : ℝ} (hv : 0 < v) : 0 < ellipseRadius h v := by
  apply Real.sqrt_pos.mpr
  nlinarith [sq_nonneg h, sq_pos_of_pos hv]

def circlePlant (h v : ℝ) (hh : 0 < h) : Plant where
  kH := circleRadius h v
  kV := circleRadius h v
  kH_pos := circleRadius_pos hh
  kV_pos := circleRadius_pos hh

def ellipsePlant (h v : ℝ) (hv : 0 < v) : Plant where
  kH := 2*ellipseRadius h v
  kV := ellipseRadius h v
  kH_pos := mul_pos (by norm_num) (ellipseRadius_pos hv)
  kV_pos := ellipseRadius_pos hv

def circleDrive (h v : ℝ) (hh : 0 < h) : Drive :=
  inverseDrive (circlePlant h v hh) ⟨h, v⟩
def ellipseDrive (h v : ℝ) (hv : 0 < v) : Drive :=
  inverseDrive (ellipsePlant h v hv) ⟨h, v⟩

theorem circleDrive_unit {h v : ℝ} (hh : 0 < h) : power (circleDrive h v hh) = 1 := by
  have hp := circleRadius_pos (v := v) hh
  have hs : circleRadius h v ^ 2 = h^2+v^2 :=
    Real.sq_sqrt (add_nonneg (sq_nonneg h) (sq_nonneg v))
  dsimp [power, circleDrive, inverseDrive, circlePlant]
  field_simp [ne_of_gt hp]
  nlinarith

theorem ellipseDrive_unit {h v : ℝ} (hv : 0 < v) : power (ellipseDrive h v hv) = 1 := by
  have hp := ellipseRadius_pos (h := h) hv
  have hs : ellipseRadius h v ^ 2 = h^2/4+v^2 :=
    Real.sq_sqrt (add_nonneg (div_nonneg (sq_nonneg h) (by norm_num)) (sq_nonneg v))
  dsimp [power, ellipseDrive, inverseDrive, ellipsePlant]
  field_simp [ne_of_gt hp]
  nlinarith

theorem same_positive_snapshot {h v : ℝ} (hh : 0 < h) (hv : 0 < v) :
    generatedGain (circlePlant h v hh) (circleDrive h v hh) = ⟨h,v⟩ ∧
    generatedGain (ellipsePlant h v hv) (ellipseDrive h v hv) = ⟨h,v⟩ ∧
    power (circleDrive h v hh) = 1 ∧ power (ellipseDrive h v hv) = 1 :=
  ⟨inverseDrive_generated _ _, inverseDrive_generated _ _, circleDrive_unit hh, ellipseDrive_unit hv⟩

theorem snapshot_readout_eq {α : Type*} (f : Gain → α) {h v : ℝ}
    (hh : 0 < h) (hv : 0 < v) :
    f (generatedGain (circlePlant h v hh) (circleDrive h v hh)) =
      f (generatedGain (ellipsePlant h v hv) (ellipseDrive h v hv)) := by
  rw [(same_positive_snapshot hh hv).1, (same_positive_snapshot hh hv).2.1]

theorem calibration_readout_eq {α : Type*} (f : Gain → α) {h v : ℝ}
    (hh : 0 < h) (hv : 0 < v) (calibration : Gain) :
    f (generatedGain (circlePlant h v hh) (inverseDrive (circlePlant h v hh) calibration)) =
      f (generatedGain (ellipsePlant h v hv) (inverseDrive (ellipsePlant h v hv) calibration)) := by
  rw [inverseDrive_generated, inverseDrive_generated]

def rotatePump (d : Drive) (theta : ℝ) : Drive :=
  ⟨d.u*Real.cos theta-d.v*Real.sin theta, d.u*Real.sin theta+d.v*Real.cos theta⟩
def normTangent (p : Plant) (d : Drive) : ℝ := 2*(p.kV^2-p.kH^2)*d.u*d.v

theorem rotatePump_power (d : Drive) (theta : ℝ) : power (rotatePump d theta) = power d := by
  dsimp [power, rotatePump]
  linear_combination (d.u^2+d.v^2)*(Real.sin_sq_add_cos_sq theta)

theorem normTangent_hasDerivAt (p : Plant) (d : Drive) :
    HasDerivAt (fun theta => gainNormSq (generatedGain p (rotatePump d theta)))
      (normTangent p d) 0 := by
  have hu : HasDerivAt (fun theta => d.u*Real.cos theta-d.v*Real.sin theta) (-d.v) 0 := by
    convert! ((Real.hasDerivAt_cos 0).const_mul d.u).sub
      ((Real.hasDerivAt_sin 0).const_mul d.v) using 1
    simp
  have hv : HasDerivAt (fun theta => d.u*Real.sin theta+d.v*Real.cos theta) d.u 0 := by
    convert! ((Real.hasDerivAt_sin 0).const_mul d.u).add
      ((Real.hasDerivAt_cos 0).const_mul d.v) using 1
    simp
  convert! ((hu.const_mul p.kH).pow 2).add ((hv.const_mul p.kV).pow 2) using 1
  dsimp [normTangent]
  simp
  ring

theorem circle_normTangent {h v : ℝ} (hh : 0 < h) :
    normTangent (circlePlant h v hh) (circleDrive h v hh) = 0 := by
  simp [normTangent, circlePlant]

theorem ellipse_normTangent {h v : ℝ} (hv : 0 < v) :
    normTangent (ellipsePlant h v hv) (ellipseDrive h v hv) = -3*h*v := by
  have hp := ellipseRadius_pos (h := h) hv
  dsimp [normTangent, ellipseDrive, inverseDrive, ellipsePlant]
  field_simp [ne_of_gt hp]
  ring

theorem snapshot_control_tangents_differ {h v : ℝ} (hh : 0 < h) (hv : 0 < v) :
    HasDerivAt (fun theta => gainNormSq
      (generatedGain (circlePlant h v hh) (rotatePump (circleDrive h v hh) theta))) 0 0 ∧
    HasDerivAt (fun theta => gainNormSq
      (generatedGain (ellipsePlant h v hv) (rotatePump (ellipseDrive h v hv) theta))) (-3*h*v) 0 ∧
    -3*h*v < 0 := by
  have hC := normTangent_hasDerivAt (circlePlant h v hh) (circleDrive h v hh)
  have hE := normTangent_hasDerivAt (ellipsePlant h v hv) (ellipseDrive h v hv)
  rw [circle_normTangent] at hC
  rw [ellipse_normTangent] at hE
  exact ⟨hC,hE,by nlinarith [mul_pos hh hv]⟩

def recoveredCouplings (d : Drive) (observed : Gain) : Gain :=
  ⟨observed.h/d.u, observed.v/d.v⟩

theorem same_plant_coupling_recovery (p : Plant) (d : Drive) (hu : d.u ≠ 0) (hv : d.v ≠ 0) :
    recoveredCouplings d (generatedGain p d) = ⟨p.kH,p.kV⟩ := by
  ext <;> dsimp [recoveredCouplings, generatedGain] <;> field_simp [hu,hv]

def feedbackDrive (current : Drive) (observed desired : Gain) : Drive :=
  ⟨current.u*desired.h/observed.h, current.v*desired.v/observed.v⟩

theorem observed_gains_nonzero (p : Plant) (d : Drive) (hu : d.u ≠ 0) (hv : d.v ≠ 0) :
    (generatedGain p d).h ≠ 0 ∧ (generatedGain p d).v ≠ 0 :=
  ⟨mul_ne_zero (ne_of_gt p.kH_pos) hu, mul_ne_zero (ne_of_gt p.kV_pos) hv⟩

theorem same_plant_feedback_drive (p : Plant) (d : Drive) (desired : Gain)
    (hu : d.u ≠ 0) (hv : d.v ≠ 0) :
    feedbackDrive d (generatedGain p d) desired = inverseDrive p desired := by
  ext <;> dsimp [feedbackDrive, generatedGain, inverseDrive] <;>
    field_simp [hu,hv,ne_of_gt p.kH_pos,ne_of_gt p.kV_pos]

theorem same_plant_feedback_generated (p : Plant) (d : Drive) (desired : Gain)
    (hu : d.u ≠ 0) (hv : d.v ≠ 0) :
    generatedGain p (feedbackDrive d (generatedGain p d) desired) = desired := by
  rw [same_plant_feedback_drive p d desired hu hv, inverseDrive_generated]

theorem feedback_positive (p : Plant) (d : Drive) (desired : Gain)
    (hu : d.u ≠ 0) (hv : d.v ≠ 0) (hh : 0 < desired.h) (hV : 0 < desired.v) :
    0 < (feedbackDrive d (generatedGain p d) desired).u ∧
      0 < (feedbackDrive d (generatedGain p d) desired).v := by
  rw [same_plant_feedback_drive p d desired hu hv]
  exact ⟨div_pos hh p.kH_pos, div_pos hV p.kV_pos⟩

def hwpRatio (d : Drive) : ℝ := d.v/d.u

theorem feedback_power_readout (p : Plant) (d : Drive) (desired : Gain)
    (hu : d.u ≠ 0) (hv : d.v ≠ 0) :
    power (feedbackDrive d (generatedGain p d) desired) =
      (desired.h/p.kH)^2+(desired.v/p.kV)^2 := by
  rw [same_plant_feedback_drive p d desired hu hv]
  rfl

theorem feedback_hwp_readout (p : Plant) (d : Drive) (desired : Gain)
    (hu : d.u ≠ 0) (hv : d.v ≠ 0) (hh : 0 < desired.h) :
    hwpRatio (feedbackDrive d (generatedGain p d) desired) =
      desired.v*p.kH/(desired.h*p.kV) := by
  rw [same_plant_feedback_drive p d desired hu hv]
  dsimp [hwpRatio,inverseDrive]
  field_simp [ne_of_gt p.kH_pos,ne_of_gt p.kV_pos,ne_of_gt hh]

theorem feedback_state_readout {α : Type*} (f : Gain → α) (p : Plant) (d : Drive)
    (desired : Gain) (hu : d.u ≠ 0) (hv : d.v ≠ 0) :
    f (generatedGain p (feedbackDrive d (generatedGain p d) desired)) = f desired := by
  rw [same_plant_feedback_generated p d desired hu hv]

end
end P23.FrameWindow.ControlIdentity
