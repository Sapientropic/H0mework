import H0mework.Versions.AD.Checks.Physics.IndependentBell.NistReal.NominalReplay.ObservableClosure.FullStatisticalFiber.Trainingchart
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan

/-! A lawful raw covariance tuple generates its common optical source and phase. -/

set_option autoImplicit false

namespace P23.ObservableClosure.CovarianceSource

open PhaseFiber

noncomputable section

structure Primitive where
  m : ℝ
  z : ℝ
  x : ℝ
  r : ℝ
  loss : ℝ
  m_nonneg : 0 ≤ m
  psd : z^2+x^2 ≤ m^2
  z_pos : 0 < z
  r_pos : 0 < r
  loss_pos : 0 < loss
  loss_le_one : loss ≤ 1
  loss_le_ratio : loss ≤ r

def radius (input : Primitive) : ℝ := Real.sqrt (input.z^2+input.x^2)
def axis (input : Primitive) : ℝ := Real.arctan (input.x/input.z)/2

theorem radius_nonneg (input : Primitive) : 0 ≤ radius input := Real.sqrt_nonneg _

theorem radius_pos (input : Primitive) : 0 < radius input := by
  apply Real.sqrt_pos.2
  nlinarith [sq_pos_of_pos input.z_pos,sq_nonneg input.x]

theorem radius_sq (input : Primitive) : radius input^2=input.z^2+input.x^2 :=
  Real.sq_sqrt (by positivity)

theorem radius_le_m (input : Primitive) : radius input ≤ input.m :=
  (Real.sqrt_le_left input.m_nonneg).2 input.psd

theorem arctan_normalizer (input : Primitive) :
    Real.sqrt (1+(input.x/input.z)^2)=radius input/input.z := by
  apply (Real.sqrt_eq_iff_eq_sq (by positivity)
    (div_nonneg (radius_nonneg input) input.z_pos.le)).2
  simp only [div_pow,radius_sq]
  field_simp [ne_of_gt input.z_pos]

theorem axis_readback (input : Primitive) :
    Real.cos (2*axis input)=input.z/radius input ∧
    Real.sin (2*axis input)=input.x/radius input := by
  have ha : 2*axis input=Real.arctan (input.x/input.z) := by dsimp [axis]; ring
  rw [ha,Real.cos_arctan,Real.sin_arctan,arctan_normalizer]
  constructor <;> field_simp [ne_of_gt input.z_pos,ne_of_gt (radius_pos input)]

/-- All physical fields and the common Jones axis are generated from five raw coordinates. -/
def rawSource (input : Primitive) : RawSource where
  nH := (input.m+radius input)/input.loss
  nV := (input.m-radius input)/input.loss
  etaA := input.loss
  etaB := input.loss/input.r
  delta := axis input
  nH_nonneg := div_nonneg (add_nonneg input.m_nonneg (radius_nonneg input)) input.loss_pos.le
  nV_nonneg := div_nonneg (sub_nonneg.mpr (radius_le_m input)) input.loss_pos.le
  nV_le_nH := div_le_div_of_nonneg_right (by linarith [radius_nonneg input]) input.loss_pos.le
  etaA_pos := input.loss_pos
  etaA_le_one := input.loss_le_one
  etaB_pos := div_pos input.loss_pos input.r_pos
  etaB_le_one := (div_le_one input.r_pos).2 input.loss_le_ratio

structure CoordinatesReadback (s : Snapshot) (input : Primitive) : Prop where
  m_eq : covarianceM s=input.m
  z_eq : covarianceZ s=input.z
  x_eq : covarianceX s=input.x
  ratio_eq : ratio s=input.r
  loss_eq : e s=input.loss

theorem baseline_hv (input : Primitive) :
    h (rawSource input).baseline=input.m+radius input ∧
    v (rawSource input).baseline=input.m-radius input := by
  constructor <;> dsimp [h,v,RawSource.baseline,RawSource.withPhase,rawSource] <;>
    field_simp [ne_of_gt input.loss_pos]

theorem baseline_radius (input : Primitive) :
    covarianceC (rawSource input).baseline=radius input := by
  have hv := baseline_hv input
  dsimp only [covarianceC]
  rw [hv.1,hv.2]
  ring

/-- The constructed source exactly reads back the primitive covariance tuple. -/
theorem baseline_coordinates (input : Primitive) :
    CoordinatesReadback (rawSource input).baseline input := by
  have hv := baseline_hv input
  have ha := axis_readback input
  refine ⟨?_,?_,?_,?_,rfl⟩
  · dsimp only [covarianceM]
    rw [hv.1,hv.2]
    ring
  · dsimp only [covarianceZ]
    rw [baseline_radius]
    change radius input*Real.cos (2*axis input)=input.z
    rw [ha.1]
    field_simp [ne_of_gt (radius_pos input)]
  · dsimp only [covarianceX]
    rw [baseline_radius]
    change radius input*Real.sin (2*axis input)=input.x
    rw [ha.2]
    field_simp [ne_of_gt (radius_pos input)]
  · dsimp [ratio,RawSource.baseline,RawSource.withPhase,rawSource]
    field_simp [ne_of_gt input.loss_pos,ne_of_gt input.r_pos]

def primitiveT2 (input : Primitive) : ℝ :=
  (input.m^2-(input.z^2+input.x^2))*
    ((input.m+input.loss)^2-(input.z^2+input.x^2))

theorem baseline_T2 (input : Primitive) :
    T2 (rawSource input).baseline (e (rawSource input).baseline)=primitiveT2 input := by
  have hc := baseline_coordinates input
  rw [covariance_T2]
  dsimp only [covarianceR2]
  rw [hc.m_eq,hc.z_eq,hc.x_eq,hc.loss_eq]
  rfl

def PhaseDomain (input : Primitive) (k : ℝ) : Prop := k^2 ≤ primitiveT2 input

theorem generated_phase_physical (input : Primitive) (k : ℝ) (hk : PhaseDomain input k) :
    PhysicalPhase (rawSource input) k := by
  apply (physical_phase_iff_square (rawSource input) k).2
  rw [baseline_T2]
  exact hk

/-- PhaseFiber generates lambda internally; no phase endpoint or finished source is supplied. -/
def generatedSnapshot (input : Primitive) (k : ℝ) (hk : PhaseDomain input k) : Snapshot :=
  PhaseFiber.generatedSnapshot (rawSource input) k (generated_phase_physical input k hk)

theorem generated_coordinates (input : Primitive) (k : ℝ) (hk : PhaseDomain input k) :
    CoordinatesReadback (generatedSnapshot input k hk) input := by
  have hc := baseline_coordinates input
  exact ⟨hc.m_eq,hc.z_eq,hc.x_eq,hc.ratio_eq,hc.loss_eq⟩

theorem generated_interference (input : Primitive) (k : ℝ) (hk : PhaseDomain input k) :
    interference (generatedSnapshot input k hk)=k :=
  PhaseFiber.generated_interference (rawSource input) k (generated_phase_physical input k hk)

theorem generated_all_cells (input : Primitive) (k : ℝ) (hk : PhaseDomain input k) :
    ∀ cell, pulse00 (generatedSnapshot input k hk) cell=affinePulse (rawSource input) cell k :=
  PhaseFiber.generated_all_cells (rawSource input) k (generated_phase_physical input k hk)

theorem boundary_pure_mode (input : Primitive) (hp : input.m^2=input.z^2+input.x^2) :
    (rawSource input).nV=0 := by
  have hr : radius input=input.m := by
    dsimp [radius]
    rw [← hp,Real.sqrt_sq input.m_nonneg]
  change (input.m-radius input)/input.loss=0
  rw [hr]
  simp

theorem boundary_zero_T (input : Primitive) (hp : input.m^2=input.z^2+input.x^2) :
    T (rawSource input).baseline=0 :=
  pure_mode_zero_T (rawSource input) (boundary_pure_mode input hp)

theorem boundary_preserves_all_phases (input : Primitive)
    (hp : input.m^2=input.z^2+input.x^2) (lam mu : ℝ)
    (hl0 : 0 ≤ lam) (hl1 : lam ≤ 1) (hm0 : 0 ≤ mu) (hm1 : mu ≤ 1) :
    ∀ cell, pulse00 ((rawSource input).withPhase lam hl0 hl1) cell=
      pulse00 ((rawSource input).withPhase mu hm0 hm1) cell :=
  zero_T_all_phases (rawSource input) (boundary_zero_T input hp) lam mu hl0 hl1 hm0 hm1

end
end P23.ObservableClosure.CovarianceSource
