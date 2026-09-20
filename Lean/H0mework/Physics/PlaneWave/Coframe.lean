import H0mework.Physics.CoframeJets.CoframeFirstJet

/-! A fixed null shear over the global logarithmic AdS chart. The radial
coordinate is x2; the wave covector is dt − dx3. No time/spatial frame swap
is used. The two scale arguments remain raw geometric material. -/

set_option autoImplicit false

namespace SaturationMonoid.PhysicsCore.Stage9C.Dynamics.PlaneWave

open ProofFreeRicherAnholonomicSource
open StageNineCoframeFirstJet
open StageNineHolonomicField
open scoped Matrix

noncomputable section

def adsCoframeScale (q : ℝ) : LorentzianCoframe :=
  Matrix.diagonal ![q, q, 1, q]

theorem adsCoframeScale_det (q : ℝ) : (adsCoframeScale q).det = q ^ 3 := by
  simp [adsCoframeScale, Matrix.det_diagonal, Fin.prod_univ_four]
  ring

theorem adsCoframeScale_inv (q : ℝ) (hq : q ≠ 0) :
    (adsCoframeScale q)⁻¹ = adsCoframeScale q⁻¹ := by
  apply Matrix.inv_eq_left_inv
  ext row column
  fin_cases row <;> fin_cases column <;>
    simp [adsCoframeScale, Matrix.mul_apply, Fin.sum_univ_four, hq]

theorem adsCoframeScale_metric (q : ℝ) :
    lorentzianMetricOfCoframe (adsCoframeScale q) =
      Matrix.diagonal ![-q ^ 2, q ^ 2, 1, q ^ 2] := by
  ext row column
  fin_cases row <;> fin_cases column <;>
    simp [lorentzianMetricOfCoframe, adsCoframeScale, minkowskiInternalMetric,
      Matrix.mul_apply, Fin.sum_univ_four] <;> ring

def nullShear (H : ℝ) : LorentzianCoframe :=
  !![1-H/2,0,0,H/2; 0,1,0,0; 0,0,1,0; -H/2,0,0,1+H/2]

theorem nullShear_mul (H K : ℝ) : nullShear H * nullShear K = nullShear (H+K) := by
  ext row column
  fin_cases row <;> fin_cases column <;>
    simp [nullShear, Matrix.mul_apply, Fin.sum_univ_four] <;> ring

@[simp] theorem nullShear_zero : nullShear 0 = 1 := by
  ext row column
  fin_cases row <;> fin_cases column <;> simp [nullShear]

theorem nullShear_det (H : ℝ) : (nullShear H).det = 1 := by
  rw [Matrix.det_succ_row_zero]
  simp +decide [nullShear, Fin.sum_univ_four, Matrix.det_fin_three]
  change (1-H/2)*(1+H/2) + -(H/2*(1*1*(-H/2)-0*0*(-H/2))) = 1
  ring

theorem nullShear_inv (H : ℝ) : (nullShear H)⁻¹ = nullShear (-H) := by
  apply Matrix.inv_eq_left_inv
  rw [nullShear_mul, neg_add_cancel, nullShear_zero]

def siklosCoframeScale (q H : ℝ) : LorentzianCoframe :=
  adsCoframeScale q * nullShear H

theorem siklosCoframeScale_det (q H : ℝ) : (siklosCoframeScale q H).det = q ^ 3 := by
  rw [siklosCoframeScale, Matrix.det_mul, adsCoframeScale_det, nullShear_det, mul_one]

theorem siklosCoframeScale_inv (q H : ℝ) (hq : q ≠ 0) :
    (siklosCoframeScale q H)⁻¹ = nullShear (-H) * adsCoframeScale q⁻¹ := by
  rw [siklosCoframeScale, Matrix.mul_inv_rev, nullShear_inv, adsCoframeScale_inv q hq]

def adsScale (point : BasePoint) : ℝ := Real.exp (-point 2)

def siklosCoframe (H : BasePoint → ℝ) (point : BasePoint) : LorentzianCoframe :=
  siklosCoframeScale (adsScale point) (H point)

theorem siklosCoframe_nondegenerate (H : BasePoint → ℝ) (point : BasePoint) :
    (siklosCoframe H point).det ≠ 0 := by
  rw [siklosCoframe, siklosCoframeScale_det]
  exact pow_ne_zero 3 (Real.exp_ne_zero _)

end
end SaturationMonoid.PhysicsCore.Stage9C.Dynamics.PlaneWave
