import H0mework.Versions.AB.Physics.LowEnergyEvolution.Gauge

/-! Orthogonal coordinate rotations act on the original coframe Hodge by its actual exterior square. -/
set_option autoImplicit false
namespace SaturationMonoid.PhysicsCore.LowEnergy.Rotation
open ProofFreeRicherAnholonomicSource StageNineGlobalIntegratedAction StageNineBlockwiseConstitutive
open StageNineCoframeTwoFormPairing
noncomputable section

def rotateZ (c s : ℝ) : LorentzianCoframe :=
  !![1,0,0,0; 0,c,s,0; 0,-s,c,0; 0,0,0,1]

def rotateY (c s : ℝ) : LorentzianCoframe :=
  !![1,0,0,0; 0,c,0,-s; 0,0,1,0; 0,s,0,c]

theorem rotateZ_orthogonal (c s : ℝ) (unit : c^2+s^2=1) :
    (rotateZ c s).transpose*rotateZ c s = 1 := by
  ext row col
  fin_cases row <;> fin_cases col <;>
    simp [rotateZ, Matrix.mul_apply, Fin.sum_univ_four] <;> nlinarith [unit]

theorem rotateY_orthogonal (c s : ℝ) (unit : c^2+s^2=1) :
    (rotateY c s).transpose*rotateY c s = 1 := by
  ext row col
  fin_cases row <;> fin_cases col <;>
    simp [rotateY, Matrix.mul_apply, Fin.sum_univ_four] <;> nlinarith [unit]

theorem rotateZ_det (c s : ℝ) (unit : c^2+s^2=1) : (rotateZ c s).det = 1 := by
  rw [Matrix.det_succ_row_zero]
  simp [rotateZ, Fin.sum_univ_four, Matrix.det_fin_three]
  nlinarith [unit]

theorem rotateY_det (c s : ℝ) (unit : c^2+s^2=1) : (rotateY c s).det = 1 := by
  rw [Matrix.det_succ_row_zero]
  simp [rotateY, Fin.sum_univ_four, Matrix.det_fin_three]
  nlinarith [unit]

theorem orthogonal_hodge_pullback (coframe rotation : LorentzianCoframe)
    (orthogonal : rotation.transpose*rotation=1) (form : GaugeTwoForm) :
    coframeGaugeSpacetimeHodgeLinear (coframe*rotation)
      (coframeTwoFormLinear rotation.transpose form) =
      coframeTwoFormLinear rotation.transpose (coframeGaugeSpacetimeHodgeLinear coframe form) := by
  have inverse : rotation⁻¹ = rotation.transpose := Matrix.inv_eq_left_inv orthogonal
  have reverse : rotation*rotation.transpose=1 := mul_eq_one_comm.mp orthogonal
  unfold coframeGaugeSpacetimeHodgeLinear inverseCoframeTwoFormLinear
  rw [Matrix.mul_inv_rev, inverse, coframeTwoFormLinear_mul, coframeTwoFormLinear_mul]
  simp only [LinearMap.comp_apply]
  have cancel : coframeTwoFormLinear rotation (coframeTwoFormLinear rotation.transpose form) = form := by
    rw [← LinearMap.comp_apply, ← coframeTwoFormLinear_mul, reverse, coframeTwoFormLinear_one]
    rfl
  rw [cancel]

theorem rotateZ_hodge_commutes (c s : ℝ) (unit : c^2+s^2=1) (form : GaugeTwoForm) :
    coframeTwoFormLinear (rotateZ c s) (lorentzianCoframeHodge form) =
      lorentzianCoframeHodge (coframeTwoFormLinear (rotateZ c s) form) := by
  funext pair
  fin_cases pair <;>
    simp [coframeTwoFormLinear, coframeWedge, rotateZ, lorentzianCoframeHodge,
      pairFirst, pairSecond, Fin.sum_univ_six] <;>
    nlinarith [congrArg (fun value : ℝ => value*form 5) unit,
      congrArg (fun value : ℝ => value*form 2) unit]

theorem rotateY_hodge_commutes (c s : ℝ) (unit : c^2+s^2=1) (form : GaugeTwoForm) :
    coframeTwoFormLinear (rotateY c s) (lorentzianCoframeHodge form) =
      lorentzianCoframeHodge (coframeTwoFormLinear (rotateY c s) form) := by
  funext pair
  fin_cases pair <;>
    simp [coframeTwoFormLinear, coframeWedge, rotateY, lorentzianCoframeHodge,
      pairFirst, pairSecond, Fin.sum_univ_six] <;>
    nlinarith [congrArg (fun value : ℝ => value*form 4) unit,
      congrArg (fun value : ℝ => value*form 1) unit]

end
end SaturationMonoid.PhysicsCore.LowEnergy.Rotation
