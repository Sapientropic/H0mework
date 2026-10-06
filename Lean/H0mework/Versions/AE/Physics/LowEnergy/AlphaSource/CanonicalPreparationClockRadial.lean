import H0mework.Versions.AE.Physics.LowEnergy.AlphaSource.CanonicalPreparationClockPoleSmooth

set_option autoImplicit false
set_option maxHeartbeats 2800000
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationVacuumClockSymbol
open PreparationActualFactor PreparationVacuumClockJacobian PreparationVacuumClockPole
open PreparationVacuumEngineSource PreparationVacuumWeyl GaussHistoryHilbert
open CanonicalPreparationCutoff CanonicalPreparationSquareCutoff PreparationPhaseSource
open scoped BigOperators ContDiff Matrix

def radial (r : ℝ) (zp : Phase) : Phase := (zp.1,r • zp.2)

theorem actualA_radial (r : ℝ) (zp : Phase) : actualA (radial r zp)=r^2*actualA zp := by
  change A (nativePhase zp).1 (nativeCovector (r • zp.2))=_
  rw [show nativeCovector (r • zp.2)=r • nativeCovector zp.2 from nativeCovectorLinear.map_smul _ _,A_smul]
  rfl
theorem actualT_radial (r : ℝ) (zp : Phase) : actualT (radial r zp)=r^2*actualT zp := by
  change T (nativePhase zp).1 (nativeCovector (r • zp.2))=_
  rw [show nativeCovector (r • zp.2)=r • nativeCovector zp.2 from nativeCovectorLinear.map_smul _ _,T_smul]
  rfl
theorem actualS_radial (r : ℝ) (zp : Phase) : actualS (radial r zp)=r^2 • actualS zp := by
  ext i k
  change S (nativePhase zp).1 (nativeCovector (r • zp.2)) i k=r^2*actualS zp i k
  rw [show nativeCovector (r • zp.2)=r • nativeCovector zp.2 from nativeCovectorLinear.map_smul _ _,S_smul]
  rfl
theorem actualC_radial (r : ℝ) (nonzero : r≠0) (zp : Phase) :
    actualC (radial r zp)=actualC zp := by
  change C (nativePhase zp).1 (nativeCovector (r • zp.2))=_
  rw [show nativeCovector (r • zp.2)=r • nativeCovector zp.2 from nativeCovectorLinear.map_smul _ _,C_smul _ _ r nonzero]
  rfl

theorem sourceM_radial (r : ℝ) (zp : Phase) : sourceM (radial r zp)=r^2 • sourceM zp := by
  rw [sourceM,actualT_radial,actualS_radial,sourceM,smul_sub,smul_smul]

theorem sourceDet_radial (r : ℝ) (zp : Phase) : sourceDet (radial r zp)=r^6*sourceDet zp := by
  rw [sourceDet,sourceM_radial,Matrix.det_smul]
  simp only [Fintype.card_fin,sourceDet]
  ring

theorem radial_admitted (r : ℝ) (nonzero : r≠0) (zp : Phase) (admitted : zp∈poleDomain) :
    radial r zp∈poleDomain := by
  refine ⟨⟨admitted.1.1,?_,?_⟩,?_⟩
  · change 0<actualA (radial r zp)
    rw [actualA_radial]; exact mul_pos (sq_pos_of_ne_zero nonzero) admitted.1.2.1
  · change 0<actualT (radial r zp)
    rw [actualT_radial]; exact mul_pos (sq_pos_of_ne_zero nonzero) admitted.1.2.2
  · change sourceDet (radial r zp)≠0
    rw [sourceDet_radial]; exact mul_ne_zero (pow_ne_zero _ nonzero) admitted.2

theorem sourceM_inverse_radial (r : ℝ) (nonzero : r≠0) (zp : Phase) (admitted : zp∈poleDomain) :
    (sourceM (radial r zp))⁻¹=(r^2)⁻¹ • (sourceM zp)⁻¹ := by
  rw [sourceM_radial]
  apply Matrix.inv_eq_right_inv
  rw [Matrix.smul_mul,Matrix.mul_smul,Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr admitted.2),smul_smul]
  simp [pow_ne_zero _ nonzero]

theorem sourceInverse_radial (r : ℝ) (nonzero : r≠0) (zp : Phase) (admitted : zp∈poleDomain) :
    sourceInverse (radial r zp)=(r^2)⁻¹ • sourceInverse zp := by
  ext a b
  refine Fin.cases ?_ (fun i => ?_) a
  · refine Fin.cases ?_ (fun k => ?_) b
    · simp only [Matrix.smul_apply,smul_eq_mul,sourceInverse_clock,actualC_radial r nonzero,actualT_radial]
      field_simp
    · simp only [sourceInverse_clock_shift,Matrix.smul_apply,smul_eq_mul,mul_zero]
  · refine Fin.cases ?_ (fun k => ?_) b
    · simp only [sourceInverse_shift_clock,Matrix.smul_apply,smul_eq_mul,mul_zero]
    · simp only [sourceInverse_shift,actualC_radial r nonzero,
        sourceM_inverse_radial r nonzero zp admitted,Matrix.smul_apply,smul_eq_mul]
      ring

theorem original_engineInverse_radial (r : ℝ) (nonzero : r≠0) (z : FlatConfiguration) (p : PhysicalMomentum)
    (position : z∈thetaPositionClosed) (direction : normalizedMomentum p∈thetaDirectionClosed)
    (momentum : p≠0) :
    (principalForceJacobian (radial r (z,p)))⁻¹=(r^2)⁻¹ • (principalForceJacobian (z,p))⁻¹ := by
  have admitted := source_support_admitted z p position direction momentum
  rw [sourceInverse_native _ (radial_admitted r nonzero _ admitted).1
      (radial_admitted r nonzero _ admitted).2,
    sourceInverse_native _ admitted.1 admitted.2,sourceInverse_radial r nonzero _ admitted]

end LowEnergy.PreparationVacuumClockSymbol
