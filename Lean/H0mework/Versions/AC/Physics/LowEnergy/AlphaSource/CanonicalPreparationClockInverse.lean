import H0mework.Versions.AC.Physics.LowEnergy.AlphaSource.CanonicalPreparationClockJacobian
import H0mework.Versions.AC.Physics.LowEnergy.AlphaSource.CanonicalPreparationEngineProgram

set_option autoImplicit false
set_option maxHeartbeats 2800000
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationVacuumClockJacobian
open PreparationActualFactor PreparationVacuumEngineSource
open scoped BigOperators Matrix

def sourceM (zp : Phase) : Matrix (Fin 3) (Fin 3) ℝ := actualT zp • 1-actualS zp

def sourceInverse (zp : Phase) : Matrix (Fin 4) (Fin 4) ℝ := fun a b =>
  Fin.cases (Fin.cases (-actualC zp^3/actualT zp) (fun _ => 0))
    (fun i => Fin.cases 0 (fun j => -actualC zp^3*(sourceM zp)⁻¹ i j)) a b

theorem sourceJ_engine (zp : Phase) : sourceJ zp=principalForceJacobian zp := rfl

theorem forceJacobian_engine (zp : Phase) (cone : nativePhase zp∈positiveCone) :
    forceJacobian zp=principalForceJacobian zp := by
  rw [forceJacobian_sourceJ zp cone,sourceJ_engine]

theorem sourceJ_clock (zp : Phase) : sourceJ zp 0 0=-actualT zp/actualC zp^3 := rfl
theorem sourceJ_clock_shift (zp : Phase) (j : Fin 3) : sourceJ zp 0 (Fin.succ j)=0 := by
  fin_cases j <;> rfl
theorem sourceJ_shift_clock (zp : Phase) (i : Fin 3) : sourceJ zp (Fin.succ i) 0=0 := by
  fin_cases i <;> rfl
theorem sourceJ_shift (zp : Phase) (i j : Fin 3) :
    sourceJ zp (Fin.succ i) (Fin.succ j)=-(sourceM zp i j)/actualC zp^3 := by
  fin_cases i <;> fin_cases j <;> simp [sourceJ,sourceM,Matrix.smul_apply,actualS]

theorem sourceInverse_clock (zp : Phase) : sourceInverse zp 0 0=-actualC zp^3/actualT zp := rfl
theorem sourceInverse_clock_shift (zp : Phase) (j : Fin 3) : sourceInverse zp 0 (Fin.succ j)=0 := rfl
theorem sourceInverse_shift_clock (zp : Phase) (i : Fin 3) : sourceInverse zp (Fin.succ i) 0=0 := rfl
theorem sourceInverse_shift (zp : Phase) (i j : Fin 3) :
    sourceInverse zp (Fin.succ i) (Fin.succ j)=-actualC zp^3*(sourceM zp)⁻¹ i j := rfl

theorem sourceJ_inverse_right (zp : Phase) (cone : nativePhase zp∈positiveCone)
    (pole : (sourceM zp).det≠0) : sourceJ zp*sourceInverse zp=1 := by
  have cne : actualC zp≠0 := (C_positive cone).ne'
  have tne : actualT zp≠0 := cone.2.2.ne'
  have matrix := (sourceM zp).mul_nonsing_inv (isUnit_iff_ne_zero.mpr pole)
  ext a b
  refine Fin.cases ?_ (fun i => ?_) a
  · refine Fin.cases ?_ (fun j => ?_) b
    · rw [Matrix.mul_apply,Fin.sum_univ_succ]
      simp only [sourceJ_clock,sourceInverse_clock,
        sourceJ_clock_shift,sourceInverse_shift_clock,zero_mul,Finset.sum_const_zero,
        add_zero,Matrix.one_apply,if_true]
      field_simp [cne,tne]
    · rw [Matrix.mul_apply,Fin.sum_univ_succ]
      simp only [sourceJ_clock_shift,sourceInverse_clock_shift,
        zero_mul,mul_zero,Finset.sum_const_zero,add_zero,Matrix.one_apply,
        if_neg (Fin.succ_ne_zero j).symm]
  · refine Fin.cases ?_ (fun j => ?_) b
    · rw [Matrix.mul_apply,Fin.sum_univ_succ]
      simp only [sourceJ_shift_clock,sourceInverse_shift_clock,
        zero_mul,mul_zero,Finset.sum_const_zero,add_zero,Matrix.one_apply]
      simp
    · rw [Matrix.mul_apply,Fin.sum_univ_succ]
      simp only [sourceJ_shift_clock,sourceInverse_clock_shift,
        zero_mul,zero_add,sourceJ_shift,sourceInverse_shift]
      have cancel (k : Fin 3) :
          (-(sourceM zp i k)/actualC zp^3)*(-actualC zp^3*(sourceM zp)⁻¹ k j)=
            sourceM zp i k*(sourceM zp)⁻¹ k j := by
        field_simp [cne]
      rw [Finset.sum_congr rfl (fun k _ => cancel k)]
      have image := congrArg (fun L : Matrix (Fin 3) (Fin 3) ℝ => L i j) matrix
      simpa only [Matrix.mul_apply,Matrix.one_apply,Fin.succ_inj] using image

theorem sourceInverse_native (zp : Phase) (cone : nativePhase zp∈positiveCone)
    (pole : (sourceM zp).det≠0) : (principalForceJacobian zp)⁻¹=sourceInverse zp := by
  rw [←sourceJ_engine]
  exact Matrix.inv_eq_right_inv (sourceJ_inverse_right zp cone pole)

theorem sourceInverse_forceJacobian (zp : Phase) (cone : nativePhase zp∈positiveCone)
    (pole : (sourceM zp).det≠0) : (forceJacobian zp)⁻¹=sourceInverse zp := by
  rw [forceJacobian_engine zp cone,sourceInverse_native zp cone pole]

theorem sourceEngine_generated_native (k : ℕ) (a : Fin 4) (zp : Phase)
    (cone : nativePhase zp∈positiveCone) (pole : (sourceM zp).det≠0) :
    sourceEngine (k+1) a (Fin.last (k+1)) zp=
      -∑ b : Fin 4,sourceInverse zp a b*
        forceOrEnergy (k+1) (sourceEngine k) (some b) (Fin.last (k+1)) zp := by
  rw [sourceEngine_generated,sourceInverse_native zp cone pole]

end LowEnergy.PreparationVacuumClockJacobian
