import H0mework.Versions.CAP.Physics.LowEnergy.AlphaSource.CanonicalPreparationClockTimeDifferential

set_option autoImplicit false
set_option maxHeartbeats 3500000
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationVacuumClockJacobian
open PreparationActualFactor
open scoped BigOperators Topology

def numeratorSecond (zp : Phase) (a : Fin 4) : Time →L[ℝ] ℝ :=
  (axis a 0) • ((actualT zp) • ((2 : ℝ) • coordinate 0))-
    ∑ i : Fin 3,∑ j : Fin 3,
      ((axis a (Fin.succ j)) • ((actualS zp i j) • coordinate (Fin.succ i))+
        (axis a (Fin.succ i)) • ((actualS zp i j) • coordinate (Fin.succ j)))
def shiftSquareSecond (a : Fin 4) : Time →L[ℝ] ℝ :=
  ∑ i : Fin 3,(axis a (Fin.succ i)) • ((2 : ℝ) • coordinate (Fin.succ i))
def denominatorSecond (a : Fin 4) (y : Time) : Time →L[ℝ] ℝ :=
  (2*y 0) • ((axis a 0) • ((2 : ℝ) • coordinate 0)-shiftSquareSecond a)+
    ((2*y 0)*(axis a 0)-shiftSquareD y (axis a)) • ((2 : ℝ) • coordinate 0)+
    (2*(axis a 0)) • ((2*y 0) • coordinate 0-shiftSquareD y)

theorem numeratorSecond_hasFDeriv (zp : Phase) (a : Fin 4) (y : Time) :
    HasFDerivAt (fun v => numeratorD zp v (axis a)) (numeratorSecond zp a) y := by
  have linear := (((coordinate 0).hasFDerivAt (x:=y)).const_mul 2).mul_const (actualT zp) |>.mul_const (axis a 0)
  have quadratic (i j : Fin 3) :=
    ((((coordinate (Fin.succ i)).hasFDerivAt (x:=y)).mul_const (actualS zp i j)).mul_const (axis a (Fin.succ j))).add
      ((((coordinate (Fin.succ j)).hasFDerivAt (x:=y)).mul_const (actualS zp i j)).mul_const (axis a (Fin.succ i)))
  have result := linear.sub (HasFDerivAt.fun_sum (u:=Finset.univ) fun i _ =>
    HasFDerivAt.fun_sum (u:=Finset.univ) fun j _ => quadratic i j)
  simpa [numeratorD,numeratorSecond,coordinate,mul_comm,mul_left_comm,mul_assoc,smul_smul] using! result

theorem shiftSquareSecond_hasFDeriv (a : Fin 4) (y : Time) :
    HasFDerivAt (fun v => shiftSquareD v (axis a)) (shiftSquareSecond a) y := by
  have result := HasFDerivAt.fun_sum (u:=Finset.univ) fun i _ =>
    (((coordinate (Fin.succ i)).hasFDerivAt (x:=y)).const_mul 2).mul_const (axis a (Fin.succ i))
  simpa only [shiftSquareD,shiftSquareSecond,sum_apply,smul_apply,
    smul_eq_mul,coordinate,ContinuousLinearMap.proj_apply] using! result

theorem denominatorSecond_hasFDeriv (a : Fin 4) (y : Time) :
    HasFDerivAt (fun v => denominatorD v (axis a)) (denominatorSecond a y) y := by
  have n := ((coordinate 0).hasFDerivAt (x:=y)).const_mul 2
  have first := n.mul ((n.mul_const (axis a 0)).sub (shiftSquareSecond_hasFDeriv a y))
  have last := (((coordinate 0).hasFDerivAt (x:=y)).pow 2 |>.sub (shiftSquare_hasFDeriv y)).mul_const (2*(axis a 0))
  simpa [denominatorD,denominatorSecond,coordinate,nsmul_eq_mul] using! first.add last

private theorem inv_derivative {f : Time → ℝ} {L : Time →L[ℝ] ℝ} {y : Time}
    (derivative : HasFDerivAt f L y) (regular : f y≠0) :
    HasFDerivAt (fun v => (f v)⁻¹) ((-(f y^2)⁻¹) • L) y := by
  convert! ((hasDerivAt_inv regular).hasFDerivAt.comp y derivative) using 1
  ext v
  simp [mul_comm]

def forceD (zp : Phase) (a : Fin 4) (y : Time) : Time →L[ℝ] ℝ :=
  -((denominator y)⁻¹ • numeratorSecond zp a+
    numeratorD zp y (axis a) • ((-(denominator y^2)⁻¹) • denominatorD y)+
    (numerator zp y*(-(denominator y^2)⁻¹)) • denominatorSecond a y+
    denominatorD y (axis a) •
      (numerator zp y • (((denominator y^2)^2)⁻¹ • ((2*denominator y) • denominatorD y))+
        (-(denominator y^2)⁻¹) • numeratorD zp y))

theorem forceExpression_hasFDeriv (zp : Phase) (a : Fin 4) (y : Time) (regular : denominator y≠0) :
    HasFDerivAt (fun v => -hamiltonianD zp v (axis a)) (forceD zp a y) y := by
  have inverse := inv_derivative (denominator_hasFDeriv y) regular
  have inverseSquare := (inv_derivative ((denominator_hasFDeriv y).pow 2) (pow_ne_zero 2 regular)).neg
  have first := inverse.mul (numeratorSecond_hasFDeriv zp a y)
  have last := ((numerator_hasFDeriv zp y).mul inverseSquare).mul (denominatorSecond_hasFDeriv a y)
  have result := ((hasFDerivAt_const (actualA zp*(axis a 0)) y).add first |>.add last).neg
  convert! result using 1
  · funext v
    simp only [hamiltonianD,add_apply,smul_apply,
      smul_eq_mul,coordinate,ContinuousLinearMap.proj_apply,Pi.add_apply,Pi.mul_apply,Pi.neg_apply]
    ring
  · ext v
    simp [forceD,nsmul_eq_mul]
    ring

def forceJacobian (zp : Phase) : Matrix (Fin 4) (Fin 4) ℝ := fun a b =>
  fderiv ℝ (fun y => force zp y a) (baseTime zp) (axis b)

def sourceJ (zp : Phase) : Matrix (Fin 4) (Fin 4) ℝ :=
  !![-actualT zp/actualC zp^3,0,0,0;
    0,(actualS zp 0 0-actualT zp)/actualC zp^3,actualS zp 0 1/actualC zp^3,actualS zp 0 2/actualC zp^3;
    0,actualS zp 1 0/actualC zp^3,(actualS zp 1 1-actualT zp)/actualC zp^3,actualS zp 1 2/actualC zp^3;
    0,actualS zp 2 0/actualC zp^3,actualS zp 2 1/actualC zp^3,(actualS zp 2 2-actualT zp)/actualC zp^3]

theorem forceJacobian_sourceJ (zp : Phase) (cone : nativePhase zp∈positiveCone) :
    forceJacobian zp=sourceJ zp := by
  have nonzero : actualC zp≠0 := (C_positive cone).ne'
  have regular := base_regular zp nonzero
  have continuous : Continuous denominator := by unfold denominator shiftSquare; fun_prop
  ext a b
  have germ : (fun y => force zp y a)=ᶠ[𝓝 (baseTime zp)]
      (fun y => -hamiltonianD zp y (axis a)) := by
    filter_upwards [continuous.continuousAt.eventually_ne regular] with y hy
    exact force_readback zp y hy a
  change fderiv ℝ (fun y => force zp y a) (baseTime zp) (axis b)=_
  rw [germ.fderiv_eq,(forceExpression_hasFDeriv zp a (baseTime zp) regular).fderiv]
  have symmetry (i j : Fin 3) : actualS zp i j=actualS zp j i := S_symmetric _ _ i j
  fin_cases a <;> fin_cases b <;>
    simp [forceD,numeratorSecond,denominatorSecond,shiftSquareSecond,numeratorD,denominatorD,
      numerator,denominator,shiftSquareD,shiftSquare,baseTime,sourceJ,axis,coordinate,
      Fin.sum_univ_three,Matrix.of_apply] <;>
    field_simp [nonzero] <;>
    first | (solve | ring) | nlinarith [symmetry 0 1,symmetry 0 2,symmetry 1 2]

end LowEnergy.PreparationVacuumClockJacobian
