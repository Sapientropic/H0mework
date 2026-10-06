import H0mework.Versions.AD.Physics.LowEnergy.AlphaSource.CanonicalPreparationMoyalGrouping
import Mathlib.Analysis.Calculus.Deriv.Inv

set_option autoImplicit false
set_option maxHeartbeats 2800000
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationVacuumClockJacobian
open PreparationActualFactor GaussHistoryHilbert
open PreparationVacuumCanonicalMoyal
open scoped BigOperators ContDiff Topology

abbrev Phase := PreparationVacuumCanonicalMoyal.Phase
abbrev Time := Fin 4 → ℝ
def coordinate (a : Fin 4) : Time →L[ℝ] ℝ := ContinuousLinearMap.proj a
def axis (a : Fin 4) : Time := Pi.single a 1
def actualA (zp : Phase) : ℝ := A (nativePhase zp).1 (nativePhase zp).2
def actualT (zp : Phase) : ℝ := T (nativePhase zp).1 (nativePhase zp).2
def actualS (zp : Phase) : Matrix (Fin 3) (Fin 3) ℝ := S (nativePhase zp).1 (nativePhase zp).2
def actualC (zp : Phase) : ℝ := C (nativePhase zp).1 (nativePhase zp).2
def baseTime (zp : Phase) : Time := ![actualC zp,0,0,0]

def shiftSquare (y : Time) : ℝ := ∑ i : Fin 3,y (Fin.succ i)^2
def shiftSquareD (y : Time) : Time →L[ℝ] ℝ :=
  ∑ i : Fin 3,(2*y (Fin.succ i)) • coordinate (Fin.succ i)
def numerator (zp : Phase) (y : Time) : ℝ :=
  y 0^2*actualT zp-∑ i : Fin 3,∑ j : Fin 3,y (Fin.succ i)*actualS zp i j*y (Fin.succ j)
def numeratorD (zp : Phase) (y : Time) : Time →L[ℝ] ℝ :=
  (actualT zp*(2*y 0)) • coordinate 0-
    ∑ i : Fin 3,∑ j : Fin 3,
      ((y (Fin.succ i)*actualS zp i j) • coordinate (Fin.succ j)+
        y (Fin.succ j) • ((actualS zp i j) • coordinate (Fin.succ i)))
def denominator (y : Time) : ℝ := 2*y 0*(y 0^2-shiftSquare y)
def denominatorD (y : Time) : Time →L[ℝ] ℝ :=
  (2*y 0) • ((2*y 0) • coordinate 0-shiftSquareD y)+
    (y 0^2-shiftSquare y) • ((2 : ℝ) • coordinate 0)
def hamiltonian (zp : Phase) (y : Time) : ℝ :=
  timelikePrincipal (nativePhase zp).1 (nativePhase zp).2 (y 0) (fun i => y (Fin.succ i))
def hamiltonianD (zp : Phase) (y : Time) : Time →L[ℝ] ℝ :=
  (actualA zp) • coordinate 0+(denominator y)⁻¹ • numeratorD zp y+
    numerator zp y • ((-(denominator y^2)⁻¹) • denominatorD y)
def force (zp : Phase) (y : Time) : Time := fun a => -fderiv ℝ (hamiltonian zp) y (axis a)

theorem shiftSquare_hasFDeriv (y : Time) : HasFDerivAt shiftSquare (shiftSquareD y) y := by
  unfold shiftSquare shiftSquareD
  simpa [coordinate,nsmul_eq_mul] using!
    HasFDerivAt.fun_sum (u:=Finset.univ) (fun i _ => ((coordinate (Fin.succ i)).hasFDerivAt (x:=y)).pow 2)

theorem numerator_hasFDeriv (zp : Phase) (y : Time) :
    HasFDerivAt (numerator zp) (numeratorD zp y) y := by
  have square := ((coordinate 0).hasFDerivAt (x:=y)).pow 2
  have quadratic (i j : Fin 3) :=
    (((coordinate (Fin.succ i)).hasFDerivAt (x:=y)).mul_const (actualS zp i j)).mul
      ((coordinate (Fin.succ j)).hasFDerivAt (x:=y))
  unfold numerator numeratorD
  simpa [coordinate,nsmul_eq_mul,smul_smul] using!
    (square.mul_const (actualT zp)).sub
      (HasFDerivAt.fun_sum (u:=Finset.univ) fun i _ =>
        HasFDerivAt.fun_sum (u:=Finset.univ) fun j _ => quadratic i j)

theorem denominator_hasFDeriv (y : Time) : HasFDerivAt denominator (denominatorD y) y := by
  unfold denominator denominatorD
  simpa [coordinate,nsmul_eq_mul] using!
    (((coordinate 0).hasFDerivAt (x:=y)).const_mul 2).mul
      (((coordinate 0).hasFDerivAt (x:=y)).pow 2 |>.sub (shiftSquare_hasFDeriv y))

private theorem inverse_hasFDeriv {f : Time → ℝ} {L : Time →L[ℝ] ℝ} {y : Time}
    (derivative : HasFDerivAt f L y) (regular : f y≠0) :
    HasFDerivAt (fun v => (f v)⁻¹) ((-(f y^2)⁻¹) • L) y := by
  convert! ((hasDerivAt_inv regular).hasFDerivAt.comp y derivative) using 1
  ext v
  simp [mul_comm]

theorem hamiltonian_hasFDeriv (zp : Phase) (y : Time) (regular : denominator y≠0) :
    HasFDerivAt (hamiltonian zp) (hamiltonianD zp y) y := by
  have reciprocal := inverse_hasFDeriv (denominator_hasFDeriv y) regular
  have same : hamiltonian zp=(fun y => coordinate 0 y*actualA zp)+
      numerator zp*(fun y => (denominator y)⁻¹) := by
    funext v
    simp only [hamiltonian,timelikePrincipal,numerator,denominator,shiftSquare,
      actualA,actualT,actualS,coordinate,ContinuousLinearMap.proj_apply,
      Pi.add_apply,Pi.mul_apply,div_eq_mul_inv]
  rw [same]
  unfold hamiltonianD
  convert! (((coordinate 0).hasFDerivAt (x:=y)).mul_const (actualA zp)).add
    ((numerator_hasFDeriv zp y).mul reciprocal) using 1
  abel

theorem force_readback (zp : Phase) (y : Time) (regular : denominator y≠0) (a : Fin 4) :
    force zp y a=-hamiltonianD zp y (axis a) := by
  rw [force,(hamiltonian_hasFDeriv zp y regular).fderiv]

theorem base_regular (zp : Phase) (nonzero : actualC zp≠0) : denominator (baseTime zp)≠0 := by
  simp [denominator,baseTime,shiftSquare,Fin.sum_univ_three,nonzero]

theorem stationary (zp : Phase) (cone : nativePhase zp∈positiveCone) : force zp (baseTime zp)=0 := by
  have positive : 0<actualC zp := C_positive cone
  have relation : 2*actualA zp*actualC zp^2=actualT zp := C_equation cone
  funext a
  rw [force_readback zp (baseTime zp) (base_regular zp positive.ne') a]
  fin_cases a <;> simp [hamiltonianD,numeratorD,denominatorD,numerator,denominator,
    shiftSquareD,shiftSquare,baseTime,axis,coordinate,Fin.sum_univ_three]
  field_simp
  nlinarith [relation]

end LowEnergy.PreparationVacuumClockJacobian
