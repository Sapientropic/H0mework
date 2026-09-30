import H0mework.NavierStokes.WindowSchurDynamic.Kernel
import Mathlib.Analysis.Calculus.FDeriv.CompCLM

set_option autoImplicit false
open scoped BigOperators Topology
namespace SaturationMonoid.NavierStokes.NativeWindowHistoryDynamicDerivative
open Set Filter MeasureTheory
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open NativeWindowHistoryDynamicKernel
noncomputable section
attribute [local instance] NativeWindowHistoryDynamicKernel.operatorGroup NativeWindowHistoryDynamicKernel.operatorSpace
local instance operatorTower (M : ℕ) : IsScalarTower ℝ (Operator M) (Operator M) :=
  IsScalarTower.right (R := ℝ) (A := Operator M)
local instance operatorComm (M : ℕ) : SMulCommClass ℝ (Operator M) (Operator M) :=
  IsScalarTower.to_smulCommClass (R := ℝ) (A := Operator M) (M := Operator M)

theorem implicit_affine (nu : Viscosity) (M : ℕ) (u : V M) :
    implicit nu M u=implicit nu M 0-transport nu M u := by
  have source:=implicit_difference nu M u 0
  rw [sub_zero] at source
  rw [← source]
  abel

theorem implicit_hasFDerivAt (nu : Viscosity) (M : ℕ) (u : V M) :
    HasFDerivAt (implicit nu M) (-transport nu M) u := by
  have actual:=((transport nu M).hasFDerivAt (x := u)).const_sub (implicit nu M 0)
  simpa only [← implicit_affine] using! actual

def derivative (nu : Viscosity) (M : ℕ) (u : V M) : V M →L[ℝ] Operator M :=
  (ContinuousLinearMap.mulLeftRight ℝ (Operator M) (kernel nu M u) (kernel nu M u)).comp (transport nu M)

theorem derivative_value (nu : Viscosity) (M : ℕ) (u v : V M) :
    derivative nu M u v=kernel nu M u*transport nu M v*kernel nu M u := rfl

theorem derivative_apply (nu : Viscosity) (M : ℕ) (u v f : V M) :
    derivative nu M u v f=kernel nu M u (transport nu M v (kernel nu M u f)) := rfl

theorem kernel_hasFDerivAt (nu : Viscosity) (M : ℕ) (u : V M) :
    HasFDerivAt (kernel nu M) (derivative nu M u) u := by
  have inverse:=hasFDerivAt_ringInverse (𝕜 := ℝ) (R := Operator M) (unit nu M u)
  have actual:=inverse.comp u (implicit_hasFDerivAt nu M u)
  have same:(-ContinuousLinearMap.mulLeftRight ℝ (Operator M) (kernel nu M u) (kernel nu M u)).comp (-transport nu M)=derivative nu M u := by
    apply ContinuousLinearMap.ext
    intro v
    simp only [ContinuousLinearMap.comp_apply,neg_apply,map_neg,neg_neg,derivative]
  change HasFDerivAt (fun v => Ring.inverse (implicit nu M v))
    ((-ContinuousLinearMap.mulLeftRight ℝ (Operator M) (kernel nu M u) (kernel nu M u)).comp (-transport nu M)) u at actual
  rw [same] at actual
  exact actual.congr_of_eventuallyEq (Eventually.of_forall fun v => (inverse_original nu M v).symm)

theorem kernel_fderiv (nu : Viscosity) (M : ℕ) (u : V M) : fderiv ℝ (kernel nu M) u=derivative nu M u :=
  (kernel_hasFDerivAt nu M u).fderiv

def solution (nu : Viscosity) (M : ℕ) (pair : V M×V M) : V M := kernel nu M pair.1 pair.2

def solutionDerivative (nu : Viscosity) (M : ℕ) (u c : V M) : V M×V M →L[ℝ] V M :=
  (kernel nu M u).comp (ContinuousLinearMap.snd ℝ (V M) (V M))+
    ((derivative nu M u).comp (ContinuousLinearMap.fst ℝ (V M) (V M))).flip c

theorem solution_hasFDerivAt (nu : Viscosity) (M : ℕ) (u c : V M) :
    HasFDerivAt (solution nu M) (solutionDerivative nu M u c) (u,c) := by
  have first := (kernel_hasFDerivAt nu M u).comp (u,c)
    (ContinuousLinearMap.fst ℝ (V M) (V M)).hasFDerivAt
  simpa only [Function.comp_def,solution,solutionDerivative] using!
    first.clm_apply (ContinuousLinearMap.snd ℝ (V M) (V M)).hasFDerivAt

theorem solutionDerivative_apply (nu : Viscosity) (M : ℕ) (u c v d : V M) :
    solutionDerivative nu M u c (v,d)=kernel nu M u
      (NativeWindowHistoryCreationGeometry.transport (NativeWholeH1Mixed.modes M) (NativeWholeH1Mixed.modes_zero M)
        (NativeWholeH1Mixed.modes_closed M) nu v (kernel nu M u c)+d) := by
  change kernel nu M u d+derivative nu M u v c=_
  rw [derivative_apply,transport_apply,map_add,add_comm]

theorem solution_hasDerivAt (nu : Viscosity) (M : ℕ) (u c : ℝ → V M) (v d : V M) (time : ℝ)
    (actual : HasDerivAt u v time) (forcing : HasDerivAt c d time) :
    HasDerivAt (fun t => kernel nu M (u t) (c t))
      (kernel nu M (u time) (NativeWindowHistoryCreationGeometry.transport (NativeWholeH1Mixed.modes M)
        (NativeWholeH1Mixed.modes_zero M) (NativeWholeH1Mixed.modes_closed M) nu v (kernel nu M (u time) (c time))+d)) time := by
  have first := (kernel_hasFDerivAt nu M (u time)).comp_hasDerivAt time actual
  have source := first.clm_apply forcing
  simpa only [Function.comp_def,derivative_apply,transport_apply,map_add] using! source

theorem remainder_original (nu : Viscosity) (M : ℕ) (u v : V M) :
    kernel nu M v-kernel nu M u-derivative nu M u (v-u)=
      (kernel nu M v-kernel nu M u)*transport nu M (v-u)*kernel nu M u := by
  calc
    _=kernel nu M v*transport nu M (v-u)*kernel nu M u-kernel nu M u*transport nu M (v-u)*kernel nu M u :=
      congrArg₂ (fun A B : Operator M => A-B) (kernel_difference nu M v u) (derivative_value nu M u (v-u))
    _=_ := by rw [sub_mul,sub_mul]

def secondBound (nu : Viscosity) (M : ℕ) : ℝ := lip nu M*‖transport nu M‖*normBound M

theorem secondBound_nonnegative (nu : Viscosity) (M : ℕ) : 0 ≤ secondBound nu M :=
  mul_nonneg (mul_nonneg (lip_nonnegative nu M) (norm_nonneg (transport nu M))) (normBound_nonnegative M)

theorem remainder_bound (nu : Viscosity) (M : ℕ) (u v : V M) :
    ‖kernel nu M v-kernel nu M u-derivative nu M u (v-u)‖ ≤ secondBound nu M*‖v-u‖^2 := by
  rw [remainder_original]
  have bound:=(norm_mul_le ((kernel nu M v-kernel nu M u)*transport nu M (v-u)) (kernel nu M u)).trans
    (mul_le_mul_of_nonneg_right (norm_mul_le (kernel nu M v-kernel nu M u) (transport nu M (v-u))) (norm_nonneg (kernel nu M u)))
  have scaled:=mul_le_mul (mul_le_mul (difference_bound nu M v u) ((transport nu M).le_opNorm (v-u))
    (norm_nonneg (transport nu M (v-u))) (mul_nonneg (lip_nonnegative nu M) (norm_nonneg (v-u))))
      (kernel_norm nu M u) (norm_nonneg (kernel nu M u))
      (mul_nonneg (mul_nonneg (lip_nonnegative nu M) (norm_nonneg (v-u)))
        (mul_nonneg (norm_nonneg (transport nu M)) (norm_nonneg (v-u))))
  exact bound.trans (scaled.trans_eq (by unfold secondBound; ring))

theorem solution_remainder_bound (nu : Viscosity) (M : ℕ) (u v c d : V M) :
    ‖solution nu M (v,c+d)-solution nu M (u,c)-solutionDerivative nu M u c (v-u,d)‖ ≤
      secondBound nu M*‖v-u‖^2*‖c‖+lip nu M*‖v-u‖*‖d‖ := by
  have identity:solution nu M (v,c+d)-solution nu M (u,c)-solutionDerivative nu M u c (v-u,d)=
      (kernel nu M v-kernel nu M u-derivative nu M u (v-u)) c+(kernel nu M v-kernel nu M u) d := by
    change kernel nu M v (c+d)-kernel nu M u c-(kernel nu M u d+derivative nu M u (v-u) c)=_
    simp only [map_add,sub_apply]
    abel
  rw [identity]
  exact (norm_add_le _ _).trans (add_le_add
    (((kernel nu M v-kernel nu M u-derivative nu M u (v-u)).le_opNorm c).trans
      (mul_le_mul_of_nonneg_right (remainder_bound nu M u v) (norm_nonneg c)))
    (((kernel nu M v-kernel nu M u).le_opNorm d).trans
      (mul_le_mul_of_nonneg_right (difference_bound nu M v u) (norm_nonneg d))))

end
end SaturationMonoid.NavierStokes.NativeWindowHistoryDynamicDerivative
