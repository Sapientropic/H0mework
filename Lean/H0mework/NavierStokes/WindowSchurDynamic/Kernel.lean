import H0mework.NavierStokes.WindowSchurFrozen.Kernel
import H0mework.NavierStokes.WindowSchurSchur.AdvectorFiber
import Mathlib.Analysis.Calculus.FDeriv.Mul

set_option autoImplicit false
open scoped BigOperators Topology
namespace SaturationMonoid.NavierStokes.NativeWindowHistoryDynamicKernel
open Set Filter MeasureTheory
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientFiniteSupportRealityTrajectory
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open NativeFiniteActionResolvent NativeCommonAdvectorAction NativeResolventAdjoint
open NativeWholeH1Mixed (modes modes_zero modes_closed)
open NativeWindowHistoryMeanAction (frozen)
noncomputable section

abbrev V (M : ℕ) : Type := physicalSpace (modes M)
abbrev Operator (M : ℕ) : Type := V M →L[ℝ] V M
local instance operatorGroup (M : ℕ) : NormedAddCommGroup (Operator M) := inferInstance
local instance operatorSpace (M : ℕ) : NormedSpace ℝ (Operator M) := inferInstance

theorem curl_reality (M : ℕ) (u : V M) : FiniteStateFourierReality (NativeWindowTraceAdjoint.curlMap M u) := by
  rw [NativeWindowTraceAdjoint.curlMap_apply]
  exact curlLift_reality (modes M) (modes_closed M) u.1 (physical_reality (fun {_} h => modes_closed M _ h) u)

def equivalence (nu : Viscosity) (M : ℕ) (u : V M) : V M ≃L[ℝ] V M :=
  (physicalResolver (modes M) (modes_zero M) (modes_closed M) nu (NativeWindowTraceAdjoint.curlMap M u)
    (curl_reality M u) 1 (by norm_num)).toContinuousLinearEquiv

def kernel (nu : Viscosity) (M : ℕ) (u : V M) : Operator M := (equivalence nu M u).toContinuousLinearMap

def implicit (nu : Viscosity) (M : ℕ) (u : V M) : Operator M := ContinuousLinearMap.id ℝ (V M)-frozen nu M u

def transport (nu : Viscosity) (M : ℕ) : V M →L[ℝ] Operator M :=
  LinearMap.toContinuousLinearMap (NativeWindowHistorySchurAdvectorFiber.transportLinear nu M)

theorem transport_apply (nu : Viscosity) (M : ℕ) (u v : V M) :
    transport nu M u v=NativeWindowHistoryCreationGeometry.transport (modes M) (modes_zero M) (modes_closed M) nu u v := by
  change (frozen nu M u-frozen nu M 0) v=_
  rw [NativeWindowHistoryCreationSource.frozen_transport,sub_zero]

theorem implicit_difference (nu : Viscosity) (M : ℕ) (u v : V M) :
    implicit nu M v-implicit nu M u=transport nu M (u-v) := by
  have linear:transport nu M (u-v)=transport nu M u-transport nu M v := (transport nu M).map_sub u v
  change transport nu M (u-v)=(frozen nu M u-frozen nu M 0)-(frozen nu M v-frozen nu M 0) at linear
  exact (show implicit nu M v-implicit nu M u=(frozen nu M u-frozen nu M 0)-(frozen nu M v-frozen nu M 0) by
    unfold implicit; abel).trans linear.symm

theorem write (nu : Viscosity) (M : ℕ) (u f : V M) : implicit nu M u (kernel nu M u f)=f := by
  simpa only [one_smul] using! resolver_write
    (physicalOperator (modes M) (modes_zero M) (modes_closed M) nu (NativeWindowTraceAdjoint.curlMap M u) (curl_reality M u))
    (pairing (modes M)) (pairing_faithful (modes M))
    (physicalOperator_dissipative (modes M) (modes_zero M) (modes_closed M) nu (NativeWindowTraceAdjoint.curlMap M u) (curl_reality M u))
    1 (by norm_num) f

theorem inverse (nu : Viscosity) (M : ℕ) (u v : V M) : kernel nu M u (implicit nu M u v)=v := by
  obtain ⟨f,original⟩:=(equivalence nu M u).surjective v
  change kernel nu M u f=v at original
  exact (congrArg (fun w : V M => kernel nu M u (implicit nu M u w)) original).symm.trans
    ((congrArg (kernel nu M u) (write nu M u f)).trans original)

def unit (nu : Viscosity) (M : ℕ) (u : V M) : (Operator M)ˣ where
  val:=implicit nu M u
  inv:=kernel nu M u
  val_inv:=ContinuousLinearMap.ext (write nu M u)
  inv_val:=ContinuousLinearMap.ext (inverse nu M u)

theorem inverse_original (nu : Viscosity) (M : ℕ) (u : V M) : Ring.inverse (implicit nu M u)=kernel nu M u :=
  Ring.inverse_unit (unit nu M u)

theorem kernel_source {nu : Viscosity} (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ) :
    kernel nu M (NativeWindowTraceAdjoint.value seed M time)=(NativeWindowHistoryFrozenInverse.physical seed M time).toContinuousLinearMap := rfl

theorem coefficient_contraction (nu : Viscosity) (M : ℕ) (u f : V M) :
    ‖coefficients (modes M) (kernel nu M u f)‖ ≤ ‖coefficients (modes M) f‖ :=
  resolver_contraction (modes M)
    (physicalOperator (modes M) (modes_zero M) (modes_closed M) nu (NativeWindowTraceAdjoint.curlMap M u) (curl_reality M u))
    (physicalOperator_dissipative (modes M) (modes_zero M) (modes_closed M) nu (NativeWindowTraceAdjoint.curlMap M u) (curl_reality M u))
    1 (by norm_num) f

private theorem coefficient_lower (M : ℕ) : ∃ a : ℝ,0 < a ∧∀ v : V M,‖v‖ ≤ a*‖coefficients (modes M) v‖ := by
  obtain ⟨a,a0,paid⟩:=(coefficients (modes M)).injective_iff_antilipschitz.mp (coefficients_injective (modes M))
  refine ⟨a,by exact_mod_cast a0,fun v => ?_⟩
  simpa only [map_zero,dist_zero_right] using paid.le_mul_dist v 0

def normBound (M : ℕ) : ℝ :=
  (Classical.choose (coefficient_lower M))*‖LinearMap.toContinuousLinearMap (coefficients (modes M))‖

theorem normBound_nonnegative (M : ℕ) : 0 ≤ normBound M :=
  mul_nonneg (Classical.choose_spec (coefficient_lower M)).1.le
    (norm_nonneg (LinearMap.toContinuousLinearMap (coefficients (modes M))))

theorem kernel_norm (nu : Viscosity) (M : ℕ) (u : V M) : ‖kernel nu M u‖ ≤ normBound M := by
  apply ContinuousLinearMap.opNorm_le_bound _ (normBound_nonnegative M)
  intro f
  have first:=(Classical.choose_spec (coefficient_lower M)).2 (kernel nu M u f)
  have last:=(coefficient_contraction nu M u f).trans ((LinearMap.toContinuousLinearMap (coefficients (modes M))).le_opNorm f)
  exact first.trans ((mul_le_mul_of_nonneg_left last (Classical.choose_spec (coefficient_lower M)).1.le).trans_eq (by unfold normBound; ring))

private theorem inverse_difference {R : Type*} [Ring R] (A B K L : R) (first : K*A=1) (last : B*L=1) :
    K-L=K*(B-A)*L := by
  rw [mul_sub,sub_mul,mul_assoc K B L,last,mul_one,first,one_mul]

theorem kernel_difference (nu : Viscosity) (M : ℕ) (u v : V M) :
    kernel nu M u-kernel nu M v=kernel nu M u*transport nu M (u-v)*kernel nu M v :=
  (inverse_difference (implicit nu M u) (implicit nu M v) (kernel nu M u) (kernel nu M v)
    (unit nu M u).inv_val (unit nu M v).val_inv).trans
      (congrArg (fun A : Operator M => kernel nu M u*A*kernel nu M v) (implicit_difference nu M u v))

def lip (nu : Viscosity) (M : ℕ) : ℝ := normBound M^2*‖transport nu M‖

theorem lip_nonnegative (nu : Viscosity) (M : ℕ) : 0 ≤ lip nu M := mul_nonneg (sq_nonneg _) (norm_nonneg (transport nu M))

theorem difference_bound (nu : Viscosity) (M : ℕ) (u v : V M) :
    ‖kernel nu M u-kernel nu M v‖ ≤ lip nu M*‖u-v‖ := by
  rw [kernel_difference]
  have bound:=(norm_mul_le (kernel nu M u*transport nu M (u-v)) (kernel nu M v)).trans
    (mul_le_mul_of_nonneg_right (norm_mul_le (kernel nu M u) (transport nu M (u-v))) (norm_nonneg (kernel nu M v)))
  have scaled:=mul_le_mul (mul_le_mul (kernel_norm nu M u) ((transport nu M).le_opNorm (u-v))
    (norm_nonneg (transport nu M (u-v))) (normBound_nonnegative M)) (kernel_norm nu M v) (norm_nonneg (kernel nu M v))
      (mul_nonneg (normBound_nonnegative M) (mul_nonneg (norm_nonneg (transport nu M)) (norm_nonneg (u-v))))
  exact bound.trans (scaled.trans_eq (by unfold lip; ring))

end
end SaturationMonoid.NavierStokes.NativeWindowHistoryDynamicKernel
