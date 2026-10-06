import H0mework.Versions.AE.Physics.LowEnergy.Quantum.SourceKineticScale
import Mathlib.Analysis.Calculus.VectorField

/-! The same source coframe Euler field has its literal brackets with native directions. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
noncomputable section
namespace LowEnergy.SourceEulerBracket
open GaussCoreDifferential GaussCoframeCore GaussHistoryHilbert GaussLiveMomentum
open SourceCoframeVolume SourceQuantumConfigurationHilbert SourceQuantumGaugeSliceCoordinates
open SourceQuantumFockGauge
open scoped ContDiff Topology

def eulerLinear : SourceCoordinateSlice →L[ℝ] SourceCoordinateSlice :=
  (ContinuousLinearMap.fst ℝ Coframe Slice).prod (0 : SourceCoordinateSlice →L[ℝ] Slice)

theorem euler_derivative (z : SourceCoordinateSlice) : HasFDerivAt euler eulerLinear z :=
  eulerLinear.hasFDerivAt

private theorem scale_curve (z : SourceCoordinateSlice) :
    HasDerivAt (fun r => scale r z) (euler z) 1 := by
  have h := ((hasDerivAt_id (1 : ℝ)).smul_const z.1).prodMk (hasDerivAt_const 1 z.2)
  simpa only [scale, euler, id_eq, one_smul] using! h

theorem direction_coframe_euler (v : Ambient) (z : physicalChart) :
    fderiv ℝ (direction v) z.val (euler z.val)=0 := by
  have hone : scale 1 z.val=z.val := by simp [scale]
  have chain := ((direction_smooth v z).differentiableAt (by simp)).hasFDerivAt
    |>.comp_hasDerivAt_of_eq 1 (scale_curve z.val) hone.symm
  have hinvariant (r : ℝ) : direction v (scale r z.val)=direction v z.val := rfl
  have hc : HasDerivAt (fun r => direction v (scale r z.val)) 0 1 := by
    simpa only [hinvariant] using hasDerivAt_const (1 : ℝ) (direction v z.val)
  exact chain.unique hc

theorem native_bracket (v : Ambient) (z : physicalChart) :
    VectorField.lieBracket ℝ euler (direction v) z.val=0 := by
  rw [VectorField.lieBracket, direction_coframe_euler v z, (euler_derivative z.val).fderiv]
  change (0 : SourceCoordinateSlice)-(0,0)=0
  exact sub_self 0

theorem coframe_bracket (i : Fin 6) (z : SourceCoordinateSlice) :
    VectorField.lieBracket ℝ euler (fun _ => coframeDirection i) z= -coframeDirection i := by
  have hc : fderiv ℝ (fun _ : SourceCoordinateSlice => coframeDirection i) z=0 :=
    (hasFDerivAt_const (coframeDirection i) z).fderiv
  rw [VectorField.lieBracket, hc, zero_apply, zero_sub, (euler_derivative z).fderiv]
  rfl

theorem native_derivative_current (v : Ambient) (f : QuantumTest) (z : physicalChart) :
    fderiv ℝ (fun x => fderiv ℝ f x (direction v x)) z.val (euler z.val) =
      fderiv ℝ (fun x => fderiv ℝ f x (euler x)) z.val (direction v z.val) := by
  have h := VectorField.fderiv_apply_lieBracket (𝕜 := ℝ) (f := (f : SourceCoordinateSlice → FockFiber))
    (V := euler) (W := direction v) (x := z.val) f.contDiff.contDiffAt (by
      simp only [minSmoothness_of_isRCLikeNormedField]
      exact ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)
    ((direction_smooth v z).differentiableAt (by simp)) (euler_derivative z.val).differentiableAt
  rw [native_bracket v z, map_zero] at h
  exact sub_eq_zero.mp h.symm

theorem coframe_derivative_current (i : Fin 6) (f : QuantumTest) (z : SourceCoordinateSlice) :
    fderiv ℝ (fun x => fderiv ℝ f x (coframeDirection i)) z (euler z) -
      fderiv ℝ (fun x => fderiv ℝ f x (euler x)) z (coframeDirection i) =
        -fderiv ℝ f z (coframeDirection i) := by
  have h := VectorField.fderiv_apply_lieBracket (𝕜 := ℝ) (f := (f : SourceCoordinateSlice → FockFiber))
    (V := euler) (W := fun _ => coframeDirection i) (x := z) f.contDiff.contDiffAt (by
      simp only [minSmoothness_of_isRCLikeNormedField]
      exact ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)
    (differentiableAt_const _) (euler_derivative z).differentiableAt
  rw [coframe_bracket i z, map_neg] at h
  exact h.symm

end LowEnergy.SourceEulerBracket
