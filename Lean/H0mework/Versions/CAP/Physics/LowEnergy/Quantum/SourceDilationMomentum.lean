import H0mework.Versions.CAP.Physics.LowEnergy.Quantum.SourceEulerCore
import H0mework.Versions.CAP.Physics.LowEnergy.Quantum.SourceDilationAlgebra
import H0mework.Versions.CAP.Physics.LowEnergy.Quantum.SourceDilationMultiplier

/-! Both actual native and coframe momentum branches consume the source scale generator. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
noncomputable section
namespace LowEnergy.SourceDilationMomentum
open GaussCoreDifferential GaussFockPair GaussCoreHilbert GaussCoframeForm GaussLiveMomentum
open GaussCoframeCore SourceCoframeVolumeCurrent SourceCoframeDilation SourceEulerCore
open SourceDilationAlgebra SourceQuantumFockGauge

private theorem euler_native (v : Ambient) : Commute eulerAction (covariantMomentum v) :=
  scalar_sum_commutes _ _ _ (euler_directional v) (euler_connection v) (-Complex.I)

private theorem number_native (v : Ambient) : Commute number (covariantMomentum v) :=
  scalar_sum_commutes _ _ _ (number_directional v) (number_connection v) (-Complex.I)

theorem native_momentum_current (v : Ambient) :
    dilation*covariantMomentum v-covariantMomentum v*dilation=0 := by
  have hE : eulerAction*covariantMomentum v-covariantMomentum v*eulerAction=
      (0 : ℂ) • covariantMomentum v := by rw [(euler_native v).eq,sub_self,zero_smul]
  rw [dilation_operator]
  simpa only [mul_zero,zero_smul,Module.End.one_eq_id] using! affine_dilation _ _ _ 0 hE (number_native v)

theorem coframe_derivative_current (i : Fin 6) :
    dilation*derivative (coframeDirection i)-derivative (coframeDirection i)*dilation =
      (2*Complex.I/3) • derivative (coframeDirection i) := by
  have hE : eulerAction*derivative (coframeDirection i)-derivative (coframeDirection i)*eulerAction=
      (-1 : ℂ) • derivative (coframeDirection i) := by
    apply LinearMap.ext
    intro f
    simpa only [neg_one_smul] using! euler_coframe_derivative i f
  rw [dilation_operator]
  have h := affine_dilation _ _ _ (-1) hE (number_coframe_derivative (coframeDirection i))
  have hc : (-2*Complex.I/3)*(-1 : ℂ)=2*Complex.I/3 := by ring
  simpa only [Module.End.one_eq_id,hc] using! h

theorem coframe_momentum_current (i : Fin 6) :
    dilation*GaussCoframeCore.momentum i-GaussCoframeCore.momentum i*dilation =
      (2*Complex.I/3) • GaussCoframeCore.momentum i :=
  homogeneous_smul dilation (derivative (coframeDirection i)) (2*Complex.I/3) (-Complex.I)
    (coframe_derivative_current i)

private theorem transpose_current (A B : CoreEnd) (a : ℂ) (ha : star a= -a)
    (pair : Paired B A) (hA : dilation*A-A*dilation=a • A) :
    dilation*B-B*dilation=a • B := by
  apply LinearMap.ext
  intro g
  apply GaussCoreLabel.pair_separates
  intro f
  have hp := congrArg (fun C : CoreEnd => sourcePair (C f) g) hA
  change sourcePair (dilation (A f)-A (dilation f)) g=sourcePair (a • A f) g at hp
  have hd (x y : GaussCoreDifferential.QuantumTest) := dilation_pair x y
  change sourcePair f (dilation (B g)-B (dilation g))=sourcePair f (a • B g)
  have hx : sourcePair f (dilation (B g))=sourcePair (A (dilation f)) g :=
    (hd f (B g)).trans (pair (dilation f) g)
  have hy : sourcePair f (B (dilation g))=sourcePair (dilation (A f)) g :=
    (pair f (dilation g)).trans (hd (A f) g)
  simp only [sourcePair,map_sub,map_smul,inner_sub_left,inner_sub_right,
    inner_smul_left,inner_smul_right,starRingEnd_apply] at hp ⊢
  rw [ha] at hp
  change sourcePair f (dilation (B g))-sourcePair f (B (dilation g))=a*sourcePair f (B g)
  rw [hx,hy,pair f g]
  change sourcePair (dilation (A f)) g-sourcePair (A (dilation f)) g= -a*sourcePair (A f) g at hp
  linear_combination -hp

theorem native_adjoint_current (v : Ambient) :
    dilation*GaussMomentumAdjoint.adjoint v-GaussMomentumAdjoint.adjoint v*dilation=0 := by
  have h := transpose_current (covariantMomentum v) (GaussMomentumAdjoint.adjoint v) 0 (by simp)
    (GaussNativeForm.adjoint_pair v) (by simpa only [zero_smul] using native_momentum_current v)
  simpa only [zero_smul] using h

theorem coframe_adjoint_current (i : Fin 6) :
    dilation*GaussCoframeCore.adjoint i-GaussCoframeCore.adjoint i*dilation=
      (2*Complex.I/3) • GaussCoframeCore.adjoint i :=
  transpose_current _ _ _ (by simp; ring)
    (GaussCoframeKinetic.adjoint_pair i) (coframe_momentum_current i)

end LowEnergy.SourceDilationMomentum
