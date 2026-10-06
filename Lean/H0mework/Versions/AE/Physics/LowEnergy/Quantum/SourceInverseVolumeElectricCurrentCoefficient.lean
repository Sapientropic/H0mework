import H0mework.Versions.AE.Physics.LowEnergy.Quantum.SourceInverseVolumeElectricCurrentForm
import H0mework.Versions.AE.Physics.LowEnergy.Quantum.SourceScalarBalancedForce

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1800000
noncomputable section
namespace LowEnergy.SourceInverseElectricCurrentCoefficient
open GaussCoreHilbert GaussCoreDifferential GaussNativeForm GaussMatterCore GaussLiveMomentum
open SourceQuantumScalarChart SourceQuantumConfigurationHilbert SourceQuantumFockGauge SourceQuantumGaugeSliceCoordinates
open SourceScalarDoubleCurrent SourceMixedNativeReturn SourceInverseElectricCurrentForm GaussYukawaCoefficient
open SourceScalarBalancedForce SourceScalarGaugeForce
open scoped ContDiff
abbrev FiberOp := FockFiber →L[ℂ] FockFiber
attribute [local irreducible] matterAction SourceMixedNativeReturn.fullAction

/-- Actual native covariance cancels all inverse-chart derivatives before the energy estimate. -/
theorem original_current_contact (sharp : Bool) (v : Ambient) (hv : v.1=0) :
    current sharp v=(-Complex.I) • bracket (matterContact v) (SourceMixedNativeReturn.fullAction sharp) := by
  have hM : bracket (covariantMomentum v) matterAction=(-Complex.I) • matterContact v := by
    apply LinearMap.ext
    intro f
    change covariantMomentum v (matterAction f)-matterAction (covariantMomentum v f)=(-Complex.I) • matterContact v f
    rw [original_matter_momentum]
    abel
  have hY := (original_gauge_full sharp v hv).eq
  have hJ : current sharp v=bracket (bracket (covariantMomentum v) matterAction)
      (SourceMixedNativeReturn.fullAction sharp) := by
    unfold current bracket
    linear_combination (norm := noncomm_ring) matterAction*hY-hY*matterAction
  rw [hJ,hM]
  simp only [bracket,smul_mul_assoc,mul_smul_comm,smul_sub]

/-- The source contact depends only on the original coframe, gauge direction and Yukawa field. -/
def currentKernel (sharp : Bool) (v : Ambient) (z : SourceCoordinateSlice) : FiberOp :=
  (-Complex.I) • (contactFiber v z*branchMap sharp (GaussNativePotential.scalarField z)-
    branchMap sharp (GaussNativePotential.scalarField z)*contactFiber v z)

private theorem full_apply (sharp : Bool) (f : QuantumTest) (z : SourceCoordinateSlice) :
    SourceMixedNativeReturn.fullAction sharp f z=branchMap sharp (GaussNativePotential.scalarField z) (f z) := by
  unfold SourceMixedNativeReturn.fullAction
  cases sharp <;> rfl

/-- No moving-input derivative or unevaluated coefficient derivative remains. -/
theorem original_current_apply (sharp : Bool) (v : Ambient) (hv : v.1=0)
    (f : QuantumTest) (z : SourceCoordinateSlice) :
    current sharp v f z=currentKernel sharp v z (f z) := by
  rw [original_current_contact sharp v hv]
  change (-Complex.I) • (matterContact v (SourceMixedNativeReturn.fullAction sharp f) z-
    SourceMixedNativeReturn.fullAction sharp (matterContact v f) z)=_
  rw [full_apply,show matterContact v f z=contactFiber v z (f z) from rfl]
  change (-Complex.I) • (contactFiber v z (SourceMixedNativeReturn.fullAction sharp f z)-
    branchMap sharp (GaussNativePotential.scalarField z) (contactFiber v z (f z)))=_
  rw [full_apply]
  rfl

/-- The window multiplies the actual contact coefficient on each independent branch. -/
theorem original_window_current_apply (sharp : Bool) (m ell : ℕ) (v : Ambient) (hv : v.1=0)
    (f : QuantumTest) (z : SourceCoordinateSlice) :
    windowCurrent sharp m ell v f z=
      (SourceNativeCutoffContact.theta m ell z : ℂ) • (currentKernel sharp v z (f z)) := by
  rw [original_window_current sharp m ell v hv]
  change SourceMixedNativeReturn.thetaAction m ell (current sharp v f) z=_
  rw [SourceMixedNativeReturn.thetaAction,←SourceNativeCutoffContact.theta_action_polynomial]
  change (SourceNativeCutoffContact.theta m ell z : ℂ) • (current sharp v f z)=_
  rw [original_current_apply sharp v hv]

end LowEnergy.SourceInverseElectricCurrentCoefficient
