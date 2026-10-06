import H0mework.Versions.AB.Physics.LowEnergy.Quantum.SourceEulerBracket
import H0mework.Versions.AB.Physics.LowEnergy.Quantum.SourceCoframeDilation

/-! Euler and Number act on the original full core before the kinetic scale law. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
noncomputable section
namespace LowEnergy.SourceEulerCore
open GaussCoreDifferential GaussCoreHilbert GaussCoframeCore GaussCoframeForm GaussFockPair
open GaussHistoryHilbert GaussLiveMomentum SourceCoframeVolume SourceCoframeDilation
open SourceCoframeVolumeCurrent SourceEulerBracket
open SourceQuantumConfigurationHilbert SourceQuantumGaugeSliceCoordinates SourceQuantumFockGauge
open scoped ContDiff Topology

theorem number_fiber (f : QuantumTest) (z : SourceCoordinateSlice) : number f z=fiberNumber (f z) := by
  apply PiLp.ext
  intro word
  rw [number_apply, fiberNumber_apply]

private theorem number_fderiv (f : QuantumTest) (z v : SourceCoordinateSlice) :
    fderiv ℝ (number f) z v=fiberNumber (fderiv ℝ f z v) := by
  let T := fiberNumber.restrictScalars ℝ
  have hf : (number f : SourceCoordinateSlice → FockFiber)=T ∘ f := funext (number_fiber f)
  have hd := T.hasFDerivAt.comp z (f.contDiff.differentiable (by decide)).differentiableAt.hasFDerivAt
  rw [hf, hd.fderiv]
  rfl

theorem number_coframe_derivative (v : SourceCoordinateSlice) : Commute number (derivative v) := by
  apply LinearMap.ext
  intro f
  apply DFunLike.ext
  intro z
  change number (derivative v f) z=derivative v (number f) z
  rw [number_fiber, derivative_apply, derivative_apply, number_fderiv]

theorem number_directional (v : Ambient) : Commute number (directional v) := by
  apply LinearMap.ext
  intro f
  apply DFunLike.ext
  intro z
  change number (directional v f) z=directional v (number f) z
  rw [number_fiber, directional_apply, directional_apply, number_fderiv]

theorem number_multiplier (B : SourceCoordinateSlice → FockFiber →L[ℂ] FockFiber)
    (smooth : ∀ z : physicalChart, ContDiffAt ℝ ∞ B z.val)
    (numberLaw : ∀ z, Commute fiberNumber (B z)) :
    Commute number (localMultiplier B smooth) := by
  apply LinearMap.ext
  intro f
  apply DFunLike.ext
  intro z
  change number (localMultiplier B smooth f) z=B z (number f z)
  rw [number_fiber, number_fiber]
  exact congrArg (fun A : FockFiber →L[ℂ] FockFiber => A (f z)) (numberLaw z).eq

theorem number_connection (v : Ambient) :
    Commute number (localMultiplier (connection v) (connection_smooth v)) :=
  number_multiplier _ _ (fun z => GaussFockWeights.native_number_commute (inverseL z v).1)

theorem euler_coframe_derivative (i : Fin 6) (f : QuantumTest) :
    eulerAction (derivative (coframeDirection i) f)-derivative (coframeDirection i) (eulerAction f)=
      -derivative (coframeDirection i) f := by
  apply DFunLike.ext
  intro z
  have hD : (derivative (coframeDirection i) f : SourceCoordinateSlice → FockFiber)=
      (fun x => fderiv ℝ f x (coframeDirection i)) := funext (derivative_apply _ f)
  have hE : (eulerAction f : SourceCoordinateSlice → FockFiber)=
      (fun x => fderiv ℝ f x (euler x)) := funext (eulerAction_apply f)
  change eulerAction (derivative (coframeDirection i) f) z-
    derivative (coframeDirection i) (eulerAction f) z = -derivative (coframeDirection i) f z
  rw [eulerAction_apply, derivative_apply, derivative_apply, hD, hE]
  exact coframe_derivative_current i f z

theorem euler_directional (v : Ambient) : Commute eulerAction (directional v) := by
  apply LinearMap.ext
  intro f
  apply DFunLike.ext
  intro z
  change eulerAction (directional v f) z=directional v (eulerAction f) z
  by_cases hz : z ∈ physicalChart
  · have hD : (directional v f : SourceCoordinateSlice → FockFiber)=
        (fun x => fderiv ℝ f x (direction v x)) := funext (directional_apply v f)
    have hE : (eulerAction f : SourceCoordinateSlice → FockFiber)=
        (fun x => fderiv ℝ f x (euler x)) := funext (eulerAction_apply f)
    rw [eulerAction_apply, directional_apply, hD, hE]
    exact native_derivative_current v f ⟨z,hz⟩
  · rw [image_eq_zero_of_notMem_tsupport (fun h => hz ((eulerAction (directional v f)).tsupport_subset h)),
      image_eq_zero_of_notMem_tsupport (fun h => hz ((directional v (eulerAction f)).tsupport_subset h))]

private theorem scale_curve (z : SourceCoordinateSlice) :
    HasDerivAt (fun r => scale r z) (euler z) 1 := by
  have h := ((hasDerivAt_id (1 : ℝ)).smul_const z.1).prodMk (hasDerivAt_const 1 z.2)
  simpa only [scale, euler, id_eq, one_smul] using! h

theorem euler_invariant_multiplier (B : SourceCoordinateSlice → FockFiber →L[ℂ] FockFiber)
    (smooth : ∀ z : physicalChart, ContDiffAt ℝ ∞ B z.val)
    (invariant : ∀ r z, B (scale r z)=B z) :
    Commute eulerAction (localMultiplier B smooth) := by
  apply LinearMap.ext
  intro f
  apply DFunLike.ext
  intro z
  let A := localMultiplier B smooth
  change eulerAction (A f) z=A (eulerAction f) z
  have hone : scale 1 z=z := by simp [scale]
  have hg := ((A f).contDiff.differentiable (by decide)).differentiableAt.hasFDerivAt
    |>.comp_hasDerivAt_of_eq 1 (scale_curve z) hone.symm
  have hf := (f.contDiff.differentiable (by decide)).differentiableAt.hasFDerivAt
    |>.comp_hasDerivAt_of_eq 1 (scale_curve z) hone.symm
  let T := (B z).restrictScalars ℝ
  have hT := T.hasFDerivAt.comp_hasDerivAt 1 hf
  change HasDerivAt (fun r => A f (scale r z)) (fderiv ℝ (A f) z (euler z)) 1 at hg
  change HasDerivAt (fun r => T (f (scale r z))) (T (fderiv ℝ f z (euler z))) 1 at hT
  have he : (fun r => A f (scale r z))=(fun r => T (f (scale r z))) := by
    funext r
    change B (scale r z) (f (scale r z))=B z (f (scale r z))
    rw [invariant r z]
  rw [he] at hg
  have hi := hg.unique hT
  rw [eulerAction_apply]
  change fderiv ℝ (A f) z (euler z)=B z (eulerAction f z)
  rw [eulerAction_apply]
  exact hi

theorem euler_connection (v : Ambient) :
    Commute eulerAction (localMultiplier (connection v) (connection_smooth v)) :=
  euler_invariant_multiplier _ _ (fun _ _ => rfl)

end LowEnergy.SourceEulerCore
