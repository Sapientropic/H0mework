import H0mework.Versions.CAP.Physics.LowEnergy.Quantum.SourceDilationKinetic

/-! Coframe scaling of every original potential and the independent-dual matter action. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
noncomputable section
namespace LowEnergy.SourceDilationRemainder
open GaussCoreDifferential GaussNativeForm GaussNativeEnergy GaussNativePotential GaussCoframeForm
open GaussHistoryHilbert GaussMatterCore GaussQuantumMultiplier
open SourceCoframeVolume SourceCoframeVolumeCurrent SourceCoframeDilation SourceEulerCore
open SourceDilationAlgebra SourceDilationMultiplier SourceDilationKinetic SourceKineticScale
open SourceKineticTranspose SourceQuantumConfigurationHilbert SourceQuantumGaugeSliceCoordinates
open SourceQuantumFockGauge SourceQuantumScalarChart
open scoped ContDiff RealInnerProductSpace

def localPotential (z : SourceCoordinateSlice) : ℝ :=
  sourceTime 0*volume z*⟪(z.2.1 : Scalar),(z.2.1 : Scalar)⟫+volumePotential z

def spatialPotential (z : SourceCoordinateSlice) : ℝ :=
  -(sourceTime 0*volume z/2 * ∑ i : Fin 3, ∑ j : Fin 3,
    inverseSpatial z i j * ⟪scalarGradient z i,scalarGradient z j⟫)+magneticPotential z

theorem potential_split (z : SourceCoordinateSlice) :
    potential z+volumePotential z=localPotential z+spatialPotential z := by
  unfold potential scalarPotential localPotential spatialPotential
  ring

theorem local_smooth (z : physicalChart) : ContDiffAt ℝ ∞ localPotential z.val := by
  have hv := scalarSlice.subtypeL.contDiff.comp
    (contDiff_fst.comp (contDiff_snd : ContDiff ℝ ∞
      (Prod.snd : SourceCoordinateSlice → scalarSlice × coordinateSlice)))
  exact ((contDiffAt_const.mul volume_smooth.contDiffAt).mul
    (hv.contDiffAt.inner ℝ hv.contDiffAt)).add (volumePotential_smooth z)

theorem spatial_smooth (z : physicalChart) : ContDiffAt ℝ ∞ spatialPotential z.val := by
  have he : spatialPotential=(fun w => potential w+volumePotential w-localPotential w) := by
    funext w
    have h := potential_split w
    linarith
  rw [he]
  exact ((potential_smooth z).add (volumePotential_smooth z)).sub (local_smooth z)

theorem local_scale (r : ℝ) (z : SourceCoordinateSlice) :
    localPotential (scale r z)=r^3*localPotential z := by
  unfold localPotential volumePotential
  rw [volume_scale]
  change sourceTime 0*(r^3*volume z)*⟪(z.2.1 : Scalar),(z.2.1 : Scalar)⟫+
    3*sourceTime 0*(r^3*volume z)=_
  ring

theorem spatial_scale (r : ℝ) (hr : r≠0) (z : SourceCoordinateSlice) :
    spatialPotential (scale r z)=r*spatialPotential z := by
  have hs : ∀ i, scalarGradient (scale r z) i=scalarGradient z i := fun _ => rfl
  have hm : ∀ i, magneticField (scale r z) i=magneticField z i := fun _ => rfl
  unfold spatialPotential magneticPotential
  simp only [volume_scale, inverse_spatial_scale, hs, hm, mul_assoc, ←Finset.mul_sum]
  field_simp [hr]

def localAction : CoreEnd := multiply localPotential local_smooth
def spatialAction : CoreEnd := multiply spatialPotential spatial_smooth

theorem original_action_split :
    GaussDiagonalHistory.diagonalAction=kineticAction+matterAction+localAction+spatialAction := by
  rw [action_split]
  have hm : multiply potential potential_smooth+multiply volumePotential volumePotential_smooth=
      localAction+spatialAction := by
    apply LinearMap.ext
    intro f
    apply DFunLike.ext
    intro z
    change (potential z : ℂ) • f z+(volumePotential z : ℂ) • f z=
      (localPotential z : ℂ) • f z+(spatialPotential z : ℂ) • f z
    rw [←add_smul,←add_smul,←Complex.ofReal_add,←Complex.ofReal_add,potential_split]
  unfold remainderAction
  calc
    _ = kineticAction+matterAction+
      (multiply potential potential_smooth+multiply volumePotential volumePotential_smooth) := by abel
    _ = _ := by rw [hm]; abel

theorem local_scale_current :
    dilation*localAction-localAction*dilation=(-2*Complex.I) • localAction := by
  have h := homogeneous_multiplier localPotential local_smooth 3
    (fun z => euler_of_scale localPotential 3 z (local_smooth z)
      (fun r _ => by simpa only [zpow_natCast] using! local_scale r z.val))
  have hc : (-2*Complex.I/3)*((3 : ℝ) : ℂ)= -2*Complex.I := by push_cast; ring
  simpa only [hc] using! h

theorem spatial_scale_current :
    dilation*spatialAction-spatialAction*dilation=(-2*Complex.I/3) • spatialAction := by
  have he (z : physicalChart) :
      fderiv ℝ spatialPotential z.val (euler z.val)=1*spatialPotential z.val := by
    have h := euler_of_scale spatialPotential 1 z (spatial_smooth z)
      (fun r hr => by simpa only [zpow_one] using! spatial_scale r hr z.val)
    simpa only [Int.cast_one] using h
  have h := homogeneous_multiplier spatialPotential spatial_smooth 1 he
  simpa using! h

private theorem coefficient_scale (r : ℝ) (z : SourceCoordinateSlice) (i b : Fin 3) :
    coefficient i b (scale r z)=r⁻¹*coefficient i b z := by
  unfold coefficient
  rw [triad_inverse_scale]
  ring

private theorem coefficient_current (i b : Fin 3) :
    dilation*multiply (coefficient i b) (coefficient_smooth i b)-
      multiply (coefficient i b) (coefficient_smooth i b)*dilation=
        (2*Complex.I/3) • multiply (coefficient i b) (coefficient_smooth i b) := by
  have he (z : physicalChart) : fderiv ℝ (coefficient i b) z.val (euler z.val)=
      -1*coefficient i b z.val := by
    have h := euler_of_scale (coefficient i b) (-1) z (coefficient_smooth i b z)
      (fun r _ => by simpa only [zpow_neg_one] using! coefficient_scale r z.val i b)
    simpa only [Int.cast_neg,Int.cast_one] using h
  have h := homogeneous_multiplier (coefficient i b) (coefficient_smooth i b) (-1) he
  have hc : (-2*Complex.I/3)*((-1 : ℝ) : ℂ)=2*Complex.I/3 := by push_cast; ring
  simpa only [hc] using! h

private theorem base_smooth (i b : Fin 3) (z : physicalChart) :
    ContDiffAt ℝ ∞ (fun w => quantized (matrixTerm b (connectionField w i))) z.val :=
  (quantumTerm b).toContinuousLinearMap.contDiff.contDiffAt.comp z.val
    (connectionField_smooth i).contDiffAt

private def baseAction (i b : Fin 3) : CoreEnd :=
  action (fun z => matrixTerm b (connectionField z i)) (base_smooth i b)

private theorem base_current (i b : Fin 3) :
    dilation*baseAction i b-baseAction i b*dilation=(0 : ℂ) • baseAction i b := by
  have hE : Commute eulerAction (baseAction i b) :=
    euler_invariant_multiplier (fun z => quantized (matrixTerm b (connectionField z i)))
      (base_smooth i b) (fun _ _ => rfl)
  have hN : Commute number (baseAction i b) :=
    number_multiplier (fun z => quantized (matrixTerm b (connectionField z i)))
      (base_smooth i b) (fun z => number_commute (matrixTerm b (connectionField z i)))
  have h : eulerAction*baseAction i b-baseAction i b*eulerAction=(0 : ℂ) • baseAction i b := by
    rw [hE.eq,sub_self,zero_smul]
  rw [dilation_operator]
  simpa only [mul_zero,zero_smul,Module.End.one_eq_id] using! affine_dilation _ _ _ 0 h hN

private theorem matter_term_split (i b : Fin 3) :
    action (localMatrix i b) (GaussMatterCore.local_smooth i b)=
      multiply (coefficient i b) (coefficient_smooth i b)*baseAction i b := by
  apply LinearMap.ext
  intro f
  apply DFunLike.ext
  intro z
  change quantizer ((coefficient i b z : ℂ) • matrixTerm b (connectionField z i)) (f z)=
    (coefficient i b z : ℂ) • quantizer (matrixTerm b (connectionField z i)) (f z)
  rw [map_smul]
  rfl

theorem matter_scale_current :
    dilation*matterAction-matterAction*dilation=(2*Complex.I/3) • matterAction := by
  apply homogeneous_sum
  intro i
  apply homogeneous_sum
  intro b
  rw [matter_term_split]
  simpa only [add_zero] using! homogeneous_mul _ _ _ _ _ (coefficient_current i b) (base_current i b)

theorem full_source_scale_current :
    dilation*GaussDiagonalHistory.diagonalAction-GaussDiagonalHistory.diagonalAction*dilation=
      (2*Complex.I) • kineticAction-(8*Complex.I/3) • gaugeKinetic+
      (2*Complex.I/3) • matterAction-(2*Complex.I) • localAction-
      (2*Complex.I/3) • spatialAction := by
  rw [original_action_split]
  calc
    _ = (dilation*kineticAction-kineticAction*dilation)+
      (dilation*matterAction-matterAction*dilation)+
      (dilation*localAction-localAction*dilation)+
      (dilation*spatialAction-spatialAction*dilation) := by noncomm_ring
    _ = _ := by
      rw [kinetic_scale_current,matter_scale_current,local_scale_current,spatial_scale_current]
      module

end LowEnergy.SourceDilationRemainder
