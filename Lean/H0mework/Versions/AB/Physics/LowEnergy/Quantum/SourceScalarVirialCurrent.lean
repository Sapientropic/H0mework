import H0mework.Versions.AB.Physics.LowEnergy.Quantum.SourceGaugeCoframeWard
import H0mework.Versions.AB.Physics.LowEnergy.Quantum.SourceScalarRetardedGram
import H0mework.Versions.AB.Physics.LowEnergy.Quantum.SourceEulerBracket

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 800000
set_option maxRecDepth 2048
noncomputable section
namespace LowEnergy.SourceScalarVirialCurrent
open GaussCoreHilbert GaussCoreDifferential GaussFockPair GaussHistoryHilbert
open GaussLiveMomentum GaussNativeEnergy GaussNativeForm GaussDiagonalHistory GaussUnitaryHistory
open SourceCoframeVolume SourceCoframeVolumeCurrent SourceDilationRemainder
open SourceScalarFlatJoint SourceScalarRetardedGram SourceScalarRadialContact
open SourceQuantumConfigurationHilbert SourceQuantumScalarChart SourceQuantumGaugeSliceCoordinates SourceQuantumFockGauge
open SourcePhysicalKineticSquare SourceMixedNativeReturn
open scoped ContDiff InnerProductSpace
abbrev End := SourceScalarGaugeScale.End

private def scalarLinear : SourceCoordinateSlice →L[ℝ] SourceCoordinateSlice :=
  (0 : SourceCoordinateSlice →L[ℝ] Coframe).prod
    (((ContinuousLinearMap.fst ℝ scalarSlice coordinateSlice).comp
      (ContinuousLinearMap.snd ℝ Coframe (scalarSlice × coordinateSlice))).prod
      (0 : SourceCoordinateSlice →L[ℝ] coordinateSlice))

private theorem scalar_derivative (z : SourceCoordinateSlice) :
    HasFDerivAt scalarEuler scalarLinear z := scalarLinear.hasFDerivAt

private theorem scalar_flat_bracket (v : scalarSlice) (z : SourceCoordinateSlice) :
    VectorField.lieBracket ℝ scalarEuler (fun _ => scalarAxis v) z= -scalarAxis v := by
  rw [VectorField.lieBracket,(hasFDerivAt_const (scalarAxis v) z).fderiv,
    zero_apply,zero_sub,(scalar_derivative z).fderiv]
  rfl

private theorem euler_derivative_current (v : scalarSlice) (f : QuantumTest) :
    scalarEulerAction (GaussCoframeCore.derivative (scalarAxis v) f)-
      GaussCoframeCore.derivative (scalarAxis v) (scalarEulerAction f)=
      -GaussCoframeCore.derivative (scalarAxis v) f := by
  apply DFunLike.ext
  intro z
  have hD : (GaussCoframeCore.derivative (scalarAxis v) f : SourceCoordinateSlice → FockFiber)=
      fun x => fderiv ℝ f x (scalarAxis v) := funext (GaussCoframeCore.derivative_apply _ f)
  have hE : (scalarEulerAction f : SourceCoordinateSlice → FockFiber)=
      fun x => fderiv ℝ f x (scalarEuler x) := funext (scalar_euler_apply f)
  change scalarEulerAction (GaussCoframeCore.derivative (scalarAxis v) f) z-
    GaussCoframeCore.derivative (scalarAxis v) (scalarEulerAction f) z=
      -GaussCoframeCore.derivative (scalarAxis v) f z
  rw [scalar_euler_apply,GaussCoframeCore.derivative_apply,
    GaussCoframeCore.derivative_apply,hD,hE]
  have h := VectorField.fderiv_apply_lieBracket (𝕜 := ℝ) (f := (f : SourceCoordinateSlice → FockFiber))
    (V := scalarEuler) (W := fun _ => scalarAxis v) (x := z) f.contDiff.contDiffAt (by
      simp only [minSmoothness_of_isRCLikeNormedField]
      exact ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)
    (differentiableAt_const _) (scalar_derivative z).differentiableAt
  rw [scalar_flat_bracket,map_neg] at h
  exact h.symm

/-- The original scalar61 native direction has Euler degree minus one. -/
theorem original_flat_momentum_euler (v : scalarSlice) :
    scalarEulerAction*flatMomentum v-flatMomentum v*scalarEulerAction= -flatMomentum v := by
  apply LinearMap.ext
  intro f
  have h := congrArg (fun q : QuantumTest => (-Complex.I) • q) (euler_derivative_current v f)
  simpa only [flatMomentum,Module.End.mul_apply,LinearMap.sub_apply,LinearMap.smul_apply,
    LinearMap.neg_apply,map_smul,smul_sub,smul_neg] using! h

private def scalarScale (r : ℝ) (z : SourceCoordinateSlice) : SourceCoordinateSlice :=
  (z.1,r • z.2.1,z.2.2)

private theorem scalar_curve (z : SourceCoordinateSlice) :
    HasDerivAt (fun r => scalarScale r z) (scalarEuler z) 1 := by
  simpa only [scalarScale,scalarEuler,id_eq,one_smul] using!
    (hasDerivAt_const (1 : ℝ) z.1).prodMk
      (((hasDerivAt_id (1 : ℝ)).smul_const z.2.1).prodMk (hasDerivAt_const (1 : ℝ) z.2.2))

private theorem euler_homogeneous_multiplier (c : SourceCoordinateSlice → ℝ)
    (hc : ∀ z : physicalChart,ContDiffAt ℝ ∞ c z.val)
    (hs : ∀ r z,c (scalarScale r z)=r*c z) :
    scalarEulerAction*multiply c hc-multiply c hc*scalarEulerAction=multiply c hc := by
  apply LinearMap.ext
  intro f
  apply DFunLike.ext
  intro z
  let A := multiply c hc
  have hone : scalarScale 1 z=z := by simp [scalarScale]
  have hg := ((A f).contDiff.differentiable (by simp)).differentiableAt.hasFDerivAt
    |>.comp_hasDerivAt_of_eq 1 (scalar_curve z) hone.symm
  have hf := (f.contDiff.differentiable (by simp)).differentiableAt.hasFDerivAt
    |>.comp_hasDerivAt_of_eq 1 (scalar_curve z) hone.symm
  have hp := (((hasDerivAt_id (1 : ℝ)).mul_const (c z)).smul hf)
  have he : (fun r => A f (scalarScale r z))=(fun r : ℝ => (r*c z) • f (scalarScale r z)) := by
    funext r
    change (c (scalarScale r z) : ℂ) • f (scalarScale r z)=_
    rw [hs]
    apply PiLp.ext
    intro word
    exact Complex.real_smul.symm
  change HasDerivAt (fun r => A f (scalarScale r z)) _ 1 at hg
  rw [he] at hg
  have hu := hg.unique hp
  simp only [Function.comp_def,one_mul,id_eq,hone] at hu
  change scalarEulerAction (A f) z-A (scalarEulerAction f) z=A f z
  rw [scalar_euler_apply]
  change fderiv ℝ (A f) z (scalarEuler z)-(c z : ℂ) • scalarEulerAction f z=
    (c z : ℂ) • f z
  rw [scalar_euler_apply,hu]
  apply PiLp.ext
  intro word
  simp only [PiLp.add_apply,PiLp.sub_apply,PiLp.smul_apply,Complex.real_smul]
  ring

def positionCoefficient (i : SourceScalarFlatJoint.SliceIndex) (z : SourceCoordinateSlice) : ℝ :=
  volume z*inner ℝ z.2.1 (scalarFrame i)

private theorem position_smooth (i : SourceScalarFlatJoint.SliceIndex) (z : physicalChart) :
    ContDiffAt ℝ ∞ (positionCoefficient i) z.val :=
  volume_smooth.contDiffAt.mul (((contDiff_fst.comp contDiff_snd).inner ℝ contDiff_const).contDiffAt)

def positionAction (i : SourceScalarFlatJoint.SliceIndex) : End :=
  multiply (positionCoefficient i) (position_smooth i)

theorem original_position_euler (i : SourceScalarFlatJoint.SliceIndex) :
    scalarEulerAction*positionAction i-positionAction i*scalarEulerAction=positionAction i := by
  apply euler_homogeneous_multiplier
  intro r z
  change volume z*inner ℝ (r • z.2.1) (scalarFrame i)=r*(volume z*inner ℝ z.2.1 (scalarFrame i))
  have h := congrArg (fun x : ℝ => volume z*x) (real_inner_smul_left z.2.1 (scalarFrame i) r)
  have h' := h.trans (mul_left_comm _ _ _)
  run_tac Lean.Elab.Tactic.withMainContext do
    (← Lean.Elab.Tactic.getMainGoal).assign (← Lean.Meta.getFVarFromUserName `h')
    Lean.Elab.Tactic.replaceMainGoal []

def radiusSquare : End := ∑ i : SourceScalarFlatJoint.SliceIndex,positionAction i*positionAction i

def flatHamiltonian : End :=
  (-(sourceTime 0 : ℂ)/2) • flatKinetic+(sourceTime 0 : ℂ) • radiusSquare

def positiveVirial : End :=
  (sourceTime 0 : ℂ) • flatKinetic+(2*(sourceTime 0 : ℂ)) • radiusSquare

private theorem current_square {R : Type*} [Ring R] [Module ℂ R]
    [IsScalarTower ℂ R R] [SMulCommClass ℂ R R] (E A : R) (c : ℂ)
    (h : E*A-A*E=c • A) : E*(A*A)-(A*A)*E=(2*c) • (A*A) := by
  have hh : E*(A*A)-(A*A)*E=(E*A-A*E)*A+A*(E*A-A*E) := by noncomm_ring
  rw [hh,h,smul_mul_assoc,mul_smul_comm,←add_smul]
  congr 1
  ring

private theorem flat_kinetic_euler :
    scalarEulerAction*flatKinetic-flatKinetic*scalarEulerAction=(-2 : ℂ) • flatKinetic := by
  unfold flatKinetic
  rw [Finset.mul_sum,Finset.sum_mul,←Finset.sum_sub_distrib,Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro i _
  have h := current_square scalarEulerAction (flatMomentum (scalarFrame i)) (-1)
    (by simpa only [neg_one_smul] using original_flat_momentum_euler (scalarFrame i))
  simpa only [mul_neg,mul_one,neg_smul,two_smul] using! h

private theorem radius_square_euler :
    scalarEulerAction*radiusSquare-radiusSquare*scalarEulerAction=(2 : ℂ) • radiusSquare := by
  unfold radiusSquare
  rw [Finset.mul_sum,Finset.sum_mul,←Finset.sum_sub_distrib,Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro i _
  have h := current_square scalarEulerAction (positionAction i) 1
    (by simpa only [one_smul] using original_position_euler i)
  simpa only [mul_one,two_smul] using! h

/-- The negative kinetic and positive quadratic source potential generate a positive scalar virial together. -/
theorem original_positive_virial :
    scalarEulerAction*flatHamiltonian-flatHamiltonian*scalarEulerAction=positiveVirial := by
  simp only [flatHamiltonian,positiveVirial,mul_add,add_mul,mul_smul_comm,smul_mul_assoc]
  have hK := flat_kinetic_euler
  have hQ := radius_square_euler
  linear_combination (norm := module) (-(sourceTime 0 : ℂ)/2) • hK+(sourceTime 0 : ℂ) • hQ

theorem original_radius_square (f : QuantumTest) :
    (sourcePair f (radiusSquare f)).re=
      ∑ i : SourceScalarFlatJoint.SliceIndex,‖embed (positionAction i f)‖^2 := by
  simp only [radiusSquare,LinearMap.sum_apply,sourcePair,map_sum,inner_sum,Complex.re_sum]
  apply Finset.sum_congr rfl
  intro i _
  have h := multiply_pair (positionCoefficient i) (position_smooth i) f (positionAction i f)
  change sourcePair f (positionAction i (positionAction i f))=sourcePair (positionAction i f) (positionAction i f) at h
  have hs : (sourcePair (positionAction i f) (positionAction i f)).re=‖embed (positionAction i f)‖^2 := by
    simpa only [sourcePair] using! (inner_self_eq_norm_sq (𝕜 := ℂ) (embed (positionAction i f)))
  exact (congrArg Complex.re h).trans hs

/-- The joint form retains every off-diagonal term by accepting the actual combined source test. -/
theorem original_positive_virial_square (f : QuantumTest) :
    (sourcePair f (positiveVirial f)).re=
      sourceTime 0*(∑ i : SourceScalarFlatJoint.SliceIndex,‖embed (flatMomentum (scalarFrame i) f)‖^2)+
      2*sourceTime 0*(∑ i : SourceScalarFlatJoint.SliceIndex,‖embed (positionAction i f)‖^2) := by
  have hc : (2*(sourceTime 0 : ℂ))=((2*sourceTime 0 : ℝ) : ℂ) := by push_cast; rfl
  simp only [positiveVirial,hc,LinearMap.add_apply,LinearMap.smul_apply,sourcePair,map_add,map_smul,
    inner_add_right,inner_smul_right,Complex.add_re,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,
    zero_mul,sub_zero]
  rw [show (inner ℂ (embed f) (embed (flatKinetic f))).re= _ from actual_flat_kinetic_square f,
    show (inner ℂ (embed f) (embed (radiusSquare f))).re= _ from original_radius_square f]

/-- The exact native70-minus-flat61 remainder; its form is the nine retained orthogonal rows. -/
def orthogonalRemainder : End :=
  volumeAction*scalarKinetic+((sourceTime 0 : ℂ)/2) • flatKinetic

/-- The original gauge, coframe, signed potential and matter actions remain literal here. -/
def nonScalarRemainder : End :=
  volumeAction*nonScalarAction-(sourceTime 0 : ℂ) • radiusSquare

def remainderCurrent : End :=
  scalarEulerAction*orthogonalRemainder-orthogonalRemainder*scalarEulerAction+
  (scalarEulerAction*nonScalarRemainder-nonScalarRemainder*scalarEulerAction)

theorem original_weighted_source_split :
    volumeAction*diagonalAction=flatHamiltonian+orthogonalRemainder+nonScalarRemainder := by
  rw [original_scalar_split]
  simp only [flatHamiltonian,orthogonalRemainder,nonScalarRemainder,mul_add]
  module

private theorem position_coefficient_sum (z : SourceCoordinateSlice) :
    (∑ i : SourceScalarFlatJoint.SliceIndex,(positionCoefficient i z)^2)=volume z^2*‖z.2.1‖^2 := by
  simp only [positionCoefficient,mul_pow,←Finset.mul_sum]
  exact congrArg (fun r : ℝ => volume z^2*r) (scalarFrame.sum_sq_inner_left z.2.1)

theorem original_radius_square_apply (f : QuantumTest) (z : SourceCoordinateSlice) :
    radiusSquare f z=((volume z^2*‖z.2.1‖^2 : ℝ) : ℂ) • f z := by
  simp only [radiusSquare,LinearMap.sum_apply,Module.End.mul_apply,sum_apply]
  change (∑ i : SourceScalarFlatJoint.SliceIndex,(positionCoefficient i z : ℂ) •
    ((positionCoefficient i z : ℂ) • f z))=_
  simp only [smul_smul,←pow_two,←Complex.ofReal_pow,←Finset.sum_smul,←Complex.ofReal_sum,
    position_coefficient_sum]

private theorem scalar_spatial_potential (z : SourceCoordinateSlice) :
    GaussNativePotential.potential z=sourceTime 0*volume z*‖z.2.1‖^2+spatialPotential z := by
  unfold GaussNativePotential.potential GaussNativePotential.scalarPotential spatialPotential
  rw [real_inner_self_eq_norm_sq]
  simp only [Submodule.norm_coe]
  ring

private theorem potential_radius_source :
    volumeAction*multiply GaussNativePotential.potential GaussNativePotential.potential_smooth=
      (sourceTime 0 : ℂ) • radiusSquare+volumeAction*spatialAction := by
  apply LinearMap.ext
  intro f
  apply DFunLike.ext
  intro z
  change (volume z : ℂ) • ((GaussNativePotential.potential z : ℂ) • f z)=
    (sourceTime 0 : ℂ) • radiusSquare f z+(volume z : ℂ) • ((spatialPotential z : ℂ) • f z)
  rw [original_radius_square_apply,scalar_spatial_potential]
  rw [smul_smul,smul_smul,smul_smul,←add_smul]
  apply congrArg (fun r : ℂ => r • f z)
  push_cast
  ring

/-- Cancellation of the actual scalar quadratic potential exposes every surviving source sector explicitly. -/
theorem original_nonScalar_remainder :
    nonScalarRemainder=volumeAction*(gaugeKinetic+GaussCoframeForm.coframeAction+
      GaussMatterCore.matterAction+spatialAction) := by
  unfold nonScalarRemainder nonScalarAction
  simp only [mul_add,potential_radius_source]
  abel

/-- The complete weighted H0 current contains the positive scalar form and the exact signed source remainder. -/
theorem original_full_virial :
    scalarEulerAction*(volumeAction*diagonalAction)-(volumeAction*diagonalAction)*scalarEulerAction=
      positiveVirial+remainderCurrent := by
  rw [original_weighted_source_split]
  simp only [mul_add,add_mul,remainderCurrent]
  have h := original_positive_virial
  linear_combination (norm := module) h

theorem original_orthogonal_remainder (f : QuantumTest) :
    (sourcePair f (orthogonalRemainder f)).re=
      -(sourceTime 0/2)*SourceScalarNativeComparison.orthogonalEnergy f := by
  have hK := SourceScalarNativeComparison.actual_native_scalar_form f
  have hs := SourceScalarNativeComparison.actual_scalar_energy_split f
  have he : sourcePair f (orthogonalRemainder f)=
      sourcePair f (volumeAction (scalarKinetic f))+((sourceTime 0 : ℂ)/2)*sourcePair f (flatKinetic f) := by
    simp only [orthogonalRemainder,LinearMap.add_apply,LinearMap.smul_apply,Module.End.mul_apply,
      sourcePair,map_add,map_smul,inner_add_right,inner_smul_right]
  rw [he,Complex.add_re]
  have hc (x : ℂ) : (((sourceTime 0 : ℂ)/2)*x).re=(sourceTime 0/2)*x.re := by
    have h : (sourceTime 0 : ℂ)/2=((sourceTime 0/2 : ℝ) : ℂ) := by push_cast; rfl
    rw [h,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero]
  rw [hc,hK,hs]
  ring

private theorem full_virial_pair (f : QuantumTest) :
    sourcePair f (positiveVirial f)=
      -sourcePair (scalarEulerAction f) (volumeAction (diagonalAction f))-
      (61 : ℂ)*sourcePair f (volumeAction (diagonalAction f))-
      sourcePair (diagonalAction (volumeAction f)) (scalarEulerAction f)-
      sourcePair f (remainderCurrent f) := by
  have h := congrArg (fun A : End => sourcePair f (A f)) original_full_virial
  simp only [LinearMap.sub_apply,LinearMap.add_apply,Module.End.mul_apply,
    sourcePair,map_sub,map_add,inner_sub_right,inner_add_right] at h
  change sourcePair f (scalarEulerAction (volumeAction (diagonalAction f)))-
      sourcePair f (volumeAction (diagonalAction (scalarEulerAction f)))=
      sourcePair f (positiveVirial f)+sourcePair f (remainderCurrent f) at h
  rw [scalar_euler_pair,scalar_euler_transpose] at h
  simp only [sourcePair,map_sub,map_neg,map_smul,inner_sub_left,inner_neg_left,inner_smul_left] at h
  have hc : starRingEnd ℂ (61 : ℂ)=(61 : ℂ) := map_natCast (starRingEnd ℂ) 61
  rw [hc] at h
  have hv : sourcePair f (volumeAction (diagonalAction (scalarEulerAction f)))=
      sourcePair (diagonalAction (volumeAction f)) (scalarEulerAction f) :=
    (multiply_pair _ _ f _).trans (diagonalAction_pair _ _)
  change -sourcePair (scalarEulerAction f) (volumeAction (diagonalAction f))-
    (61 : ℂ)*sourcePair f (volumeAction (diagonalAction f))-
    sourcePair f (volumeAction (diagonalAction (scalarEulerAction f)))=
    sourcePair f (positiveVirial f)+sourcePair f (remainderCurrent f) at h
  rw [hv] at h
  exact eq_sub_of_add_eq h.symm

/-- The source volume commutator is retained before substituting either actual resolvent state. -/
theorem original_full_virial_source_pair (f : QuantumTest) :
    sourcePair f (positiveVirial f)=
      -sourcePair (scalarEulerAction f) (volumeAction (diagonalAction f))-
      (61 : ℂ)*sourcePair f (volumeAction (diagonalAction f))-
      sourcePair (volumeAction (diagonalAction f)+
        (-3*Complex.I*(sourceTime 0 : ℂ)/4) • dilation f) (scalarEulerAction f)-
      sourcePair f (remainderCurrent f) := by
  have h := LinearMap.congr_fun SourceHamiltonianVolume.full_source_volume_current f
  have he : diagonalAction (volumeAction f)=volumeAction (diagonalAction f)+
      (-3*Complex.I*(sourceTime 0 : ℂ)/4) • dilation f := by
    have hs : diagonalAction (volumeAction f)-volumeAction (diagonalAction f)=
        (-3*Complex.I*(sourceTime 0 : ℂ)/4) • dilation f := h
    exact (sub_eq_iff_eq_add.mp hs).trans (add_comm _ _)
  rw [full_virial_pair,he]

/-- Same-F p/q are mixed before the positive current is evaluated; all native cross terms survive. -/
theorem actual_joint_virial_square (F : Index) (z : ℂ) (hz : z.im≠0)
    (g k : diagonal.domain) (a b : ℂ) :
    (sourcePair (jointState F z hz g k a b) (positiveVirial (jointState F z hz g k a b))).re=
      sourceTime 0*(∑ i : SourceScalarFlatJoint.SliceIndex,
        ‖a • embed (flatMomentum (scalarFrame i) (leftState F z hz k))+
          b • embed (flatMomentum (scalarFrame i) (rightState F z hz g))‖^2)+
      2*sourceTime 0*(∑ i : SourceScalarFlatJoint.SliceIndex,
        ‖a • embed (positionAction i (leftState F z hz k))+
          b • embed (positionAction i (rightState F z hz g))‖^2) := by
  rw [original_positive_virial_square]
  simp only [jointState,map_add,map_smul]

private theorem full_virial_real (f : QuantumTest) :
    (sourcePair f (positiveVirial f)).re=
      -2*(sourcePair (volumeAction (scalarEulerAction f)) (diagonalAction f)).re-
      61*(sourcePair (volumeAction f) (diagonalAction f)).re-
      (sourcePair ((-3*Complex.I*(sourceTime 0 : ℂ)/4) • dilation f) (scalarEulerAction f)).re-
      (sourcePair f (remainderCurrent f)).re := by
  have h := congrArg Complex.re (original_full_virial_source_pair f)
  have hu (x y : QuantumTest) : sourcePair x (volumeAction y)=sourcePair (volumeAction x) y :=
    multiply_pair _ _ x y
  have hp : (sourcePair (volumeAction (diagonalAction f)+
        (-3*Complex.I*(sourceTime 0 : ℂ)/4) • dilation f) (scalarEulerAction f)).re=
      (sourcePair (volumeAction (scalarEulerAction f)) (diagonalAction f)).re+
      (sourcePair ((-3*Complex.I*(sourceTime 0 : ℂ)/4) • dilation f) (scalarEulerAction f)).re := by
    change (inner ℂ (embed (volumeAction (diagonalAction f)+
      (-3*Complex.I*(sourceTime 0 : ℂ)/4) • dilation f)) (embed (scalarEulerAction f))).re=_
    rw [map_add,inner_add_left,Complex.add_re]
    congr 1
    have hsym : (inner ℂ (embed (volumeAction (diagonalAction f))) (embed (scalarEulerAction f))).re=
        (inner ℂ (embed (scalarEulerAction f)) (embed (volumeAction (diagonalAction f)))).re := by
      simpa only using! inner_re_symm (𝕜 := ℂ)
        (embed (volumeAction (diagonalAction f))) (embed (scalarEulerAction f))
    exact hsym.trans (congrArg Complex.re (hu (scalarEulerAction f) (diagonalAction f)))
  simp only [Complex.sub_re,Complex.neg_re] at h
  rw [hp,hu,hu] at h
  have h61 (x : ℂ) : ((61 : ℂ)*x).re=61*x.re := by norm_num [Complex.mul_re]
  rw [h61] at h
  linarith

/-- Explicit same-F signed virial cost; no bound on any state moment is assumed. -/
def signedVirialCost (F : Index) (z : ℂ) (hz : z.im≠0)
    (g k : diagonal.domain) (a b : ℂ) : ℝ :=
  let f := jointState F z hz g k a b
  let h := jointInput g k a b+jointFrequency F z g k a b+jointDefect F z hz g k a b
  show ℝ from
  -2*(inner ℂ (embed (volumeAction (scalarEulerAction f))) h).re-
  61*(inner ℂ (embed (volumeAction f)) h).re-
  (sourcePair ((-3*Complex.I*(sourceTime 0 : ℂ)/4) • dilation f) (scalarEulerAction f)).re-
  (sourcePair f (remainderCurrent f)).re

/-- Both original source equations enter before real-part extraction; every d_F and p/q cross survives. -/
theorem actual_joint_virial_source_cost (F : Index) (z : ℂ) (hz : z.im≠0)
    (g k : diagonal.domain) (a b : ℂ) :
    signedVirialCost F z hz g k a b=
      (sourcePair (jointState F z hz g k a b) (positiveVirial (jointState F z hz g k a b))).re := by
  have h := full_virial_real (jointState F z hz g k a b)
  simpa only [signedVirialCost,sourcePair,actual_joint_source_action] using! h.symm

theorem actual_joint_virial_nonnegative (F : Index) (z : ℂ) (hz : z.im≠0)
    (g k : diagonal.domain) (a b : ℂ) : 0 ≤ signedVirialCost F z hz g k a b := by
  rw [actual_joint_virial_source_cost,original_positive_virial_square]
  have hn : 0<sourceTime 0 := by
    rw [source_time_generated]
    exact SaturationMonoid.PhysicsCore.Stage9C.Material.SpinPair.lapse_pos
  exact add_nonneg (mul_nonneg hn.le (Finset.sum_nonneg (fun _ _ => sq_nonneg _)))
    (mul_nonneg (by positivity) (Finset.sum_nonneg (fun _ _ => sq_nonneg _)))

end LowEnergy.SourceScalarVirialCurrent
