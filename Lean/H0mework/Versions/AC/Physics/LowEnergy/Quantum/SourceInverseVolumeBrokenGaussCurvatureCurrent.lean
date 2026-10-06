import H0mework.Versions.AC.Physics.LowEnergy.Quantum.SourceInverseVolumeNativeMixedCurvatureReduction
import H0mework.Versions.AC.Physics.LowEnergy.Quantum.SourceInverseVolumeScalarOscillatorAbsorption

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1200000
set_option maxRecDepth 2048
set_option synthInstance.maxHeartbeats 200000
noncomputable section
namespace LowEnergy.SourceBrokenGaussCurvatureCurrent
open GaussCoreHilbert GaussCoreDifferential GaussFockPair GaussHistoryHilbert GaussNativeForm
open GaussNativeEnergy GaussLiveMomentum GaussDiagonalHistory GaussUnitaryHistory GaussNativeMatter
open SourceQuantumScalarChart SourceQuantumConfigurationHilbert SourceQuantumGaugeSliceCoordinates
open SourceQuantumFockGauge SourceQuantumResidualFlow SourceScalarFlatJoint
open SourceScalarNativeComparison SourceScalarVirialCurrent SourceHamiltonianVolume
open SourceCoframeVolume SourceCoframeVolumeCurrent SourcePhysicalKineticSquare
open SourceElectricColumns SourceNativeMixedCurvatureReduction
open scoped InnerProductSpace ContDiff
abbrev End := QuantumTest →ₗ[ℂ] QuantumTest

private theorem normal_kernel (x : Scalar) (hx : sourceNormal x=0) : x∈scalarSlice := by
  apply (Submodule.mem_orthogonal _ _).2
  rintro _ ⟨a,rfl⟩
  let b : broken := broken.orthogonalProjectionOnto a
  let h : stabilizer := stabilizer.orthogonalProjectionOnto a
  have hab : (h : NativeLie)+(b : NativeLie)=a := stabilizer.starProjection_add_starProjection_orthogonal a
  have ho : orbit a=brokenOrbit b := by
    rw [←hab,map_add]
    have hh : orbit (h : NativeLie)=0 := h.property
    rw [hh,zero_add]
    rfl
  rw [ho]
  have hi := LinearMap.adjoint_inner_right brokenOrbit b x
  change inner ℝ b (sourceNormal x)=inner ℝ (brokenOrbit b) x at hi
  rw [hx,inner_zero_right] at hi
  exact hi.symm

/-- The original noncharacteristic chart solves the broken component; no caller matrix is supplied. -/
def normalLift (z : physicalChart) (v : Scalar) : broken :=
  (chartConsistencyEquiv ⟨z.val.2.1,z.property.2.2.2.1⟩).symm (sourceNormal v)

private theorem normal_lift_source (z : physicalChart) (v : Scalar) :
    sourceNormal (action (vacuum+(z.val.2.1 : Scalar)) (normalLift z v))=sourceNormal v :=
  chartConsistency_right_inverse ⟨z.val.2.1,z.property.2.2.2.1⟩ (sourceNormal v)

def tangentCompensation (z : physicalChart) (v : Scalar) : scalarSlice :=
  ⟨action (vacuum+(z.val.2.1 : Scalar)) (normalLift z v)-v,by
    apply normal_kernel
    rw [map_sub,normal_lift_source,sub_self]⟩

def gaugeCompensation (z : physicalChart) (v : Scalar) : Gauge :=
  nativeGauge (normalLift z v) (z.val.2.2 : Gauge)

/-- The resolved row keeps its fiber charge and both real derivative sectors. -/
def chargeValue (z : physicalChart) (v : Scalar) (f : QuantumTest) : FockFiber :=
  (-Complex.I) • nativeFock (normalLift z v) (f z.val)-
    flatMomentum (tangentCompensation z v) f z.val-
    covariantMomentum (0,gaugeCompensation z v) f z.val

/-- Exact Gauss resolution of every original scalar row, including its orthogonal nine. -/
theorem original_scalar_gauss_resolution (z : physicalChart) (v : Scalar) (f : QuantumTest) :
    covariantMomentum (v,0) f z.val=chargeValue z v f := by
  have hv : ((v,0) : Ambient)=orbitMap z.val (normalLift z v)-
      ((tangentCompensation z v : Scalar),0)-(0,gaugeCompensation z v) := by
    apply Prod.ext
    · change v=action (vacuum+(z.val.2.1 : Scalar)) (normalLift z v)-
        (action (vacuum+(z.val.2.1 : Scalar)) (normalLift z v)-v)-0
      abel
    · change (0 : Gauge)=nativeGauge (normalLift z v) (z.val.2.2 : Gauge)-0-
        nativeGauge (normalLift z v) (z.val.2.2 : Gauge)
      abel
  have hp := congrArg (pointMomentum f z.val) hv
  simp only [map_sub] at hp
  change covariantMomentum (v,0) f z.val=
    covariantMomentum (orbitMap z.val (normalLift z v)) f z.val-
      covariantMomentum ((tangentCompensation z v : Scalar),0) f z.val-
      covariantMomentum (0,gaugeCompensation z v) f z.val at hp
  rw [covariantMomentum_orbit,actual_flat_momentum] at hp
  exact hp

/-- Source columns use the already generated nine-dimensional orthogonal frame. -/
def orthogonalColumn (i : OrthogonalIndex) : End := covariantMomentum ((orthogonalFrame i : Scalar),0)
def orthogonalTranspose (i : OrthogonalIndex) : End := GaussMomentumAdjoint.adjoint ((orthogonalFrame i : Scalar),0)
def orthogonalGram : End := ∑ i : OrthogonalIndex,orthogonalTranspose i*orthogonalColumn i

theorem original_orthogonal_gauss_resolution (z : physicalChart) (i : OrthogonalIndex) (f : QuantumTest) :
    orthogonalColumn i f z.val=chargeValue z (orthogonalFrame i) f :=
  original_scalar_gauss_resolution z (orthogonalFrame i) f

private theorem row_pair (i : OrthogonalIndex) (f g : QuantumTest) :
    sourcePair f (orthogonalTranspose i g)=sourcePair (orthogonalColumn i f) g :=
  adjoint_pair _ _ _

private theorem orthogonal_gram_pair (f g : QuantumTest) :
    sourcePair f (orthogonalGram g)=∑ i : OrthogonalIndex,sourcePair (orthogonalColumn i f) (orthogonalColumn i g) := by
  simp only [orthogonalGram,LinearMap.sum_apply,Module.End.mul_apply,sourcePair,map_sum,inner_sum]
  apply Finset.sum_congr rfl
  intro i _
  exact adjoint_pair _ _ _

private theorem orthogonal_gram_self (f : QuantumTest) :
    (sourcePair f (orthogonalGram f)).re=orthogonalEnergy f := by
  rw [orthogonal_gram_pair,Complex.re_sum]
  unfold orthogonalEnergy
  apply Finset.sum_congr rfl
  intro i _
  exact inner_self_eq_norm_sq (𝕜 := ℂ) (embed (orthogonalColumn i f))

private theorem flat_pair (f g : QuantumTest) : sourcePair f (flatKinetic g)=sourcePair (flatKinetic f) g := by
  simp only [flatKinetic,LinearMap.sum_apply,sourcePair,map_sum,inner_sum,sum_inner]
  apply Finset.sum_congr rfl
  intro i _
  change sourcePair f (flatMomentum (scalarFrame i) (flatMomentum (scalarFrame i) g))=
    sourcePair (flatMomentum (scalarFrame i) (flatMomentum (scalarFrame i) f)) g
  rw [flat_momentum_pair,flat_momentum_pair]

private theorem gram_pair_symmetric (f g : QuantumTest) :
    sourcePair f (orthogonalGram g)=sourcePair (orthogonalGram f) g := by
  simp only [orthogonalGram,LinearMap.sum_apply,Module.End.mul_apply,sourcePair,map_sum,inner_sum,sum_inner]
  apply Finset.sum_congr rfl
  intro i _
  exact (adjoint_pair _ _ _).trans (GaussMomentumAdjoint.momentum_pair _ _ _)

private theorem remainder_pair (f g : QuantumTest) :
    sourcePair f (orthogonalRemainder g)=sourcePair (orthogonalRemainder f) g := by
  have hu (p q : QuantumTest) : sourcePair p (volumeAction q)=sourcePair (volumeAction p) q :=
    multiply_pair _ _ _ _
  have hp : sourcePair f (volumeAction (scalarKinetic g))=sourcePair (volumeAction (scalarKinetic f)) g := by
    rw [hu,scalarKinetic_pair]
    exact congrArg (fun x => sourcePair x g) (LinearMap.congr_fun scalar_kinetic_volume.eq f)
  have hc : (sourceTime 0 : ℂ)/2=((sourceTime 0/2 : ℝ):ℂ) := by push_cast;rfl
  simp only [orthogonalRemainder,LinearMap.add_apply,LinearMap.smul_apply,Module.End.mul_apply,hc,
    sourcePair,map_add,map_smul,inner_add_right,inner_add_left,inner_smul_right,inner_smul_left,Complex.conj_ofReal]
  exact congrArg₂ (fun a b : ℂ => a+((sourceTime 0/2 : ℝ):ℂ)*b) hp (flat_pair f g)

private theorem symmetric_im (A : End)
    (hA : ∀ f g,sourcePair f (A g)=sourcePair (A f) g) (f : QuantumTest) :
    (sourcePair f (A f)).im=0 := by
  have h := congrArg Complex.im ((pair_conjugate f (A f)).trans (hA f f).symm)
  simp only [Complex.conj_im] at h
  linarith

private theorem source_form_ext (A B : End)
    (hA : ∀ f g,sourcePair f (A g)=sourcePair (A f) g)
    (hB : ∀ f g,sourcePair f (B g)=sourcePair (B f) g)
    (h : ∀ f,(sourcePair f (A f)).re=(sourcePair f (B f)).re) : A=B := by
  let AC : Core →ₗ[ℂ] Core := coreEquiv.toLinearMap.comp (A.comp coreEquiv.symm.toLinearMap)
  let BC : Core →ₗ[ℂ] Core := coreEquiv.toLinearMap.comp (B.comp coreEquiv.symm.toLinearMap)
  have he : AC=BC := (ext_inner_map AC BC).mp (by
    intro x
    obtain ⟨f,rfl⟩ := coreEquiv.surjective x
    change sourcePair (A (coreEquiv.symm (coreEquiv f))) f=
      sourcePair (B (coreEquiv.symm (coreEquiv f))) f
    rw [coreEquiv.symm_apply_apply,←hA,←hB]
    exact Complex.ext (h f) ((symmetric_im A hA f).trans (symmetric_im B hB f).symm))
  apply LinearMap.ext
  intro f
  apply coreEquiv.injective
  have hh := LinearMap.congr_fun he (coreEquiv f)
  change coreEquiv (A (coreEquiv.symm (coreEquiv f)))=coreEquiv (B (coreEquiv.symm (coreEquiv f))) at hh
  simpa only [coreEquiv.symm_apply_apply] using hh

/-- The orthogonal source remainder is precisely the Gram of the nine true native rows. -/
theorem original_orthogonal_gram : orthogonalRemainder=(-(sourceTime 0 : ℂ)/2) • orthogonalGram := by
  apply source_form_ext _ _ remainder_pair
  · intro f g
    have hc : -(sourceTime 0 : ℂ)/2=((-sourceTime 0/2 : ℝ):ℂ) := by push_cast;rfl
    simp only [LinearMap.smul_apply,hc,sourcePair,map_smul,inner_smul_right,inner_smul_left,Complex.conj_ofReal]
    exact congrArg (fun c : ℂ => ((-sourceTime 0/2 : ℝ):ℂ)*c) (gram_pair_symmetric f g)
  · intro f
    rw [original_orthogonal_remainder]
    have hc : -(sourceTime 0 : ℂ)/2=((-sourceTime 0/2 : ℝ):ℂ) := by push_cast;rfl
    simp only [LinearMap.smul_apply,hc,sourcePair,map_smul,inner_smul_right,
      Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero]
    change -(sourceTime 0/2)*orthogonalEnergy f=(-sourceTime 0/2)*(sourcePair f (orthogonalGram f)).re
    rw [orthogonal_gram_self]
    ring

/-- Curvature is generated from the full electric action and each actual row. -/
def curvatureColumn (i : OrthogonalIndex) : End := orthogonalColumn i*gaugeKinetic-gaugeKinetic*orthogonalColumn i

def curvatureTranspose (i : OrthogonalIndex) : End := gaugeKinetic*orthogonalTranspose i-orthogonalTranspose i*gaugeKinetic

private theorem curvature_pair (i : OrthogonalIndex) (f g : QuantumTest) :
    sourcePair f (curvatureTranspose i g)=sourcePair (curvatureColumn i f) g := by
  simp only [curvatureTranspose,curvatureColumn,LinearMap.sub_apply,Module.End.mul_apply,sourcePair,map_sub,inner_sub_right,inner_sub_left]
  change sourcePair f (gaugeKinetic (orthogonalTranspose i g))-sourcePair f (orthogonalTranspose i (gaugeKinetic g))=
    sourcePair (orthogonalColumn i (gaugeKinetic f)) g-sourcePair (gaugeKinetic (orthogonalColumn i f)) g
  rw [gaugeKinetic_pair,row_pair,row_pair,gaugeKinetic_pair]

/-- The complete nine-row mixed current contains only actual curvature rows;
its electric action on the paired principal rows cancels by source symmetry. -/
theorem original_orthogonal_curvature :
    orthogonalRemainder*gaugeKinetic-gaugeKinetic*orthogonalRemainder=
      (-(sourceTime 0 : ℂ)/2) • ∑ i : OrthogonalIndex,
        (orthogonalTranspose i*curvatureColumn i-curvatureTranspose i*orthogonalColumn i) := by
  rw [original_orthogonal_gram]
  simp only [smul_mul_assoc,mul_smul_comm,←smul_sub,orthogonalGram,Finset.sum_mul,Finset.mul_sum,←Finset.sum_sub_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  unfold curvatureColumn curvatureTranspose
  noncomm_ring

private theorem curvature_gram_pair (f : QuantumTest) :
    sourcePair f ((∑ i : OrthogonalIndex,
      (orthogonalTranspose i*curvatureColumn i-curvatureTranspose i*orthogonalColumn i)) f)=
      (∑ i : OrthogonalIndex,sourcePair (orthogonalColumn i f) (curvatureColumn i f))-
      star (∑ i : OrthogonalIndex,sourcePair (orthogonalColumn i f) (curvatureColumn i f)) := by
  simp only [LinearMap.sum_apply,LinearMap.sub_apply,Module.End.mul_apply,sourcePair,map_sum,map_sub,
    inner_sum,inner_sub_right,star_sum,←Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  change sourcePair f (orthogonalTranspose i (curvatureColumn i f))-sourcePair f (curvatureTranspose i (orthogonalColumn i f))=
    sourcePair (orthogonalColumn i f) (curvatureColumn i f)-star (sourcePair (orthogonalColumn i f) (curvatureColumn i f))
  rw [row_pair,curvature_pair]
  exact congrArg (fun c : ℂ => sourcePair (orthogonalColumn i f) (curvatureColumn i f)-c) (pair_conjugate _ _).symm


private theorem inverse_commute (A : End) (h : Commute A volumeAction) : Commute A inverseVolumeAction := by
  have hVU : Commute inverseVolumeAction volumeAction := real_volume _ _
  apply LinearMap.ext
  intro f
  have hi (q : QuantumTest) : inverseVolumeAction (volumeAction q)=q :=
    (LinearMap.congr_fun hVU.eq q).trans (volume_inverse q)
  have he := congrArg inverseVolumeAction (LinearMap.congr_fun h.eq (inverseVolumeAction f))
  simpa only [Module.End.mul_apply,volume_inverse,hi] using he.symm

private theorem row_inverse (i : OrthogonalIndex) : Commute (orthogonalColumn i) inverseVolumeAction :=
  inverse_commute _ (native_momentum_volume _)
private theorem row_transpose_inverse (i : OrthogonalIndex) : Commute (orthogonalTranspose i) inverseVolumeAction :=
  inverse_commute _ (native_adjoint_volume _)
private theorem gauge_inverse : Commute gaugeKinetic inverseVolumeAction :=
  inverse_commute _ gauge_kinetic_volume
private theorem curvature_inverse (i : OrthogonalIndex) : Commute (curvatureColumn i) inverseVolumeAction :=
  ((row_inverse i).mul_left gauge_inverse).sub_left (gauge_inverse.mul_left (row_inverse i))

def curvatureOperator : End := ∑ i : OrthogonalIndex,
  (orthogonalTranspose i*curvatureColumn i-curvatureTranspose i*orthogonalColumn i)

private theorem curvature_operator_source : curvatureOperator=orthogonalGram*gaugeKinetic-gaugeKinetic*orthogonalGram := by
  simp only [curvatureOperator,orthogonalGram,Finset.sum_mul,Finset.mul_sum,←Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  unfold curvatureColumn curvatureTranspose
  noncomm_ring

private theorem curvature_operator_inverse : Commute curvatureOperator inverseVolumeAction := by
  have hG : Commute orthogonalGram inverseVolumeAction := by
    unfold orthogonalGram
    apply Commute.sum_left
    intro i _
    exact (row_transpose_inverse i).mul_left (row_inverse i)
  rw [curvature_operator_source]
  exact (hG.mul_left gauge_inverse).sub_left (gauge_inverse.mul_left hG)

def signedCurvaturePair (f : QuantumTest) : ℂ := ∑ i : OrthogonalIndex,
  sourcePair (inverseVolumeAction (orthogonalColumn i f)) (inverseVolumeAction (curvatureColumn i f))

private theorem inverse_pair (f g : QuantumTest) :
    sourcePair f (inverseVolumeAction g)=sourcePair (inverseVolumeAction f) g :=
  multiply_pair _ _ _ _

private theorem weighted_curvature_pair (f : QuantumTest) :
    sourcePair f (inverseVolumeAction (inverseVolumeAction (curvatureOperator f)))=
      signedCurvaturePair f-star (signedCurvaturePair f) := by
  have hv : inverseVolumeAction (curvatureOperator f)=curvatureOperator (inverseVolumeAction f) :=
    (LinearMap.congr_fun curvature_operator_inverse.eq f).symm
  rw [inverse_pair,hv]
  have hp := curvature_gram_pair (inverseVolumeAction f)
  change sourcePair (inverseVolumeAction f) (curvatureOperator (inverseVolumeAction f))=_ at hp
  have hr (i : OrthogonalIndex) : orthogonalColumn i (inverseVolumeAction f)=inverseVolumeAction (orthogonalColumn i f) :=
    LinearMap.congr_fun (row_inverse i).eq f
  have hc (i : OrthogonalIndex) : curvatureColumn i (inverseVolumeAction f)=inverseVolumeAction (curvatureColumn i f) :=
    LinearMap.congr_fun (curvature_inverse i).eq f
  simpa only [hr,hc,signedCurvaturePair] using hp

/-- The actual mixed44 current keeps one signed nine-row curvature pairing.
No absolute value or independent electric-row budget is introduced. -/
theorem original_mixed_half_current (f : QuantumTest) :
    (sourcePair f (((44 : ℂ) • (inverseVolumeAction*
      (scalarKinetic*gaugeKinetic-gaugeKinetic*scalarKinetic))) f)).im/2=
      -22*sourceTime 0*(signedCurvaturePair f).im := by
  have he : (44 : ℂ) • (inverseVolumeAction*(scalarKinetic*gaugeKinetic-gaugeKinetic*scalarKinetic))=
      (-22*(sourceTime 0 : ℂ)) • (inverseVolumeAction*(inverseVolumeAction*curvatureOperator)) := by
    rw [original_mixed_kinetic_reduction,original_orthogonal_curvature]
    simp only [mul_smul_comm,smul_smul]
    congr 1
    ring
  rw [he]
  change (sourcePair f ((-22*(sourceTime 0 : ℂ)) •
    inverseVolumeAction (inverseVolumeAction (curvatureOperator f)))).im/2=_
  have hs (c : ℂ) (q : QuantumTest) : sourcePair f (c • q)=c*sourcePair f q := by
    simp only [sourcePair,map_smul,inner_smul_right]
  rw [hs,weighted_curvature_pair]
  simp only [Complex.mul_im,Complex.mul_re,Complex.neg_re,Complex.neg_im,Complex.ofReal_re,Complex.ofReal_im,
    Complex.re_ofNat,Complex.im_ofNat,Complex.sub_re,Complex.sub_im,Complex.star_def,Complex.conj_re,Complex.conj_im]
  ring

/-- The current carrier uses the same resolved Gauss row even on the full electric output. -/
theorem original_curvature_gauss_resolution (z : physicalChart) (i : OrthogonalIndex) (f : QuantumTest) :
    curvatureColumn i f z.val=chargeValue z (orthogonalFrame i) (gaugeKinetic f)-
      gaugeKinetic (orthogonalColumn i f) z.val := by
  change orthogonalColumn i (gaugeKinetic f) z.val-gaugeKinetic (orthogonalColumn i f) z.val=_
  rw [original_orthogonal_gauss_resolution]


open SourceQuantumResidualChartFlow GaussNativePotential GaussRadialMomentum Filter
open SaturationMonoid.PhysicsCore StageNineHolonomicField StageNineP286GaugeConnectionVariationDensity
open scoped Topology

private theorem scalar_skew (a : stabilizer) (x y : Scalar) :
    inner ℝ (scalarP286ActionBilinear (a : NativeLie) x) y+
      inner ℝ x (scalarP286ActionBilinear (a : NativeLie) y)=0 := by
  have h := StageNineP286LinkedActiveScalarPairingSkew.scalarCoordinatePairingRe_scalarMotherLieAction_skew
    (SU7MotherLieAlgebra.p286LieBlockEmbed (p286CoordinateEquiv.symm (a : NativeLie))) x y
  rw [original_scalar_pairing,original_scalar_pairing] at h
  exact h

private theorem normal_intertwine (a : stabilizer) (v : Scalar) :
    sourceNormal (scalarP286ActionBilinear (a : NativeLie) v)=brokenGenerator a (sourceNormal v) := by
  apply ext_inner_left ℝ
  intro b
  have h1 := LinearMap.adjoint_inner_right brokenOrbit b (scalarP286ActionBilinear (a : NativeLie) v)
  have h2 := LinearMap.adjoint_inner_right brokenOrbit (brokenGenerator a b) v
  have hs := scalar_skew a (brokenOrbit b) v
  have hb := brokenGenerator_skew a b (sourceNormal v)
  rw [orbit_intertwine] at hs
  change inner ℝ b (sourceNormal (scalarP286ActionBilinear (a : NativeLie) v))=_ at h1
  change inner ℝ (brokenGenerator a b) (sourceNormal v)=_ at h2
  linarith

def normalMatrix (z : SourceCoordinateSlice) : broken →L[ℝ] broken := consistencyFamily (scalarField z)
def normalLiftField (v : Scalar) (z : SourceCoordinateSlice) : broken :=
  ContinuousLinearMap.inverse (normalMatrix z) (sourceNormal v)

private theorem normal_field_source (z : physicalChart) (v : Scalar) : normalLiftField v z.val=normalLift z v := by
  change ContinuousLinearMap.inverse
    (chartConsistencyEquiv ⟨z.val.2.1,z.property.2.2.2.1⟩).toContinuousLinearEquiv.toContinuousLinearMap (sourceNormal v)=_
  rw [ContinuousLinearMap.inverse_equiv]
  rfl

private theorem normal_matrix_source (z : physicalChart) (v : Scalar) :
    normalMatrix z.val (normalLift z v)=sourceNormal v := normal_lift_source z v

set_option backward.isDefEq.respectTransparency false in
private theorem normal_matrix_smooth : ContDiff ℝ ∞ normalMatrix := by
  let C : Scalar →L[ℝ] (broken →L[ℝ] broken) := consistencyFamily.toContinuousLinearMap
  exact (ContinuousLinearMap.contDiff (𝕜 := ℝ) (E := Scalar) (F := broken →L[ℝ] broken) C).comp scalarField_smooth

private theorem normal_field_smooth (v : Scalar) (z : physicalChart) : ContDiffAt ℝ ∞ (normalLiftField v) z.val := by
  have hi : ContDiffAt ℝ ∞ ContinuousLinearMap.inverse (normalMatrix z.val) :=
    contDiffAt_map_inverse (chartConsistencyEquiv ⟨z.val.2.1,z.property.2.2.2.1⟩).toContinuousLinearEquiv
  exact (hi.comp z.val normal_matrix_smooth.contDiffAt).clm_apply (contDiffAt_const (c := sourceNormal v))

private theorem scalar_field_gauge (z : physicalChart) (w : Gauge) :
    fderiv ℝ scalarField z.val (direction (0,w) z.val)=
      -scalarP286ActionBilinear ((residualInverse z.val w).1 : NativeLie) (scalarField z.val) := by
  have hf : HasFDerivAt scalarField scalarCoordinate z.val := scalarCoordinate.hasFDerivAt.const_add vacuum
  rw [hf.fderiv]
  change (((inverseL z.val (0,w)).2.1 : scalarSlice) : Scalar)=_
  rw [original_gauge_inverse]
  change -((scalarAction (residualInverse z.val w).1 z.val.2.1 : scalarSlice) : Scalar)=_
  exact congrArg Neg.neg (scalar_stabilizer z.val.2.1 (residualInverse z.val w).1).symm

set_option backward.isDefEq.respectTransparency false in
private theorem normal_matrix_gauge (z : physicalChart) (w : Gauge) (b : broken) :
    (fderiv ℝ normalMatrix z.val (direction (0,w) z.val)) b=
      -brokenGenerator (residualInverse z.val w).1 (normalMatrix z.val b)+
        normalMatrix z.val (brokenGenerator (residualInverse z.val w).1 b) := by
  let C : Scalar →L[ℝ] (broken →L[ℝ] broken) := consistencyFamily.toContinuousLinearMap
  let D : SourceCoordinateSlice →L[ℝ] (broken →L[ℝ] broken) := C.comp scalarCoordinate
  have hD : HasFDerivAt (fun x => D x) D z.val := ContinuousLinearMap.hasFDerivAt (𝕜 := ℝ) (E := SourceCoordinateSlice) (F := broken →L[ℝ] broken) D
  have hd : HasFDerivAt (fun x => consistencyFamily vacuum+D x) D z.val :=
    (hasFDerivAt_const_add_iff (𝕜 := ℝ) (E := SourceCoordinateSlice) (F := broken →L[ℝ] broken)
      (f := fun x => D x) (f' := D) (x := z.val) (consistencyFamily vacuum)).mpr hD
  have he : normalMatrix=(fun x => consistencyFamily vacuum+D x) := by
    funext x
    exact map_add consistencyFamily vacuum (scalarCoordinate x)
  rw [←he] at hd
  have h := congrArg (fun L : SourceCoordinateSlice →L[ℝ] (broken →L[ℝ] broken) => L (direction (0,w) z.val)) hd.fderiv
  change fderiv ℝ normalMatrix z.val (direction (0,w) z.val)=
    consistencyFamily (scalarCoordinate (direction (0,w) z.val)) at h
  have hf : HasFDerivAt scalarField scalarCoordinate z.val := scalarCoordinate.hasFDerivAt.const_add vacuum
  have hp := scalar_field_gauge z w
  rw [hf.fderiv] at hp
  rw [hp,map_neg] at h
  rw [h]
  have hc := LinearMap.congr_fun (consistency_commutator (residualInverse z.val w).1 (scalarField z.val)) b
  change consistency (scalarP286ActionBilinear ((residualInverse z.val w).1 : NativeLie) (scalarField z.val)) b=
    brokenGenerator (residualInverse z.val w).1 (normalMatrix z.val b)-normalMatrix z.val (brokenGenerator (residualInverse z.val w).1 b) at hc
  change -(consistency (scalarP286ActionBilinear ((residualInverse z.val w).1 : NativeLie) (scalarField z.val)) b)=_
  rw [hc]
  abel

/-- Native gauge differentiation closes inside the same broken frame; no second inverse-consistency price remains. -/
theorem original_normal_lift_gauge_derivative (z : physicalChart) (v : Scalar) (w : Gauge) :
    fderiv ℝ (normalLiftField v) z.val (direction (0,w) z.val)=
      normalLift z (scalarP286ActionBilinear ((residualInverse z.val w).1 : NativeLie) v)-
        brokenGenerator (residualInverse z.val w).1 (normalLift z v) := by
  have hM := (normal_matrix_smooth.differentiable (by simp)).differentiableAt.hasFDerivAt (x := z.val)
  have hB := ((normal_field_smooth v z).differentiableAt (by simp)).hasFDerivAt
  have hp := hM.clm_apply hB
  have heq : (fun x => normalMatrix x (normalLiftField v x))=ᶠ[𝓝 z.val] (fun _ => sourceNormal v) := by
    filter_upwards [physicalChart.isOpen.mem_nhds z.property] with x hx
    rw [normal_field_source ⟨x,hx⟩ v]
    exact normal_matrix_source ⟨x,hx⟩ v
  have hh := (hp.congr_of_eventuallyEq heq.symm).unique (hasFDerivAt_const (sourceNormal v) z.val)
  have h := congrArg (fun D : SourceCoordinateSlice →L[ℝ] broken => D (direction (0,w) z.val)) hh
  change normalMatrix z.val (fderiv ℝ (normalLiftField v) z.val (direction (0,w) z.val))+
    (fderiv ℝ normalMatrix z.val (direction (0,w) z.val)) (normalLiftField v z.val)=0 at h
  rw [normal_field_source,normal_matrix_gauge,normal_matrix_source] at h
  apply (chartConsistencyEquiv ⟨z.val.2.1,z.property.2.2.2.1⟩).injective
  change normalMatrix z.val (fderiv ℝ (normalLiftField v) z.val (direction (0,w) z.val))=
    normalMatrix z.val (normalLift z (scalarP286ActionBilinear ((residualInverse z.val w).1 : NativeLie) v)-
      brokenGenerator (residualInverse z.val w).1 (normalLift z v))
  rw [map_sub,normal_matrix_source,normal_intertwine]
  linear_combination (norm := abel) h


open DiracExteriorMatterAction SU7MotherLieAlgebra SU7MotherGaugeTheory
open StageNineCoframeGravityGaugeRegularity StageNineP286LinkedActiveLieRepresentation
open GaussQuantumMultiplier
attribute [local instance] SourceRealScalarFock.branchOrder
local instance : DecidableEq Mode := Classical.decEq _
local instance : DecidableEq LowEnergy.Quantum.Index := Classical.decEq _

private theorem alg_bracket {R S : Type*} [Ring R] [Ring S] [Algebra ℂ R] [Algebra ℂ S]
    (e : R ≃ₐ[ℂ] S) (A B C : R) (h : A*B-B*A=C) : e A*e B-e B*e A=e C := by
  rw [←map_mul,←map_mul,←map_sub,h]

private theorem primal_bracket (a : stabilizer) (b : broken) :
    nativePrimal (a : NativeLie)*nativePrimal (b : NativeLie)-
      nativePrimal (b : NativeLie)*nativePrimal (a : NativeLie)=nativePrimal (brokenGenerator a b) := by
  have hp := (diracExteriorMotherLieAction_bracket
    (p286LieBlockEmbed (p286CoordinateEquiv.symm (a : NativeLie)))
    (p286LieBlockEmbed (p286CoordinateEquiv.symm (b : NativeLie)))).symm
  change LowEnergy.Quantum.operatorMatrix (diracExteriorMotherLieAction (p286LieBlockEmbed (p286CoordinateEquiv.symm (a : NativeLie))))*
      LowEnergy.Quantum.operatorMatrix (diracExteriorMotherLieAction (p286LieBlockEmbed (p286CoordinateEquiv.symm (b : NativeLie))))-
      LowEnergy.Quantum.operatorMatrix (diracExteriorMotherLieAction (p286LieBlockEmbed (p286CoordinateEquiv.symm (b : NativeLie))))*
      LowEnergy.Quantum.operatorMatrix (diracExteriorMotherLieAction (p286LieBlockEmbed (p286CoordinateEquiv.symm (a : NativeLie))))=
      LowEnergy.Quantum.operatorMatrix (diracExteriorMotherLieAction (p286LieBlockEmbed
        (p286CoordinateEquiv.symm (jointP286CoordinateLieBracket (a : NativeLie) (b : NativeLie)))))
  rw [jointP286CoordinateLieBracket,p286CoordinateEquiv.symm_apply_apply,p286LieBlockEmbed_bracket]
  simpa only using! alg_bracket (R := Module.End ℂ DiracExteriorMatterCarrier)
    (S := Matrix LowEnergy.Quantum.Index LowEnergy.Quantum.Index ℂ) LowEnergy.Quantum.operatorMatrix _ _ _ hp

private theorem full_bracket (a : stabilizer) (b : broken) :
    nativeFull (a : NativeLie)*nativeFull (b : NativeLie)-
      nativeFull (b : NativeLie)*nativeFull (a : NativeLie)=nativeFull (brokenGenerator a b) := by
  change Matrix.fromBlocks (nativePrimal (a : NativeLie)) 0 0 ((nativePrimal (a : NativeLie)).map (starRingEnd ℂ))*
      Matrix.fromBlocks (nativePrimal (b : NativeLie)) 0 0 ((nativePrimal (b : NativeLie)).map (starRingEnd ℂ))-
      Matrix.fromBlocks (nativePrimal (b : NativeLie)) 0 0 ((nativePrimal (b : NativeLie)).map (starRingEnd ℂ))*
      Matrix.fromBlocks (nativePrimal (a : NativeLie)) 0 0 ((nativePrimal (a : NativeLie)).map (starRingEnd ℂ))=
      Matrix.fromBlocks (nativePrimal (brokenGenerator a b)) 0 0 ((nativePrimal (brokenGenerator a b)).map (starRingEnd ℂ))
  rw [Matrix.fromBlocks_multiply,Matrix.fromBlocks_multiply,sub_eq_add_neg,Matrix.fromBlocks_neg,Matrix.fromBlocks_add]
  simp only [Matrix.zero_mul,Matrix.mul_zero,zero_add,add_zero,neg_zero]
  congr 1
  · exact (sub_eq_add_neg _ _).symm.trans (primal_bracket a b)
  · have h := congrArg (fun A => A.map (starRingEnd ℂ)) (primal_bracket a b)
    rw [Matrix.map_sub (starRingEnd ℂ) (map_sub (starRingEnd ℂ)),Matrix.map_mul,Matrix.map_mul] at h
    exact (sub_eq_add_neg _ _).symm.trans h

private theorem quantized_bracket (A B : Matrix Mode Mode ℂ) :
    quantized A*quantized B-quantized B*quantized A=quantized (A*B-B*A) := by
  apply ContinuousLinearMap.ext
  intro f
  apply fiberCoordinates.injective
  simpa only [quantized,quantizedFiber,LinearMap.comp_apply,LinearEquiv.coe_toLinearMap,
    LinearEquiv.apply_symm_apply,map_sub] using!
    LinearMap.congr_fun (SourceJointCurrentHeisenberg.quantize_commutator A B) (fiberCoordinates f)

/-- The original positive-conjugate Lie dual and actual CAR action close on the broken generator. -/
theorem original_native_fock_bracket (a : stabilizer) (b : broken) :
    nativeFock (a : NativeLie)*nativeFock (b : NativeLie)-nativeFock (b : NativeLie)*nativeFock (a : NativeLie)=
      nativeFock (brokenGenerator a b) := by
  change quantized (nativeFull (a : NativeLie))*quantized (nativeFull (b : NativeLie))-
    quantized (nativeFull (b : NativeLie))*quantized (nativeFull (a : NativeLie))=quantized (nativeFull (brokenGenerator a b))
  rw [quantized_bracket,full_bracket]


private def brokenFock : broken →L[ℝ] (FockFiber →L[ℂ] FockFiber) :=
  nativeFock.toContinuousLinearMap.comp broken.subtypeL

def normalFiber (i : OrthogonalIndex) (z : SourceCoordinateSlice) : FockFiber →L[ℂ] FockFiber :=
  brokenFock (normalLiftField (orthogonalFrame i) z)

private theorem normal_fiber_smooth (i : OrthogonalIndex) (z : physicalChart) :
    ContDiffAt ℝ ∞ (normalFiber i) z.val :=
  brokenFock.contDiff.contDiffAt.comp z.val (normal_field_smooth (orthogonalFrame i) z)

def fiberColumn (i : OrthogonalIndex) : End := localMultiplier (normalFiber i) (normal_fiber_smooth i)

def normalRotation (w : Gauge) (i j : OrthogonalIndex) (z : SourceCoordinateSlice) : ℝ :=
  inner ℝ (orthogonalFrame i : Scalar)
    (scalarP286ActionBilinear (inverseL z (0,w)).1 (orthogonalFrame j : Scalar))

private theorem normal_rotation_smooth (w : Gauge) (i j : OrthogonalIndex) (z : physicalChart) :
    ContDiffAt ℝ ∞ (normalRotation w i j) z.val := by
  let L : NativeLie →L[ℝ] Scalar := (action (orthogonalFrame j : Scalar)).toContinuousLinearMap
  exact contDiffAt_const.inner ℝ (L.contDiff.contDiffAt.comp z.val
    (((inverse_smooth z).clm_apply (contDiffAt_const (c := ((0,w) : Ambient)))).fst))

def normalRotationAction (w : Gauge) (i j : OrthogonalIndex) : End :=
  multiply (normalRotation w i j) (normal_rotation_smooth w i j)

private theorem normal_preserved (a : stabilizer) (v : scalarSliceᗮ) :
    scalarP286ActionBilinear (a : NativeLie) (v : Scalar)∈scalarSliceᗮ := by
  apply (Submodule.mem_orthogonal _ _).2
  intro x hx
  have hs := scalar_skew a x (v : Scalar)
  have hmem : scalarP286ActionBilinear (a : NativeLie) x∈scalarSlice := (scalarAction a ⟨x,hx⟩).property
  have hz := (Submodule.mem_orthogonal _ _).1 v.property _ hmem
  rw [hz,zero_add] at hs
  exact hs

private theorem normal_rotation_skew (w : Gauge) (i j : OrthogonalIndex) :
    normalRotationAction w i j= -normalRotationAction w j i := by
  apply LinearMap.ext
  intro f
  apply DFunLike.ext
  intro z
  by_cases hz : z∈physicalChart
  · have hs := scalar_skew (residualInverse z w).1 (orthogonalFrame j : Scalar) (orthogonalFrame i : Scalar)
    rw [real_inner_comm (orthogonalFrame i : Scalar)
      (scalarP286ActionBilinear ((residualInverse z w).1 : NativeLie) (orthogonalFrame j : Scalar))] at hs
    have hc : normalRotation w i j z= -normalRotation w j i z := by
      unfold normalRotation
      rw [original_gauge_inverse ⟨z,hz⟩]
      exact eq_neg_of_add_eq_zero_left hs
    change (normalRotation w i j z : ℂ) • f z= -((normalRotation w j i z : ℂ) • f z)
    rw [hc,Complex.ofReal_neg,neg_smul]
  · have h0 (q : QuantumTest) : q z=0 := image_eq_zero_of_notMem_tsupport (fun h => hz (q.tsupport_subset h))
    exact (h0 _).trans (h0 _).symm

private def normalMap (z : physicalChart) : Scalar →ₗ[ℝ] broken :=
  (chartConsistencyEquiv ⟨z.val.2.1,z.property.2.2.2.1⟩).symm.toLinearMap.comp sourceNormal

private theorem normal_fiber_rotation (z : physicalChart) (w : Gauge) (i : OrthogonalIndex) :
    nativeFock (normalLift z (scalarP286ActionBilinear ((residualInverse z.val w).1 : NativeLie) (orthogonalFrame i : Scalar)))=
      ∑ j : OrthogonalIndex,normalRotation w j i z.val • normalFiber j z.val := by
  let a := (residualInverse z.val w).1
  let v : scalarSliceᗮ := ⟨scalarP286ActionBilinear (a : NativeLie) (orthogonalFrame i : Scalar),normal_preserved a (orthogonalFrame i)⟩
  have hc (j : OrthogonalIndex) : inner ℝ (orthogonalFrame j) v=normalRotation w j i z.val := by
    unfold normalRotation
    rw [original_gauge_inverse z w]
    rfl
  have he : scalarP286ActionBilinear (a : NativeLie) (orthogonalFrame i : Scalar)=
      ∑ j : OrthogonalIndex,normalRotation w j i z.val • (orthogonalFrame j : Scalar) := by
    have h := congrArg (fun v : scalarSliceᗮ => (v : Scalar)) (orthogonalFrame.sum_repr' v)
    simpa only [Submodule.coe_sum,Submodule.coe_smul,hc] using h.symm
  let C : Scalar →ₗ[ℝ] (FockFiber →L[ℂ] FockFiber) := nativeFock.comp (broken.subtype.comp (normalMap z))
  have h := congrArg C he
  simp only [map_sum,map_smul] at h
  change nativeFock (normalLift z (scalarP286ActionBilinear (a : NativeLie) (orthogonalFrame i : Scalar)))=
    ∑ j : OrthogonalIndex,normalRotation w j i z.val • nativeFock (normalLift z (orthogonalFrame j)) at h
  simpa only [normalFiber,normal_field_source,brokenFock,ContinuousLinearMap.comp_apply,
    Submodule.subtypeL_apply,LinearMap.coe_toContinuousLinearMap',a] using h

private theorem normal_fiber_gauge_derivative (z : physicalChart) (w : Gauge) (i : OrthogonalIndex) :
    fderiv ℝ (normalFiber i) z.val (direction (0,w) z.val)=
      nativeFock (normalLift z (scalarP286ActionBilinear ((residualInverse z.val w).1 : NativeLie) (orthogonalFrame i : Scalar)))-
        nativeFock (brokenGenerator (residualInverse z.val w).1 (normalLift z (orthogonalFrame i))) := by
  have hf := ((normal_field_smooth (orthogonalFrame i) z).differentiableAt (by simp)).hasFDerivAt
  have hb : HasFDerivAt brokenFock brokenFock (normalLiftField (orthogonalFrame i) z.val) := brokenFock.hasFDerivAt
  have hd := hb.comp z.val hf
  have h := congrArg (fun D : SourceCoordinateSlice →L[ℝ] (FockFiber →L[ℂ] FockFiber) => D (direction (0,w) z.val)) hd.fderiv
  change fderiv ℝ (normalFiber i) z.val (direction (0,w) z.val)=
    brokenFock (fderiv ℝ (normalLiftField (orthogonalFrame i)) z.val (direction (0,w) z.val)) at h
  rw [original_normal_lift_gauge_derivative,map_sub] at h
  exact h

private theorem normal_fiber_covariant_derivative (z : physicalChart) (w : Gauge) (i : OrthogonalIndex) :
    fderiv ℝ (normalFiber i) z.val (direction (0,w) z.val)+
      connection (0,w) z.val*normalFiber i z.val-normalFiber i z.val*connection (0,w) z.val=
        ∑ j : OrthogonalIndex,normalRotation w j i z.val • normalFiber j z.val := by
  have hc : connection (0,w) z.val=nativeFock ((residualInverse z.val w).1 : NativeLie) := by
    unfold connection
    rw [original_gauge_inverse]
  have hn : normalFiber i z.val=nativeFock (normalLift z (orthogonalFrame i)) := by
    rw [normalFiber,normal_field_source]
    rfl
  rw [normal_fiber_gauge_derivative,hc,hn,←normal_fiber_rotation]
  have h := original_native_fock_bracket (residualInverse z.val w).1 (normalLift z (orthogonalFrame i))
  linear_combination (norm := module) h

private theorem real_fock_smul (r : ℝ) (x : FockFiber) : r • x=(r : ℂ) • x := by
  apply PiLp.ext
  intro word
  exact Complex.real_smul

private theorem fiber_native_current (w : Gauge) (i : OrthogonalIndex) :
    covariantMomentum (0,w)*fiberColumn i-fiberColumn i*covariantMomentum (0,w)=
      (-Complex.I) • ∑ j : OrthogonalIndex,normalRotationAction w j i*fiberColumn j := by
  apply LinearMap.ext
  intro f
  apply DFunLike.ext
  intro z
  by_cases hz : z∈physicalChart
  · let B := normalFiber i
    have hB := ((normal_fiber_smooth i ⟨z,hz⟩).differentiableAt (by simp)).hasFDerivAt
    have hr := (ContinuousLinearMap.restrictScalarsL ℂ FockFiber FockFiber ℝ ℝ).hasFDerivAt.comp z hB
    have h := (hr.clm_apply (f.contDiff.differentiable (by simp)).differentiableAt.hasFDerivAt).fderiv
    have he : (fiberColumn i f : SourceCoordinateSlice → FockFiber)=fun x => B x (f x) := rfl
    have hd : directional (0,w) (fiberColumn i f) z=
        B z (directional (0,w) f z)+(fderiv ℝ B z (direction (0,w) z)) (f z) := by
      rw [directional_apply,he]
      change fderiv ℝ (fun x => B x (f x)) z=_ at h
      rw [h]
      rfl
    have hc := congrArg (fun T : FockFiber →L[ℂ] FockFiber => T (f z))
      (normal_fiber_covariant_derivative ⟨z,hz⟩ w i)
    simp only [add_apply,sub_apply,mul_apply_eq_comp,sum_apply,smul_apply,
      real_fock_smul] at hc
    change (-Complex.I) • (directional (0,w) (fiberColumn i f) z+
        connection (0,w) z (B z (f z)))-
      B z ((-Complex.I) • (directional (0,w) f z+connection (0,w) z (f z)))=_
    rw [hd,map_smul,map_add]
    simp only [LinearMap.smul_apply,LinearMap.sum_apply,Module.End.mul_apply,smul_apply,sum_apply,
      normalRotationAction,multiply_apply]
    change (-Complex.I) • (B z (directional (0,w) f z)+
        (fderiv ℝ B z (direction (0,w) z)) (f z)+connection (0,w) z (B z (f z)))-
      (-Complex.I) • (B z (directional (0,w) f z)+B z (connection (0,w) z (f z)))=
      (-Complex.I) • ∑ j : OrthogonalIndex,(normalRotation w j i z : ℂ) • normalFiber j z (f z)
    linear_combination (norm := module) (-Complex.I) • hc
  · have h0 (q : QuantumTest) : q z=0 := image_eq_zero_of_notMem_tsupport (fun h => hz (q.tsupport_subset h))
    exact (h0 _).trans (h0 _).symm

private theorem rotation_fiber_commute (w : Gauge) (i j k : OrthogonalIndex) :
    Commute (normalRotationAction w i j) (fiberColumn k) := by
  apply LinearMap.ext
  intro f
  apply DFunLike.ext
  intro z
  exact (map_smul (normalFiber k z) (normalRotation w i j z : ℂ) (f z)).symm

/-- The charge Gram uses the true skew native Lie action, with no assumption that its rows commute. -/
def fiberGram : End := -(∑ i : OrthogonalIndex,fiberColumn i*fiberColumn i)

private theorem fiber_gram_native (w : Gauge) : Commute fiberGram (covariantMomentum (0,w)) := by
  have h (i : OrthogonalIndex) :
      covariantMomentum (0,w)*(fiberColumn i*fiberColumn i)-(fiberColumn i*fiberColumn i)*covariantMomentum (0,w)=
        (-Complex.I) • ∑ j : OrthogonalIndex,
          normalRotationAction w j i*(fiberColumn j*fiberColumn i+fiberColumn i*fiberColumn j) := by
    have he : covariantMomentum (0,w)*(fiberColumn i*fiberColumn i)-(fiberColumn i*fiberColumn i)*covariantMomentum (0,w)=
        (covariantMomentum (0,w)*fiberColumn i-fiberColumn i*covariantMomentum (0,w))*fiberColumn i+
        fiberColumn i*(covariantMomentum (0,w)*fiberColumn i-fiberColumn i*covariantMomentum (0,w)) := by noncomm_ring
    rw [he,fiber_native_current]
    simp only [smul_mul_assoc,mul_smul_comm,Finset.sum_mul,Finset.mul_sum,←smul_add,←Finset.sum_add_distrib]
    congr 1
    apply Finset.sum_congr rfl
    intro j _
    rw [←mul_assoc (fiberColumn i), (rotation_fiber_commute w j i i).eq.symm]
    noncomm_ring
  have hs : (∑ i : OrthogonalIndex,∑ j : OrthogonalIndex,
      normalRotationAction w j i*(fiberColumn j*fiberColumn i+fiberColumn i*fiberColumn j))=0 := by
    let S := ∑ i : OrthogonalIndex,∑ j : OrthogonalIndex,
      normalRotationAction w j i*(fiberColumn j*fiberColumn i+fiberColumn i*fiberColumn j)
    have he : S= -S := by
      calc
        _ = ∑ j : OrthogonalIndex,∑ i : OrthogonalIndex,
          normalRotationAction w j i*(fiberColumn j*fiberColumn i+fiberColumn i*fiberColumn j) := Finset.sum_comm
        _ = _ := by
          simp only [S,←Finset.sum_neg_distrib]
          apply Finset.sum_congr rfl
          intro i _
          apply Finset.sum_congr rfl
          intro j _
          rw [normal_rotation_skew w i j,neg_mul,add_comm (fiberColumn i*fiberColumn j)]
    have hz : (2 : ℂ) • S=0 := by
      rw [two_smul]
      exact eq_neg_iff_add_eq_zero.mp he
    exact (smul_eq_zero.mp hz).resolve_left (by norm_num)
  have hg : Commute (covariantMomentum (0,w)) (∑ i : OrthogonalIndex,fiberColumn i*fiberColumn i) := by
    apply sub_eq_zero.mp
    rw [Finset.mul_sum,Finset.sum_mul,←Finset.sum_sub_distrib]
    simp only [h,←Finset.smul_sum,hs,smul_zero]
  exact hg.symm.neg_left

private theorem fiber_pair_skew (i : OrthogonalIndex) (f g : QuantumTest) :
    sourcePair (fiberColumn i f) g+sourcePair f (fiberColumn i g)=0 := by
  open MeasureTheory in
  rw [sourcePair_integral,sourcePair_integral,
    ←integral_add (densityPair_integrable (fiberColumn i f) g) (densityPair_integrable f (fiberColumn i g))]
  apply MeasureTheory.integral_eq_zero_of_ae
  exact Filter.Eventually.of_forall (fun z =>
    GaussFockWeights.native_weighted_skew (fun N => GaussDensityCore.complexDensity N z)
      (normalLiftField (orthogonalFrame i) z : NativeLie) (f z) (g z))

private theorem fiber_gram_pair (f g : QuantumTest) :
    sourcePair f (fiberGram g)=sourcePair (fiberGram f) g := by
  simp only [fiberGram,LinearMap.neg_apply,LinearMap.sum_apply,Module.End.mul_apply,
    sourcePair,map_neg,map_sum,inner_neg_right,inner_neg_left,inner_sum,sum_inner]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  have h₁ := fiber_pair_skew i f (fiberColumn i g)
  have h₂ := fiber_pair_skew i (fiberColumn i f) g
  change sourcePair f (fiberColumn i (fiberColumn i g))=sourcePair (fiberColumn i (fiberColumn i f)) g
  linear_combination h₁-h₂

private theorem fiber_gram_adjoint (w : Gauge) : Commute fiberGram (GaussMomentumAdjoint.adjoint (0,w)) := by
  apply LinearMap.ext
  intro g
  apply SourceCoframeVolume.pair_ext
  intro f
  change sourcePair f (fiberGram (GaussMomentumAdjoint.adjoint (0,w) g))=
    sourcePair f (GaussMomentumAdjoint.adjoint (0,w) (fiberGram g))
  rw [fiber_gram_pair,adjoint_pair,adjoint_pair,fiber_gram_pair]
  exact congrArg (fun q => sourcePair q g) (LinearMap.congr_fun (fiber_gram_native w).eq.symm f)

private theorem fiber_multiplier_commute (c : SourceCoordinateSlice → ℝ)
    (hc : ∀ z : physicalChart,ContDiffAt ℝ ∞ c z.val) (i : OrthogonalIndex) :
    Commute (fiberColumn i) (multiply c hc) := by
  apply LinearMap.ext
  intro f
  apply DFunLike.ext
  intro z
  exact map_smul (normalFiber i z) (c z : ℂ) (f z)

/-- The entire broken-charge square exits the actual electric mixed current;
its Number-weighted independent transpose is retained. -/
theorem original_fiber_gauge_kinetic : Commute fiberGram gaugeKinetic := by
  unfold gaugeKinetic
  apply Commute.smul_right
  apply Commute.sum_right
  intro a _
  apply Commute.sum_right
  intro i _
  apply Commute.sum_right
  intro j _
  have hw : Commute fiberGram (multiply (fun z => gaugeWeight z i j) (gaugeWeight_smooth i j)) := by
    apply Commute.neg_left
    apply Commute.sum_left
    intro k _
    exact (fiber_multiplier_commute _ _ k).mul_left (fiber_multiplier_commute _ _ k)
  exact (fiber_gram_adjoint (gaugeDirection i a).2).mul_right
    (hw.mul_right (fiber_gram_native (gaugeDirection j a).2))

def chargeColumn (i : OrthogonalIndex) : End := (-Complex.I) • fiberColumn i

def derivativeCompensation (i : OrthogonalIndex) : End := orthogonalColumn i-chargeColumn i

def derivativeCompensationTranspose (i : OrthogonalIndex) : End := orthogonalTranspose i-chargeColumn i

/-- Both derivative sectors and all charge/derivative cross terms are retained. -/
def compensationGram : End := ∑ i : OrthogonalIndex,
  (derivativeCompensationTranspose i*derivativeCompensation i+
    chargeColumn i*derivativeCompensation i+derivativeCompensationTranspose i*chargeColumn i)

/-- The complementary row is precisely the original flat and gauge compensation,
not a pure-fiber replacement for the original momentum. -/
theorem original_derivative_compensation (z : physicalChart) (i : OrthogonalIndex) (f : QuantumTest) :
    derivativeCompensation i f z.val=
      -flatMomentum (tangentCompensation z (orthogonalFrame i)) f z.val-
        covariantMomentum (0,gaugeCompensation z (orthogonalFrame i)) f z.val := by
  change orthogonalColumn i f z.val-(-Complex.I) • normalFiber i z.val (f z.val)=_
  rw [original_orthogonal_gauss_resolution,normalFiber,normal_field_source]
  change chargeValue z (orthogonalFrame i) f-(-Complex.I) • nativeFock (normalLift z (orthogonalFrame i)) (f z.val)=_
  unfold chargeValue
  module

private theorem orthogonal_gram_split : orthogonalGram=fiberGram+compensationGram := by
  have h (i : OrthogonalIndex) :
      orthogonalTranspose i*orthogonalColumn i=
        -(fiberColumn i*fiberColumn i)+
          (derivativeCompensationTranspose i*derivativeCompensation i+
            chargeColumn i*derivativeCompensation i+derivativeCompensationTranspose i*chargeColumn i) := by
    unfold derivativeCompensationTranspose derivativeCompensation chargeColumn
    have hc : (-Complex.I)*(-Complex.I)=(-1 : ℂ) := by rw [neg_mul_neg,Complex.I_mul_I]
    simp only [sub_mul,mul_sub,smul_mul_assoc,mul_smul_comm,smul_smul,hc,neg_one_smul]
    module
  simp only [orthogonalGram,h,Finset.sum_add_distrib,Finset.sum_neg_distrib,fiberGram,compensationGram]

/-- The genuine broken-charge Casimir is removed before estimating the remaining mixed current. -/
theorem original_orthogonal_compensation_current :
    orthogonalRemainder*gaugeKinetic-gaugeKinetic*orthogonalRemainder=
      (-(sourceTime 0 : ℂ)/2) • (compensationGram*gaugeKinetic-gaugeKinetic*compensationGram) := by
  rw [original_orthogonal_gram,orthogonal_gram_split]
  simp only [smul_mul_assoc,mul_smul_comm,add_mul,mul_add]
  rw [original_fiber_gauge_kinetic.eq]
  module

/-- The same full scalar/electric mixed block now contains only the source compensators and cross terms. -/
theorem original_mixed_compensation_current :
    scalarKinetic*gaugeKinetic-gaugeKinetic*scalarKinetic=
      (-(sourceTime 0 : ℂ)/2) • (inverseVolumeAction*
        (compensationGram*gaugeKinetic-gaugeKinetic*compensationGram)) := by
  rw [original_mixed_kinetic_reduction,original_orthogonal_compensation_current,mul_smul_comm]

open SourceInverseNoetherEnergy SourceScalarVirialBulk

/-- Literal full H/bulk consumer; the other signed sectors are unchanged. -/
theorem original_bulk_compensation_current :
    bulkCurrent=(3*Complex.I*(sourceTime 0 : ℂ)/4) •
      (inverseVolumeAction*dilation*inverseVolumeAction*positiveBulk)+
      inverseVolumeAction*((44 : ℂ) • ((-(sourceTime 0 : ℂ)/2) • (inverseVolumeAction*
          (compensationGram*gaugeKinetic-gaugeKinetic*compensationGram)))-
        (8 : ℂ) • ((diagonalAction-scalarKinetic-gaugeKinetic)*scalarKinetic-
          scalarKinetic*(diagonalAction-scalarKinetic-gaugeKinetic))+
        (36 : ℂ) • ((diagonalAction-scalarKinetic-gaugeKinetic)*gaugeKinetic-
          gaugeKinetic*(diagonalAction-scalarKinetic-gaugeKinetic))+
        (8 : ℂ) • (diagonalAction*shiftedAction-shiftedAction*diagonalAction)) := by
  rw [original_current_kinetic_source,original_mixed_compensation_current]

end LowEnergy.SourceBrokenGaussCurvatureCurrent
