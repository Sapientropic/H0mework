import H0mework.Versions.AE.Physics.LowEnergy.Quantum.SourceInverseVolumeNativeDensityTrace
import H0mework.Versions.AE.Physics.LowEnergy.Quantum.SourceInverseVolumeNativeTraceContraction

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1200000
set_option maxRecDepth 2048
noncomputable section
namespace LowEnergy.SourceIntrinsicJointCancellation
open GaussLiveMomentum GaussInverseSecond GaussCoreDifferential GaussCoreHilbert GaussHistoryHilbert
open GaussNativeForm GaussNativeEnergy GaussFockPair
open SourceQuantumScalarChart SourceQuantumConfigurationHilbert SourceQuantumGaugeSliceCoordinates
open SourceNativeMomentumCurvature SourceNativeDensityTrace SourceDoubleGramCurvatureForm
open SourceJointScalarGaugeCoefficientForm
open SaturationMonoid.PhysicsCore StageNineHolonomicField StageNineP286BracketCalculus
open StageNineP286GaugeConnectionVariationDensity StageNineP286LinkedActiveLieRepresentation
open SourceQuantumFockGauge SourceQuantumResidualGaugeSlice
open scoped ContDiff InnerProductSpace Topology

/-- The actual horizontal complement of the inverse-source direction. -/
def sourceHorizontal (u : Ambient) (z : SourceCoordinateSlice) : Ambient :=
  sliceMap (inverseL z u).2

private theorem inverse_lie_derivative (u : Ambient) (z : physicalChart) (h : SourceCoordinateSlice) :
    fderiv ℝ (fun x => inverseLie x u) z.val h=(fderiv ℝ inverseL z.val h u).1 := by
  have hi := ((inverse_smooth z).differentiableAt (by simp)).hasFDerivAt
  have hv := (hi.clm_apply (hasFDerivAt_const u z.val)).fst
  have he := congrArg (fun D : SourceCoordinateSlice →L[ℝ] NativeLie => D h) hv.fderiv
  simp only [ContinuousLinearMap.comp_apply,ContinuousLinearMap.coe_fst',ContinuousLinearMap.flip_apply,
    add_apply,zero_apply,map_zero,zero_add] at he
  exact he

private theorem inverse_lie_source (u v : Ambient) (z : physicalChart) :
    fderiv ℝ (fun x => inverseLie x v) z.val (direction u z.val)=
      -sourceLieResponse (sourceHorizontal u z.val) z.val (inverseLie z.val v) := by
  rw [inverse_lie_derivative,inverse_derivative]
  rfl

private theorem response_trace_sum (v : Ambient) (z : SourceCoordinateSlice) :
    intrinsicDensity v z=∑ b : LieIndex,inner ℝ (lieBasis b) (inverseLie z (nativeRead v (lieBasis b))) := by
  rw [intrinsicDensity,LinearMap.trace_eq_matrix_trace ℝ lieBasis.toBasis]
  simp only [Matrix.trace,Matrix.diag,LinearMap.toMatrix_apply,
    OrthonormalBasis.coe_toBasis_repr_apply,OrthonormalBasis.coe_toBasis,OrthonormalBasis.repr_apply_apply]
  rfl

/-- The derivative of the true inverse-source trace is another trace on that same source. -/
theorem original_intrinsic_density_derivative (u v : Ambient) (z : physicalChart) :
    fderiv ℝ (intrinsicDensity v) z.val (direction u z.val)=
      -LinearMap.trace ℝ NativeLie ((sourceLieResponse (sourceHorizontal u z.val) z.val).comp (sourceLieResponse v z.val)) := by
  have he : intrinsicDensity v=(fun x => ∑ b : LieIndex,
      inner ℝ (lieBasis b) (inverseLie x (nativeRead v (lieBasis b)))) := funext (response_trace_sum v)
  have hb (b : LieIndex) : DifferentiableAt ℝ (fun x => inverseLie x (nativeRead v (lieBasis b))) z.val :=
    (((inverse_smooth z).differentiableAt (by simp)).clm_apply (differentiableAt_const _)).fst
  have hd (b : LieIndex) : fderiv ℝ (fun x => inner ℝ (lieBasis b)
      (inverseLie x (nativeRead v (lieBasis b)))) z.val (direction u z.val)=
      -inner ℝ (lieBasis b) (sourceLieResponse (sourceHorizontal u z.val) z.val
        (inverseLie z.val (nativeRead v (lieBasis b)))) := by
    have hh := (innerSL ℝ (lieBasis b)).hasFDerivAt.comp z.val (hb b).hasFDerivAt
    have hv := congrArg (fun D : SourceCoordinateSlice →L[ℝ] ℝ => D (direction u z.val)) hh.fderiv
    change fderiv ℝ (fun x => inner ℝ (lieBasis b) (inverseLie x (nativeRead v (lieBasis b)))) z.val
      (direction u z.val)=inner ℝ (lieBasis b) (fderiv ℝ (fun x => inverseLie x (nativeRead v (lieBasis b))) z.val (direction u z.val)) at hv
    rw [hv,inverse_lie_source,inner_neg_right]
  rw [he,fderiv_fun_sum (fun b _ => (differentiableAt_const (lieBasis b)).inner ℝ (hb b))]
  simp only [sum_apply,hd,Finset.sum_neg_distrib]
  rw [LinearMap.trace_eq_matrix_trace ℝ lieBasis.toBasis]
  simp only [Matrix.trace,Matrix.diag,LinearMap.toMatrix_apply,
    OrthonormalBasis.coe_toBasis_repr_apply,OrthonormalBasis.coe_toBasis,OrthonormalBasis.repr_apply_apply,
    LinearMap.comp_apply,sourceLieResponse]

private theorem scalar_rotation_derivative (u : Ambient) (s r : ScalarIndex) (z : physicalChart) (h : SourceCoordinateSlice) :
    fderiv ℝ (scalarRotation u s r) z.val h=
      inner ℝ (scalarBasis s) (scalarP286ActionBilinear (fderiv ℝ inverseL z.val h u).1 (scalarBasis r)) := by
  let L : NativeLie →L[ℝ] Scalar := (action (scalarBasis r)).toContinuousLinearMap
  have hi := (((inverse_smooth z).differentiableAt (by simp)).hasFDerivAt.clm_apply
    (hasFDerivAt_const u z.val)).fst
  have ha := L.hasFDerivAt.comp z.val hi
  have hh := (innerSL ℝ (scalarBasis s)).hasFDerivAt.comp z.val ha
  have hv := congrArg (fun D : SourceCoordinateSlice →L[ℝ] ℝ => D h) hh.fderiv
  simp only [ContinuousLinearMap.comp_apply,ContinuousLinearMap.coe_fst',
    ContinuousLinearMap.flip_apply,add_apply,zero_apply,map_zero,zero_add] at hv
  change fderiv ℝ (scalarRotation u s r) z.val h=
    inner ℝ (scalarBasis s) (scalarP286ActionBilinear (fderiv ℝ inverseL z.val h u).1 (scalarBasis r)) at hv
  exact hv

/-- The derivative and gauge-rotation contribution combine before any norm or trace estimate. -/
theorem original_scalar_gauge_connection_difference (u v : Ambient) (z : physicalChart) :
    (fderiv ℝ inverseL z.val (direction u z.val) v).1-inverseLie z.val (ambientAction (inverseLie z.val u) v)=
      -inverseLie z.val (ambientAction (inverseLie z.val v) u)+
        nativeBracket (inverseLie z.val v) (inverseLie z.val u)-
        sourceLieResponse (sourceHorizontal v z.val) z.val (inverseLie z.val u) := by
  have h := congrArg Prod.fst (original_inverse_curvature z u v)
  have hd := inverse_lie_source v u z
  rw [inverse_lie_derivative] at hd
  have hb : nativeBracket (inverseLie z.val u) (inverseLie z.val v)=
      -nativeBracket (inverseLie z.val v) (inverseLie z.val u) := coordinateBracket_skew _ _
  change (fderiv ℝ inverseL z.val (direction u z.val) v).1-
    (fderiv ℝ inverseL z.val (direction v z.val) u).1=
      inverseLie z.val (ambientAction (inverseLie z.val u) v-ambientAction (inverseLie z.val v) u)-
        nativeBracket (inverseLie z.val u) (inverseLie z.val v) at h
  rw [map_sub,hd,hb] at h
  linear_combination (norm := module) h


open SourceNativeTraceContraction

def scalarRead (z : SourceCoordinateSlice) : Scalar →ₗ[ℝ] NativeLie :=
  (inverseLie z).comp (LinearMap.inl ℝ Scalar Gauge)

private theorem scalar_response (s : Scalar) (z : SourceCoordinateSlice) :
    sourceLieResponse (s,0) z=(scalarRead z).comp (action s) := by
  ext a
  change inverseLie z (scalarP286ActionBilinear a s,nativeGauge a 0)=inverseLie z (scalarP286ActionBilinear a s,0)
  rw [map_zero]

private def gaugeInsert (j : Fin 3) : NativeLie →ₗ[ℝ] Gauge :=
  gaugeCoordinates.symm.toLinearMap.comp (LinearMap.single ℝ (fun _ : Fin 3 => NativeLie) j)

private theorem gauge_insert_bracket (j : Fin 3) (a b : NativeLie) :
    nativeGauge a (gaugeInsert j b)=gaugeInsert j (SourceCartanCubic.nativeBracket a b) := by
  apply gaugeCoordinates.injective
  funext k
  have hg (x : NativeLie) : gaugeCoordinates (gaugeInsert j x)=Pi.single j x := by
    change gaugeCoordinates (gaugeCoordinates.symm (Pi.single j x))=_
    rw [gaugeCoordinates.apply_symm_apply]
  have hn (x : Gauge) : gaugeCoordinates (nativeGauge a x) k=
      SourceCartanCubic.nativeBracket a (gaugeCoordinates x k) := rfl
  rw [hn,hg,hg]
  by_cases h : k=j
  · subst k
    simp only [Pi.single_eq_same]
  · simp only [Pi.single_eq_of_ne h,map_zero]

private theorem gauge_rotation_source (r : ScalarIndex) (j : Fin 3) (a : LieIndex) (z : SourceCoordinateSlice) :
    ambientAction (inverseLie z (scalarDirection r)) (gaugeDirection j a)=
      ∑ b : LieIndex,gaugeRotation r b a z • gaugeDirection j b := by
  have hg : nativeGauge (inverseL z (scalarDirection r)).1 (gaugeDirection j a).2=
      ∑ b : LieIndex,gaugeRotation r b a z • (gaugeDirection j b).2 := by
    change nativeGauge (inverseL z (scalarDirection r)).1 (gaugeInsert j (lieBasis a))=_
    rw [gauge_insert_bracket]
    have h := congrArg (gaugeInsert j) (lieBasis.sum_repr'
      (SourceCartanCubic.nativeBracket (inverseL z (scalarDirection r)).1 (lieBasis a)))
    simp only [map_sum,map_smul] at h
    exact h.symm
  apply Prod.ext
  · simp only [ambientAction,LinearMap.prodMap_apply,gaugeDirection,map_zero,Prod.fst_sum,Prod.smul_fst,smul_zero,Finset.sum_const_zero]
  · change nativeGauge (inverseL z (scalarDirection r)).1 (gaugeDirection j a).2=
      (∑ b : LieIndex,gaugeRotation r b a z • gaugeDirection j b).2
    simpa only [Prod.snd_sum,Prod.smul_snd] using hg

private theorem gauge_rotation_contraction (r s : ScalarIndex) (j : Fin 3) (a : LieIndex) (z : SourceCoordinateSlice) :
    (∑ b : LieIndex,gaugeRotation r b a z*scalarRotation (gaugeDirection j b) s r z)=
      inner ℝ (scalarBasis s) (scalarP286ActionBilinear
        (inverseLie z (ambientAction (inverseLie z (scalarDirection r)) (gaugeDirection j a))) (scalarBasis r)) := by
  change _=inner ℝ (scalarBasis s) (action (scalarBasis r)
    (inverseLie z (ambientAction (inverseLie z (scalarDirection r)) (gaugeDirection j a))))
  rw [gauge_rotation_source,map_sum,map_sum]
  simp only [map_smul,inner_sum,inner_smul_right]
  rfl

private theorem intrinsic_vector_cancellation (n : Scalar →ₗ[ℝ] NativeLie) (a : NativeLie) :
    (∑ r : ScalarIndex,(
      -scalarP286ActionBilinear (n (scalarP286ActionBilinear a (scalarBasis r))) (scalarBasis r)+
      scalarP286ActionBilinear (nativeBracket a (n (scalarBasis r))) (scalarBasis r)+
      LinearMap.trace ℝ NativeLie (n.comp (action (scalarBasis r))) • scalarP286ActionBilinear a (scalarBasis r)))=0 := by
  have hb (b : NativeLie) (s : Scalar) : scalarP286ActionBilinear (nativeBracket a b) s=
      scalarP286ActionBilinear a (scalarP286ActionBilinear b s)-
      scalarP286ActionBilinear b (scalarP286ActionBilinear a s) :=
    scalarP286ActionBilinear_coordinateBracket a b s
  have ht := congrArg (scalarP286ActionBilinear a) (original_trace_vector n)
  simp only [map_sum,map_smul,map_neg] at ht
  simp only [hb,Finset.sum_add_distrib,Finset.sum_sub_distrib,Finset.sum_neg_distrib]
  rw [original_skew_frame_contraction n a,ht]
  module

/-- The intrinsic scalar/gauge coefficient vanishes by the same inverse-source trace contractions. -/
theorem original_intrinsic_joint_coefficient_zero (j : Fin 3) (a : LieIndex) (s : ScalarIndex) (z : physicalChart) :
    intrinsicJointCoefficient j a s z.val=0 := by
  let g := gaugeDirection j a
  let ag := inverseLie z.val g
  let n := scalarRead z.val
  let M := sourceLieResponse (sourceHorizontal g z.val) z.val
  have hs (r : ScalarIndex) : sourceLieResponse (scalarDirection r) z.val=n.comp (action (scalarBasis r)) :=
    scalar_response (scalarBasis r) z.val
  have hn (r : ScalarIndex) : inverseLie z.val (scalarDirection r)=n (scalarBasis r) := rfl
  have ha (r : ScalarIndex) : inverseLie z.val (ambientAction ag (scalarDirection r))=
      n (scalarP286ActionBilinear ag (scalarBasis r)) := by
    simp only [ambientAction,LinearMap.prodMap_apply,scalarDirection,map_zero]
    rfl
  have ht : fderiv ℝ (intrinsicDensity (scalarDirection s)) z.val (direction g z.val)=
      ∑ r : ScalarIndex,inner ℝ (scalarBasis s) (scalarP286ActionBilinear (M (n (scalarBasis r))) (scalarBasis r)) := by
    rw [original_intrinsic_density_derivative,hs]
    change -LinearMap.trace ℝ NativeLie (M.comp (n.comp (action (scalarBasis s))))=_
    rw [original_trace_contraction,neg_neg]
  have hr (r : ScalarIndex) :
      fderiv ℝ (scalarRotation g s r) z.val (direction (scalarDirection r) z.val)-
        (∑ b : LieIndex,gaugeRotation r b a z.val*scalarRotation (gaugeDirection j b) s r z.val)=
      inner ℝ (scalarBasis s) (
        -scalarP286ActionBilinear (n (scalarP286ActionBilinear ag (scalarBasis r))) (scalarBasis r)+
        scalarP286ActionBilinear (nativeBracket ag (n (scalarBasis r))) (scalarBasis r)-
        scalarP286ActionBilinear (M (n (scalarBasis r))) (scalarBasis r)) := by
    rw [scalar_rotation_derivative,gauge_rotation_contraction]
    have hsource := original_scalar_gauge_connection_difference (scalarDirection r) g z
    change (fderiv ℝ inverseL z.val (direction (scalarDirection r) z.val) g).1-
      inverseLie z.val (ambientAction (inverseLie z.val (scalarDirection r)) g)=
      -inverseLie z.val (ambientAction ag (scalarDirection r))+
        nativeBracket ag (inverseLie z.val (scalarDirection r))-M (inverseLie z.val (scalarDirection r)) at hsource
    rw [ha,hn] at hsource
    have h := congrArg (action (scalarBasis r)) hsource
    simp only [map_sub,map_add,map_neg] at h
    have hinner := congrArg (fun x => inner ℝ (scalarBasis s) x) h
    simp only [inner_sub_right,inner_add_right,inner_neg_right] at hinner ⊢
    exact hinner
  have hv := congrArg (fun x => inner ℝ (scalarBasis s) x) (intrinsic_vector_cancellation n ag)
  simp only [inner_sum,inner_add_right,inner_neg_right,inner_smul_right,inner_zero_right] at hv
  unfold intrinsicJointCoefficient
  have he (r : ScalarIndex) :
      fderiv ℝ (scalarRotation g s r) z.val (direction (scalarDirection r) z.val)+
        intrinsicDensity (scalarDirection r) z.val*scalarRotation g s r z.val-
        (∑ b : LieIndex,gaugeRotation r b a z.val*scalarRotation (gaugeDirection j b) s r z.val)=
      (fderiv ℝ (scalarRotation g s r) z.val (direction (scalarDirection r) z.val)-
        (∑ b : LieIndex,gaugeRotation r b a z.val*scalarRotation (gaugeDirection j b) s r z.val))+
        intrinsicDensity (scalarDirection r) z.val*scalarRotation g s r z.val := by ring
  change (∑ r : ScalarIndex,(
    fderiv ℝ (scalarRotation g s r) z.val (direction (scalarDirection r) z.val)+
      intrinsicDensity (scalarDirection r) z.val*scalarRotation g s r z.val-
      ∑ b : LieIndex,gaugeRotation r b a z.val*scalarRotation (gaugeDirection j b) s r z.val))+
    fderiv ℝ (intrinsicDensity (scalarDirection s)) z.val (direction g z.val)=0
  simp_rw [he]
  simp_rw [hr]
  rw [ht]
  simp only [inner_sub_right,inner_add_right,inner_neg_right,Finset.sum_add_distrib,Finset.sum_sub_distrib]
  have hd (r : ScalarIndex) : intrinsicDensity (scalarDirection r) z.val=
      LinearMap.trace ℝ NativeLie (n.comp (action (scalarBasis r))) := congrArg (LinearMap.trace ℝ NativeLie) (hs r)
  simp_rw [hd]
  change _=0 at hv
  simp only [Finset.sum_add_distrib] at hv
  change (∑ r : ScalarIndex,-inner ℝ (scalarBasis s) (scalarP286ActionBilinear (n (scalarP286ActionBilinear ag (scalarBasis r))) (scalarBasis r)))+
    (∑ r : ScalarIndex,inner ℝ (scalarBasis s) (scalarP286ActionBilinear (nativeBracket ag (n (scalarBasis r))) (scalarBasis r)))-
    (∑ r : ScalarIndex,inner ℝ (scalarBasis s) (scalarP286ActionBilinear (M (n (scalarBasis r))) (scalarBasis r)))+
    (∑ r : ScalarIndex,LinearMap.trace ℝ NativeLie (n.comp (action (scalarBasis r)))*inner ℝ (scalarBasis s) (scalarP286ActionBilinear ag (scalarBasis r)))+
    (∑ r : ScalarIndex,inner ℝ (scalarBasis s) (scalarP286ActionBilinear (M (n (scalarBasis r))) (scalarBasis r)))=0
  linarith


/-- The complete original Number-weighted joint coefficient vanishes on the actual source chart. -/
theorem original_joint_coefficient_zero (N : ℕ) (j : Fin 3) (a : LieIndex) (s : ScalarIndex) (z : physicalChart) :
    jointCoefficient N j a s z.val=0 := by
  rw [original_joint_density_cancellation,original_intrinsic_joint_coefficient_zero,Complex.ofReal_zero]

/-- The actual joint scalar/gauge row vanishes as a core operator, including its density and curvature contacts. -/
theorem original_joint_scalar_gauge_row_zero (j : Fin 3) (a : LieIndex) :
    jointScalarGaugeRow j a=0 := by
  apply LinearMap.ext
  intro f
  apply DFunLike.ext
  intro z
  change jointScalarGaugeRow j a f z=0
  by_cases hz : z ∈ physicalChart
  · rw [original_intrinsic_joint_row j a f ⟨z,hz⟩]
    apply Finset.sum_eq_zero
    intro s _
    rw [original_intrinsic_joint_coefficient_zero j a s ⟨z,hz⟩,Complex.ofReal_zero,zero_smul]
  · exact image_eq_zero_of_notMem_tsupport (fun h => hz ((jointScalarGaugeRow j a f).tsupport_subset h))

/-- The same source joint form has no scalar/gauge mixed contribution. -/
theorem original_joint_scalar_gauge_form_zero (f : QuantumTest) : jointScalarGaugeForm f=0 := by
  unfold jointScalarGaugeForm jointScalarGaugePair
  simp only [original_joint_scalar_gauge_row_zero,LinearMap.zero_apply,map_zero,sourcePair,
    inner_zero_right,Finset.sum_const_zero,Complex.zero_im,zero_div]

/-- The literal signed mixed44 bulk current is eliminated without a norm estimate. -/
theorem original_mixed44_current_zero (f : QuantumTest) :
    (sourcePair f (((44 : ℂ) • (SourcePhysicalKineticSquare.inverseVolumeAction*
      (scalarKinetic*gaugeKinetic-gaugeKinetic*scalarKinetic))) f)).im/2=0 := by
  rw [original_mixed44_joint_scalar_gauge_form,original_joint_scalar_gauge_form_zero,mul_zero]

end LowEnergy.SourceIntrinsicJointCancellation
