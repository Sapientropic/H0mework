import H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceClockPhiCoframeForwardCore
import Mathlib.LinearAlgebra.Determinant
import Mathlib.MeasureTheory.Group.Measure

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1500000
set_option maxRecDepth 2048
noncomputable section
namespace LowEnergy.SourceClockPhiCoframeForwardPair
open GaussCoreHilbert GaussCoreDifferential GaussFockPair GaussHistoryHilbert GaussNativeForm
open GaussNativeEnergy GaussLiveMomentum GaussCoframeCore SourceQuantumConfigurationHilbert
open SourceQuantumScalarChart SourceQuantumGaugeSliceCoordinates SourceQuantumFockGauge
open SourceCoframeVolume SourceClockPhiCoframeForwardCore
open MeasureTheory Set Function
open scoped ContDiff Topology InnerProductSpace

private instance coframe_haar : coframeMeasure.IsAddHaarMeasure := by
  unfold coframeMeasure
  infer_instance
private instance scalar_haar : SourceQuantumScalarHilbert.sliceMeasure.IsAddHaarMeasure := by
  unfold SourceQuantumScalarHilbert.sliceMeasure
  infer_instance
private instance coordinate_haar : coordinateGaugeMeasure.IsAddHaarMeasure := by
  unfold coordinateGaugeMeasure
  infer_instance
private instance configuration_haar : GaussHistoryHilbert.configurationMeasure.IsAddHaarMeasure := by
  unfold GaussHistoryHilbert.configurationMeasure
  let _ : (SourceQuantumScalarHilbert.sliceMeasure.prod coordinateGaugeMeasure).IsAddHaarMeasure :=
    Measure.prod.instIsAddHaarMeasure _ _
  exact Measure.prod.instIsAddHaarMeasure _ _

private def coframeDerivative (t : ℝ) (z : SourceCoordinateSlice) : Coframe →L[ℝ] Coframe :=
  (ContinuousLinearMap.fst ℝ Coframe Slice).comp
    ((forwardPointDerivative t z).comp (ContinuousLinearMap.inl ℝ Coframe Slice))

private theorem full_derivative_product (t : ℝ) (z : SourceCoordinateSlice) :
    (forwardPointDerivative t z).toLinearMap=
      LinearMap.prodMap (coframeDerivative t z).toLinearMap (LinearMap.id : Slice →ₗ[ℝ] Slice) := by
  apply LinearMap.ext
  intro x
  apply Prod.ext
  · simp only [forwardPointDerivative,coframeDerivative,ContinuousLinearMap.coe_coe,
      ContinuousLinearMap.prod_apply,add_apply,smul_apply,
      ContinuousLinearMap.coe_fst',ContinuousLinearMap.comp_apply,ContinuousLinearMap.inl_apply,
      ContinuousLinearMap.smulRight_apply,LinearMap.prodMap_apply ]
    rw [volume_derivative,volume_derivative]
  · rfl

private theorem coframe_matrix (t : ℝ) (ht : 0 ≤ t) (z : physicalChart) :
    LinearMap.toMatrix (EuclideanSpace.basisFun (Fin 6) ℝ).toBasis
      (EuclideanSpace.basisFun (Fin 6) ℝ).toBasis (coframeDerivative t z.val).toLinearMap=
      coframeJacobianMatrix t z.val := by
  ext i j
  rw [LinearMap.toMatrix_apply]
  simp only [EuclideanSpace.basisFun_toBasis,PiLp.basisFun_apply,PiLp.basisFun_repr]
  change (coframeDerivative t z.val (EuclideanSpace.single j 1)) i=_
  exact actual_coframe_matrix_reads_DF t ht z i j

theorem actual_full_configuration_jacobian (t : ℝ) (ht : 0 ≤ t) (z : physicalChart) :
    (forwardPointDerivative t z.val).toLinearMap.det=forwardRatio t z.val := by
  rw [full_derivative_product,LinearMap.det_prodMap,LinearMap.det_id,mul_one]
  rw [←LinearMap.det_toMatrix (EuclideanSpace.basisFun (Fin 6) ℝ).toBasis,
    coframe_matrix t ht z,actual_coframe_jacobian_matrix t ht z]

private theorem forward_injOn (t : ℝ) (ht : 0 ≤ t) :
    InjOn (forwardPoint t) (physicalChart : Set SourceCoordinateSlice) := by
  intro x hx y hy he
  have h:=congrArg (backwardPoint t) he
  rw [backward_forward t ht ⟨x,hx⟩,backward_forward t ht ⟨y,hy⟩] at h
  exact h

private theorem density_zero_right (f g : QuantumTest) (z : SourceCoordinateSlice) (hg : g z=0) :
    densityPair f g z=0 := by
  simp only [densityPair_sum,hg,PiLp.zero_apply,mul_zero,Finset.sum_const_zero]

private theorem density_zero_off_chart (f g : QuantumTest) (z : SourceCoordinateSlice)
    (hz : z∉physicalChart) : densityPair f g z=0 := by
  apply density_zero_right
  exact image_eq_zero_of_notMem_tsupport (fun h=>hz (g.tsupport_subset h))

private theorem forward_density_zero_off_image (t : ℝ) (ht : 0 ≤ t) (f g : QuantumTest)
    (z : SourceCoordinateSlice) (hz : z∉forwardPoint t '' (physicalChart : Set SourceCoordinateSlice)) :
    densityPair (sourceForwardCore t ht f) (sourceForwardCore t ht g) z=0 := by
  apply density_zero_right
  apply image_eq_zero_of_notMem_tsupport
  intro h
  have hs:=forward_support t ht g
  change tsupport (sourceForwardCore t ht g)⊆forwardPoint t '' tsupport g at hs
  obtain ⟨x,hx,he⟩:=hs h
  exact hz ⟨x,g.tsupport_subset hx,he⟩

/-- The genuine full configuration Jacobian and original Number density produce the forward core isometry. -/
theorem actual_forward_core_pair (t : ℝ) (ht : 0 ≤ t) (f g : QuantumTest) :
    sourcePair (sourceForwardCore t ht f) (sourceForwardCore t ht g)=sourcePair f g := by
  have hchange:=integral_image_eq_integral_abs_det_fderiv_smul
    GaussHistoryHilbert.configurationMeasure physicalChart.isOpen.measurableSet
    (fun z hz=>(actual_forwardPoint_derivative t ht ⟨z,hz⟩).hasFDerivWithinAt)
    (forward_injOn t ht) (densityPair (sourceForwardCore t ht f) (sourceForwardCore t ht g))
  have hpoint (z : SourceCoordinateSlice) (hz : z∈physicalChart) :
      |(forwardPointDerivative t z).toLinearMap.det| •
        densityPair (sourceForwardCore t ht f) (sourceForwardCore t ht g) (forwardPoint t z)=
          densityPair f g z := by
    rw [actual_full_configuration_jacobian t ht ⟨z,hz⟩,
      abs_of_pos (forward_ratio_pos t ht ⟨z,hz⟩),forwardDensity_return t ht f g ⟨z,hz⟩,
      smul_smul,mul_inv_cancel₀ (forward_ratio_pos t ht ⟨z,hz⟩).ne',one_smul]
  have hp:(∫z : SourceCoordinateSlice in physicalChart,
      |(forwardPointDerivative t z).toLinearMap.det| •
        densityPair (sourceForwardCore t ht f) (sourceForwardCore t ht g) (forwardPoint t z)
        ∂GaussHistoryHilbert.configurationMeasure)=
      ∫z : SourceCoordinateSlice in physicalChart,densityPair f g z
        ∂GaussHistoryHilbert.configurationMeasure :=
    setIntegral_congr_fun physicalChart.isOpen.measurableSet hpoint
  rw [hp] at hchange
  have hleft:(∫z : SourceCoordinateSlice in forwardPoint t '' (physicalChart : Set SourceCoordinateSlice),
      densityPair (sourceForwardCore t ht f) (sourceForwardCore t ht g) z
        ∂GaussHistoryHilbert.configurationMeasure)=
      ∫z : SourceCoordinateSlice,densityPair (sourceForwardCore t ht f) (sourceForwardCore t ht g) z
        ∂GaussHistoryHilbert.configurationMeasure :=
    setIntegral_eq_integral_of_forall_compl_eq_zero (forward_density_zero_off_image t ht f g)
  have hright:(∫z : SourceCoordinateSlice in physicalChart,densityPair f g z
      ∂GaussHistoryHilbert.configurationMeasure)=
      ∫z : SourceCoordinateSlice,densityPair f g z ∂GaussHistoryHilbert.configurationMeasure :=
    setIntegral_eq_integral_of_forall_compl_eq_zero (density_zero_off_chart f g)
  rw [hleft,hright] at hchange
  rw [sourcePair_integral,sourcePair_integral]
  exact hchange


end LowEnergy.SourceClockPhiCoframeForwardPair
